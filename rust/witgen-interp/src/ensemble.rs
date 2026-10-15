//! Whole-ensemble checking over native Clean rows.
//!
//! Unlike the SP1 row-map conformance path, this checker evaluates fixed lookups,
//! full interaction messages, the public verifier row, and every channel's balance.
//! The instance is the trusted circuit/fixed-table description; the trace is untrusted.
//! This is an executable AIR checker, not a cryptographic proof verifier or a proof
//! that the instance implements RISC-V. Rust correctness is a tested trust boundary.

use crate::eval::{eval_expr, witgen, Ctx, Tables};
use crate::field::Field;
use crate::wire::{Expr, Op, Program};
use std::collections::{HashMap, HashSet};

#[derive(Clone, Debug)]
pub struct Component {
    pub name: String,
    pub input_width: usize,
    pub program: Program,
}

#[derive(Clone, Debug)]
pub struct Channel {
    pub name: String,
    pub width: usize,
}

#[derive(Clone, Debug)]
pub struct FixedTable {
    pub name: String,
    pub width: usize,
    pub rows: Vec<Vec<u64>>,
}

/// A complete, explicitly ordered native ensemble description.
#[derive(Clone, Debug)]
pub struct Instance {
    pub modulus: u64,
    pub components: Vec<Component>,
    pub verifier: Component,
    pub channels: Vec<Channel>,
    pub fixed_tables: Vec<FixedTable>,
}

/// Table and row order agree with the instance. The verifier has exactly one row,
/// supplied separately as `public_input`, and generates no additional cells.
#[derive(Clone, Debug)]
pub struct Trace {
    pub public_input: Vec<u64>,
    pub tables: Vec<Vec<Vec<u64>>>,
}

/// Inputs and hints for one row; witness cells are constructed by the IR interpreter.
#[derive(Clone, Debug)]
pub struct RowInput<F> {
    pub cells: Vec<F>,
    pub hints: Tables<F>,
}

fn row_width(component: &Component) -> Result<usize, String> {
    component
        .input_width
        .checked_add(component.program.local_length)
        .ok_or_else(|| format!("{}: row width overflow", component.name))
}

fn validate_expr(expr: &Expr, width: usize, modulus: u64) -> Result<(), String> {
    match expr {
        Expr::Var(index) if *index >= width => {
            Err(format!("cell {index} outside row width {width}"))
        }
        Expr::Const(value) if *value >= modulus => Err("noncanonical field constant".into()),
        Expr::Add(left, right) | Expr::Mul(left, right) => {
            validate_expr(left, width, modulus)?;
            validate_expr(right, width, modulus)
        }
        _ => Ok(()),
    }
}

fn canonical_row<F: Field>(row: &[u64], width: usize) -> Result<Vec<F>, String> {
    if row.len() != width {
        return Err(format!("row width {} does not match {width}", row.len()));
    }
    row.iter()
        .map(|value| {
            if *value >= F::MODULUS {
                Err(format!("noncanonical field element {value}"))
            } else {
                Ok(F::from_u64(*value))
            }
        })
        .collect()
}

impl Instance {
    /// Check the schema even when the trace contains no rows. Missing providers,
    /// ambiguous names, and malformed operations cannot hide in inactive tables.
    pub fn validate<F: Field>(&self) -> Result<(), String> {
        if self.modulus != F::MODULUS {
            return Err("instance field does not match interpreter field".into());
        }
        if self.verifier.program.local_length != 0 {
            return Err("verifier must not generate witness cells".into());
        }
        let mut channels = HashMap::new();
        for channel in &self.channels {
            if channel.name.is_empty()
                || channels
                    .insert(channel.name.as_str(), channel.width)
                    .is_some()
            {
                return Err("empty or duplicate channel name".into());
            }
        }
        let mut fixed = HashMap::new();
        for table in &self.fixed_tables {
            if table.name.is_empty() || fixed.insert(table.name.as_str(), table.width).is_some() {
                return Err("empty or duplicate fixed-table name".into());
            }
            for row in &table.rows {
                canonical_row::<F>(row, table.width)?;
            }
        }
        let mut names = HashSet::new();
        for component in self
            .components
            .iter()
            .chain(std::iter::once(&self.verifier))
        {
            if component.name.is_empty() || !names.insert(&component.name) {
                return Err("empty or duplicate component name".into());
            }
            let width = row_width(component)?;
            let mut witnesses = 0usize;
            for op in &component.program.ops {
                match op {
                    Op::Witness { m, .. } => {
                        witnesses = witnesses.checked_add(*m).ok_or("witness width overflow")?;
                    }
                    Op::Assert(expr) => validate_expr(expr, width, self.modulus)?,
                    Op::Lookup { table, entry } => {
                        if fixed.get(table.as_str()) != Some(&entry.len()) {
                            return Err(format!("missing or wrong-width fixed lookup {table}"));
                        }
                        for expr in entry {
                            validate_expr(expr, width, self.modulus)?;
                        }
                    }
                    Op::Interact {
                        channel,
                        multiplicity,
                        message,
                    } => {
                        if channels.get(channel.as_str()) != Some(&message.len()) {
                            return Err(format!("unknown or wrong-width channel {channel}"));
                        }
                        validate_expr(multiplicity, width, self.modulus)?;
                        for expr in message {
                            validate_expr(expr, width, self.modulus)?;
                        }
                    }
                }
            }
            if witnesses != component.program.local_length {
                return Err(format!(
                    "{}: witness size disagrees with localLength",
                    component.name
                ));
            }
        }
        Ok(())
    }

    /// Evaluate all rows and the public verifier, then check exact field balance.
    /// Zero-multiplicity interactions still count towards Clean's length bound.
    pub fn check_trace<F: Field>(&self, trace: &Trace) -> Result<(), String> {
        self.validate::<F>()?;
        if trace.tables.len() != self.components.len() {
            return Err("trace table count does not match ensemble".into());
        }
        let fixed: HashMap<_, HashSet<_>> = self
            .fixed_tables
            .iter()
            .map(|table| (table.name.as_str(), table.rows.iter().cloned().collect()))
            .collect();
        let mut counts: HashMap<&str, u64> = self
            .channels
            .iter()
            .map(|channel| (channel.name.as_str(), 0))
            .collect();
        let mut balances: HashMap<(String, Vec<u64>), F> = HashMap::new();
        let empty = Tables::default();
        let mut check_row = |component: &Component, raw: &[u64]| -> Result<(), String> {
            let cells = canonical_row::<F>(raw, row_width(component)?)?;
            let ctx = Ctx {
                cells: &cells,
                locals: &[],
                idx: 0,
                hints: &empty,
                data: &empty,
            };
            for (index, op) in component.program.ops.iter().enumerate() {
                match op {
                    Op::Witness { .. } => {}
                    Op::Assert(expr) => {
                        if eval_expr(ctx, expr) != F::zero() {
                            return Err(format!(
                                "{} operation {index}: assertion failed",
                                component.name
                            ));
                        }
                    }
                    Op::Lookup { table, entry } => {
                        let values: Vec<_> = entry
                            .iter()
                            .map(|expr| eval_expr(ctx, expr).val())
                            .collect();
                        if !fixed[table.as_str()].contains(&values) {
                            return Err(format!(
                                "{} operation {index}: lookup {table} failed",
                                component.name
                            ));
                        }
                    }
                    Op::Interact {
                        channel,
                        multiplicity,
                        message,
                    } => {
                        let count = counts.get_mut(channel.as_str()).expect("validated channel");
                        *count = count.checked_add(1).ok_or("interaction count overflow")?;
                        if *count >= F::MODULUS {
                            return Err(format!(
                                "channel {channel}: interaction count reaches field characteristic"
                            ));
                        }
                        let values: Vec<_> = message
                            .iter()
                            .map(|expr| eval_expr(ctx, expr).val())
                            .collect();
                        let key = (channel.clone(), values);
                        let total = balances.entry(key).or_insert_with(F::zero);
                        *total = total.add(eval_expr(ctx, multiplicity));
                    }
                }
            }
            Ok(())
        };
        for (component, rows) in self.components.iter().zip(&trace.tables) {
            for (index, row) in rows.iter().enumerate() {
                check_row(component, row).map_err(|error| format!("row {index}: {error}"))?;
            }
        }
        check_row(&self.verifier, &trace.public_input)?;
        for ((channel, message), total) in balances {
            if total != F::zero() {
                return Err(format!("channel {channel}: unbalanced message {message:?}"));
            }
        }
        Ok(())
    }

    /// Generate witness cells for already assembled table inputs and check the
    /// resulting complete ensemble. Event routing/provider recipes are a separate
    /// producer of `inputs`; this function does not pretend to infer missing tables.
    pub fn build_rows<F: Field>(
        &self,
        public_input: &[F],
        inputs: &[Vec<RowInput<F>>],
        data: &Tables<F>,
    ) -> Result<Trace, String> {
        self.validate::<F>()?;
        if inputs.len() != self.components.len() {
            return Err("input table count does not match ensemble".into());
        }
        let mut tables = Vec::with_capacity(inputs.len());
        for (component, rows) in self.components.iter().zip(inputs) {
            let mut table = Vec::with_capacity(rows.len());
            for row in rows {
                if row.cells.len() != component.input_width {
                    return Err(format!("{}: incorrect input width", component.name));
                }
                let (cells, _) = witgen(&component.program, &row.cells, &row.hints, data)?;
                table.push(cells.into_iter().map(Field::val).collect());
            }
            tables.push(table);
        }
        let trace = Trace {
            public_input: public_input.iter().map(|value| value.val()).collect(),
            tables,
        };
        self.check_trace::<F>(&trace)?;
        Ok(trace)
    }
}

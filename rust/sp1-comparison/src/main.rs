//! Independent inventory from the released SP1 machine, including mode-associated columns.

use serde::{Deserialize, Serialize};
use slop_air::BaseAir;
use slop_algebra::PrimeField64;
use sp1_core_machine::{riscv::RiscvAir, SupervisorMode, TrustMode, UserMode};
use sp1_hypercube::air::MachineAir;
use sp1_primitives::SP1Field;
use std::{collections::BTreeMap, mem::size_of};

#[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Table {
    name: String,
    main_width: usize,
    preprocessed_width: usize,
}

#[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct ModeColumns {
    adapter: usize,
    syscall_instruction: usize,
    slice_protection: usize,
    alu_x0_selectors: usize,
    trap_code: usize,
}

impl ModeColumns {
    fn of<M: TrustMode>() -> Self {
        // SP1 uses byte-instantiated repr(C) structs to count field columns.
        Self {
            adapter: size_of::<M::AdapterCols<u8>>(),
            syscall_instruction: size_of::<M::SyscallInstrCols<u8>>(),
            slice_protection: size_of::<M::SliceProtCols<u8>>(),
            alu_x0_selectors: size_of::<M::AluX0SelectorCols<u8>>(),
            trap_code: size_of::<M::TrapCodeCols<u8>>(),
        }
    }
}

#[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Inventory {
    mprotect: bool,
    field_modulus: u64,
    num_public_values: usize,
    supervisor_columns: ModeColumns,
    user_columns: ModeColumns,
    /// Shared layouts; each cluster entry below is an index, preserving order and repetitions.
    layouts: Vec<Table>,
    clusters: Vec<Vec<usize>>,
}

fn inventory() -> Inventory {
    let machine = RiscvAir::<SP1Field>::machine();
    let mut indices = BTreeMap::new();
    let mut layouts = Vec::new();
    let clusters = machine
        .shape()
        .chip_clusters
        .iter()
        .map(|cluster| {
            cluster
                .iter()
                .map(|chip| {
                    let name = chip.name().to_string();
                    let main_width = chip.width();
                    let preprocessed_width = chip.preprocessed_width();
                    *indices
                        .entry((name.clone(), main_width, preprocessed_width))
                        .or_insert_with(|| {
                            let index = layouts.len();
                            layouts.push(Table {
                                name,
                                main_width,
                                preprocessed_width,
                            });
                            index
                        })
                })
                .collect()
        })
        .collect();
    Inventory {
        mprotect: cfg!(feature = "mprotect"),
        field_modulus: SP1Field::ORDER_U64,
        num_public_values: machine.num_pv_elts(),
        supervisor_columns: ModeColumns::of::<SupervisorMode>(),
        user_columns: ModeColumns::of::<UserMode>(),
        layouts,
        clusters,
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    if std::env::args().len() != 1 {
        return Err(
            "usage: sp1-clean-comparison (configuration is selected through Cargo features)".into(),
        );
    }
    serde_json::to_writer_pretty(std::io::stdout().lock(), &inventory())?;
    println!();
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn released_inventory_matches_reviewed_snapshot() {
        let snapshot = if cfg!(feature = "mprotect") {
            include_str!("../inventory/mprotect.json")
        } else {
            include_str!("../inventory/supervisor.json")
        };
        let expected: Inventory = serde_json::from_str(snapshot).unwrap();
        assert_eq!(inventory(), expected);
    }

    #[test]
    fn mode_columns_are_static_and_not_runtime_options() {
        let inventory = inventory();
        assert_eq!(
            inventory.supervisor_columns,
            ModeColumns {
                adapter: 0,
                syscall_instruction: 0,
                slice_protection: 0,
                alu_x0_selectors: 0,
                trap_code: 0,
            }
        );
        assert_eq!(
            inventory.user_columns,
            ModeColumns {
                adapter: 1,
                syscall_instruction: 52,
                slice_protection: 24,
                alu_x0_selectors: 33,
                trap_code: 1,
            }
        );
    }
}

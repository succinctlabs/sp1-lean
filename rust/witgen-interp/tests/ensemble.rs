use witgen_interp::ensemble::{Channel, Component, FixedTable, Instance, RowInput, Trace};
use witgen_interp::eval::Tables;
use witgen_interp::field::{Field, KoalaBear as F};
use witgen_interp::wire::{parse_program, Expr, FExpr, Op, Program, VExpr};

fn component(name: &str, ops: Vec<Op>) -> Component {
    Component {
        name: name.into(),
        input_width: 1,
        program: Program {
            local_length: 0,
            ops,
        },
    }
}

fn interaction(mult: u64) -> Op {
    Op::Interact {
        channel: "values".into(),
        multiplicity: Expr::Const(mult),
        message: vec![Expr::Var(0)],
    }
}

fn instance() -> Instance {
    Instance {
        modulus: F::MODULUS,
        components: vec![component(
            "provider",
            vec![
                Op::Lookup {
                    table: "allowed".into(),
                    entry: vec![Expr::Var(0)],
                },
                interaction(1),
            ],
        )],
        verifier: component("public", vec![interaction(F::MODULUS - 1)]),
        channels: vec![Channel {
            name: "values".into(),
            width: 1,
        }],
        fixed_tables: vec![FixedTable {
            name: "allowed".into(),
            width: 1,
            rows: vec![vec![7], vec![9]],
        }],
    }
}

fn trace() -> Trace {
    Trace {
        public_input: vec![7],
        tables: vec![vec![vec![7]]],
    }
}

#[test]
fn whole_ensemble_checks_public_binding_and_fixed_membership() {
    let instance = instance();
    assert!(instance.check_trace::<F>(&trace()).is_ok());
    let mut wrong_public = trace();
    wrong_public.public_input = vec![9];
    assert!(instance
        .check_trace::<F>(&wrong_public)
        .unwrap_err()
        .contains("unbalanced"));
    let forged = Trace {
        public_input: vec![8],
        tables: vec![vec![vec![8]]],
    };
    assert!(instance
        .check_trace::<F>(&forged)
        .unwrap_err()
        .contains("lookup"));
}

#[test]
fn missing_duplicate_and_malformed_schema_is_rejected_before_rows() {
    for mutation in 0..8 {
        let mut instance = instance();
        match mutation {
            0 => instance.fixed_tables.clear(),
            1 => instance.channels.clear(),
            2 => instance.channels.push(instance.channels[0].clone()),
            3 => instance.fixed_tables.push(instance.fixed_tables[0].clone()),
            4 => instance.channels[0].width = 2,
            5 => instance.fixed_tables[0].rows[0].clear(),
            6 => instance.modulus += 2,
            7 => instance.components.push(instance.components[0].clone()),
            _ => unreachable!(),
        }
        assert!(
            instance
                .check_trace::<F>(&Trace {
                    public_input: vec![7],
                    tables: vec![vec![]]
                })
                .is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn table_shape_and_noncanonical_values_are_rejected() {
    let instance = instance();
    for trace in [
        Trace {
            public_input: vec![7],
            tables: vec![],
        },
        Trace {
            public_input: vec![7],
            tables: vec![vec![vec![]]],
        },
        Trace {
            public_input: vec![7, 0],
            tables: vec![vec![vec![7]]],
        },
        Trace {
            public_input: vec![7],
            tables: vec![vec![vec![F::MODULUS + 7]]],
        },
    ] {
        assert!(instance.check_trace::<F>(&trace).is_err());
    }
}

#[test]
fn verifier_constraints_are_checked() {
    let mut instance = instance();
    instance.verifier.program.ops.push(Op::Assert(Expr::Var(0)));
    assert!(instance
        .check_trace::<F>(&trace())
        .unwrap_err()
        .contains("assertion"));
}

#[test]
fn inconsistent_multiplicity_and_duplicate_rows_do_not_cancel_silently() {
    let mut trace = trace();
    trace.tables[0].push(vec![7]);
    assert!(instance()
        .check_trace::<F>(&trace)
        .unwrap_err()
        .contains("unbalanced"));
}

#[test]
fn row_builder_generates_native_cells_and_checks_all_tables() {
    let mut instance = instance();
    instance.components[0].program.local_length = 1;
    instance.components[0].program.ops.insert(
        0,
        Op::Witness {
            m: 1,
            steps: vec![],
            output: VExpr::Elements(vec![FExpr::Expr(Expr::Var(0))]),
        },
    );
    instance.components[0]
        .program
        .ops
        .push(Op::Assert(Expr::Add(
            Box::new(Expr::Var(1)),
            Box::new(Expr::Mul(
                Box::new(Expr::Const(F::MODULUS - 1)),
                Box::new(Expr::Var(0)),
            )),
        )));
    let rows = vec![vec![RowInput {
        cells: vec![F::from_u64(7)],
        hints: Tables::default(),
    }]];
    let built = instance
        .build_rows(&[F::from_u64(7)], &rows, &Tables::default())
        .unwrap();
    assert_eq!(built.tables, vec![vec![vec![7, 7]]]);
    assert!(instance
        .build_rows(&[F::from_u64(9)], &rows, &Tables::default())
        .is_err());
}

#[test]
fn lookup_wire_payload_is_preserved_and_ambiguous_operations_fail() {
    let program = parse_program(
        &serde_json::json!({ "version": 1, "localLength": 0, "operations": [
        { "lookup": { "table": "allowed", "entry": [{ "type": "var", "index": 0 }] } }
    ] }),
    )
    .unwrap();
    assert!(
        matches!(&program.ops[0], Op::Lookup { table, entry } if table == "allowed" && entry.len() == 1)
    );
    for operation in [
        serde_json::json!({"lookup": {}}),
        serde_json::json!({"lookup": {"table": "allowed", "entry": []}, "assert": {"type": "const", "value": 0}}),
        serde_json::json!({"assert": {"type": "const", "value": 0}, "ignoredConstraint": {}}),
    ] {
        assert!(parse_program(
            &serde_json::json!({"version": 1, "localLength": 0, "operations": [operation]})
        )
        .is_err());
    }
}

// A small field exercises the characteristic bound without allocating billions of rows.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct F3(u64);
impl Field for F3 {
    const MODULUS: u64 = 3;
    fn from_u64(value: u64) -> Self {
        Self(value % 3)
    }
    fn val(self) -> u64 {
        self.0
    }
    fn add(self, other: Self) -> Self {
        Self::from_u64(self.0 + other.0)
    }
    fn mul(self, other: Self) -> Self {
        Self::from_u64(self.0 * other.0)
    }
    fn inv(self) -> Self {
        self
    }
}

#[test]
fn zero_multiplicity_rows_still_count_against_characteristic() {
    let instance = Instance {
        modulus: 3,
        components: vec![component("padding", vec![interaction(0)])],
        verifier: component("public", vec![]),
        channels: vec![Channel {
            name: "values".into(),
            width: 1,
        }],
        fixed_tables: vec![],
    };
    let mut trace = Trace {
        public_input: vec![0],
        tables: vec![vec![vec![0], vec![0]]],
    };
    assert!(instance.check_trace::<F3>(&trace).is_ok());
    trace.tables[0].push(vec![0]);
    assert!(instance
        .check_trace::<F3>(&trace)
        .unwrap_err()
        .contains("characteristic"));
}

#[test]
fn malformed_programs_fail_even_when_their_tables_are_empty() {
    for operation in [
        Op::Assert(Expr::Var(1)),
        Op::Assert(Expr::Const(F::MODULUS)),
    ] {
        let mut instance = instance();
        instance.components[0].program.ops.push(operation);
        assert!(instance.validate::<F>().is_err());
    }
    let mut instance = instance();
    instance.components[0].program.local_length = 1;
    assert!(instance
        .validate::<F>()
        .unwrap_err()
        .contains("localLength"));
    instance.verifier.program.local_length = 1;
    assert!(instance.validate::<F>().unwrap_err().contains("verifier"));
}

#[test]
fn lean_exported_ensemble_checks_valid_and_rejects_forged_trace() {
    use witgen_interp::ensemble_wire::{parse_instance, parse_trace, trace_to_json};
    let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../export/ensemble");
    let read = |file: &str| -> serde_json::Value {
        serde_json::from_slice(&std::fs::read(directory.join(file)).unwrap()).unwrap()
    };
    let instance = parse_instance(&read("lookup.instance.json")).unwrap();
    let valid = parse_trace(&read("lookup.valid.json")).unwrap();
    let forged = parse_trace(&read("lookup.forged.json")).unwrap();
    instance.check_trace::<F>(&valid).unwrap();
    assert!(instance
        .check_trace::<F>(&forged)
        .unwrap_err()
        .contains("lookup"));
    instance
        .check_trace::<F>(&parse_trace(&trace_to_json(&valid)).unwrap())
        .unwrap();
    let mut unknown = read("lookup.instance.json");
    unknown["additionalConstraintSystem"] = serde_json::json!({});
    assert!(parse_instance(&unknown).is_err());
    let mut wrong_version = read("lookup.valid.json");
    wrong_version["version"] = serde_json::json!(2);
    assert!(parse_trace(&wrong_version).is_err());
}

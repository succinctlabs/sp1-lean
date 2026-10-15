//! Parsing the historical complete-instance JSON fixtures retained during export migration.
//! Unknown metadata fields are rejected so future semantics require a version change.

use crate::ensemble::{Channel, Component, FixedTable, Instance, Trace};
use crate::wire::parse_program;
use serde_json::{Map, Value};

fn object<'a>(value: &'a Value, keys: &[&str]) -> Result<&'a Map<String, Value>, String> {
    let object = value.as_object().ok_or("expected object")?;
    if object.len() != keys.len() || keys.iter().any(|key| !object.contains_key(*key)) {
        return Err(format!("expected exactly fields {keys:?}"));
    }
    Ok(object)
}

fn array(value: &Value) -> Result<&Vec<Value>, String> {
    value.as_array().ok_or_else(|| "expected array".into())
}

fn number(value: &Value) -> Result<u64, String> {
    value
        .as_u64()
        .ok_or_else(|| "expected unsigned integer".into())
}

fn width(value: &Value) -> Result<usize, String> {
    usize::try_from(number(value)?).map_err(|_| "width exceeds host usize".into())
}

fn name(value: &Value) -> Result<String, String> {
    value
        .as_str()
        .map(str::to_owned)
        .ok_or_else(|| "expected name string".into())
}

fn row(value: &Value) -> Result<Vec<u64>, String> {
    array(value)?.iter().map(number).collect()
}

fn rows(value: &Value) -> Result<Vec<Vec<u64>>, String> {
    array(value)?.iter().map(row).collect()
}

fn component(value: &Value) -> Result<Component, String> {
    let value = object(value, &["name", "inputWidth", "program"])?;
    Ok(Component {
        name: name(&value["name"])?,
        input_width: width(&value["inputWidth"])?,
        program: parse_program(&value["program"])?,
    })
}

pub fn parse_instance(value: &Value) -> Result<Instance, String> {
    let value = object(
        value,
        &[
            "version",
            "modulus",
            "components",
            "verifier",
            "channels",
            "fixedTables",
        ],
    )?;
    if number(&value["version"])? != 1 {
        return Err("unsupported ensemble wire version".into());
    }
    let components = array(&value["components"])?
        .iter()
        .map(component)
        .collect::<Result<_, _>>()?;
    let channels = array(&value["channels"])?
        .iter()
        .map(|value| {
            let value = object(value, &["name", "width"])?;
            Ok(Channel {
                name: name(&value["name"])?,
                width: width(&value["width"])?,
            })
        })
        .collect::<Result<_, String>>()?;
    let fixed_tables = array(&value["fixedTables"])?
        .iter()
        .map(|value| {
            let value = object(value, &["name", "width", "rows"])?;
            Ok(FixedTable {
                name: name(&value["name"])?,
                width: width(&value["width"])?,
                rows: rows(&value["rows"])?,
            })
        })
        .collect::<Result<_, String>>()?;
    Ok(Instance {
        modulus: number(&value["modulus"])?,
        components,
        verifier: component(&value["verifier"])?,
        channels,
        fixed_tables,
    })
}

pub fn parse_trace(value: &Value) -> Result<Trace, String> {
    let value = object(value, &["version", "publicInput", "tables"])?;
    if number(&value["version"])? != 1 {
        return Err("unsupported trace wire version".into());
    }
    Ok(Trace {
        public_input: row(&value["publicInput"])?,
        tables: array(&value["tables"])?
            .iter()
            .map(rows)
            .collect::<Result<_, _>>()?,
    })
}

pub fn trace_to_json(trace: &Trace) -> Value {
    serde_json::json!({ "version": 1, "publicInput": trace.public_input, "tables": trace.tables })
}

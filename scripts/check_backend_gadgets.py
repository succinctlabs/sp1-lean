#!/usr/bin/env python3
"""Check the full snarkjs witness, separately comparing original cells to Lean."""
import argparse
import json
from pathlib import Path
import struct
import subprocess
import sys


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def load(path):
    return json.loads(path.read_text())


def read_witness(path, prime):
    """Read the standard v2 wtns sections; retain the binary for explicit cell mutations."""
    data = bytearray(path.read_bytes())
    require(data[:4] == b"wtns", f"{path}: invalid witness magic")
    version, section_count = struct.unpack_from("<II", data, 4)
    require(version == 2 and section_count == 2, f"{path}: unexpected witness format")
    sections = {}
    cursor = 12
    for _ in range(section_count):
        kind, size = struct.unpack_from("<IQ", data, cursor)
        cursor += 12
        require(kind not in sections and cursor + size <= len(data), "invalid wtns section")
        sections[kind] = (cursor, size)
        cursor += size
    require(cursor == len(data) and set(sections) == {1, 2}, "invalid wtns sections")
    header, header_size = sections[1]
    width = struct.unpack_from("<I", data, header)[0]
    require(width == 32 and header_size == width + 8, "unexpected BN254 header width")
    actual_prime = int.from_bytes(data[header + 4:header + 4 + width], "little")
    count = struct.unpack_from("<I", data, header + 4 + width)[0]
    offset, size = sections[2]
    require(actual_prime == prime and size == width * count, "wrong field or witness length")
    values = [int.from_bytes(data[offset + i * width:offset + (i + 1) * width], "little")
              for i in range(count)]
    require(values[0] == 1 and all(value < prime for value in values), "noncanonical witness")
    return data, offset, width, values


def run(command):
    return subprocess.run(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)


def check_r1cs(cli, r1cs, witness, accepted, label):
    command = ["node", str(cli), "wtns", "check", str(r1cs), str(witness)]
    checked = run(command)
    correct = "WITNESS IS CORRECT" in checked.stdout
    incorrect = "WITNESS IS NOT CORRECT" in checked.stdout
    # A crash, a missing tool, or an unrecognized diagnostic must never count as rejection.
    require(correct != incorrect, f"{label}: snarkjs did not report a witness verdict:\n{checked.stdout}")
    require(correct == accepted and checked.returncode == (0 if accepted else 1),
            f"{label}: expected accepted={accepted}; snarkjs returned {checked.returncode}:\n{checked.stdout}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("artifacts", type=Path)
    parser.add_argument("scratch", type=Path)
    parser.add_argument("--cli", type=Path, required=True)
    args = parser.parse_args()
    manifest = load(args.artifacts / "manifest.json")
    require([gadget["name"] for gadget in manifest["gadgets"]] ==
            ["is-zero", "is-zero-word", "word-range-check"], "wrong gadget inventory")
    prime = int(manifest["prime"])
    args.scratch.mkdir(parents=True, exist_ok=True)
    cases_checked = mutations_checked = 0
    for gadget in manifest["gadgets"]:
        name = gadget["name"]
        directory = args.artifacts / name
        scratch = args.scratch / name
        scratch.mkdir(exist_ok=True)
        layout = load(directory / "layout.json")
        constraints = load(directory / "circuit.r1cs.json")
        mapping = layout["originalCells"]
        require([cell["cell"] for cell in mapping] == list(range(len(mapping))), "invalid cell inventory")
        signals = [cell["signal"] for cell in mapping]
        require(sorted(signals) == list(range(1, len(mapping) + 1)), "incomplete original signal map")
        require(gadget["signals"] == constraints["nVars"] and
                gadget["r1csConstraints"] == constraints["nConstraints"] == len(constraints["constraints"]),
                "manifest R1CS cost mismatch")
        require(layout["auxiliarySignalsStart"] == len(mapping) + 1, "wrong auxiliary boundary")
        cases = load(directory / "cases.json")
        require(cases and len(cases) == gadget["cases"], f"{name}: missing cases")
        require(len({case["id"] for case in cases}) == len(cases), f"{name}: duplicate cases")
        for case in cases:
            label = f"{name}/{case['id']}"
            input_path = directory / "inputs" / f"{case['id']}.json"
            require(load(input_path) == case["input"], f"{label}: input mismatch")
            require(all(isinstance(value, str) and value.isdecimal() and int(value) < prime
                        for value in case["input"].values()), f"{label}: noncanonical input")
            witness = scratch / f"{case['id']}.wtns"
            calculated = run(["node", str(args.cli), "wtns", "calculate",
                              str(directory / "circuit.wasm"), str(input_path), str(witness)])
            require(calculated.returncode == 0, f"{label}: witness calculation failed:\n{calculated.stdout}")
            data, offset, width, values = read_witness(witness, prime)
            require(len(values) == gadget["signals"], f"{label}: missing auxiliary signals")
            require(len(case["leanCells"]) == len(mapping), f"{label}: missing Lean cells")
            for cell, expected in zip(mapping, case["leanCells"]):
                require(isinstance(expected, str) and values[cell["signal"]] == int(expected),
                        f"{label}: Lean cell {cell['cell']} ({cell['name']}) differs from WASM signal {cell['signal']}")
            check_r1cs(args.cli, directory / "circuit.r1cs", witness, case["accepted"], label)
            cases_checked += 1
            for mutation in case["mutations"]:
                changed = bytearray(data)
                signal = mapping[mutation["cell"]]["signal"]
                start = offset + width * signal
                changed[start:start + width] = int(mutation["value"]).to_bytes(width, "little")
                destination = scratch / f"{case['id']}-{mutation['id']}.wtns"
                destination.write_bytes(changed)
                check_r1cs(args.cli, directory / "circuit.r1cs", destination, mutation["accepted"],
                           f"{label}/{mutation['id']}")
                mutations_checked += 1
            # Confirm that full backend auxiliaries are constrained, not just mapped Lean cells.
            if case["accepted"] and case["id"] == "zero" and len(values) > len(mapping) + 1:
                signal = layout["auxiliarySignalsStart"]
                changed = bytearray(data)
                start = offset + width * signal
                changed[start:start + width] = ((values[signal] + 1) % prime).to_bytes(width, "little")
                destination = scratch / "corrupt-backend-auxiliary.wtns"
                destination.write_bytes(changed)
                check_r1cs(args.cli, directory / "circuit.r1cs", destination, False,
                           f"{name}/corrupt-backend-auxiliary")
                mutations_checked += 1
        print(f"PASS {name}: {gadget['witnessCells']} Lean witness cells, "
              f"{gadget['r1csConstraints']} R1CS constraints, {gadget['signals']} total signals")
    print(f"PASS {cases_checked} generated witnesses and {mutations_checked} explicit mutations; "
          "every original Lean cell compared and full R1CS checked")


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, ValueError, KeyError, OSError, struct.error) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)

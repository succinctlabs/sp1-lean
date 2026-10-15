"""Native column reuse must be checked against independent Rust reflection output."""

from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from update_extracted import native_structs, validate_native_layouts


class NativeLayoutTests(unittest.TestCase):
    native = {"Row": ("SP1Clean.Circuits.Types.Row", "  value : F\n  limbs : (Vector F 4)\n")}

    def body(self, fields="  value : F\n  limbs : (Vector F 4)\n"):
        return "structure Row (F : Type) where\n" + fields + "deriving ProvableStruct\n"

    def test_matching_rust_layout(self):
        validate_native_layouts({"Chip": self.body()}, self.native, complete=True)

    def test_reordered_fields(self):
        with self.assertRaisesRegex(ValueError, "Rust layout"):
            validate_native_layouts({"Chip": self.body("  limbs : (Vector F 4)\n  value : F\n")},
                                    self.native, complete=True)

    def test_changed_width_or_field_name(self):
        for body in [self.body().replace("F 4", "F 8"), self.body().replace("value :", "other :")]:
            with self.assertRaisesRegex(ValueError, "Rust layout"):
                validate_native_layouts({"Chip": body}, self.native, complete=True)

    def test_disagreeing_rust_emitters(self):
        with self.assertRaisesRegex(ValueError, "OtherChip"):
            validate_native_layouts({"Chip": self.body(), "OtherChip": self.body().replace("F 4", "F 2")},
                                    self.native, complete=True)

    def test_missing_full_run_evidence(self):
        with self.assertRaisesRegex(ValueError, "not checked against Rust"):
            validate_native_layouts({}, self.native, complete=True)
        validate_native_layouts({}, self.native, complete=False)

    def test_unsupported_native_declaration_is_not_silently_skipped(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Row.lean").write_text(self.body())
            (root / "Other.lean").write_text("structure Other (enabled : Bool) (F : Type) where\n  value : F\n")
            with self.assertRaisesRegex(ValueError, "unsupported native column"):
                native_structs(root)

    def test_field_documentation_does_not_change_layout(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Row.lean").write_text(self.body().replace(
                "  value :", "  /-- The scalar value. -/\n  value :"))
            validate_native_layouts({"Chip": self.body()}, native_structs(root), complete=True)


if __name__ == "__main__":
    unittest.main()

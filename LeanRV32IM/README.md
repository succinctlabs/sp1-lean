# Lean RISC-V spec for RV32IM ISA

Note that `run_hart_active` is not present. We only care about the `execute`
function that executes each instruction.

However, this does mean that to accurately one RISC-V cycle, the monadic action
should be
```lean
do
  writeReg nextPC (BitVec.addInt (← readReg PC) 4)
  execute_XXX arg0 arg1 arg2
```
because `execute` doesn't take care of incrementing `pc`; it's `run_hart_active`
that does this.

## How to generate

1. Checkout `gzgz/modularize-rv32im` branch of GZGavinZhao/sail-riscv.
2. Install rems-project/sail for Sail 0.19.1 (HEAD @ 5abc6cfa65363ba26a5d0fd6665d88115976d14e).
3. Run `sail --project model/riscv.sail_project --variable ARCH=RV32 --lean --config config/rv32im.json --lean-import-file handwritten_support/RiscvExtrasExecutable.lean --lean-output-dir build/ -o Lean_RV32IM --lean-force-output I M riscv_postlude`.
4. The result is in the `build` directory.


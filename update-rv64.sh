git clone https://github.com/opencompl/sail-riscv-lean

rm -rf LeanRV64D LeanRV64D.lean
cp -r sail-riscv-lean/LeanRV64D ./LeanRV64D
cp sail-riscv-lean/LeanRV64D.lean ./LeanRV64D.lean
rm -rf sail-riscv-lean

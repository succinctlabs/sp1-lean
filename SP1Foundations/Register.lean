import Mathlib
import LeanRV64IM.RiscvInstsEnd
import SP1Foundations.Misc

-- dt: should this be a macro instead?
@[simp] abbrev SailState := PreSail.SequentialState RegisterType Sail.trivialChoiceSource

section regidx

instance : DecidableEq regidx | .Regidx v, .Regidx v' => by simp; infer_instance

/-- Convert a bitvec into the corresponding `RV64` register.
dt: some of the lemmas below would be nicer if we just mapped `0#5` and `31#5` to diff values. -/
def reg_idx_to_Register (idx : BitVec 5) : Register :=
  match idx with
  | 1#5 => Register.x1
  | 2#5 => Register.x2
  | 3#5 => Register.x3
  | 4#5 => Register.x4
  | 5#5 => Register.x5
  | 6#5 => Register.x6
  | 7#5 => Register.x7
  | 8#5 => Register.x8
  | 9#5 => Register.x9
  | 10#5 => Register.x10
  | 11#5 => Register.x11
  | 12#5 => Register.x12
  | 13#5 => Register.x13
  | 14#5 => Register.x14
  | 15#5 => Register.x15
  | 16#5 => Register.x16
  | 17#5 => Register.x17
  | 18#5 => Register.x18
  | 19#5 => Register.x19
  | 20#5 => Register.x20
  | 21#5 => Register.x21
  | 22#5 => Register.x22
  | 23#5 => Register.x23
  | 24#5 => Register.x24
  | 25#5 => Register.x25
  | 26#5 => Register.x26
  | 27#5 => Register.x27
  | 28#5 => Register.x28
  | 29#5 => Register.x29
  | 30#5 => Register.x30
  | _ => Register.x31

lemma reg_idx_31_is_x31 : reg_idx_to_Register 31#5 = Register.x31 := rfl

/-- All of the registers corresponding to a `BitVec 5` contain 64-bit values. -/
lemma reg_idx_must_64 (idx : BitVec 5) :
    RegisterType (reg_idx_to_Register idx) = BitVec 64 := by
  simp [reg_idx_to_Register]
  split <;> rfl

lemma case_31 {val : BitVec 64} {s : SailState} :
    s.regs.insert (reg_idx_to_Register 31#5) val = s.regs.insert Register.x31 val := rfl

@[simp] lemma reg_idx_toRegister_ne_nextPC (idx : BitVec 5) :
    reg_idx_to_Register idx ≠ Register.nextPC := by
  unfold reg_idx_to_Register; split <;> trivial

@[simp] lemma nextPC_ne_reg_idx_toRegister (idx : BitVec 5) :
    Register.nextPC ≠ reg_idx_to_Register idx := by
  unfold reg_idx_to_Register; split <;> trivial

@[simp] lemma reg_idx_toRegister_ne_PC (idx : BitVec 5) :
    reg_idx_to_Register idx ≠ Register.PC := by
  unfold reg_idx_to_Register; split <;> trivial

@[simp] lemma PC_ne_reg_idx_toRegister (idx : BitVec 5) :
    Register.PC ≠ reg_idx_to_Register idx := by
  unfold reg_idx_to_Register; split <;> trivial

@[simp] lemma reg_idx_toRegister_ne_misa (idx : BitVec 5) :
    reg_idx_to_Register idx ≠ Register.misa := by
  unfold reg_idx_to_Register; split <;> trivial

@[simp] lemma misa_ne_reg_idx_toRegister (idx : BitVec 5) :
    Register.misa ≠ reg_idx_to_Register idx := by
  unfold reg_idx_to_Register; split <;> trivial

@[simp] lemma regidxToRegister_eq_x1_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x1 ↔ idx = 1#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x2_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x2 ↔ idx = 2#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x3_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x3 ↔ idx = 3#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x4_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x4 ↔ idx = 4#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x5_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x5 ↔ idx = 5#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x6_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x6 ↔ idx = 6#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x7_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x7 ↔ idx = 7#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x8_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x8 ↔ idx = 8#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x9_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x9 ↔ idx = 9#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x10_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x10 ↔ idx = 10#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x11_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x11 ↔ idx = 11#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x12_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x12 ↔ idx = 12#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x13_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x13 ↔ idx = 13#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x14_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x14 ↔ idx = 14#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x15_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x15 ↔ idx = 15#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x16_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x16 ↔ idx = 16#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x17_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x17 ↔ idx = 17#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x18_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x18 ↔ idx = 18#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x19_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x19 ↔ idx = 19#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x20_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x20 ↔ idx = 20#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x21_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x21 ↔ idx = 21#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x22_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x22 ↔ idx = 22#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x23_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x23 ↔ idx = 23#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x24_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x24 ↔ idx = 24#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x25_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x25 ↔ idx = 25#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x26_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x26 ↔ idx = 26#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x27_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x27 ↔ idx = 27#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x28_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x28 ↔ idx = 28#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x29_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x29 ↔ idx = 29#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x30_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x30 ↔ idx = 30#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x31_iff (idx : BitVec 5) :
reg_idx_to_Register idx = .x31 ↔ idx = 31#5 ∨ idx = 0#5 := by fin_cases idx <;> trivial

@[simp] lemma regidxToRegister_eq_x1_iff' (idx : BitVec 5) :
.x1 = reg_idx_to_Register idx ↔ idx = 1#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x2_iff' (idx : BitVec 5) :
.x2 = reg_idx_to_Register idx ↔ idx = 2#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x3_iff' (idx : BitVec 5) :
.x3 = reg_idx_to_Register idx ↔ idx = 3#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x4_iff' (idx : BitVec 5) :
.x4 = reg_idx_to_Register idx ↔ idx = 4#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x5_iff' (idx : BitVec 5) :
.x5 = reg_idx_to_Register idx ↔ idx = 5#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x6_iff' (idx : BitVec 5) :
.x6 = reg_idx_to_Register idx ↔ idx = 6#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x7_iff' (idx : BitVec 5) :
.x7 = reg_idx_to_Register idx ↔ idx = 7#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x8_iff' (idx : BitVec 5) :
.x8 = reg_idx_to_Register idx ↔ idx = 8#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x9_iff' (idx : BitVec 5) :
.x9 = reg_idx_to_Register idx ↔ idx = 9#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x10_iff' (idx : BitVec 5) :
.x10 = reg_idx_to_Register idx ↔ idx = 10#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x11_iff' (idx : BitVec 5) :
.x11 = reg_idx_to_Register idx ↔ idx = 11#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x12_iff' (idx : BitVec 5) :
.x12 = reg_idx_to_Register idx ↔ idx = 12#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x13_iff' (idx : BitVec 5) :
.x13 = reg_idx_to_Register idx ↔ idx = 13#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x14_iff' (idx : BitVec 5) :
.x14 = reg_idx_to_Register idx ↔ idx = 14#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x15_iff' (idx : BitVec 5) :
.x15 = reg_idx_to_Register idx ↔ idx = 15#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x16_iff' (idx : BitVec 5) :
.x16 = reg_idx_to_Register idx ↔ idx = 16#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x17_iff' (idx : BitVec 5) :
.x17 = reg_idx_to_Register idx ↔ idx = 17#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x18_iff' (idx : BitVec 5) :
.x18 = reg_idx_to_Register idx ↔ idx = 18#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x19_iff' (idx : BitVec 5) :
.x19 = reg_idx_to_Register idx ↔ idx = 19#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x20_iff' (idx : BitVec 5) :
.x20 = reg_idx_to_Register idx ↔ idx = 20#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x21_iff' (idx : BitVec 5) :
.x21 = reg_idx_to_Register idx ↔ idx = 21#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x22_iff' (idx : BitVec 5) :
.x22 = reg_idx_to_Register idx ↔ idx = 22#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x23_iff' (idx : BitVec 5) :
.x23 = reg_idx_to_Register idx ↔ idx = 23#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x24_iff' (idx : BitVec 5) :
.x24 = reg_idx_to_Register idx ↔ idx = 24#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x25_iff' (idx : BitVec 5) :
.x25 = reg_idx_to_Register idx ↔ idx = 25#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x26_iff' (idx : BitVec 5) :
.x26 = reg_idx_to_Register idx ↔ idx = 26#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x27_iff' (idx : BitVec 5) :
.x27 = reg_idx_to_Register idx ↔ idx = 27#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x28_iff' (idx : BitVec 5) :
.x28 = reg_idx_to_Register idx ↔ idx = 28#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x29_iff' (idx : BitVec 5) :
.x29 = reg_idx_to_Register idx ↔ idx = 29#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x30_iff' (idx : BitVec 5) :
.x30 = reg_idx_to_Register idx ↔ idx = 30#5 := by fin_cases idx <;> trivial
@[simp] lemma regidxToRegister_eq_x31_iff' (idx : BitVec 5) :
.x31 = reg_idx_to_Register idx ↔ idx = 31#5 ∨ idx = 0#5 := by fin_cases idx <;> trivial

@[simp] lemma regidxToRegister_ofNat_0 : reg_idx_to_Register 0#5 = .x31 := rfl
@[simp] lemma regidxToRegister_ofNat_1 : reg_idx_to_Register 1#5 = .x1 := rfl
@[simp] lemma regidxToRegister_ofNat_2 : reg_idx_to_Register 2#5 = .x2 := rfl
@[simp] lemma regidxToRegister_ofNat_3 : reg_idx_to_Register 3#5 = .x3 := rfl
@[simp] lemma regidxToRegister_ofNat_4 : reg_idx_to_Register 4#5 = .x4 := rfl
@[simp] lemma regidxToRegister_ofNat_5 : reg_idx_to_Register 5#5 = .x5 := rfl
@[simp] lemma regidxToRegister_ofNat_6 : reg_idx_to_Register 6#5 = .x6 := rfl
@[simp] lemma regidxToRegister_ofNat_7 : reg_idx_to_Register 7#5 = .x7 := rfl
@[simp] lemma regidxToRegister_ofNat_8 : reg_idx_to_Register 8#5 = .x8 := rfl
@[simp] lemma regidxToRegister_ofNat_9 : reg_idx_to_Register 9#5 = .x9 := rfl
@[simp] lemma regidxToRegister_ofNat_10 : reg_idx_to_Register 10#5 = .x10 := rfl
@[simp] lemma regidxToRegister_ofNat_11 : reg_idx_to_Register 11#5 = .x11 := rfl
@[simp] lemma regidxToRegister_ofNat_12 : reg_idx_to_Register 12#5 = .x12 := rfl
@[simp] lemma regidxToRegister_ofNat_13 : reg_idx_to_Register 13#5 = .x13 := rfl
@[simp] lemma regidxToRegister_ofNat_14 : reg_idx_to_Register 14#5 = .x14 := rfl
@[simp] lemma regidxToRegister_ofNat_15 : reg_idx_to_Register 15#5 = .x15 := rfl
@[simp] lemma regidxToRegister_ofNat_16 : reg_idx_to_Register 16#5 = .x16 := rfl
@[simp] lemma regidxToRegister_ofNat_17 : reg_idx_to_Register 17#5 = .x17 := rfl
@[simp] lemma regidxToRegister_ofNat_18 : reg_idx_to_Register 18#5 = .x18 := rfl
@[simp] lemma regidxToRegister_ofNat_19 : reg_idx_to_Register 19#5 = .x19 := rfl
@[simp] lemma regidxToRegister_ofNat_20 : reg_idx_to_Register 20#5 = .x20 := rfl
@[simp] lemma regidxToRegister_ofNat_21 : reg_idx_to_Register 21#5 = .x21 := rfl
@[simp] lemma regidxToRegister_ofNat_22 : reg_idx_to_Register 22#5 = .x22 := rfl
@[simp] lemma regidxToRegister_ofNat_23 : reg_idx_to_Register 23#5 = .x23 := rfl
@[simp] lemma regidxToRegister_ofNat_24 : reg_idx_to_Register 24#5 = .x24 := rfl
@[simp] lemma regidxToRegister_ofNat_25 : reg_idx_to_Register 25#5 = .x25 := rfl
@[simp] lemma regidxToRegister_ofNat_26 : reg_idx_to_Register 26#5 = .x26 := rfl
@[simp] lemma regidxToRegister_ofNat_27 : reg_idx_to_Register 27#5 = .x27 := rfl
@[simp] lemma regidxToRegister_ofNat_28 : reg_idx_to_Register 28#5 = .x28 := rfl
@[simp] lemma regidxToRegister_ofNat_29 : reg_idx_to_Register 29#5 = .x29 := rfl
@[simp] lemma regidxToRegister_ofNat_30 : reg_idx_to_Register 30#5 = .x30 := rfl
@[simp] lemma regidxToRegister_ofNat_31 : reg_idx_to_Register 31#5 = .x31 := rfl

@[simp] lemma regidxToRegister_inj (idx idx' : BitVec 5) :
    reg_idx_to_Register idx = reg_idx_to_Register idx' ↔
      idx = idx' ∨ (idx = 0#5 ∧ idx' = 31#5) ∨ (idx = 31#5 ∧ idx' = 0#5) := by
  fin_cases idx
  all_goals {
    simp [eq_comm (a := idx')]
    try {aesop}
  }

end regidx

import LeanRV64D.Flow
import LeanRV64D.Prelude
import LeanRV64D.RiscvXlen
import LeanRV64D.RiscvRegs
import LeanRV64D.RiscvPcAccess
import LeanRV64D.RiscvSysRegs
import LeanRV64D.RiscvSmcntrpmf
import LeanRV64D.RiscvSysControl

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

noncomputable section

namespace LeanRV64D.Functions

open zvk_vsm4r_funct6
open zvk_vsha2_funct6
open zvk_vaesem_funct6
open zvk_vaesef_funct6
open zvk_vaesdm_funct6
open zvk_vaesdf_funct6
open zicondop
open wxfunct6
open wvxfunct6
open wvvfunct6
open wvfunct6
open wrsop
open write_kind
open wmvxfunct6
open wmvvfunct6
open vxsgfunct6
open vxmsfunct6
open vxmfunct6
open vxmcfunct6
open vxfunct6
open vxcmpfunct6
open vvmsfunct6
open vvmfunct6
open vvmcfunct6
open vvfunct6
open vvcmpfunct6
open vregno
open vregidx
open vmlsop
open vlewidth
open visgfunct6
open virtaddr
open vimsfunct6
open vimfunct6
open vimcfunct6
open vifunct6
open vicmpfunct6
open vfwunary0
open vfunary1
open vfunary0
open vfnunary0
open vextfunct6
open uop
open sopw
open sop
open seed_opst
open rounding_mode
open ropw
open rop
open rmvvfunct6
open rivvfunct6
open rfvvfunct6
open regno
open regidx
open read_kind
open pmpAddrMatch
open physaddr
open option
open nxsfunct6
open nxfunct6
open nvsfunct6
open nvfunct6
open ntl_type
open nisfunct6
open nifunct6
open mvxmafunct6
open mvxfunct6
open mvvmafunct6
open mvvfunct6
open mmfunct6
open maskfunct3
open iop
open instruction
open fwvvmafunct6
open fwvvfunct6
open fwvfunct6
open fwvfmafunct6
open fwvffunct6
open fwffunct6
open fvvmfunct6
open fvvmafunct6
open fvvfunct6
open fvfmfunct6
open fvfmafunct6
open fvffunct6
open fregno
open fregidx
open f_un_x_op_H
open f_un_x_op_D
open f_un_rm_xf_op_S
open f_un_rm_xf_op_H
open f_un_rm_xf_op_D
open f_un_rm_fx_op_S
open f_un_rm_fx_op_H
open f_un_rm_fx_op_D
open f_un_rm_ff_op_S
open f_un_rm_ff_op_H
open f_un_rm_ff_op_D
open f_un_op_x_S
open f_un_op_f_S
open f_un_f_op_H
open f_un_f_op_D
open f_madd_op_S
open f_madd_op_H
open f_madd_op_D
open f_bin_x_op_H
open f_bin_x_op_D
open f_bin_rm_op_S
open f_bin_rm_op_H
open f_bin_rm_op_D
open f_bin_op_x_S
open f_bin_op_f_S
open f_bin_f_op_H
open f_bin_f_op_D
open extop_zbb
open extension
open exception
open ctl_result
open csrop
open cregidx
open checked_cbop
open cfregidx
open cbop_zicbom
open cbie
open bropw_zbb
open brop_zbs
open brop_zbkb
open brop_zbb
open bop
open biop_zbs
open barrier_kind
open amoop
open agtype
open WaitReason
open TrapVectorMode
open Step
open SATPMode
open Register
open Privilege
open PmpAddrMatchType
open PTW_Error
open PTE_Check
open InterruptType
open ISA_Format
open HartState
open FetchResult
open Ext_DataAddr_Check
open Ext_ControlAddr_Check
open ExtStatus
open ExecutionResult
open ExceptionType
open Architecture
open AccessType

def plat_cache_block_size_exp : Nat := 6

def plat_enable_dirty_update : Bool := false

def plat_enable_misaligned_access : Bool := true

def plat_mtval_has_illegal_inst_bits : Bool := false

def htif_tohost_base (_ : Unit) : (BitVec (if ( 64 = 32  : Bool) then 34 else 64)) :=
  (trunc (m := 64) (plat_htif_tohost ()))

/-- Type quantifiers: width : Int, width ≤ max_mem_access -/
def within_phys_mem (typ_0 : physaddr) (width : Int) : SailM Bool := do
  let .Physaddr addr : physaddr := typ_0
  let addr_int := (BitVec.toNat addr)
  let ram_base_int ← do (pure (BitVec.toNat (← readReg plat_ram_base)))
  let rom_base_int ← do (pure (BitVec.toNat (← readReg plat_rom_base)))
  let ram_size_int ← do (pure (BitVec.toNat (← readReg plat_ram_size)))
  let rom_size_int ← do (pure (BitVec.toNat (← readReg plat_rom_size)))
  if (((ram_base_int ≤b addr_int) && ((addr_int +i width) ≤b (ram_base_int +i ram_size_int))) : Bool)
  then (pure true)
  else
    (do
      if (((rom_base_int ≤b addr_int) && ((addr_int +i width) ≤b (rom_base_int +i rom_size_int))) : Bool)
      then (pure true)
      else
        (do
          if ((get_config_print_platform ()) : Bool)
          then
            (do
              let _ : Unit :=
                (print_endline
                  (HAppend.hAppend "within_phys_mem: "
                    (HAppend.hAppend (BitVec.toFormatted addr) " not within phys-mem:")))
              (pure (print_endline
                  (HAppend.hAppend "  plat_rom_base: "
                    (BitVec.toFormatted (← readReg plat_rom_base)))))
              (pure (print_endline
                  (HAppend.hAppend "  plat_rom_size: "
                    (BitVec.toFormatted (← readReg plat_rom_size)))))
              (pure (print_endline
                  (HAppend.hAppend "  plat_ram_base: "
                    (BitVec.toFormatted (← readReg plat_ram_base)))))
              (pure (print_endline
                  (HAppend.hAppend "  plat_ram_size: "
                    (BitVec.toFormatted (← readReg plat_ram_size))))))
          else (pure ())
          (pure false)))

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def within_clint (typ_0 : physaddr) (width : Nat) : SailM Bool := do
  let .Physaddr addr : physaddr := typ_0
  let addr_int := (BitVec.toNat addr)
  let clint_base_int ← do (pure (BitVec.toNat (← readReg plat_clint_base)))
  let clint_size_int ← do (pure (BitVec.toNat (← readReg plat_clint_size)))
  (pure ((clint_base_int ≤b addr_int) && ((addr_int +i width) ≤b (clint_base_int +i clint_size_int))))

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def within_htif_writable (typ_0 : physaddr) (width : Nat) : Bool :=
  let .Physaddr addr : physaddr := typ_0
  ((plat_enable_htif ()) && (((htif_tohost_base ()) == addr) || (((BitVec.addInt
            (htif_tohost_base ()) 4) == addr) && (width == 4))))

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def within_htif_readable (typ_0 : physaddr) (width : Nat) : Bool :=
  let .Physaddr addr : physaddr := typ_0
  ((plat_enable_htif ()) && (((htif_tohost_base ()) == addr) || (((BitVec.addInt
            (htif_tohost_base ()) 4) == addr) && (width == 4))))

def plat_insns_per_tick : nat1 := 2

def MSIP_BASE : physaddrbits := (zero_extend (m := 64) (0x00000 : (BitVec 20)))

def MTIMECMP_BASE : physaddrbits := (zero_extend (m := 64) (0x04000 : (BitVec 20)))

def MTIMECMP_BASE_HI : physaddrbits := (zero_extend (m := 64) (0x04004 : (BitVec 20)))

def MTIME_BASE : physaddrbits := (zero_extend (m := 64) (0x0BFF8 : (BitVec 20)))

def MTIME_BASE_HI : physaddrbits := (zero_extend (m := 64) (0x0BFFC : (BitVec 20)))

/-- Type quantifiers: width : Nat, width ≥ 0, width > 0 -/
def clint_load (t : (AccessType Unit)) (app_1 : physaddr) (width : Nat) : SailM (Result (BitVec (8 * width)) ExceptionType) := do
  let .Physaddr addr := app_1
  let addr ← do (pure (addr - (← readReg plat_clint_base)))
  if (((addr == MSIP_BASE) && ((width == 8) || (width == 4))) : Bool)
  then
    (do
      if ((get_config_print_platform ()) : Bool)
      then
        (pure (print_endline
            (HAppend.hAppend "clint["
              (HAppend.hAppend (BitVec.toFormatted addr)
                (HAppend.hAppend "] -> "
                  (BitVec.toFormatted (_get_Minterrupts_MSI (← readReg mip))))))))
      else (pure ())
      (pure (Ok (zero_extend (m := (8 *i width)) (_get_Minterrupts_MSI (← readReg mip))))))
  else
    (do
      if (((addr == MTIMECMP_BASE) && (width == 4)) : Bool)
      then
        (do
          if ((get_config_print_platform ()) : Bool)
          then
            (pure (print_endline
                (HAppend.hAppend "clint<4>["
                  (HAppend.hAppend (BitVec.toFormatted addr)
                    (HAppend.hAppend "] -> "
                      (BitVec.toFormatted (Sail.BitVec.extractLsb (← readReg mtimecmp) 31 0)))))))
          else (pure ())
          (pure (Ok (zero_extend (m := 32) (Sail.BitVec.extractLsb (← readReg mtimecmp) 31 0)))))
      else
        (do
          if (((addr == MTIMECMP_BASE) && (width == 8)) : Bool)
          then
            (do
              if ((get_config_print_platform ()) : Bool)
              then
                (pure (print_endline
                    (HAppend.hAppend "clint<8>["
                      (HAppend.hAppend (BitVec.toFormatted addr)
                        (HAppend.hAppend "] -> " (BitVec.toFormatted (← readReg mtimecmp)))))))
              else (pure ())
              (pure (Ok (zero_extend (m := 64) (← readReg mtimecmp)))))
          else
            (do
              if (((addr == MTIMECMP_BASE_HI) && (width == 4)) : Bool)
              then
                (do
                  if ((get_config_print_platform ()) : Bool)
                  then
                    (pure (print_endline
                        (HAppend.hAppend "clint-hi<4>["
                          (HAppend.hAppend (BitVec.toFormatted addr)
                            (HAppend.hAppend "] -> "
                              (BitVec.toFormatted
                                (Sail.BitVec.extractLsb (← readReg mtimecmp) 63 32)))))))
                  else (pure ())
                  (pure (Ok
                      (zero_extend (m := 32) (Sail.BitVec.extractLsb (← readReg mtimecmp) 63 32)))))
              else
                (do
                  if (((addr == MTIME_BASE) && (width == 4)) : Bool)
                  then
                    (do
                      if ((get_config_print_platform ()) : Bool)
                      then
                        (pure (print_endline
                            (HAppend.hAppend "clint["
                              (HAppend.hAppend (BitVec.toFormatted addr)
                                (HAppend.hAppend "] -> " (BitVec.toFormatted (← readReg mtime)))))))
                      else (pure ())
                      (pure (Ok
                          (zero_extend (m := 32) (Sail.BitVec.extractLsb (← readReg mtime) 31 0)))))
                  else
                    (do
                      if (((addr == MTIME_BASE) && (width == 8)) : Bool)
                      then
                        (do
                          if ((get_config_print_platform ()) : Bool)
                          then
                            (pure (print_endline
                                (HAppend.hAppend "clint["
                                  (HAppend.hAppend (BitVec.toFormatted addr)
                                    (HAppend.hAppend "] -> "
                                      (BitVec.toFormatted (← readReg mtime)))))))
                          else (pure ())
                          (pure (Ok (zero_extend (m := 64) (← readReg mtime)))))
                      else
                        (do
                          if (((addr == MTIME_BASE_HI) && (width == 4)) : Bool)
                          then
                            (do
                              if ((get_config_print_platform ()) : Bool)
                              then
                                (pure (print_endline
                                    (HAppend.hAppend "clint["
                                      (HAppend.hAppend (BitVec.toFormatted addr)
                                        (HAppend.hAppend "] -> "
                                          (BitVec.toFormatted (← readReg mtime)))))))
                              else (pure ())
                              (pure (Ok
                                  (zero_extend (m := 32)
                                    (Sail.BitVec.extractLsb (← readReg mtime) 63 32)))))
                          else
                            (let _ : Unit :=
                              if ((get_config_print_platform ()) : Bool)
                              then
                                (print_endline
                                  (HAppend.hAppend "clint["
                                    (HAppend.hAppend (BitVec.toFormatted addr) "] -> <not-mapped>")))
                              else ()
                            match t with
                            | .InstructionFetch () => (pure (Err (E_Fetch_Access_Fault ())))
                            | .Read Data => (pure (Err (E_Load_Access_Fault ())))
                            | _ => (pure (Err (E_SAMO_Access_Fault ()))))))))))

def clint_dispatch (_ : Unit) : SailM Unit := do
  writeReg mip (Sail.BitVec.updateSubrange (← readReg mip) 7 7
    (bool_to_bits (zopz0zIzJ_u (← readReg mtimecmp) (← readReg mtime))))
  if (((← (currentlyEnabled Ext_Sstc)) && ((_get_MEnvcfg_STCE (← readReg menvcfg)) == (0b1 : (BitVec 1)))) : Bool)
  then
    writeReg mip (Sail.BitVec.updateSubrange (← readReg mip) 5 5
      (bool_to_bits (zopz0zIzJ_u (← readReg stimecmp) (← readReg mtime))))
  else (pure ())
  if ((get_config_print_platform ()) : Bool)
  then
    (pure (print_endline
        (HAppend.hAppend "clint mtime "
          (HAppend.hAppend (BitVec.toFormatted (← readReg mtime))
            (HAppend.hAppend " (mip.MTI <- "
              (HAppend.hAppend (BitVec.toFormatted (_get_Minterrupts_MTI (← readReg mip)))
                (HAppend.hAppend
                  (← do
                    if ((← (currentlyEnabled Ext_Sstc)) : Bool)
                    then
                      (pure (HAppend.hAppend ", mip.STI <- "
                          (BitVec.toFormatted (_get_Minterrupts_STI (← readReg mip)))))
                    else (pure "")) ")")))))))
  else (pure ())

/-- Type quantifiers: width : Nat, width ≥ 0, width > 0 -/
def clint_store (app_0 : physaddr) (width : Nat) (data : (BitVec (8 * width))) : SailM (Result Bool ExceptionType) := do
  let .Physaddr addr := app_0
  let addr ← do (pure (addr - (← readReg plat_clint_base)))
  if (((addr == MSIP_BASE) && ((width == 8) || (width == 4))) : Bool)
  then
    (do
      let _ : Unit :=
        if ((get_config_print_platform ()) : Bool)
        then
          (print_endline
            (HAppend.hAppend "clint["
              (HAppend.hAppend (BitVec.toFormatted addr)
                (HAppend.hAppend "] <- "
                  (HAppend.hAppend (BitVec.toFormatted data)
                    (HAppend.hAppend " (mip.MSI <- "
                      (HAppend.hAppend (BitVec.toFormatted (Sail.BitVec.extractLsb data 0 0)) ")")))))))
        else ()
      writeReg mip (Sail.BitVec.updateSubrange (← readReg mip) 3 3
        (BitVec.join1 [(BitVec.access data 0)]))
      (clint_dispatch ())
      (pure (Ok true)))
  else
    (do
      if (((addr == MTIMECMP_BASE) && (width == 8)) : Bool)
      then
        (do
          let _ : Unit :=
            if ((get_config_print_platform ()) : Bool)
            then
              (print_endline
                (HAppend.hAppend "clint<8>["
                  (HAppend.hAppend (BitVec.toFormatted addr)
                    (HAppend.hAppend "] <- "
                      (HAppend.hAppend (BitVec.toFormatted data) " (mtimecmp)")))))
            else ()
          writeReg mtimecmp (zero_extend (m := 64) data)
          (clint_dispatch ())
          (pure (Ok true)))
      else
        (do
          if (((addr == MTIMECMP_BASE) && (width == 4)) : Bool)
          then
            (do
              let _ : Unit :=
                if ((get_config_print_platform ()) : Bool)
                then
                  (print_endline
                    (HAppend.hAppend "clint<4>["
                      (HAppend.hAppend (BitVec.toFormatted addr)
                        (HAppend.hAppend "] <- "
                          (HAppend.hAppend (BitVec.toFormatted data) " (mtimecmp)")))))
                else ()
              writeReg mtimecmp (Sail.BitVec.updateSubrange (← readReg mtimecmp) 31 0
                (zero_extend (m := 32) data))
              (clint_dispatch ())
              (pure (Ok true)))
          else
            (do
              if (((addr == MTIMECMP_BASE_HI) && (width == 4)) : Bool)
              then
                (do
                  let _ : Unit :=
                    if ((get_config_print_platform ()) : Bool)
                    then
                      (print_endline
                        (HAppend.hAppend "clint<4>["
                          (HAppend.hAppend (BitVec.toFormatted addr)
                            (HAppend.hAppend "] <- "
                              (HAppend.hAppend (BitVec.toFormatted data) " (mtimecmp)")))))
                    else ()
                  writeReg mtimecmp (Sail.BitVec.updateSubrange (← readReg mtimecmp) 63 32
                    (zero_extend (m := 32) data))
                  (clint_dispatch ())
                  (pure (Ok true)))
              else
                (do
                  if (((addr == MTIME_BASE) && (width == 8)) : Bool)
                  then
                    (do
                      let _ : Unit :=
                        if ((get_config_print_platform ()) : Bool)
                        then
                          (print_endline
                            (HAppend.hAppend "clint<8>["
                              (HAppend.hAppend (BitVec.toFormatted addr)
                                (HAppend.hAppend "] <- "
                                  (HAppend.hAppend (BitVec.toFormatted data) " (mtime)")))))
                        else ()
                      writeReg mtime data
                      (clint_dispatch ())
                      (pure (Ok true)))
                  else
                    (do
                      if (((addr == MTIME_BASE) && (width == 4)) : Bool)
                      then
                        (do
                          let _ : Unit :=
                            if ((get_config_print_platform ()) : Bool)
                            then
                              (print_endline
                                (HAppend.hAppend "clint<4>["
                                  (HAppend.hAppend (BitVec.toFormatted addr)
                                    (HAppend.hAppend "] <- "
                                      (HAppend.hAppend (BitVec.toFormatted data) " (mtime)")))))
                            else ()
                          writeReg mtime (Sail.BitVec.updateSubrange (← readReg mtime) 31 0 data)
                          (clint_dispatch ())
                          (pure (Ok true)))
                      else
                        (do
                          if (((addr == MTIME_BASE_HI) && (width == 4)) : Bool)
                          then
                            (do
                              let _ : Unit :=
                                if ((get_config_print_platform ()) : Bool)
                                then
                                  (print_endline
                                    (HAppend.hAppend "clint<4>["
                                      (HAppend.hAppend (BitVec.toFormatted addr)
                                        (HAppend.hAppend "] <- "
                                          (HAppend.hAppend (BitVec.toFormatted data) " (mtime)")))))
                                else ()
                              writeReg mtime (Sail.BitVec.updateSubrange (← readReg mtime) 63 32
                                data)
                              (clint_dispatch ())
                              (pure (Ok true)))
                          else
                            (let _ : Unit :=
                              if ((get_config_print_platform ()) : Bool)
                              then
                                (print_endline
                                  (HAppend.hAppend "clint["
                                    (HAppend.hAppend (BitVec.toFormatted addr)
                                      (HAppend.hAppend "] <- "
                                        (HAppend.hAppend (BitVec.toFormatted data) " (<unmapped>)")))))
                              else ()
                            (pure (Err (E_SAMO_Access_Fault ()))))))))))

def should_inc_mcycle (priv : Privilege) : SailM Bool := do
  (pure (((_get_Counterin_CY (← readReg mcountinhibit)) == (0b0 : (BitVec 1))) && ((counter_priv_filter_bit
          (← readReg mcyclecfg) priv) == (0b0 : (BitVec 1)))))

def should_inc_minstret (priv : Privilege) : SailM Bool := do
  (pure (((_get_Counterin_IR (← readReg mcountinhibit)) == (0b0 : (BitVec 1))) && ((counter_priv_filter_bit
          (← readReg minstretcfg) priv) == (0b0 : (BitVec 1)))))

def tick_clock (_ : Unit) : SailM Unit := do
  if ((← (should_inc_mcycle (← readReg cur_privilege))) : Bool)
  then writeReg mcycle (BitVec.addInt (← readReg mcycle) 1)
  else (pure ())
  writeReg mtime (BitVec.addInt (← readReg mtime) 1)
  (clint_dispatch ())

def undefined_htif_cmd (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_htif_cmd (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_htif_cmd_cmd (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 55 48)

def _update_htif_cmd_cmd (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 48 x)

def _set_htif_cmd_cmd (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_htif_cmd_cmd r v)

def _get_htif_cmd_device (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 63 56)

def _update_htif_cmd_device (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 56 x)

def _set_htif_cmd_device (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_htif_cmd_device r v)

def _get_htif_cmd_payload (v : (BitVec 64)) : (BitVec 48) :=
  (Sail.BitVec.extractLsb v 47 0)

def _update_htif_cmd_payload (v : (BitVec 64)) (x : (BitVec 48)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 0 x)

def _set_htif_cmd_payload (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 48)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_htif_cmd_payload r v)

def reset_htif (_ : Unit) : SailM Unit := do
  writeReg htif_cmd_write 0#1
  writeReg htif_payload_writes (0x0 : (BitVec 4))
  writeReg htif_tohost (zeros (n := 64))

/-- Type quantifiers: width : Nat, width ≥ 0, width > 0 -/
def htif_load (t : (AccessType Unit)) (app_1 : physaddr) (width : Nat) : SailM (Result (BitVec (8 * width)) ExceptionType) := do
  let .Physaddr paddr := app_1
  if ((get_config_print_platform ()) : Bool)
  then
    (pure (print_endline
        (HAppend.hAppend "htif["
          (HAppend.hAppend (hex_bits_str paddr)
            (HAppend.hAppend "] -> " (BitVec.toFormatted (← readReg htif_tohost)))))))
  else (pure ())
  if (((width == 8) && (paddr == (htif_tohost_base ()))) : Bool)
  then (pure (Ok (zero_extend (m := 64) (← readReg htif_tohost))))
  else
    (do
      if (((width == 4) && (paddr == (htif_tohost_base ()))) : Bool)
      then
        (pure (Ok (zero_extend (m := 32) (Sail.BitVec.extractLsb (← readReg htif_tohost) 31 0))))
      else
        (do
          if (((width == 4) && (paddr == (BitVec.addInt (htif_tohost_base ()) 4))) : Bool)
          then
            (pure (Ok
                (zero_extend (m := 32) (Sail.BitVec.extractLsb (← readReg htif_tohost) 63 32))))
          else
            (match t with
            | .InstructionFetch () => (pure (Err (E_Fetch_Access_Fault ())))
            | .Read Data => (pure (Err (E_Load_Access_Fault ())))
            | _ => (pure (Err (E_SAMO_Access_Fault ()))))))

/-- Type quantifiers: width : Nat, width ≥ 0, 0 < width ∧ width ≤ 8 -/
def htif_store (app_0 : physaddr) (width : Nat) (data : (BitVec (8 * width))) : SailM (Result Bool ExceptionType) := do
  let .Physaddr paddr := app_0
  let _ : Unit :=
    if ((get_config_print_platform ()) : Bool)
    then
      (print_endline
        (HAppend.hAppend "htif["
          (HAppend.hAppend (hex_bits_str paddr) (HAppend.hAppend "] <- " (BitVec.toFormatted data)))))
    else ()
  if ((width == 8) : Bool)
  then
    (do
      writeReg htif_cmd_write 1#1
      writeReg htif_payload_writes (BitVec.addInt (← readReg htif_payload_writes) 1)
      writeReg htif_tohost (zero_extend (m := 64) data))
  else
    (do
      if (((width == 4) && (paddr == (htif_tohost_base ()))) : Bool)
      then
        (do
          if ((data == (Sail.BitVec.extractLsb (← readReg htif_tohost) 31 0)) : Bool)
          then writeReg htif_payload_writes (BitVec.addInt (← readReg htif_payload_writes) 1)
          else writeReg htif_payload_writes (0x1 : (BitVec 4))
          writeReg htif_tohost (Sail.BitVec.updateSubrange (← readReg htif_tohost) 31 0 data))
      else
        (do
          if (((width == 4) && (paddr == (BitVec.addInt (htif_tohost_base ()) 4))) : Bool)
          then
            (do
              if (((Sail.BitVec.extractLsb data 15 0) == (Sail.BitVec.extractLsb
                     (← readReg htif_tohost) 47 32)) : Bool)
              then writeReg htif_payload_writes (BitVec.addInt (← readReg htif_payload_writes) 1)
              else writeReg htif_payload_writes (0x1 : (BitVec 4))
              writeReg htif_cmd_write 1#1
              writeReg htif_tohost (Sail.BitVec.updateSubrange (← readReg htif_tohost) 63 32 data))
          else writeReg htif_tohost (zero_extend (m := 64) data)))
  if (((((← readReg htif_cmd_write) == 1#1) && (← do
           (pure ((BitVec.toNat (← readReg htif_payload_writes)) >b 0)))) || (← do
         (pure ((BitVec.toNat (← readReg htif_payload_writes)) >b 2)))) : Bool)
  then
    (do
      let cmd ← do (pure (Mk_htif_cmd (← readReg htif_tohost)))
      let b__0 := (_get_htif_cmd_device cmd)
      if ((b__0 == (0x00 : (BitVec 8))) : Bool)
      then
        (do
          let _ : Unit :=
            if ((get_config_print_platform ()) : Bool)
            then
              (print_endline
                (HAppend.hAppend "htif-syscall-proxy cmd: "
                  (BitVec.toFormatted (_get_htif_cmd_payload cmd))))
            else ()
          if (((BitVec.access (_get_htif_cmd_payload cmd) 0) == 1#1) : Bool)
          then
            (do
              writeReg htif_done true
              writeReg htif_exit_code (shiftr (zero_extend (m := 64) (_get_htif_cmd_payload cmd)) 1))
          else (pure ()))
      else
        (do
          if ((b__0 == (0x01 : (BitVec 8))) : Bool)
          then
            (do
              let _ : Unit :=
                if ((get_config_print_platform ()) : Bool)
                then
                  (print_endline
                    (HAppend.hAppend "htif-term cmd: "
                      (BitVec.toFormatted (_get_htif_cmd_payload cmd))))
                else ()
              let b__2 := (_get_htif_cmd_cmd cmd)
              if ((b__2 == (0x00 : (BitVec 8))) : Bool)
              then (pure ())
              else
                (do
                  if ((b__2 == (0x01 : (BitVec 8))) : Bool)
                  then (plat_term_write (Sail.BitVec.extractLsb (_get_htif_cmd_payload cmd) 7 0))
                  else
                    (pure (print (HAppend.hAppend "Unknown term cmd: " (BitVec.toFormatted b__2)))))
              (reset_htif ()))
          else (pure (print (HAppend.hAppend "htif-???? cmd: " (BitVec.toFormatted data))))))
  else (pure ())
  (pure (Ok true))

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def within_mmio_readable (addr : physaddr) (width : Nat) : SailM Bool := do
  if ((get_config_rvfi ()) : Bool)
  then (pure false)
  else
    (pure ((← (within_clint addr width)) || ((within_htif_readable addr width) && (1 ≤b width))))

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def within_mmio_writable (addr : physaddr) (width : Nat) : SailM Bool := do
  if ((get_config_rvfi ()) : Bool)
  then (pure false)
  else
    (pure ((← (within_clint addr width)) || ((within_htif_writable addr width) && (width ≤b 8))))

/-- Type quantifiers: width : Nat, width ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mmio_read (t : (AccessType Unit)) (paddr : physaddr) (width : Nat) : SailM (Result (BitVec (8 * width)) ExceptionType) := do
  if ((← (within_clint paddr width)) : Bool)
  then (clint_load t paddr width)
  else
    (do
      if (((within_htif_readable paddr width) && (1 ≤b width)) : Bool)
      then (htif_load t paddr width)
      else
        (match t with
        | .InstructionFetch () => (pure (Err (E_Fetch_Access_Fault ())))
        | .Read Data => (pure (Err (E_Load_Access_Fault ())))
        | _ => (pure (Err (E_SAMO_Access_Fault ())))))

/-- Type quantifiers: width : Nat, width ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mmio_write (paddr : physaddr) (width : Nat) (data : (BitVec (8 * width))) : SailM (Result Bool ExceptionType) := do
  if ((← (within_clint paddr width)) : Bool)
  then (clint_store paddr width data)
  else
    (do
      if (((within_htif_writable paddr width) && (width ≤b 8)) : Bool)
      then (htif_store paddr width data)
      else (pure (Err (E_SAMO_Access_Fault ()))))

def init_platform (_ : Unit) : SailM Unit := do
  writeReg htif_tohost (zeros (n := 64))
  writeReg htif_done false
  writeReg htif_exit_code (zeros (n := 64))
  writeReg htif_cmd_write 0#1
  writeReg htif_payload_writes (zeros (n := 4))

def handle_illegal (instbits : (BitVec 32)) : SailM Unit := do
  let info :=
    if (plat_mtval_has_illegal_inst_bits : Bool)
    then (some (zero_extend (m := xlen) instbits))
    else none
  let t : sync_exception :=
    { trap := (E_Illegal_Instr ())
      excinfo := info
      ext := none }
  (set_next_pc (← (exception_handler (← readReg cur_privilege) (CTL_TRAP t) (← readReg PC))))

def platform_wfi (_ : Unit) : Unit :=
  ()


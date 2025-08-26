import LeanRV64D.Flow
import LeanRV64D.Prelude
import LeanRV64D.RiscvErrors
import LeanRV64D.RiscvXlen
import LeanRV64D.RiscvExtensions
import LeanRV64D.RiscvTypes
import LeanRV64D.RiscvCallbacks
import LeanRV64D.RiscvRegs
import LeanRV64D.RiscvPcAccess
import LeanRV64D.RiscvSysRegs
import LeanRV64D.RiscvSysExceptions
import LeanRV64D.RiscvPmpRegs
import LeanRV64D.RiscvPmpControl
import LeanRV64D.RiscvVextRegs

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
open Ext_FetchAddr_Check
open Ext_DataAddr_Check
open Ext_ControlAddr_Check
open ExtStatus
open ExecutionResult
open ExceptionType
open Architecture
open AccessType

def effectivePrivilege (t : (AccessType Unit)) (m : (BitVec 64)) (priv : Privilege) : SailM Privilege := do
  if (((bne t (InstructionFetch ())) && ((_get_Mstatus_MPRV m) == (0b1 : (BitVec 1)))) : Bool)
  then (privLevel_of_bits (_get_Mstatus_MPP m))
  else (pure priv)

def csrAccess (csr : (BitVec 12)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb csr 11 10)

def csrPriv (csr : (BitVec 12)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb csr 9 8)

def check_CSR_priv (csr : (BitVec 12)) (p : Privilege) : Bool :=
  (zopz0zKzJ_u (privLevel_to_bits p) (csrPriv csr))

/-- Type quantifiers: k_ex373816# : Bool -/
def check_CSR_access (csr : (BitVec 12)) (isWrite : Bool) : Bool :=
  (not (isWrite && ((csrAccess csr) == (0b11 : (BitVec 2)))))

def sstc_CSRs_accessible (priv : Privilege) : SailM Bool := do
  (pure ((priv == Machine) || ((priv == Supervisor) && (((_get_Counteren_TM (← readReg mcounteren)) == (0b1 : (BitVec 1))) && ((_get_MEnvcfg_STCE
              (← readReg menvcfg)) == (0b1 : (BitVec 1)))))))

/-- Type quantifiers: k_ex373852# : Bool -/
def is_CSR_accessible (b__0 : (BitVec 12)) (g__2 : Privilege) (g__3 : Bool) : SailM Bool := do
  if ((b__0 == (0x301 : (BitVec 12))) : Bool)
  then (pure true)
  else
    (do
      if ((b__0 == (0x300 : (BitVec 12))) : Bool)
      then (pure true)
      else
        (do
          if ((b__0 == (0x310 : (BitVec 12))) : Bool)
          then (pure (xlen == 32))
          else
            (do
              if ((b__0 == (0x747 : (BitVec 12))) : Bool)
              then (currentlyEnabled Ext_Zkr)
              else
                (do
                  if ((b__0 == (0x757 : (BitVec 12))) : Bool)
                  then (pure ((← (currentlyEnabled Ext_Zkr)) && (xlen == 32)))
                  else
                    (do
                      if ((b__0 == (0x30A : (BitVec 12))) : Bool)
                      then (currentlyEnabled Ext_U)
                      else
                        (do
                          if ((b__0 == (0x31A : (BitVec 12))) : Bool)
                          then (pure ((← (currentlyEnabled Ext_U)) && (xlen == 32)))
                          else
                            (do
                              if ((b__0 == (0x10A : (BitVec 12))) : Bool)
                              then (currentlyEnabled Ext_S)
                              else
                                (do
                                  if ((b__0 == (0x304 : (BitVec 12))) : Bool)
                                  then (pure true)
                                  else
                                    (do
                                      if ((b__0 == (0x344 : (BitVec 12))) : Bool)
                                      then (pure true)
                                      else
                                        (do
                                          if ((b__0 == (0x302 : (BitVec 12))) : Bool)
                                          then (currentlyEnabled Ext_S)
                                          else
                                            (do
                                              if ((b__0 == (0x312 : (BitVec 12))) : Bool)
                                              then
                                                (pure ((← (currentlyEnabled Ext_S)) && (xlen == 32)))
                                              else
                                                (do
                                                  if ((b__0 == (0x303 : (BitVec 12))) : Bool)
                                                  then (currentlyEnabled Ext_S)
                                                  else
                                                    (do
                                                      if ((b__0 == (0x342 : (BitVec 12))) : Bool)
                                                      then (pure true)
                                                      else
                                                        (do
                                                          if ((b__0 == (0x343 : (BitVec 12))) : Bool)
                                                          then (pure true)
                                                          else
                                                            (do
                                                              if ((b__0 == (0x340 : (BitVec 12))) : Bool)
                                                              then (pure true)
                                                              else
                                                                (do
                                                                  if ((b__0 == (0x106 : (BitVec 12))) : Bool)
                                                                  then (currentlyEnabled Ext_S)
                                                                  else
                                                                    (do
                                                                      if ((b__0 == (0x306 : (BitVec 12))) : Bool)
                                                                      then (currentlyEnabled Ext_U)
                                                                      else
                                                                        (do
                                                                          if ((b__0 == (0x320 : (BitVec 12))) : Bool)
                                                                          then (pure true)
                                                                          else
                                                                            (do
                                                                              if ((b__0 == (0xF11 : (BitVec 12))) : Bool)
                                                                              then (pure true)
                                                                              else
                                                                                (do
                                                                                  if ((b__0 == (0xF12 : (BitVec 12))) : Bool)
                                                                                  then (pure true)
                                                                                  else
                                                                                    (do
                                                                                      if ((b__0 == (0xF13 : (BitVec 12))) : Bool)
                                                                                      then
                                                                                        (pure true)
                                                                                      else
                                                                                        (do
                                                                                          if ((b__0 == (0xF14 : (BitVec 12))) : Bool)
                                                                                          then
                                                                                            (pure true)
                                                                                          else
                                                                                            (do
                                                                                              if ((b__0 == (0xF15 : (BitVec 12))) : Bool)
                                                                                              then
                                                                                                (pure true)
                                                                                              else
                                                                                                (do
                                                                                                  if ((b__0 == (0x100 : (BitVec 12))) : Bool)
                                                                                                  then
                                                                                                    (currentlyEnabled
                                                                                                      Ext_S)
                                                                                                  else
                                                                                                    (do
                                                                                                      if ((b__0 == (0x144 : (BitVec 12))) : Bool)
                                                                                                      then
                                                                                                        (currentlyEnabled
                                                                                                          Ext_S)
                                                                                                      else
                                                                                                        (do
                                                                                                          if ((b__0 == (0x104 : (BitVec 12))) : Bool)
                                                                                                          then
                                                                                                            (currentlyEnabled
                                                                                                              Ext_S)
                                                                                                          else
                                                                                                            (do
                                                                                                              if ((b__0 == (0x140 : (BitVec 12))) : Bool)
                                                                                                              then
                                                                                                                (currentlyEnabled
                                                                                                                  Ext_S)
                                                                                                              else
                                                                                                                (do
                                                                                                                  if ((b__0 == (0x142 : (BitVec 12))) : Bool)
                                                                                                                  then
                                                                                                                    (currentlyEnabled
                                                                                                                      Ext_S)
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      if ((b__0 == (0x143 : (BitVec 12))) : Bool)
                                                                                                                      then
                                                                                                                        (currentlyEnabled
                                                                                                                          Ext_S)
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          if ((b__0 == (0x7A0 : (BitVec 12))) : Bool)
                                                                                                                          then
                                                                                                                            (pure true)
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              if ((b__0 == (0x105 : (BitVec 12))) : Bool)
                                                                                                                              then
                                                                                                                                (currentlyEnabled
                                                                                                                                  Ext_S)
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  if ((b__0 == (0x141 : (BitVec 12))) : Bool)
                                                                                                                                  then
                                                                                                                                    (currentlyEnabled
                                                                                                                                      Ext_S)
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      if ((b__0 == (0x305 : (BitVec 12))) : Bool)
                                                                                                                                      then
                                                                                                                                        (pure true)
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          if ((b__0 == (0x341 : (BitVec 12))) : Bool)
                                                                                                                                          then
                                                                                                                                            (pure true)
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              if (((Sail.BitVec.extractLsb
                                                                                                                                                     b__0
                                                                                                                                                     11
                                                                                                                                                     4) == (0x3A : (BitVec 8))) : Bool)
                                                                                                                                              then
                                                                                                                                                (let idx : (BitVec 4) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    b__0
                                                                                                                                                    3
                                                                                                                                                    0)
                                                                                                                                                (pure ((sys_pmp_count >b (4 *i (BitVec.toNat
                                                                                                                                                          idx))) && (((BitVec.access
                                                                                                                                                          idx
                                                                                                                                                          0) == 0#1) || (xlen == 32)))))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  if (((Sail.BitVec.extractLsb
                                                                                                                                                         b__0
                                                                                                                                                         11
                                                                                                                                                         4) == (0x3B : (BitVec 8))) : Bool)
                                                                                                                                                  then
                                                                                                                                                    (let idx : (BitVec 4) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        b__0
                                                                                                                                                        3
                                                                                                                                                        0)
                                                                                                                                                    (pure (sys_pmp_count >b (BitVec.toNat
                                                                                                                                                          ((0b00 : (BitVec 2)) ++ idx)))))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      if (((Sail.BitVec.extractLsb
                                                                                                                                                             b__0
                                                                                                                                                             11
                                                                                                                                                             4) == (0x3C : (BitVec 8))) : Bool)
                                                                                                                                                      then
                                                                                                                                                        (let idx : (BitVec 4) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            b__0
                                                                                                                                                            3
                                                                                                                                                            0)
                                                                                                                                                        (pure (sys_pmp_count >b (BitVec.toNat
                                                                                                                                                              ((0b01 : (BitVec 2)) ++ idx)))))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          if (((Sail.BitVec.extractLsb
                                                                                                                                                                 b__0
                                                                                                                                                                 11
                                                                                                                                                                 4) == (0x3D : (BitVec 8))) : Bool)
                                                                                                                                                          then
                                                                                                                                                            (let idx : (BitVec 4) :=
                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                b__0
                                                                                                                                                                3
                                                                                                                                                                0)
                                                                                                                                                            (pure (sys_pmp_count >b (BitVec.toNat
                                                                                                                                                                  ((0b10 : (BitVec 2)) ++ idx)))))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              if (((Sail.BitVec.extractLsb
                                                                                                                                                                     b__0
                                                                                                                                                                     11
                                                                                                                                                                     4) == (0x3E : (BitVec 8))) : Bool)
                                                                                                                                                              then
                                                                                                                                                                (let idx : (BitVec 4) :=
                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                    b__0
                                                                                                                                                                    3
                                                                                                                                                                    0)
                                                                                                                                                                (pure (sys_pmp_count >b (BitVec.toNat
                                                                                                                                                                      ((0b11 : (BitVec 2)) ++ idx)))))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  if ((b__0 == (0x001 : (BitVec 12))) : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (pure ((← (currentlyEnabled
                                                                                                                                                                            Ext_F)) || (← (currentlyEnabled
                                                                                                                                                                            Ext_Zfinx))))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      if ((b__0 == (0x002 : (BitVec 12))) : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (pure ((← (currentlyEnabled
                                                                                                                                                                                Ext_F)) || (← (currentlyEnabled
                                                                                                                                                                                Ext_Zfinx))))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          if ((b__0 == (0x003 : (BitVec 12))) : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (pure ((← (currentlyEnabled
                                                                                                                                                                                    Ext_F)) || (← (currentlyEnabled
                                                                                                                                                                                    Ext_Zfinx))))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              if ((b__0 == (0x008 : (BitVec 12))) : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                (currentlyEnabled
                                                                                                                                                                                  Ext_V)
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  if ((b__0 == (0x009 : (BitVec 12))) : Bool)
                                                                                                                                                                                  then
                                                                                                                                                                                    (currentlyEnabled
                                                                                                                                                                                      Ext_V)
                                                                                                                                                                                  else
                                                                                                                                                                                    (do
                                                                                                                                                                                      if ((b__0 == (0x00A : (BitVec 12))) : Bool)
                                                                                                                                                                                      then
                                                                                                                                                                                        (currentlyEnabled
                                                                                                                                                                                          Ext_V)
                                                                                                                                                                                      else
                                                                                                                                                                                        (do
                                                                                                                                                                                          if ((b__0 == (0x00F : (BitVec 12))) : Bool)
                                                                                                                                                                                          then
                                                                                                                                                                                            (currentlyEnabled
                                                                                                                                                                                              Ext_V)
                                                                                                                                                                                          else
                                                                                                                                                                                            (do
                                                                                                                                                                                              if ((b__0 == (0xC20 : (BitVec 12))) : Bool)
                                                                                                                                                                                              then
                                                                                                                                                                                                (currentlyEnabled
                                                                                                                                                                                                  Ext_V)
                                                                                                                                                                                              else
                                                                                                                                                                                                (do
                                                                                                                                                                                                  if ((b__0 == (0xC21 : (BitVec 12))) : Bool)
                                                                                                                                                                                                  then
                                                                                                                                                                                                    (currentlyEnabled
                                                                                                                                                                                                      Ext_V)
                                                                                                                                                                                                  else
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      if ((b__0 == (0xC22 : (BitVec 12))) : Bool)
                                                                                                                                                                                                      then
                                                                                                                                                                                                        (currentlyEnabled
                                                                                                                                                                                                          Ext_V)
                                                                                                                                                                                                      else
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          if ((b__0 == (0x321 : (BitVec 12))) : Bool)
                                                                                                                                                                                                          then
                                                                                                                                                                                                            (currentlyEnabled
                                                                                                                                                                                                              Ext_Smcntrpmf)
                                                                                                                                                                                                          else
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              if ((b__0 == (0x721 : (BitVec 12))) : Bool)
                                                                                                                                                                                                              then
                                                                                                                                                                                                                (pure ((← (currentlyEnabled
                                                                                                                                                                                                                        Ext_Smcntrpmf)) && (xlen == 32)))
                                                                                                                                                                                                              else
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  if ((b__0 == (0x322 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                  then
                                                                                                                                                                                                                    (currentlyEnabled
                                                                                                                                                                                                                      Ext_Smcntrpmf)
                                                                                                                                                                                                                  else
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      if ((b__0 == (0x722 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                      then
                                                                                                                                                                                                                        (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                Ext_Smcntrpmf)) && (xlen == 32)))
                                                                                                                                                                                                                      else
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          if ((b__0 == (0x180 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                          then
                                                                                                                                                                                                                            (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                    Ext_S)) && (not
                                                                                                                                                                                                                                  ((g__2 == Supervisor) && ((_get_Mstatus_TVM
                                                                                                                                                                                                                                        (← readReg mstatus)) == (0b1 : (BitVec 1)))))))
                                                                                                                                                                                                                          else
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              if ((b__0 == (0x015 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                        Ext_Zkr)) && (g__3 && (← do
                                                                                                                                                                                                                                        match g__2 with
                                                                                                                                                                                                                                        | Machine =>
                                                                                                                                                                                                                                          (pure true)
                                                                                                                                                                                                                                        | Supervisor =>
                                                                                                                                                                                                                                          (pure ((_get_Seccfg_SSEED
                                                                                                                                                                                                                                                (← readReg mseccfg)) == (0b1 : (BitVec 1))))
                                                                                                                                                                                                                                        | User =>
                                                                                                                                                                                                                                          (pure ((_get_Seccfg_USEED
                                                                                                                                                                                                                                                (← readReg mseccfg)) == (0b1 : (BitVec 1))))))))
                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  if ((((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                           b__0
                                                                                                                                                                                                                                           11
                                                                                                                                                                                                                                           5) == (0b0011001 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                                                                         (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                           b__0
                                                                                                                                                                                                                                           4
                                                                                                                                                                                                                                           0)
                                                                                                                                                                                                                                       ((BitVec.toNat
                                                                                                                                                                                                                                           index) ≥b 3) : Bool)) : Bool)
                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                    (currentlyEnabled
                                                                                                                                                                                                                                      Ext_Zihpm)
                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      if ((((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                               b__0
                                                                                                                                                                                                                                               11
                                                                                                                                                                                                                                               5) == (0b1011000 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                                                                             (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                               b__0
                                                                                                                                                                                                                                               4
                                                                                                                                                                                                                                               0)
                                                                                                                                                                                                                                           ((BitVec.toNat
                                                                                                                                                                                                                                               index) ≥b 3) : Bool)) : Bool)
                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                        (currentlyEnabled
                                                                                                                                                                                                                                          Ext_Zihpm)
                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          if ((((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                   b__0
                                                                                                                                                                                                                                                   11
                                                                                                                                                                                                                                                   5) == (0b1011100 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                                                                                 (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                   b__0
                                                                                                                                                                                                                                                   4
                                                                                                                                                                                                                                                   0)
                                                                                                                                                                                                                                               ((BitVec.toNat
                                                                                                                                                                                                                                                   index) ≥b 3) : Bool)) : Bool)
                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                            (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                    Ext_Zihpm)) && (xlen == 32)))
                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              if ((((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                       b__0
                                                                                                                                                                                                                                                       11
                                                                                                                                                                                                                                                       5) == (0b1100000 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                                                                                     (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                       b__0
                                                                                                                                                                                                                                                       4
                                                                                                                                                                                                                                                       0)
                                                                                                                                                                                                                                                   ((BitVec.toNat
                                                                                                                                                                                                                                                       index) ≥b 3) : Bool)) : Bool)
                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  let index : (BitVec 5) :=
                                                                                                                                                                                                                                                    (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                      b__0
                                                                                                                                                                                                                                                      4
                                                                                                                                                                                                                                                      0)
                                                                                                                                                                                                                                                  (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                          Ext_Zihpm)) && ((← (currentlyEnabled
                                                                                                                                                                                                                                                            Ext_U)) && (← (counter_enabled
                                                                                                                                                                                                                                                            (BitVec.toNat
                                                                                                                                                                                                                                                              index)
                                                                                                                                                                                                                                                            g__2))))))
                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  if ((((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                           b__0
                                                                                                                                                                                                                                                           11
                                                                                                                                                                                                                                                           5) == (0b1100100 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                                                                                         (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                           b__0
                                                                                                                                                                                                                                                           4
                                                                                                                                                                                                                                                           0)
                                                                                                                                                                                                                                                       ((BitVec.toNat
                                                                                                                                                                                                                                                           index) ≥b 3) : Bool)) : Bool)
                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      let index : (BitVec 5) :=
                                                                                                                                                                                                                                                        (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                          b__0
                                                                                                                                                                                                                                                          4
                                                                                                                                                                                                                                                          0)
                                                                                                                                                                                                                                                      (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                              Ext_Zihpm)) && ((← (currentlyEnabled
                                                                                                                                                                                                                                                                Ext_U)) && ((xlen == 32) && (← (counter_enabled
                                                                                                                                                                                                                                                                  (BitVec.toNat
                                                                                                                                                                                                                                                                    index)
                                                                                                                                                                                                                                                                  g__2)))))))
                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      if ((((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                               b__0
                                                                                                                                                                                                                                                               11
                                                                                                                                                                                                                                                               5) == (0b0111001 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                                                                                             (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                               b__0
                                                                                                                                                                                                                                                               4
                                                                                                                                                                                                                                                               0)
                                                                                                                                                                                                                                                           ((BitVec.toNat
                                                                                                                                                                                                                                                               index) ≥b 3) : Bool)) : Bool)
                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                        (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                Ext_Sscofpmf)) && (xlen == 32)))
                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          if ((b__0 == (0xDA0 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                            (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                    Ext_Sscofpmf)) && (← (currentlyEnabled
                                                                                                                                                                                                                                                                    Ext_S))))
                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              if ((b__0 == (0x14D : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                        Ext_S)) && ((← (currentlyEnabled
                                                                                                                                                                                                                                                                          Ext_Sstc)) && (← (sstc_CSRs_accessible
                                                                                                                                                                                                                                                                          g__2)))))
                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  if ((b__0 == (0x15D : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                    (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                            Ext_S)) && ((← (currentlyEnabled
                                                                                                                                                                                                                                                                              Ext_Sstc)) && ((xlen == 32) && (← (sstc_CSRs_accessible
                                                                                                                                                                                                                                                                                g__2))))))
                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      if ((b__0 == (0xC00 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                        (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                Ext_Zicntr)) && (← (counter_enabled
                                                                                                                                                                                                                                                                                0
                                                                                                                                                                                                                                                                                g__2))))
                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          if ((b__0 == (0xC01 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                            (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                    Ext_Zicntr)) && (← (counter_enabled
                                                                                                                                                                                                                                                                                    1
                                                                                                                                                                                                                                                                                    g__2))))
                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              if ((b__0 == (0xC02 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                        Ext_Zicntr)) && (← (counter_enabled
                                                                                                                                                                                                                                                                                        2
                                                                                                                                                                                                                                                                                        g__2))))
                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  if ((b__0 == (0xC80 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                    (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                            Ext_Zicntr)) && ((xlen == 32) && (← (counter_enabled
                                                                                                                                                                                                                                                                                              0
                                                                                                                                                                                                                                                                                              g__2)))))
                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      if ((b__0 == (0xC81 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                        (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                Ext_Zicntr)) && ((xlen == 32) && (← (counter_enabled
                                                                                                                                                                                                                                                                                                  1
                                                                                                                                                                                                                                                                                                  g__2)))))
                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                          if ((b__0 == (0xC82 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                            (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                    Ext_Zicntr)) && ((xlen == 32) && (← (counter_enabled
                                                                                                                                                                                                                                                                                                      2
                                                                                                                                                                                                                                                                                                      g__2)))))
                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                              if ((b__0 == (0xB00 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                (currentlyEnabled
                                                                                                                                                                                                                                                                                                  Ext_Zicntr)
                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                  if ((b__0 == (0xB02 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                    (currentlyEnabled
                                                                                                                                                                                                                                                                                                      Ext_Zicntr)
                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                      if ((b__0 == (0xB80 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                        (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                Ext_Zicntr)) && (xlen == 32)))
                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                          if ((b__0 == (0xB82 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                            (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                    Ext_Zicntr)) && (xlen == 32)))
                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                            (pure false)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Type quantifiers: k_ex374443# : Bool -/
def check_CSR (csr : (BitVec 12)) (p : Privilege) (isWrite : Bool) : SailM Bool := do
  (pure ((check_CSR_priv csr p) && ((check_CSR_access csr isWrite) && (← (is_CSR_accessible csr p
            isWrite)))))

def exception_delegatee (e : ExceptionType) (p : Privilege) : SailM Privilege := do
  let idx := (num_of_ExceptionType e)
  let super ← do (bit_to_bool (BitVec.access (← readReg medeleg) idx))
  let deleg ← do
    if (((← (currentlyEnabled Ext_S)) && super) : Bool)
    then (pure Supervisor)
    else (pure Machine)
  if ((zopz0zI_u (privLevel_to_bits deleg) (privLevel_to_bits p)) : Bool)
  then (pure p)
  else (pure deleg)

def findPendingInterrupt (ip : (BitVec 64)) : (Option InterruptType) :=
  let ip := (Mk_Minterrupts ip)
  if (((_get_Minterrupts_MEI ip) == (0b1 : (BitVec 1))) : Bool)
  then (some I_M_External)
  else
    (if (((_get_Minterrupts_MSI ip) == (0b1 : (BitVec 1))) : Bool)
    then (some I_M_Software)
    else
      (if (((_get_Minterrupts_MTI ip) == (0b1 : (BitVec 1))) : Bool)
      then (some I_M_Timer)
      else
        (if (((_get_Minterrupts_SEI ip) == (0b1 : (BitVec 1))) : Bool)
        then (some I_S_External)
        else
          (if (((_get_Minterrupts_SSI ip) == (0b1 : (BitVec 1))) : Bool)
          then (some I_S_Software)
          else
            (if (((_get_Minterrupts_STI ip) == (0b1 : (BitVec 1))) : Bool)
            then (some I_S_Timer)
            else none)))))

def getPendingSet (priv : Privilege) : SailM (Option ((BitVec 64) × Privilege)) := do
  assert ((← (currentlyEnabled Ext_S)) || ((← readReg mideleg) == (zeros (n := 64)))) "riscv_sys_control.sail:70.58-70.59"
  let pending_m ← do
    (pure ((← readReg mip) &&& ((← readReg mie) &&& (Complement.complement (← readReg mideleg)))))
  let pending_s ← do (pure ((← readReg mip) &&& ((← readReg mie) &&& (← readReg mideleg))))
  let mIE ← do
    (pure (((priv == Machine) && ((_get_Mstatus_MIE (← readReg mstatus)) == (0b1 : (BitVec 1)))) || ((priv == Supervisor) || (priv == User))))
  let sIE ← do
    (pure (((priv == Supervisor) && ((_get_Mstatus_SIE (← readReg mstatus)) == (0b1 : (BitVec 1)))) || (priv == User)))
  if ((mIE && (pending_m != (zeros (n := 64)))) : Bool)
  then (pure (some (pending_m, Machine)))
  else
    (if ((sIE && (pending_s != (zeros (n := 64)))) : Bool)
    then (pure (some (pending_s, Supervisor)))
    else (pure none))

def shouldWakeForInterrupt (_ : Unit) : SailM Bool := do
  (pure (((← readReg mip) &&& (← readReg mie)) != (zeros (n := 64))))

def dispatchInterrupt (priv : Privilege) : SailM (Option (InterruptType × Privilege)) := do
  match (← (getPendingSet priv)) with
  | none => (pure none)
  | .some (ip, p) =>
    (match (findPendingInterrupt ip) with
    | none => (pure none)
    | .some i => (pure (some (i, p))))

def tval (excinfo : (Option (BitVec 64))) : (BitVec 64) :=
  match excinfo with
  | .some e => e
  | none => (zeros (n := 64))

def track_trap (p : Privilege) : SailM Unit := do
  (long_csr_write_callback "mstatus" "mstatush" (← readReg mstatus))
  match p with
  | Machine =>
    (do
      (csr_name_write_callback "mcause" (← readReg mcause))
      (csr_name_write_callback "mtval" (← readReg mtval))
      (csr_name_write_callback "mepc" (← readReg mepc)))
  | Supervisor =>
    (do
      (csr_name_write_callback "scause" (← readReg scause))
      (csr_name_write_callback "stval" (← readReg stval))
      (csr_name_write_callback "sepc" (← readReg sepc)))
  | User => (internal_error "riscv_sys_control.sail" 150 "Invalid privilege level")

/-- Type quantifiers: k_ex374509# : Bool -/
def trap_handler (del_priv : Privilege) (intr : Bool) (c : (BitVec 8)) (pc : (BitVec 64)) (info : (Option (BitVec 64))) (ext : (Option Unit)) : SailM (BitVec 64) := do
  let _ : Unit := (trap_callback ())
  let _ : Unit :=
    if ((get_config_print_platform ()) : Bool)
    then
      (print_endline
        (HAppend.hAppend "handling "
          (HAppend.hAppend
            (if (intr : Bool)
            then "int#"
            else "exc#")
            (HAppend.hAppend (BitVec.toFormatted c)
              (HAppend.hAppend " at priv "
                (HAppend.hAppend (privLevel_to_str del_priv)
                  (HAppend.hAppend " with tval " (BitVec.toFormatted (tval info)))))))))
    else ()
  match del_priv with
  | Machine =>
    (do
      writeReg mcause (Sail.BitVec.updateSubrange (← readReg mcause) (64 -i 1) (64 -i 1)
        (bool_to_bits intr))
      writeReg mcause (Sail.BitVec.updateSubrange (← readReg mcause) (64 -i 2) 0
        (zero_extend (m := (64 -i 1)) c))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 7 7
        (_get_Mstatus_MIE (← readReg mstatus)))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 3 3 (0b0 : (BitVec 1)))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 12 11
        (privLevel_to_bits (← readReg cur_privilege)))
      writeReg mtval (tval info)
      writeReg mepc pc
      writeReg cur_privilege del_priv
      let _ : Unit := (handle_trap_extension del_priv pc ext)
      (track_trap del_priv)
      (prepare_trap_vector del_priv (← readReg mcause)))
  | Supervisor =>
    (do
      assert (← (currentlyEnabled Ext_S)) "no supervisor mode present for delegation"
      writeReg scause (Sail.BitVec.updateSubrange (← readReg scause) (64 -i 1) (64 -i 1)
        (bool_to_bits intr))
      writeReg scause (Sail.BitVec.updateSubrange (← readReg scause) (64 -i 2) 0
        (zero_extend (m := (64 -i 1)) c))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 5 5
        (_get_Mstatus_SIE (← readReg mstatus)))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 1 1 (0b0 : (BitVec 1)))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 8 8
        (← do
          match (← readReg cur_privilege) with
          | User => (pure (0b0 : (BitVec 1)))
          | Supervisor => (pure (0b1 : (BitVec 1)))
          | Machine =>
            (internal_error "riscv_sys_control.sail" 193 "invalid privilege for s-mode trap")))
      writeReg stval (tval info)
      writeReg sepc pc
      writeReg cur_privilege del_priv
      let _ : Unit := (handle_trap_extension del_priv pc ext)
      (track_trap del_priv)
      (prepare_trap_vector del_priv (← readReg scause)))
  | User => (internal_error "riscv_sys_control.sail" 206 "Invalid privilege level")

def exception_handler (cur_priv : Privilege) (ctl : ctl_result) (pc : (BitVec 64)) : SailM (BitVec 64) := do
  match (cur_priv, ctl) with
  | (_, .CTL_TRAP e) =>
    (do
      let del_priv ← do (exception_delegatee e.trap cur_priv)
      let _ : Unit :=
        if ((get_config_print_platform ()) : Bool)
        then
          (print_endline
            (HAppend.hAppend "trapping from "
              (HAppend.hAppend (privLevel_to_str cur_priv)
                (HAppend.hAppend " to "
                  (HAppend.hAppend (privLevel_to_str del_priv)
                    (HAppend.hAppend " to handle " (exceptionType_to_str e.trap)))))))
        else ()
      (trap_handler del_priv false (exceptionType_to_bits e.trap) pc e.excinfo e.ext))
  | (_, .CTL_MRET ()) =>
    (do
      let prev_priv ← do readReg cur_privilege
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 3 3
        (_get_Mstatus_MPIE (← readReg mstatus)))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 7 7 (0b1 : (BitVec 1)))
      writeReg cur_privilege (← (privLevel_of_bits (_get_Mstatus_MPP (← readReg mstatus))))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 12 11
        (privLevel_to_bits
          (← do
            if ((← (currentlyEnabled Ext_U)) : Bool)
            then (pure User)
            else (pure Machine))))
      if ((bne (← readReg cur_privilege) Machine) : Bool)
      then
        writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 17 17 (0b0 : (BitVec 1)))
      else (pure ())
      (long_csr_write_callback "mstatus" "mstatush" (← readReg mstatus))
      if ((get_config_print_platform ()) : Bool)
      then
        (pure (print_endline
            (HAppend.hAppend "ret-ing from "
              (HAppend.hAppend (privLevel_to_str prev_priv)
                (HAppend.hAppend " to " (privLevel_to_str (← readReg cur_privilege)))))))
      else (pure ())
      (prepare_xret_target Machine))
  | (_, .CTL_SRET ()) =>
    (do
      let prev_priv ← do readReg cur_privilege
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 1 1
        (_get_Mstatus_SPIE (← readReg mstatus)))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 5 5 (0b1 : (BitVec 1)))
      writeReg cur_privilege (← do
        if (((_get_Mstatus_SPP (← readReg mstatus)) == (0b1 : (BitVec 1))) : Bool)
        then (pure Supervisor)
        else (pure User))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 8 8 (0b0 : (BitVec 1)))
      if ((bne (← readReg cur_privilege) Machine) : Bool)
      then
        writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 17 17 (0b0 : (BitVec 1)))
      else (pure ())
      (long_csr_write_callback "mstatus" "mstatush" (← readReg mstatus))
      if ((get_config_print_platform ()) : Bool)
      then
        (pure (print_endline
            (HAppend.hAppend "ret-ing from "
              (HAppend.hAppend (privLevel_to_str prev_priv)
                (HAppend.hAppend " to " (privLevel_to_str (← readReg cur_privilege)))))))
      else (pure ())
      (prepare_xret_target Supervisor))

def handle_mem_exception (typ_0 : virtaddr) (e : ExceptionType) : SailM Unit := do
  let .Virtaddr addr : virtaddr := typ_0
  let t : sync_exception :=
    { trap := e
      excinfo := (some addr)
      ext := none }
  (set_next_pc (← (exception_handler (← readReg cur_privilege) (CTL_TRAP t) (← readReg PC))))

def handle_exception (e : ExceptionType) : SailM Unit := do
  let t : sync_exception :=
    { trap := e
      excinfo := none
      ext := none }
  (set_next_pc (← (exception_handler (← readReg cur_privilege) (CTL_TRAP t) (← readReg PC))))

def handle_interrupt (i : InterruptType) (del_priv : Privilege) : SailM Unit := do
  (set_next_pc
    (← (trap_handler del_priv true (interruptType_to_bits i) (← readReg PC) none none)))

def reset_misa (_ : Unit) : SailM Unit := do
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 0 0
    (bool_to_bits (hartSupports Ext_A)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 2 2
    (bool_to_bits (hartSupports Ext_C)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 1 1
    (bool_to_bits (hartSupports Ext_B)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 12 12
    (bool_to_bits (hartSupports Ext_M)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 20 20
    (bool_to_bits (hartSupports Ext_U)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 18 18
    (bool_to_bits (hartSupports Ext_S)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 21 21
    (bool_to_bits (hartSupports Ext_V)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 4 4 (bool_to_bits base_E_enabled))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 8 8
    (Complement.complement (_get_Misa_E (← readReg misa))))
  if (((hartSupports Ext_F) && (hartSupports Ext_Zfinx)) : Bool)
  then (internal_error "riscv_sys_control.sail" 288 "F and Zfinx cannot both be enabled!")
  else (pure ())
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 5 5
    (bool_to_bits (hartSupports Ext_F)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 3 3
    (bool_to_bits (hartSupports Ext_D)))
  (csr_name_write_callback "misa" (← readReg misa))

def reset_sys (_ : Unit) : SailM Unit := do
  writeReg cur_privilege Machine
  writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 3 3 (0b0 : (BitVec 1)))
  writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 17 17 (0b0 : (BitVec 1)))
  (long_csr_write_callback "mstatus" "mstatush" (← readReg mstatus))
  (reset_misa ())
  (cancel_reservation ())
  writeReg mcause (zeros (n := 64))
  (csr_name_write_callback "mcause" (← readReg mcause))
  (reset_pmp ())
  writeReg mseccfg (Sail.BitVec.updateSubrange (← readReg mseccfg) 9 9
    (bool_to_bits (false : Bool)))
  writeReg mseccfg (Sail.BitVec.updateSubrange (← readReg mseccfg) 8 8
    (bool_to_bits (false : Bool)))
  writeReg vstart (zeros (n := 64))
  writeReg vl (zeros (n := 64))
  writeReg vcsr (Sail.BitVec.updateSubrange (← readReg vcsr) 2 1 (0b00 : (BitVec 2)))
  writeReg vcsr (Sail.BitVec.updateSubrange (← readReg vcsr) 0 0 (0b0 : (BitVec 1)))
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) (64 -i 1) (64 -i 1)
    (0b1 : (BitVec 1)))
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) (64 -i 2) 8
    (zeros (n := (64 -i 9))))
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) 7 7 (0b0 : (BitVec 1)))
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) 6 6 (0b0 : (BitVec 1)))
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) 5 3 (0b000 : (BitVec 3)))
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) 2 0 (0b000 : (BitVec 3)))

/-- Type quantifiers: k_t : Type -/
def MemoryOpResult_add_meta (r : (Result k_t ExceptionType)) (m : Unit) : (Result (k_t × Unit) ExceptionType) :=
  match r with
  | .Ok v => (Ok (v, m))
  | .Err e => (Err e)

/-- Type quantifiers: k_t : Type -/
def MemoryOpResult_drop_meta (r : (Result (k_t × Unit) ExceptionType)) : (Result k_t ExceptionType) :=
  match r with
  | .Ok (v, m) => (Ok v)
  | .Err e => (Err e)


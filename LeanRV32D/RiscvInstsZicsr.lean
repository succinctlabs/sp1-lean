import LeanRV32D.Prelude
import LeanRV32D.RiscvErrors
import LeanRV32D.RiscvXlen
import LeanRV32D.RiscvTypes
import LeanRV32D.RiscvCallbacks
import LeanRV32D.RiscvRegs
import LeanRV32D.RiscvSysRegs
import LeanRV32D.RiscvPmpRegs
import LeanRV32D.RiscvExtRegs
import LeanRV32D.RiscvVextRegs
import LeanRV32D.RiscvVextControl
import LeanRV32D.RiscvSysExceptions
import LeanRV32D.RiscvZihpm
import LeanRV32D.RiscvSscofpmf
import LeanRV32D.RiscvZkrControl
import LeanRV32D.RiscvFdextRegs
import LeanRV32D.RiscvSmcntrpmf
import LeanRV32D.RiscvSysControl
import LeanRV32D.RiscvInstRetire

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

noncomputable section

namespace LeanRV32D.Functions

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
open nisfunct6
open nifunct6
open mvxmafunct6
open mvxfunct6
open mvvmafunct6
open mvvfunct6
open mmfunct6
open maskfunct3
open iop
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
open cbop_zicbom
open cbie
open bropw_zbb
open bropw_zba
open brop_zbs
open brop_zbkb
open brop_zbb
open brop_zba
open bop
open biop_zbs
open barrier_kind
open ast
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
open Ext_PhysAddr_Check
open Ext_FetchAddr_Check
open Ext_DataAddr_Check
open Ext_ControlAddr_Check
open ExtStatus
open ExecutionResult
open ExceptionType
open Architecture
open AccessType

def encdec_csrop_forwards (arg_ : csrop) : (BitVec 2) :=
  match arg_ with
  | CSRRW => (0b01 : (BitVec 2))
  | CSRRS => (0b10 : (BitVec 2))
  | CSRRC => (0b11 : (BitVec 2))

def encdec_csrop_backwards (arg_ : (BitVec 2)) : SailM csrop := do
  let b__0 := arg_
  bif (b__0 == (0b01 : (BitVec 2)))
  then (pure CSRRW)
  else
    (do
      bif (b__0 == (0b10 : (BitVec 2)))
      then (pure CSRRS)
      else
        (do
          bif (b__0 == (0b11 : (BitVec 2)))
          then (pure CSRRC)
          else
            (do
              assert false "Pattern match failure at unknown location"
              throw Error.Exit)))

def encdec_csrop_forwards_matches (arg_ : csrop) : Bool :=
  match arg_ with
  | CSRRW => true
  | CSRRS => true
  | CSRRC => true

def encdec_csrop_backwards_matches (arg_ : (BitVec 2)) : Bool :=
  let b__0 := arg_
  bif (b__0 == (0b01 : (BitVec 2)))
  then true
  else
    (bif (b__0 == (0b10 : (BitVec 2)))
    then true
    else
      (bif (b__0 == (0b11 : (BitVec 2)))
      then true
      else false))

def read_CSR (b__0 : (BitVec 12)) : SailM (BitVec 32) := do
  bif (b__0 == (0x301 : (BitVec 12)))
  then readReg misa
  else
    (do
      bif (b__0 == (0x300 : (BitVec 12)))
      then (pure (Sail.BitVec.extractLsb (← readReg mstatus) (xlen -i 1) 0))
      else
        (do
          bif ((b__0 == (0x310 : (BitVec 12))) && (xlen == 32))
          then (pure (Sail.BitVec.extractLsb (← readReg mstatus) 63 32))
          else
            (do
              bif (b__0 == (0x747 : (BitVec 12)))
              then (pure (Sail.BitVec.extractLsb (← readReg mseccfg) (xlen -i 1) 0))
              else
                (do
                  bif ((b__0 == (0x757 : (BitVec 12))) && (xlen == 32))
                  then (pure (Sail.BitVec.extractLsb (← readReg mseccfg) 63 32))
                  else
                    (do
                      bif (b__0 == (0x30A : (BitVec 12)))
                      then (pure (Sail.BitVec.extractLsb (← readReg menvcfg) (xlen -i 1) 0))
                      else
                        (do
                          bif ((b__0 == (0x31A : (BitVec 12))) && (xlen == 32))
                          then (pure (Sail.BitVec.extractLsb (← readReg menvcfg) 63 32))
                          else
                            (do
                              bif (b__0 == (0x10A : (BitVec 12)))
                              then
                                (pure (Sail.BitVec.extractLsb (← readReg senvcfg) (xlen -i 1) 0))
                              else
                                (do
                                  bif (b__0 == (0x304 : (BitVec 12)))
                                  then readReg mie
                                  else
                                    (do
                                      bif (b__0 == (0x344 : (BitVec 12)))
                                      then readReg mip
                                      else
                                        (do
                                          bif (b__0 == (0x302 : (BitVec 12)))
                                          then
                                            (pure (Sail.BitVec.extractLsb (← readReg medeleg)
                                                (xlen -i 1) 0))
                                          else
                                            (do
                                              bif ((b__0 == (0x312 : (BitVec 12))) && (xlen == 32))
                                              then
                                                (pure (Sail.BitVec.extractLsb (← readReg medeleg)
                                                    63 32))
                                              else
                                                (do
                                                  bif (b__0 == (0x303 : (BitVec 12)))
                                                  then readReg mideleg
                                                  else
                                                    (do
                                                      bif (b__0 == (0x342 : (BitVec 12)))
                                                      then readReg mcause
                                                      else
                                                        (do
                                                          bif (b__0 == (0x343 : (BitVec 12)))
                                                          then readReg mtval
                                                          else
                                                            (do
                                                              bif (b__0 == (0x340 : (BitVec 12)))
                                                              then readReg mscratch
                                                              else
                                                                (do
                                                                  bif (b__0 == (0x106 : (BitVec 12)))
                                                                  then
                                                                    (pure (zero_extend (m := 32)
                                                                        (← readReg scounteren)))
                                                                  else
                                                                    (do
                                                                      bif (b__0 == (0x306 : (BitVec 12)))
                                                                      then
                                                                        (pure (zero_extend (m := 32)
                                                                            (← readReg mcounteren)))
                                                                      else
                                                                        (do
                                                                          bif (b__0 == (0x320 : (BitVec 12)))
                                                                          then
                                                                            (pure (zero_extend
                                                                                (m := 32)
                                                                                (← readReg mcountinhibit)))
                                                                          else
                                                                            (do
                                                                              bif (b__0 == (0xF11 : (BitVec 12)))
                                                                              then
                                                                                (pure (zero_extend
                                                                                    (m := 32)
                                                                                    (← readReg mvendorid)))
                                                                              else
                                                                                (do
                                                                                  bif (b__0 == (0xF12 : (BitVec 12)))
                                                                                  then
                                                                                    readReg marchid
                                                                                  else
                                                                                    (do
                                                                                      bif (b__0 == (0xF13 : (BitVec 12)))
                                                                                      then
                                                                                        readReg mimpid
                                                                                      else
                                                                                        (do
                                                                                          bif (b__0 == (0xF14 : (BitVec 12)))
                                                                                          then
                                                                                            readReg mhartid
                                                                                          else
                                                                                            (do
                                                                                              bif (b__0 == (0xF15 : (BitVec 12)))
                                                                                              then
                                                                                                readReg mconfigptr
                                                                                              else
                                                                                                (do
                                                                                                  bif (b__0 == (0x100 : (BitVec 12)))
                                                                                                  then
                                                                                                    (pure (Sail.BitVec.extractLsb
                                                                                                        (lower_mstatus
                                                                                                          (← readReg mstatus))
                                                                                                        (xlen -i 1)
                                                                                                        0))
                                                                                                  else
                                                                                                    (do
                                                                                                      bif (b__0 == (0x144 : (BitVec 12)))
                                                                                                      then
                                                                                                        (pure (lower_mip
                                                                                                            (← readReg mip)
                                                                                                            (← readReg mideleg)))
                                                                                                      else
                                                                                                        (do
                                                                                                          bif (b__0 == (0x104 : (BitVec 12)))
                                                                                                          then
                                                                                                            (pure (lower_mie
                                                                                                                (← readReg mie)
                                                                                                                (← readReg mideleg)))
                                                                                                          else
                                                                                                            (do
                                                                                                              bif (b__0 == (0x140 : (BitVec 12)))
                                                                                                              then
                                                                                                                readReg sscratch
                                                                                                              else
                                                                                                                (do
                                                                                                                  bif (b__0 == (0x142 : (BitVec 12)))
                                                                                                                  then
                                                                                                                    readReg scause
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      bif (b__0 == (0x143 : (BitVec 12)))
                                                                                                                      then
                                                                                                                        readReg stval
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          bif (b__0 == (0x7A0 : (BitVec 12)))
                                                                                                                          then
                                                                                                                            (pure (Complement.complement
                                                                                                                                (← readReg tselect)))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              bif (((Sail.BitVec.extractLsb
                                                                                                                                       b__0
                                                                                                                                       11
                                                                                                                                       4) == (0x3A : (BitVec 8))) && (let idx : (BitVec 4) :=
                                                                                                                                     (Sail.BitVec.extractLsb
                                                                                                                                       b__0
                                                                                                                                       3
                                                                                                                                       0)
                                                                                                                                   (((BitVec.access
                                                                                                                                         idx
                                                                                                                                         0) == 0#1) || (xlen == 32))))
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  let idx : (BitVec 4) :=
                                                                                                                                    (Sail.BitVec.extractLsb
                                                                                                                                      b__0
                                                                                                                                      3
                                                                                                                                      0)
                                                                                                                                  (pmpReadCfgReg
                                                                                                                                    (BitVec.toNat
                                                                                                                                      idx)))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  bif ((Sail.BitVec.extractLsb
                                                                                                                                         b__0
                                                                                                                                         11
                                                                                                                                         4) == (0x3B : (BitVec 8)))
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      let idx : (BitVec 4) :=
                                                                                                                                        (Sail.BitVec.extractLsb
                                                                                                                                          b__0
                                                                                                                                          3
                                                                                                                                          0)
                                                                                                                                      (pmpReadAddrReg
                                                                                                                                        (BitVec.toNat
                                                                                                                                          ((0b00 : (BitVec 2)) ++ idx))))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      bif ((Sail.BitVec.extractLsb
                                                                                                                                             b__0
                                                                                                                                             11
                                                                                                                                             4) == (0x3C : (BitVec 8)))
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          let idx : (BitVec 4) :=
                                                                                                                                            (Sail.BitVec.extractLsb
                                                                                                                                              b__0
                                                                                                                                              3
                                                                                                                                              0)
                                                                                                                                          (pmpReadAddrReg
                                                                                                                                            (BitVec.toNat
                                                                                                                                              ((0b01 : (BitVec 2)) ++ idx))))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          bif ((Sail.BitVec.extractLsb
                                                                                                                                                 b__0
                                                                                                                                                 11
                                                                                                                                                 4) == (0x3D : (BitVec 8)))
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              let idx : (BitVec 4) :=
                                                                                                                                                (Sail.BitVec.extractLsb
                                                                                                                                                  b__0
                                                                                                                                                  3
                                                                                                                                                  0)
                                                                                                                                              (pmpReadAddrReg
                                                                                                                                                (BitVec.toNat
                                                                                                                                                  ((0b10 : (BitVec 2)) ++ idx))))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              bif ((Sail.BitVec.extractLsb
                                                                                                                                                     b__0
                                                                                                                                                     11
                                                                                                                                                     4) == (0x3E : (BitVec 8)))
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  let idx : (BitVec 4) :=
                                                                                                                                                    (Sail.BitVec.extractLsb
                                                                                                                                                      b__0
                                                                                                                                                      3
                                                                                                                                                      0)
                                                                                                                                                  (pmpReadAddrReg
                                                                                                                                                    (BitVec.toNat
                                                                                                                                                      ((0b11 : (BitVec 2)) ++ idx))))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  bif (b__0 == (0x008 : (BitVec 12)))
                                                                                                                                                  then
                                                                                                                                                    readReg vstart
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      bif (b__0 == (0x009 : (BitVec 12)))
                                                                                                                                                      then
                                                                                                                                                        (pure (zero_extend
                                                                                                                                                            (m := 32)
                                                                                                                                                            (_get_Vcsr_vxsat
                                                                                                                                                              (← readReg vcsr))))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          bif (b__0 == (0x00A : (BitVec 12)))
                                                                                                                                                          then
                                                                                                                                                            (pure (zero_extend
                                                                                                                                                                (m := 32)
                                                                                                                                                                (_get_Vcsr_vxrm
                                                                                                                                                                  (← readReg vcsr))))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              bif (b__0 == (0x00F : (BitVec 12)))
                                                                                                                                                              then
                                                                                                                                                                (pure (zero_extend
                                                                                                                                                                    (m := 32)
                                                                                                                                                                    (← readReg vcsr)))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  bif (b__0 == (0xC20 : (BitVec 12)))
                                                                                                                                                                  then
                                                                                                                                                                    readReg vl
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      bif (b__0 == (0xC21 : (BitVec 12)))
                                                                                                                                                                      then
                                                                                                                                                                        readReg vtype
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          bif (b__0 == (0xC22 : (BitVec 12)))
                                                                                                                                                                          then
                                                                                                                                                                            (pure VLENB)
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              bif (b__0 == (0x105 : (BitVec 12)))
                                                                                                                                                                              then
                                                                                                                                                                                (get_stvec
                                                                                                                                                                                  ())
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  bif (b__0 == (0x141 : (BitVec 12)))
                                                                                                                                                                                  then
                                                                                                                                                                                    (get_xepc
                                                                                                                                                                                      Supervisor)
                                                                                                                                                                                  else
                                                                                                                                                                                    (do
                                                                                                                                                                                      bif (b__0 == (0x305 : (BitVec 12)))
                                                                                                                                                                                      then
                                                                                                                                                                                        (get_mtvec
                                                                                                                                                                                          ())
                                                                                                                                                                                      else
                                                                                                                                                                                        (do
                                                                                                                                                                                          bif (b__0 == (0x341 : (BitVec 12)))
                                                                                                                                                                                          then
                                                                                                                                                                                            (get_xepc
                                                                                                                                                                                              Machine)
                                                                                                                                                                                          else
                                                                                                                                                                                            (do
                                                                                                                                                                                              bif (((Sail.BitVec.extractLsb
                                                                                                                                                                                                       b__0
                                                                                                                                                                                                       11
                                                                                                                                                                                                       5) == (0b0011001 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                                     (Sail.BitVec.extractLsb
                                                                                                                                                                                                       b__0
                                                                                                                                                                                                       4
                                                                                                                                                                                                       0)
                                                                                                                                                                                                   ((BitVec.toNat
                                                                                                                                                                                                       index) ≥b 3) : Bool))
                                                                                                                                                                                              then
                                                                                                                                                                                                (do
                                                                                                                                                                                                  let index : (BitVec 5) :=
                                                                                                                                                                                                    (Sail.BitVec.extractLsb
                                                                                                                                                                                                      b__0
                                                                                                                                                                                                      4
                                                                                                                                                                                                      0)
                                                                                                                                                                                                  (read_mhpmevent
                                                                                                                                                                                                    (← (hpmidx_from_bits
                                                                                                                                                                                                        index))))
                                                                                                                                                                                              else
                                                                                                                                                                                                (do
                                                                                                                                                                                                  bif (((Sail.BitVec.extractLsb
                                                                                                                                                                                                           b__0
                                                                                                                                                                                                           11
                                                                                                                                                                                                           5) == (0b1011000 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                                         (Sail.BitVec.extractLsb
                                                                                                                                                                                                           b__0
                                                                                                                                                                                                           4
                                                                                                                                                                                                           0)
                                                                                                                                                                                                       ((BitVec.toNat
                                                                                                                                                                                                           index) ≥b 3) : Bool))
                                                                                                                                                                                                  then
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      let index : (BitVec 5) :=
                                                                                                                                                                                                        (Sail.BitVec.extractLsb
                                                                                                                                                                                                          b__0
                                                                                                                                                                                                          4
                                                                                                                                                                                                          0)
                                                                                                                                                                                                      (read_mhpmcounter
                                                                                                                                                                                                        (← (hpmidx_from_bits
                                                                                                                                                                                                            index))))
                                                                                                                                                                                                  else
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      bif (((Sail.BitVec.extractLsb
                                                                                                                                                                                                               b__0
                                                                                                                                                                                                               11
                                                                                                                                                                                                               5) == (0b1011100 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                                             (Sail.BitVec.extractLsb
                                                                                                                                                                                                               b__0
                                                                                                                                                                                                               4
                                                                                                                                                                                                               0)
                                                                                                                                                                                                           ((xlen == 32) && (((BitVec.toNat
                                                                                                                                                                                                                 index) ≥b 3) : Bool))))
                                                                                                                                                                                                      then
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          let index : (BitVec 5) :=
                                                                                                                                                                                                            (Sail.BitVec.extractLsb
                                                                                                                                                                                                              b__0
                                                                                                                                                                                                              4
                                                                                                                                                                                                              0)
                                                                                                                                                                                                          (read_mhpmcounterh
                                                                                                                                                                                                            (← (hpmidx_from_bits
                                                                                                                                                                                                                index))))
                                                                                                                                                                                                      else
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          bif (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                   b__0
                                                                                                                                                                                                                   11
                                                                                                                                                                                                                   5) == (0b1100000 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                                                 (Sail.BitVec.extractLsb
                                                                                                                                                                                                                   b__0
                                                                                                                                                                                                                   4
                                                                                                                                                                                                                   0)
                                                                                                                                                                                                               ((BitVec.toNat
                                                                                                                                                                                                                   index) ≥b 3) : Bool))
                                                                                                                                                                                                          then
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              let index : (BitVec 5) :=
                                                                                                                                                                                                                (Sail.BitVec.extractLsb
                                                                                                                                                                                                                  b__0
                                                                                                                                                                                                                  4
                                                                                                                                                                                                                  0)
                                                                                                                                                                                                              (read_mhpmcounter
                                                                                                                                                                                                                (← (hpmidx_from_bits
                                                                                                                                                                                                                    index))))
                                                                                                                                                                                                          else
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              bif (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                       b__0
                                                                                                                                                                                                                       11
                                                                                                                                                                                                                       5) == (0b1100100 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                                                     (Sail.BitVec.extractLsb
                                                                                                                                                                                                                       b__0
                                                                                                                                                                                                                       4
                                                                                                                                                                                                                       0)
                                                                                                                                                                                                                   ((xlen == 32) && (((BitVec.toNat
                                                                                                                                                                                                                         index) ≥b 3) : Bool))))
                                                                                                                                                                                                              then
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  let index : (BitVec 5) :=
                                                                                                                                                                                                                    (Sail.BitVec.extractLsb
                                                                                                                                                                                                                      b__0
                                                                                                                                                                                                                      4
                                                                                                                                                                                                                      0)
                                                                                                                                                                                                                  (read_mhpmcounterh
                                                                                                                                                                                                                    (← (hpmidx_from_bits
                                                                                                                                                                                                                        index))))
                                                                                                                                                                                                              else
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  bif (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                           b__0
                                                                                                                                                                                                                           11
                                                                                                                                                                                                                           5) == (0b0111001 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                                                         (Sail.BitVec.extractLsb
                                                                                                                                                                                                                           b__0
                                                                                                                                                                                                                           4
                                                                                                                                                                                                                           0)
                                                                                                                                                                                                                       ((xlen == 32) && (((BitVec.toNat
                                                                                                                                                                                                                             index) ≥b 3) : Bool))))
                                                                                                                                                                                                                  then
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      let index : (BitVec 5) :=
                                                                                                                                                                                                                        (Sail.BitVec.extractLsb
                                                                                                                                                                                                                          b__0
                                                                                                                                                                                                                          4
                                                                                                                                                                                                                          0)
                                                                                                                                                                                                                      (read_mhpmeventh
                                                                                                                                                                                                                        (← (hpmidx_from_bits
                                                                                                                                                                                                                            index))))
                                                                                                                                                                                                                  else
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      bif (b__0 == (0xDA0 : (BitVec 12)))
                                                                                                                                                                                                                      then
                                                                                                                                                                                                                        (pure (zero_extend
                                                                                                                                                                                                                            (m := 32)
                                                                                                                                                                                                                            (← (get_scountovf
                                                                                                                                                                                                                                (← readReg cur_privilege)))))
                                                                                                                                                                                                                      else
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          bif (b__0 == (0x015 : (BitVec 12)))
                                                                                                                                                                                                                          then
                                                                                                                                                                                                                            (read_seed_csr
                                                                                                                                                                                                                              ())
                                                                                                                                                                                                                          else
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              bif (b__0 == (0xC00 : (BitVec 12)))
                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                    (← readReg mcycle)
                                                                                                                                                                                                                                    (xlen -i 1)
                                                                                                                                                                                                                                    0))
                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  bif (b__0 == (0xC01 : (BitVec 12)))
                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                    (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                        (← readReg mtime)
                                                                                                                                                                                                                                        (xlen -i 1)
                                                                                                                                                                                                                                        0))
                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      bif (b__0 == (0xC02 : (BitVec 12)))
                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                        (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                            (← readReg minstret)
                                                                                                                                                                                                                                            (xlen -i 1)
                                                                                                                                                                                                                                            0))
                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          bif ((b__0 == (0xC80 : (BitVec 12))) && (xlen == 32))
                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                            (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                (← readReg mcycle)
                                                                                                                                                                                                                                                63
                                                                                                                                                                                                                                                32))
                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              bif ((b__0 == (0xC81 : (BitVec 12))) && (xlen == 32))
                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                    (← readReg mtime)
                                                                                                                                                                                                                                                    63
                                                                                                                                                                                                                                                    32))
                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  bif ((b__0 == (0xC82 : (BitVec 12))) && (xlen == 32))
                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                    (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                        (← readReg minstret)
                                                                                                                                                                                                                                                        63
                                                                                                                                                                                                                                                        32))
                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      bif (b__0 == (0xB00 : (BitVec 12)))
                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                        (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                            (← readReg mcycle)
                                                                                                                                                                                                                                                            (xlen -i 1)
                                                                                                                                                                                                                                                            0))
                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          bif (b__0 == (0xB02 : (BitVec 12)))
                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                            (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                (← readReg minstret)
                                                                                                                                                                                                                                                                (xlen -i 1)
                                                                                                                                                                                                                                                                0))
                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              bif ((b__0 == (0xB80 : (BitVec 12))) && (xlen == 32))
                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                    (← readReg mcycle)
                                                                                                                                                                                                                                                                    63
                                                                                                                                                                                                                                                                    32))
                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  bif ((b__0 == (0xB82 : (BitVec 12))) && (xlen == 32))
                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                    (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                        (← readReg minstret)
                                                                                                                                                                                                                                                                        63
                                                                                                                                                                                                                                                                        32))
                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      bif (b__0 == (0x001 : (BitVec 12)))
                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                        (pure (zero_extend
                                                                                                                                                                                                                                                                            (m := 32)
                                                                                                                                                                                                                                                                            (_get_Fcsr_FFLAGS
                                                                                                                                                                                                                                                                              (← readReg fcsr))))
                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          bif (b__0 == (0x002 : (BitVec 12)))
                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                            (pure (zero_extend
                                                                                                                                                                                                                                                                                (m := 32)
                                                                                                                                                                                                                                                                                (_get_Fcsr_FRM
                                                                                                                                                                                                                                                                                  (← readReg fcsr))))
                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              bif (b__0 == (0x003 : (BitVec 12)))
                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                (pure (zero_extend
                                                                                                                                                                                                                                                                                    (m := 32)
                                                                                                                                                                                                                                                                                    (← readReg fcsr)))
                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  bif (b__0 == (0x321 : (BitVec 12)))
                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                    (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                        (← readReg mcyclecfg)
                                                                                                                                                                                                                                                                                        (xlen -i 1)
                                                                                                                                                                                                                                                                                        0))
                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      bif ((b__0 == (0x721 : (BitVec 12))) && (xlen == 32))
                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                        (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                            (← readReg mcyclecfg)
                                                                                                                                                                                                                                                                                            63
                                                                                                                                                                                                                                                                                            32))
                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                          bif (b__0 == (0x322 : (BitVec 12)))
                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                            (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                (← readReg minstretcfg)
                                                                                                                                                                                                                                                                                                (xlen -i 1)
                                                                                                                                                                                                                                                                                                0))
                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                              bif ((b__0 == (0x722 : (BitVec 12))) && (xlen == 32))
                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                    (← readReg minstretcfg)
                                                                                                                                                                                                                                                                                                    63
                                                                                                                                                                                                                                                                                                    32))
                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                  bif (b__0 == (0x14D : (BitVec 12)))
                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                    (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                        (← readReg stimecmp)
                                                                                                                                                                                                                                                                                                        (xlen -i 1)
                                                                                                                                                                                                                                                                                                        0))
                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                      bif ((b__0 == (0x15D : (BitVec 12))) && (xlen == 32))
                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                        (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                            (← readReg stimecmp)
                                                                                                                                                                                                                                                                                                            63
                                                                                                                                                                                                                                                                                                            32))
                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                          bif (b__0 == (0x180 : (BitVec 12)))
                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                            readReg satp
                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                            (internal_error
                                                                                                                                                                                                                                                                                                              "riscv_csr_end.sail"
                                                                                                                                                                                                                                                                                                              17
                                                                                                                                                                                                                                                                                                              (HAppend.hAppend
                                                                                                                                                                                                                                                                                                                "Read from CSR that does not exist: "
                                                                                                                                                                                                                                                                                                                (BitVec.toFormatted
                                                                                                                                                                                                                                                                                                                  b__0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def write_CSR (b__0 : (BitVec 12)) (value : (BitVec 32)) : SailM (BitVec 32) := do
  bif (b__0 == (0x301 : (BitVec 12)))
  then
    (do
      writeReg misa (← (legalize_misa (← readReg misa) value))
      readReg misa)
  else
    (do
      bif ((b__0 == (0x300 : (BitVec 12))) && (xlen == 64))
      then
        (do
          writeReg mstatus (← (legalize_mstatus (← readReg mstatus) value))
          readReg mstatus)
      else
        (do
          bif ((b__0 == (0x300 : (BitVec 12))) && (xlen == 32))
          then
            (do
              writeReg mstatus (← (legalize_mstatus (← readReg mstatus)
                  ((Sail.BitVec.extractLsb (← readReg mstatus) 63 32) ++ value)))
              (pure (Sail.BitVec.extractLsb (← readReg mstatus) 31 0)))
          else
            (do
              bif ((b__0 == (0x310 : (BitVec 12))) && (xlen == 32))
              then
                (do
                  writeReg mstatus (← (legalize_mstatus (← readReg mstatus)
                      (value ++ (Sail.BitVec.extractLsb (← readReg mstatus) 31 0))))
                  (pure (Sail.BitVec.extractLsb (← readReg mstatus) 63 32)))
              else
                (do
                  bif ((b__0 == (0x747 : (BitVec 12))) && (xlen == 32))
                  then
                    (do
                      writeReg mseccfg (← (legalize_mseccfg (← readReg mseccfg)
                          ((Sail.BitVec.extractLsb (← readReg mseccfg) 63 32) ++ value)))
                      (pure (Sail.BitVec.extractLsb (← readReg mseccfg) 31 0)))
                  else
                    (do
                      bif ((b__0 == (0x747 : (BitVec 12))) && (xlen == 64))
                      then
                        (do
                          writeReg mseccfg (← (legalize_mseccfg (← readReg mseccfg) value))
                          readReg mseccfg)
                      else
                        (do
                          bif ((b__0 == (0x757 : (BitVec 12))) && (xlen == 32))
                          then
                            (do
                              writeReg mseccfg (← (legalize_mseccfg (← readReg mseccfg)
                                  (value ++ (Sail.BitVec.extractLsb (← readReg mseccfg) 31 0))))
                              (pure (Sail.BitVec.extractLsb (← readReg mseccfg) 63 32)))
                          else
                            (do
                              bif ((b__0 == (0x30A : (BitVec 12))) && (xlen == 32))
                              then
                                (do
                                  writeReg menvcfg (← (legalize_menvcfg (← readReg menvcfg)
                                      ((Sail.BitVec.extractLsb (← readReg menvcfg) 63 32) ++ value)))
                                  (pure (Sail.BitVec.extractLsb (← readReg menvcfg) 31 0)))
                              else
                                (do
                                  bif ((b__0 == (0x30A : (BitVec 12))) && (xlen == 64))
                                  then
                                    (do
                                      writeReg menvcfg (← (legalize_menvcfg (← readReg menvcfg)
                                          value))
                                      readReg menvcfg)
                                  else
                                    (do
                                      bif ((b__0 == (0x31A : (BitVec 12))) && (xlen == 32))
                                      then
                                        (do
                                          writeReg menvcfg (← (legalize_menvcfg
                                              (← readReg menvcfg)
                                              (value ++ (Sail.BitVec.extractLsb
                                                  (← readReg menvcfg) 31 0))))
                                          (pure (Sail.BitVec.extractLsb (← readReg menvcfg) 63 32)))
                                      else
                                        (do
                                          bif (b__0 == (0x10A : (BitVec 12)))
                                          then
                                            (do
                                              writeReg senvcfg (← (legalize_senvcfg
                                                  (← readReg senvcfg)
                                                  (zero_extend (m := 32) value)))
                                              (pure (Sail.BitVec.extractLsb (← readReg senvcfg)
                                                  (xlen -i 1) 0)))
                                          else
                                            (do
                                              bif (b__0 == (0x304 : (BitVec 12)))
                                              then
                                                (do
                                                  writeReg mie (← (legalize_mie (← readReg mie)
                                                      value))
                                                  readReg mie)
                                              else
                                                (do
                                                  bif (b__0 == (0x344 : (BitVec 12)))
                                                  then
                                                    (do
                                                      writeReg mip (← (legalize_mip
                                                          (← readReg mip) value))
                                                      readReg mip)
                                                  else
                                                    (do
                                                      bif ((b__0 == (0x302 : (BitVec 12))) && (xlen == 64))
                                                      then
                                                        (do
                                                          writeReg medeleg (legalize_medeleg
                                                            (← readReg medeleg) value)
                                                          readReg medeleg)
                                                      else
                                                        (do
                                                          bif ((b__0 == (0x302 : (BitVec 12))) && (xlen == 32))
                                                          then
                                                            (do
                                                              writeReg medeleg (legalize_medeleg
                                                                (← readReg medeleg)
                                                                ((Sail.BitVec.extractLsb
                                                                    (← readReg medeleg) 63 32) ++ value))
                                                              (pure (Sail.BitVec.extractLsb
                                                                  (← readReg medeleg) 31 0)))
                                                          else
                                                            (do
                                                              bif ((b__0 == (0x312 : (BitVec 12))) && (xlen == 32))
                                                              then
                                                                (do
                                                                  writeReg medeleg (legalize_medeleg
                                                                    (← readReg medeleg)
                                                                    (value ++ (Sail.BitVec.extractLsb
                                                                        (← readReg medeleg) 31 0)))
                                                                  (pure (Sail.BitVec.extractLsb
                                                                      (← readReg medeleg) 63 32)))
                                                              else
                                                                (do
                                                                  bif (b__0 == (0x303 : (BitVec 12)))
                                                                  then
                                                                    (do
                                                                      writeReg mideleg (legalize_mideleg
                                                                        (← readReg mideleg) value)
                                                                      readReg mideleg)
                                                                  else
                                                                    (do
                                                                      bif (b__0 == (0x342 : (BitVec 12)))
                                                                      then
                                                                        (do
                                                                          writeReg mcause value
                                                                          readReg mcause)
                                                                      else
                                                                        (do
                                                                          bif (b__0 == (0x343 : (BitVec 12)))
                                                                          then
                                                                            (do
                                                                              writeReg mtval value
                                                                              readReg mtval)
                                                                          else
                                                                            (do
                                                                              bif (b__0 == (0x340 : (BitVec 12)))
                                                                              then
                                                                                (do
                                                                                  writeReg mscratch value
                                                                                  readReg mscratch)
                                                                              else
                                                                                (do
                                                                                  bif (b__0 == (0x106 : (BitVec 12)))
                                                                                  then
                                                                                    (do
                                                                                      writeReg scounteren (legalize_scounteren
                                                                                        (← readReg scounteren)
                                                                                        value)
                                                                                      (pure (zero_extend
                                                                                          (m := 32)
                                                                                          (← readReg scounteren))))
                                                                                  else
                                                                                    (do
                                                                                      bif (b__0 == (0x306 : (BitVec 12)))
                                                                                      then
                                                                                        (do
                                                                                          writeReg mcounteren (legalize_mcounteren
                                                                                            (← readReg mcounteren)
                                                                                            value)
                                                                                          (pure (zero_extend
                                                                                              (m := 32)
                                                                                              (← readReg mcounteren))))
                                                                                      else
                                                                                        (do
                                                                                          bif (b__0 == (0x320 : (BitVec 12)))
                                                                                          then
                                                                                            (do
                                                                                              writeReg mcountinhibit (legalize_mcountinhibit
                                                                                                (← readReg mcountinhibit)
                                                                                                value)
                                                                                              (pure (zero_extend
                                                                                                  (m := 32)
                                                                                                  (← readReg mcountinhibit))))
                                                                                          else
                                                                                            (do
                                                                                              bif (b__0 == (0x100 : (BitVec 12)))
                                                                                              then
                                                                                                (do
                                                                                                  writeReg mstatus (← (legalize_sstatus
                                                                                                      (← readReg mstatus)
                                                                                                      value))
                                                                                                  (pure (Sail.BitVec.extractLsb
                                                                                                      (lower_mstatus
                                                                                                        (← readReg mstatus))
                                                                                                      (xlen -i 1)
                                                                                                      0)))
                                                                                              else
                                                                                                (do
                                                                                                  bif (b__0 == (0x144 : (BitVec 12)))
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg mip (legalize_sip
                                                                                                        (← readReg mip)
                                                                                                        (← readReg mideleg)
                                                                                                        value)
                                                                                                      (pure (lower_mip
                                                                                                          (← readReg mip)
                                                                                                          (← readReg mideleg))))
                                                                                                  else
                                                                                                    (do
                                                                                                      bif (b__0 == (0x104 : (BitVec 12)))
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg mie (legalize_sie
                                                                                                            (← readReg mie)
                                                                                                            (← readReg mideleg)
                                                                                                            value)
                                                                                                          (pure (lower_mie
                                                                                                              (← readReg mie)
                                                                                                              (← readReg mideleg))))
                                                                                                      else
                                                                                                        (do
                                                                                                          bif (b__0 == (0x140 : (BitVec 12)))
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg sscratch value
                                                                                                              readReg sscratch)
                                                                                                          else
                                                                                                            (do
                                                                                                              bif (b__0 == (0x142 : (BitVec 12)))
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg scause value
                                                                                                                  readReg scause)
                                                                                                              else
                                                                                                                (do
                                                                                                                  bif (b__0 == (0x143 : (BitVec 12)))
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg stval value
                                                                                                                      readReg stval)
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      bif (b__0 == (0x7A0 : (BitVec 12)))
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg tselect value
                                                                                                                          readReg tselect)
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          bif (((Sail.BitVec.extractLsb
                                                                                                                                   b__0
                                                                                                                                   11
                                                                                                                                   4) == (0x3A : (BitVec 8))) && (let idx : (BitVec 4) :=
                                                                                                                                 (Sail.BitVec.extractLsb
                                                                                                                                   b__0
                                                                                                                                   3
                                                                                                                                   0)
                                                                                                                               (((BitVec.access
                                                                                                                                     idx
                                                                                                                                     0) == 0#1) || (xlen == 32))))
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              let idx : (BitVec 4) :=
                                                                                                                                (Sail.BitVec.extractLsb
                                                                                                                                  b__0
                                                                                                                                  3
                                                                                                                                  0)
                                                                                                                              let idx :=
                                                                                                                                (BitVec.toNat
                                                                                                                                  idx)
                                                                                                                              (pmpWriteCfgReg
                                                                                                                                idx
                                                                                                                                value)
                                                                                                                              (pmpReadCfgReg
                                                                                                                                idx))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              bif ((Sail.BitVec.extractLsb
                                                                                                                                     b__0
                                                                                                                                     11
                                                                                                                                     4) == (0x3B : (BitVec 8)))
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  let idx : (BitVec 4) :=
                                                                                                                                    (Sail.BitVec.extractLsb
                                                                                                                                      b__0
                                                                                                                                      3
                                                                                                                                      0)
                                                                                                                                  let idx :=
                                                                                                                                    (BitVec.toNat
                                                                                                                                      ((0b00 : (BitVec 2)) ++ idx))
                                                                                                                                  (pmpWriteAddrReg
                                                                                                                                    idx
                                                                                                                                    value)
                                                                                                                                  (pmpReadAddrReg
                                                                                                                                    idx))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  bif ((Sail.BitVec.extractLsb
                                                                                                                                         b__0
                                                                                                                                         11
                                                                                                                                         4) == (0x3C : (BitVec 8)))
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      let idx : (BitVec 4) :=
                                                                                                                                        (Sail.BitVec.extractLsb
                                                                                                                                          b__0
                                                                                                                                          3
                                                                                                                                          0)
                                                                                                                                      let idx :=
                                                                                                                                        (BitVec.toNat
                                                                                                                                          ((0b01 : (BitVec 2)) ++ idx))
                                                                                                                                      (pmpWriteAddrReg
                                                                                                                                        idx
                                                                                                                                        value)
                                                                                                                                      (pmpReadAddrReg
                                                                                                                                        idx))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      bif ((Sail.BitVec.extractLsb
                                                                                                                                             b__0
                                                                                                                                             11
                                                                                                                                             4) == (0x3D : (BitVec 8)))
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          let idx : (BitVec 4) :=
                                                                                                                                            (Sail.BitVec.extractLsb
                                                                                                                                              b__0
                                                                                                                                              3
                                                                                                                                              0)
                                                                                                                                          let idx :=
                                                                                                                                            (BitVec.toNat
                                                                                                                                              ((0b10 : (BitVec 2)) ++ idx))
                                                                                                                                          (pmpWriteAddrReg
                                                                                                                                            idx
                                                                                                                                            value)
                                                                                                                                          (pmpReadAddrReg
                                                                                                                                            idx))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          bif ((Sail.BitVec.extractLsb
                                                                                                                                                 b__0
                                                                                                                                                 11
                                                                                                                                                 4) == (0x3E : (BitVec 8)))
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              let idx : (BitVec 4) :=
                                                                                                                                                (Sail.BitVec.extractLsb
                                                                                                                                                  b__0
                                                                                                                                                  3
                                                                                                                                                  0)
                                                                                                                                              let idx :=
                                                                                                                                                (BitVec.toNat
                                                                                                                                                  ((0b11 : (BitVec 2)) ++ idx))
                                                                                                                                              (pmpWriteAddrReg
                                                                                                                                                idx
                                                                                                                                                value)
                                                                                                                                              (pmpReadAddrReg
                                                                                                                                                idx))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              bif (b__0 == (0x008 : (BitVec 12)))
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  (set_vstart
                                                                                                                                                    (Sail.BitVec.extractLsb
                                                                                                                                                      value
                                                                                                                                                      15
                                                                                                                                                      0))
                                                                                                                                                  readReg vstart)
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  bif (b__0 == (0x009 : (BitVec 12)))
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      (ext_write_vcsr
                                                                                                                                                        (_get_Vcsr_vxrm
                                                                                                                                                          (← readReg vcsr))
                                                                                                                                                        (Sail.BitVec.extractLsb
                                                                                                                                                          value
                                                                                                                                                          0
                                                                                                                                                          0))
                                                                                                                                                      (pure (zero_extend
                                                                                                                                                          (m := 32)
                                                                                                                                                          (_get_Vcsr_vxsat
                                                                                                                                                            (← readReg vcsr)))))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      bif (b__0 == (0x00A : (BitVec 12)))
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          (ext_write_vcsr
                                                                                                                                                            (Sail.BitVec.extractLsb
                                                                                                                                                              value
                                                                                                                                                              1
                                                                                                                                                              0)
                                                                                                                                                            (_get_Vcsr_vxsat
                                                                                                                                                              (← readReg vcsr)))
                                                                                                                                                          (pure (zero_extend
                                                                                                                                                              (m := 32)
                                                                                                                                                              (_get_Vcsr_vxrm
                                                                                                                                                                (← readReg vcsr)))))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          bif (b__0 == (0x00F : (BitVec 12)))
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              (ext_write_vcsr
                                                                                                                                                                (Sail.BitVec.extractLsb
                                                                                                                                                                  value
                                                                                                                                                                  2
                                                                                                                                                                  1)
                                                                                                                                                                (Sail.BitVec.extractLsb
                                                                                                                                                                  value
                                                                                                                                                                  0
                                                                                                                                                                  0))
                                                                                                                                                              (pure (zero_extend
                                                                                                                                                                  (m := 32)
                                                                                                                                                                  (← readReg vcsr))))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              bif (b__0 == (0x105 : (BitVec 12)))
                                                                                                                                                              then
                                                                                                                                                                (set_stvec
                                                                                                                                                                  value)
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  bif (b__0 == (0x141 : (BitVec 12)))
                                                                                                                                                                  then
                                                                                                                                                                    (set_xepc
                                                                                                                                                                      Supervisor
                                                                                                                                                                      value)
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      bif (b__0 == (0x305 : (BitVec 12)))
                                                                                                                                                                      then
                                                                                                                                                                        (set_mtvec
                                                                                                                                                                          value)
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          bif (b__0 == (0x341 : (BitVec 12)))
                                                                                                                                                                          then
                                                                                                                                                                            (set_xepc
                                                                                                                                                                              Machine
                                                                                                                                                                              value)
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              bif (((Sail.BitVec.extractLsb
                                                                                                                                                                                       b__0
                                                                                                                                                                                       11
                                                                                                                                                                                       5) == (0b0011001 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                     (Sail.BitVec.extractLsb
                                                                                                                                                                                       b__0
                                                                                                                                                                                       4
                                                                                                                                                                                       0)
                                                                                                                                                                                   ((BitVec.toNat
                                                                                                                                                                                       index) ≥b 3) : Bool))
                                                                                                                                                                              then
                                                                                                                                                                                (do
                                                                                                                                                                                  let index : (BitVec 5) :=
                                                                                                                                                                                    (Sail.BitVec.extractLsb
                                                                                                                                                                                      b__0
                                                                                                                                                                                      4
                                                                                                                                                                                      0)
                                                                                                                                                                                  let index ← do
                                                                                                                                                                                    (hpmidx_from_bits
                                                                                                                                                                                      index)
                                                                                                                                                                                  (write_mhpmevent
                                                                                                                                                                                    index
                                                                                                                                                                                    value)
                                                                                                                                                                                  (read_mhpmevent
                                                                                                                                                                                    index))
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  bif (((Sail.BitVec.extractLsb
                                                                                                                                                                                           b__0
                                                                                                                                                                                           11
                                                                                                                                                                                           5) == (0b1011000 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                         (Sail.BitVec.extractLsb
                                                                                                                                                                                           b__0
                                                                                                                                                                                           4
                                                                                                                                                                                           0)
                                                                                                                                                                                       ((BitVec.toNat
                                                                                                                                                                                           index) ≥b 3) : Bool))
                                                                                                                                                                                  then
                                                                                                                                                                                    (do
                                                                                                                                                                                      let index : (BitVec 5) :=
                                                                                                                                                                                        (Sail.BitVec.extractLsb
                                                                                                                                                                                          b__0
                                                                                                                                                                                          4
                                                                                                                                                                                          0)
                                                                                                                                                                                      let index ← do
                                                                                                                                                                                        (hpmidx_from_bits
                                                                                                                                                                                          index)
                                                                                                                                                                                      (write_mhpmcounter
                                                                                                                                                                                        index
                                                                                                                                                                                        value)
                                                                                                                                                                                      (read_mhpmcounter
                                                                                                                                                                                        index))
                                                                                                                                                                                  else
                                                                                                                                                                                    (do
                                                                                                                                                                                      bif (((Sail.BitVec.extractLsb
                                                                                                                                                                                               b__0
                                                                                                                                                                                               11
                                                                                                                                                                                               5) == (0b1011100 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                             (Sail.BitVec.extractLsb
                                                                                                                                                                                               b__0
                                                                                                                                                                                               4
                                                                                                                                                                                               0)
                                                                                                                                                                                           ((xlen == 32) && (((BitVec.toNat
                                                                                                                                                                                                 index) ≥b 3) : Bool))))
                                                                                                                                                                                      then
                                                                                                                                                                                        (do
                                                                                                                                                                                          let index : (BitVec 5) :=
                                                                                                                                                                                            (Sail.BitVec.extractLsb
                                                                                                                                                                                              b__0
                                                                                                                                                                                              4
                                                                                                                                                                                              0)
                                                                                                                                                                                          let index ← do
                                                                                                                                                                                            (hpmidx_from_bits
                                                                                                                                                                                              index)
                                                                                                                                                                                          (write_mhpmcounterh
                                                                                                                                                                                            index
                                                                                                                                                                                            value)
                                                                                                                                                                                          (read_mhpmcounterh
                                                                                                                                                                                            index))
                                                                                                                                                                                      else
                                                                                                                                                                                        (do
                                                                                                                                                                                          bif (((Sail.BitVec.extractLsb
                                                                                                                                                                                                   b__0
                                                                                                                                                                                                   11
                                                                                                                                                                                                   5) == (0b0111001 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                                 (Sail.BitVec.extractLsb
                                                                                                                                                                                                   b__0
                                                                                                                                                                                                   4
                                                                                                                                                                                                   0)
                                                                                                                                                                                               ((xlen == 32) && (((BitVec.toNat
                                                                                                                                                                                                     index) ≥b 3) : Bool))))
                                                                                                                                                                                          then
                                                                                                                                                                                            (do
                                                                                                                                                                                              let index : (BitVec 5) :=
                                                                                                                                                                                                (Sail.BitVec.extractLsb
                                                                                                                                                                                                  b__0
                                                                                                                                                                                                  4
                                                                                                                                                                                                  0)
                                                                                                                                                                                              let index ← do
                                                                                                                                                                                                (hpmidx_from_bits
                                                                                                                                                                                                  index)
                                                                                                                                                                                              (write_mhpmeventh
                                                                                                                                                                                                index
                                                                                                                                                                                                value)
                                                                                                                                                                                              (read_mhpmeventh
                                                                                                                                                                                                index))
                                                                                                                                                                                          else
                                                                                                                                                                                            (do
                                                                                                                                                                                              bif (b__0 == (0x015 : (BitVec 12)))
                                                                                                                                                                                              then
                                                                                                                                                                                                (pure (write_seed_csr
                                                                                                                                                                                                    ()))
                                                                                                                                                                                              else
                                                                                                                                                                                                (do
                                                                                                                                                                                                  bif (b__0 == (0xB00 : (BitVec 12)))
                                                                                                                                                                                                  then
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      writeReg mcycle (Sail.BitVec.updateSubrange
                                                                                                                                                                                                        (← readReg mcycle)
                                                                                                                                                                                                        (xlen -i 1)
                                                                                                                                                                                                        0
                                                                                                                                                                                                        value)
                                                                                                                                                                                                      (pure value))
                                                                                                                                                                                                  else
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      bif (b__0 == (0xB02 : (BitVec 12)))
                                                                                                                                                                                                      then
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          writeReg minstret (Sail.BitVec.updateSubrange
                                                                                                                                                                                                            (← readReg minstret)
                                                                                                                                                                                                            (xlen -i 1)
                                                                                                                                                                                                            0
                                                                                                                                                                                                            value)
                                                                                                                                                                                                          writeReg minstret_increment false
                                                                                                                                                                                                          (pure value))
                                                                                                                                                                                                      else
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          bif ((b__0 == (0xB80 : (BitVec 12))) && (xlen == 32))
                                                                                                                                                                                                          then
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              writeReg mcycle (Sail.BitVec.updateSubrange
                                                                                                                                                                                                                (← readReg mcycle)
                                                                                                                                                                                                                63
                                                                                                                                                                                                                32
                                                                                                                                                                                                                value)
                                                                                                                                                                                                              (pure value))
                                                                                                                                                                                                          else
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              bif ((b__0 == (0xB82 : (BitVec 12))) && (xlen == 32))
                                                                                                                                                                                                              then
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  writeReg minstret (Sail.BitVec.updateSubrange
                                                                                                                                                                                                                    (← readReg minstret)
                                                                                                                                                                                                                    63
                                                                                                                                                                                                                    32
                                                                                                                                                                                                                    value)
                                                                                                                                                                                                                  writeReg minstret_increment false
                                                                                                                                                                                                                  (pure value))
                                                                                                                                                                                                              else
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  bif (b__0 == (0x001 : (BitVec 12)))
                                                                                                                                                                                                                  then
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      (write_fcsr
                                                                                                                                                                                                                        (_get_Fcsr_FRM
                                                                                                                                                                                                                          (← readReg fcsr))
                                                                                                                                                                                                                        (Sail.BitVec.extractLsb
                                                                                                                                                                                                                          value
                                                                                                                                                                                                                          4
                                                                                                                                                                                                                          0))
                                                                                                                                                                                                                      (pure (zero_extend
                                                                                                                                                                                                                          (m := 32)
                                                                                                                                                                                                                          (_get_Fcsr_FFLAGS
                                                                                                                                                                                                                            (← readReg fcsr)))))
                                                                                                                                                                                                                  else
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      bif (b__0 == (0x002 : (BitVec 12)))
                                                                                                                                                                                                                      then
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          (write_fcsr
                                                                                                                                                                                                                            (Sail.BitVec.extractLsb
                                                                                                                                                                                                                              value
                                                                                                                                                                                                                              2
                                                                                                                                                                                                                              0)
                                                                                                                                                                                                                            (_get_Fcsr_FFLAGS
                                                                                                                                                                                                                              (← readReg fcsr)))
                                                                                                                                                                                                                          (pure (zero_extend
                                                                                                                                                                                                                              (m := 32)
                                                                                                                                                                                                                              (_get_Fcsr_FRM
                                                                                                                                                                                                                                (← readReg fcsr)))))
                                                                                                                                                                                                                      else
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          bif (b__0 == (0x003 : (BitVec 12)))
                                                                                                                                                                                                                          then
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              (write_fcsr
                                                                                                                                                                                                                                (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                  value
                                                                                                                                                                                                                                  7
                                                                                                                                                                                                                                  5)
                                                                                                                                                                                                                                (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                  value
                                                                                                                                                                                                                                  4
                                                                                                                                                                                                                                  0))
                                                                                                                                                                                                                              (pure (zero_extend
                                                                                                                                                                                                                                  (m := 32)
                                                                                                                                                                                                                                  (← readReg fcsr))))
                                                                                                                                                                                                                          else
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              bif ((b__0 == (0x321 : (BitVec 12))) && (xlen == 64))
                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  writeReg mcyclecfg (← (legalize_smcntrpmf
                                                                                                                                                                                                                                      (← readReg mcyclecfg)
                                                                                                                                                                                                                                      value))
                                                                                                                                                                                                                                  readReg mcyclecfg)
                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  bif ((b__0 == (0x321 : (BitVec 12))) && (xlen == 32))
                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      writeReg mcyclecfg (← (legalize_smcntrpmf
                                                                                                                                                                                                                                          (← readReg mcyclecfg)
                                                                                                                                                                                                                                          ((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                              (← readReg mcyclecfg)
                                                                                                                                                                                                                                              63
                                                                                                                                                                                                                                              32) ++ value)))
                                                                                                                                                                                                                                      (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                          (← readReg mcyclecfg)
                                                                                                                                                                                                                                          (xlen -i 1)
                                                                                                                                                                                                                                          0)))
                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      bif ((b__0 == (0x721 : (BitVec 12))) && (xlen == 32))
                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          writeReg mcyclecfg (← (legalize_smcntrpmf
                                                                                                                                                                                                                                              (← readReg mcyclecfg)
                                                                                                                                                                                                                                              (value ++ (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                  (← readReg mcyclecfg)
                                                                                                                                                                                                                                                  31
                                                                                                                                                                                                                                                  0))))
                                                                                                                                                                                                                                          (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                              (← readReg mcyclecfg)
                                                                                                                                                                                                                                              63
                                                                                                                                                                                                                                              32)))
                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          bif ((b__0 == (0x322 : (BitVec 12))) && (xlen == 64))
                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              writeReg minstretcfg (← (legalize_smcntrpmf
                                                                                                                                                                                                                                                  (← readReg minstretcfg)
                                                                                                                                                                                                                                                  value))
                                                                                                                                                                                                                                              (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                  (← readReg minstretcfg)
                                                                                                                                                                                                                                                  (xlen -i 1)
                                                                                                                                                                                                                                                  0)))
                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              bif ((b__0 == (0x322 : (BitVec 12))) && (xlen == 32))
                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  writeReg minstretcfg (← (legalize_smcntrpmf
                                                                                                                                                                                                                                                      (← readReg minstretcfg)
                                                                                                                                                                                                                                                      ((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                          (← readReg minstretcfg)
                                                                                                                                                                                                                                                          63
                                                                                                                                                                                                                                                          32) ++ value)))
                                                                                                                                                                                                                                                  (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                      (← readReg minstretcfg)
                                                                                                                                                                                                                                                      (xlen -i 1)
                                                                                                                                                                                                                                                      0)))
                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  bif ((b__0 == (0x722 : (BitVec 12))) && (xlen == 32))
                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      writeReg minstretcfg (← (legalize_smcntrpmf
                                                                                                                                                                                                                                                          (← readReg minstretcfg)
                                                                                                                                                                                                                                                          (value ++ (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                              (← readReg minstretcfg)
                                                                                                                                                                                                                                                              31
                                                                                                                                                                                                                                                              0))))
                                                                                                                                                                                                                                                      (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                          (← readReg minstretcfg)
                                                                                                                                                                                                                                                          63
                                                                                                                                                                                                                                                          32)))
                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      bif (b__0 == (0x14D : (BitVec 12)))
                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          writeReg stimecmp (Sail.BitVec.updateSubrange
                                                                                                                                                                                                                                                            (← readReg stimecmp)
                                                                                                                                                                                                                                                            (xlen -i 1)
                                                                                                                                                                                                                                                            0
                                                                                                                                                                                                                                                            value)
                                                                                                                                                                                                                                                          (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                              (← readReg stimecmp)
                                                                                                                                                                                                                                                              (xlen -i 1)
                                                                                                                                                                                                                                                              0)))
                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          bif ((b__0 == (0x15D : (BitVec 12))) && (xlen == 32))
                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              writeReg stimecmp (Sail.BitVec.updateSubrange
                                                                                                                                                                                                                                                                (← readReg stimecmp)
                                                                                                                                                                                                                                                                63
                                                                                                                                                                                                                                                                32
                                                                                                                                                                                                                                                                value)
                                                                                                                                                                                                                                                              (pure (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                  (← readReg stimecmp)
                                                                                                                                                                                                                                                                  63
                                                                                                                                                                                                                                                                  32)))
                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              bif (b__0 == (0x180 : (BitVec 12)))
                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  writeReg satp (← (legalize_satp
                                                                                                                                                                                                                                                                      (← (cur_architecture
                                                                                                                                                                                                                                                                          ()))
                                                                                                                                                                                                                                                                      (← readReg satp)
                                                                                                                                                                                                                                                                      value))
                                                                                                                                                                                                                                                                  readReg satp)
                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                (internal_error
                                                                                                                                                                                                                                                                  "riscv_csr_end.sail"
                                                                                                                                                                                                                                                                  23
                                                                                                                                                                                                                                                                  (HAppend.hAppend
                                                                                                                                                                                                                                                                    "Write to CSR that does not exist: "
                                                                                                                                                                                                                                                                    (BitVec.toFormatted
                                                                                                                                                                                                                                                                      b__0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Type quantifiers: k_ex377529# : Bool -/
def doCSR (csr : (BitVec 12)) (rs1_val : (BitVec 32)) (rd : regidx) (op : csrop) (is_CSR_Write : Bool) : SailM ExecutionResult := do
  bif (not (← (check_CSR csr (← readReg cur_privilege) is_CSR_Write)))
  then (pure (Illegal_Instruction ()))
  else
    (do
      bif (not (ext_check_CSR csr (← readReg cur_privilege) is_CSR_Write))
      then (pure (Ext_CSR_Check_Failure ()))
      else
        (do
          let is_CSR_Read := (not ((op == CSRRW) && (rd == zreg)))
          let csr_val ← (( do
            bif is_CSR_Read
            then (read_CSR csr)
            else (pure (zeros (n := 32))) ) : SailM xlenbits )
          bif is_CSR_Write
          then
            (do
              let new_val : xlenbits :=
                match op with
                | CSRRW => rs1_val
                | CSRRS => (csr_val ||| rs1_val)
                | CSRRC => (csr_val &&& (Complement.complement rs1_val))
              let final_val ← do (write_CSR csr new_val)
              (csr_id_write_callback csr final_val))
          else (csr_id_read_callback csr csr_val)
          (wX_bits rd csr_val)
          (pure RETIRE_SUCCESS)))

def csr_mnemonic_backwards (arg_ : String) : SailM csrop := do
  match arg_ with
  | "csrrw" => (pure CSRRW)
  | "csrrs" => (pure CSRRS)
  | "csrrc" => (pure CSRRC)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def csr_mnemonic_forwards_matches (arg_ : csrop) : Bool :=
  match arg_ with
  | CSRRW => true
  | CSRRS => true
  | CSRRC => true

def csr_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "csrrw" => true
  | "csrrs" => true
  | "csrrc" => true
  | _ => false


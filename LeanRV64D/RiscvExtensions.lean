import LeanRV64D.Flow
import LeanRV64D.Prelude
import LeanRV64D.RiscvXlen

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

def extensionName_forwards (arg_ : extension) : String :=
  match arg_ with
  | Ext_M => "m"
  | Ext_A => "a"
  | Ext_F => "f"
  | Ext_D => "d"
  | Ext_B => "b"
  | Ext_V => "v"
  | Ext_S => "s"
  | Ext_U => "u"
  | Ext_H => "h"
  | Ext_Zicbom => "zicbom"
  | Ext_Zicboz => "zicboz"
  | Ext_Zicntr => "zicntr"
  | Ext_Zicond => "zicond"
  | Ext_Zicsr => "zicsr"
  | Ext_Zifencei => "zifencei"
  | Ext_Zihintntl => "zihintntl"
  | Ext_Zihintpause => "zihintpause"
  | Ext_Zihpm => "zihpm"
  | Ext_Zimop => "zimop"
  | Ext_Zmmul => "zmmul"
  | Ext_Zaamo => "zaamo"
  | Ext_Zabha => "zabha"
  | Ext_Zacas => "zacas"
  | Ext_Zalrsc => "zalrsc"
  | Ext_Zawrs => "zawrs"
  | Ext_Zfa => "zfa"
  | Ext_Zfh => "zfh"
  | Ext_Zfhmin => "zfhmin"
  | Ext_Zfinx => "zfinx"
  | Ext_Zdinx => "zdinx"
  | Ext_Zca => "zca"
  | Ext_Zcb => "zcb"
  | Ext_Zcd => "zcd"
  | Ext_Zcf => "zcf"
  | Ext_Zcmop => "zcmop"
  | Ext_C => "c"
  | Ext_Zba => "zba"
  | Ext_Zbb => "zbb"
  | Ext_Zbc => "zbc"
  | Ext_Zbkb => "zbkb"
  | Ext_Zbkc => "zbkc"
  | Ext_Zbkx => "zbkx"
  | Ext_Zbs => "zbs"
  | Ext_Zknd => "zknd"
  | Ext_Zkne => "zkne"
  | Ext_Zknh => "zknh"
  | Ext_Zkr => "zkr"
  | Ext_Zksed => "zksed"
  | Ext_Zksh => "zksh"
  | Ext_Zkt => "zkt"
  | Ext_Zhinx => "zhinx"
  | Ext_Zhinxmin => "zhinxmin"
  | Ext_Zvbb => "zvbb"
  | Ext_Zvbc => "zvbc"
  | Ext_Zvkb => "zvkb"
  | Ext_Zvkg => "zvkg"
  | Ext_Zvkned => "zvkned"
  | Ext_Zvknha => "zvknha"
  | Ext_Zvknhb => "zvknhb"
  | Ext_Zvksed => "zvksed"
  | Ext_Zvksh => "zvksh"
  | Ext_Zvkt => "zvkt"
  | Ext_Zvkn => "zvkn"
  | Ext_Zvknc => "zvknc"
  | Ext_Zvkng => "zvkng"
  | Ext_Zvks => "zvks"
  | Ext_Zvksc => "zvksc"
  | Ext_Zvksg => "zvksg"
  | Ext_Sscofpmf => "sscofpmf"
  | Ext_Sstc => "sstc"
  | Ext_Svinval => "svinval"
  | Ext_Svnapot => "svnapot"
  | Ext_Svpbmt => "svpbmt"
  | Ext_Svbare => "svbare"
  | Ext_Sv32 => "sv32"
  | Ext_Sv39 => "sv39"
  | Ext_Sv48 => "sv48"
  | Ext_Sv57 => "sv57"
  | Ext_Smcntrpmf => "smcntrpmf"

def extensionName_backwards (arg_ : String) : SailM extension := do
  match arg_ with
  | "m" => (pure Ext_M)
  | "a" => (pure Ext_A)
  | "f" => (pure Ext_F)
  | "d" => (pure Ext_D)
  | "b" => (pure Ext_B)
  | "v" => (pure Ext_V)
  | "s" => (pure Ext_S)
  | "u" => (pure Ext_U)
  | "h" => (pure Ext_H)
  | "zicbom" => (pure Ext_Zicbom)
  | "zicboz" => (pure Ext_Zicboz)
  | "zicntr" => (pure Ext_Zicntr)
  | "zicond" => (pure Ext_Zicond)
  | "zicsr" => (pure Ext_Zicsr)
  | "zifencei" => (pure Ext_Zifencei)
  | "zihintntl" => (pure Ext_Zihintntl)
  | "zihintpause" => (pure Ext_Zihintpause)
  | "zihpm" => (pure Ext_Zihpm)
  | "zimop" => (pure Ext_Zimop)
  | "zmmul" => (pure Ext_Zmmul)
  | "zaamo" => (pure Ext_Zaamo)
  | "zabha" => (pure Ext_Zabha)
  | "zacas" => (pure Ext_Zacas)
  | "zalrsc" => (pure Ext_Zalrsc)
  | "zawrs" => (pure Ext_Zawrs)
  | "zfa" => (pure Ext_Zfa)
  | "zfh" => (pure Ext_Zfh)
  | "zfhmin" => (pure Ext_Zfhmin)
  | "zfinx" => (pure Ext_Zfinx)
  | "zdinx" => (pure Ext_Zdinx)
  | "zca" => (pure Ext_Zca)
  | "zcb" => (pure Ext_Zcb)
  | "zcd" => (pure Ext_Zcd)
  | "zcf" => (pure Ext_Zcf)
  | "zcmop" => (pure Ext_Zcmop)
  | "c" => (pure Ext_C)
  | "zba" => (pure Ext_Zba)
  | "zbb" => (pure Ext_Zbb)
  | "zbc" => (pure Ext_Zbc)
  | "zbkb" => (pure Ext_Zbkb)
  | "zbkc" => (pure Ext_Zbkc)
  | "zbkx" => (pure Ext_Zbkx)
  | "zbs" => (pure Ext_Zbs)
  | "zknd" => (pure Ext_Zknd)
  | "zkne" => (pure Ext_Zkne)
  | "zknh" => (pure Ext_Zknh)
  | "zkr" => (pure Ext_Zkr)
  | "zksed" => (pure Ext_Zksed)
  | "zksh" => (pure Ext_Zksh)
  | "zkt" => (pure Ext_Zkt)
  | "zhinx" => (pure Ext_Zhinx)
  | "zhinxmin" => (pure Ext_Zhinxmin)
  | "zvbb" => (pure Ext_Zvbb)
  | "zvbc" => (pure Ext_Zvbc)
  | "zvkb" => (pure Ext_Zvkb)
  | "zvkg" => (pure Ext_Zvkg)
  | "zvkned" => (pure Ext_Zvkned)
  | "zvknha" => (pure Ext_Zvknha)
  | "zvknhb" => (pure Ext_Zvknhb)
  | "zvksed" => (pure Ext_Zvksed)
  | "zvksh" => (pure Ext_Zvksh)
  | "zvkt" => (pure Ext_Zvkt)
  | "zvkn" => (pure Ext_Zvkn)
  | "zvknc" => (pure Ext_Zvknc)
  | "zvkng" => (pure Ext_Zvkng)
  | "zvks" => (pure Ext_Zvks)
  | "zvksc" => (pure Ext_Zvksc)
  | "zvksg" => (pure Ext_Zvksg)
  | "sscofpmf" => (pure Ext_Sscofpmf)
  | "sstc" => (pure Ext_Sstc)
  | "svinval" => (pure Ext_Svinval)
  | "svnapot" => (pure Ext_Svnapot)
  | "svpbmt" => (pure Ext_Svpbmt)
  | "svbare" => (pure Ext_Svbare)
  | "sv32" => (pure Ext_Sv32)
  | "sv39" => (pure Ext_Sv39)
  | "sv48" => (pure Ext_Sv48)
  | "sv57" => (pure Ext_Sv57)
  | "smcntrpmf" => (pure Ext_Smcntrpmf)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def extensionName_forwards_matches (arg_ : extension) : Bool :=
  match arg_ with
  | Ext_M => true
  | Ext_A => true
  | Ext_F => true
  | Ext_D => true
  | Ext_B => true
  | Ext_V => true
  | Ext_S => true
  | Ext_U => true
  | Ext_H => true
  | Ext_Zicbom => true
  | Ext_Zicboz => true
  | Ext_Zicntr => true
  | Ext_Zicond => true
  | Ext_Zicsr => true
  | Ext_Zifencei => true
  | Ext_Zihintntl => true
  | Ext_Zihintpause => true
  | Ext_Zihpm => true
  | Ext_Zimop => true
  | Ext_Zmmul => true
  | Ext_Zaamo => true
  | Ext_Zabha => true
  | Ext_Zacas => true
  | Ext_Zalrsc => true
  | Ext_Zawrs => true
  | Ext_Zfa => true
  | Ext_Zfh => true
  | Ext_Zfhmin => true
  | Ext_Zfinx => true
  | Ext_Zdinx => true
  | Ext_Zca => true
  | Ext_Zcb => true
  | Ext_Zcd => true
  | Ext_Zcf => true
  | Ext_Zcmop => true
  | Ext_C => true
  | Ext_Zba => true
  | Ext_Zbb => true
  | Ext_Zbc => true
  | Ext_Zbkb => true
  | Ext_Zbkc => true
  | Ext_Zbkx => true
  | Ext_Zbs => true
  | Ext_Zknd => true
  | Ext_Zkne => true
  | Ext_Zknh => true
  | Ext_Zkr => true
  | Ext_Zksed => true
  | Ext_Zksh => true
  | Ext_Zkt => true
  | Ext_Zhinx => true
  | Ext_Zhinxmin => true
  | Ext_Zvbb => true
  | Ext_Zvbc => true
  | Ext_Zvkb => true
  | Ext_Zvkg => true
  | Ext_Zvkned => true
  | Ext_Zvknha => true
  | Ext_Zvknhb => true
  | Ext_Zvksed => true
  | Ext_Zvksh => true
  | Ext_Zvkt => true
  | Ext_Zvkn => true
  | Ext_Zvknc => true
  | Ext_Zvkng => true
  | Ext_Zvks => true
  | Ext_Zvksc => true
  | Ext_Zvksg => true
  | Ext_Sscofpmf => true
  | Ext_Sstc => true
  | Ext_Svinval => true
  | Ext_Svnapot => true
  | Ext_Svpbmt => true
  | Ext_Svbare => true
  | Ext_Sv32 => true
  | Ext_Sv39 => true
  | Ext_Sv48 => true
  | Ext_Sv57 => true
  | Ext_Smcntrpmf => true

def extensionName_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "m" => true
  | "a" => true
  | "f" => true
  | "d" => true
  | "b" => true
  | "v" => true
  | "s" => true
  | "u" => true
  | "h" => true
  | "zicbom" => true
  | "zicboz" => true
  | "zicntr" => true
  | "zicond" => true
  | "zicsr" => true
  | "zifencei" => true
  | "zihintntl" => true
  | "zihintpause" => true
  | "zihpm" => true
  | "zimop" => true
  | "zmmul" => true
  | "zaamo" => true
  | "zabha" => true
  | "zacas" => true
  | "zalrsc" => true
  | "zawrs" => true
  | "zfa" => true
  | "zfh" => true
  | "zfhmin" => true
  | "zfinx" => true
  | "zdinx" => true
  | "zca" => true
  | "zcb" => true
  | "zcd" => true
  | "zcf" => true
  | "zcmop" => true
  | "c" => true
  | "zba" => true
  | "zbb" => true
  | "zbc" => true
  | "zbkb" => true
  | "zbkc" => true
  | "zbkx" => true
  | "zbs" => true
  | "zknd" => true
  | "zkne" => true
  | "zknh" => true
  | "zkr" => true
  | "zksed" => true
  | "zksh" => true
  | "zkt" => true
  | "zhinx" => true
  | "zhinxmin" => true
  | "zvbb" => true
  | "zvbc" => true
  | "zvkb" => true
  | "zvkg" => true
  | "zvkned" => true
  | "zvknha" => true
  | "zvknhb" => true
  | "zvksed" => true
  | "zvksh" => true
  | "zvkt" => true
  | "zvkn" => true
  | "zvknc" => true
  | "zvkng" => true
  | "zvks" => true
  | "zvksc" => true
  | "zvksg" => true
  | "sscofpmf" => true
  | "sstc" => true
  | "svinval" => true
  | "svnapot" => true
  | "svpbmt" => true
  | "svbare" => true
  | "sv32" => true
  | "sv39" => true
  | "sv48" => true
  | "sv57" => true
  | "smcntrpmf" => true
  | _ => false

def hartSupports_measure (ext : extension) : Int :=
  match ext with
  | Ext_D => 1
  | Ext_Zvkn => 1
  | Ext_Zvks => 1
  | Ext_C => 2
  | Ext_Zvknc => 2
  | Ext_Zvkng => 2
  | Ext_Zvksc => 2
  | Ext_Zvksg => 2
  | _ => 0

def hartSupports (merge_var : extension) : Bool :=
  match merge_var with
  | Ext_M => true
  | Ext_A => true
  | Ext_F => true
  | Ext_D => (true && (hartSupports Ext_F))
  | Ext_B => true
  | Ext_V => true
  | Ext_S => true
  | Ext_U => true
  | Ext_H => false
  | Ext_Zicbom => true
  | Ext_Zicboz => true
  | Ext_Zicntr => true
  | Ext_Zicond => true
  | Ext_Zicsr => true
  | Ext_Zifencei => true
  | Ext_Zihintntl => true
  | Ext_Zihintpause => true
  | Ext_Zihpm => true
  | Ext_Zimop => true
  | Ext_Zmmul => false
  | Ext_Zaamo => false
  | Ext_Zabha => true
  | Ext_Zacas => true
  | Ext_Zalrsc => false
  | Ext_Zawrs => true
  | Ext_Zfa => true
  | Ext_Zfh => true
  | Ext_Zfhmin => false
  | Ext_Zfinx => false
  | Ext_Zdinx => false
  | Ext_Zca => true
  | Ext_Zcb => true
  | Ext_Zcd => true
  | Ext_Zcf => ((false : Bool) && (xlen == 32))
  | Ext_Zcmop => true
  | Ext_C =>
    ((hartSupports Ext_Zca) && (((hartSupports Ext_Zcf) || ((not (hartSupports Ext_F)) || (xlen != 32))) && ((hartSupports
            Ext_Zcd) || (not (hartSupports Ext_D)))))
  | Ext_Zba => false
  | Ext_Zbb => false
  | Ext_Zbc => true
  | Ext_Zbkb => true
  | Ext_Zbkc => true
  | Ext_Zbkx => true
  | Ext_Zbs => false
  | Ext_Zknd => true
  | Ext_Zkne => true
  | Ext_Zknh => true
  | Ext_Zkr => true
  | Ext_Zksed => true
  | Ext_Zksh => true
  | Ext_Zkt => true
  | Ext_Zhinx => false
  | Ext_Zhinxmin => false
  | Ext_Zvbb => true
  | Ext_Zvbc => true
  | Ext_Zvkb => false
  | Ext_Zvkg => true
  | Ext_Zvkned => true
  | Ext_Zvknha => true
  | Ext_Zvknhb => true
  | Ext_Zvksed => true
  | Ext_Zvksh => true
  | Ext_Zvkt => true
  | Ext_Zvkn =>
    ((hartSupports Ext_Zvkned) && ((hartSupports Ext_Zvknhb) && ((hartSupports Ext_Zvkb) && (hartSupports
            Ext_Zvkt))))
  | Ext_Zvknc => ((hartSupports Ext_Zvkn) && (hartSupports Ext_Zvbc))
  | Ext_Zvkng => ((hartSupports Ext_Zvkn) && (hartSupports Ext_Zvkg))
  | Ext_Zvks =>
    ((hartSupports Ext_Zvksed) && ((hartSupports Ext_Zvksh) && ((hartSupports Ext_Zvkb) && (hartSupports
            Ext_Zvkt))))
  | Ext_Zvksc => ((hartSupports Ext_Zvks) && (hartSupports Ext_Zvbc))
  | Ext_Zvksg => ((hartSupports Ext_Zvks) && (hartSupports Ext_Zvkg))
  | Ext_Sscofpmf => true
  | Ext_Sstc => true
  | Ext_Svinval => true
  | Ext_Svnapot => false
  | Ext_Svpbmt => false
  | Ext_Svbare => true
  | Ext_Sv32 => ((false : Bool) && (xlen == 32))
  | Ext_Sv39 => ((true : Bool) && (xlen == 64))
  | Ext_Sv48 => ((true : Bool) && (xlen == 64))
  | Ext_Sv57 => ((true : Bool) && (xlen == 64))
  | Ext_Smcntrpmf => true
termination_by let ext := merge_var; ((hartSupports_measure ext)).toNat

def extensions_ordered_for_isa_string :=
  #v[Ext_Smcntrpmf, Ext_Svpbmt, Ext_Svnapot, Ext_Svinval, Ext_Sstc, Ext_Sscofpmf, Ext_Zvkt, Ext_Zvksh, Ext_Zvksg, Ext_Zvksed, Ext_Zvksc, Ext_Zvks, Ext_Zvknhb, Ext_Zvknha, Ext_Zvkng, Ext_Zvkned, Ext_Zvknc, Ext_Zvkn, Ext_Zvkg, Ext_Zvkb, Ext_Zvbc, Ext_Zvbb, Ext_Zkt, Ext_Zksh, Ext_Zksed, Ext_Zkr, Ext_Zknh, Ext_Zkne, Ext_Zknd, Ext_Zbs, Ext_Zbkx, Ext_Zbkc, Ext_Zbkb, Ext_Zbc, Ext_Zbb, Ext_Zba, Ext_Zcmop, Ext_Zcf, Ext_Zcd, Ext_Zcb, Ext_Zca, Ext_Zhinxmin, Ext_Zhinx, Ext_Zdinx, Ext_Zfinx, Ext_Zfhmin, Ext_Zfh, Ext_Zfa, Ext_Zawrs, Ext_Zalrsc, Ext_Zacas, Ext_Zabha, Ext_Zaamo, Ext_Zmmul, Ext_Zimop, Ext_Zihpm, Ext_Zihintpause, Ext_Zihintntl, Ext_Zifencei, Ext_Zicsr, Ext_Zicond, Ext_Zicntr, Ext_Zicboz, Ext_Zicbom, Ext_H, Ext_V, Ext_B, Ext_C, Ext_D, Ext_F, Ext_A, Ext_M]


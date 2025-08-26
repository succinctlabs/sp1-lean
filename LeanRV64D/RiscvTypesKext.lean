import LeanRV64D.Prelude
import LeanRV64D.RiscvErrors

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

def xt2 (x : (BitVec 8)) : SailM (BitVec 8) := do
  (pure ((shiftl x 1) ^^^ (← do
        if ((← (bit_to_bool (BitVec.access x 7))) : Bool)
        then (pure (0x1B : (BitVec 8)))
        else (pure (0x00 : (BitVec 8))))))

def xt3 (x : (BitVec 8)) : SailM (BitVec 8) := do
  (pure (x ^^^ (← (xt2 x))))

def gfmul (x : (BitVec 8)) (y : (BitVec 4)) : SailM (BitVec 8) := do
  (pure ((← do
        if ((← (bit_to_bool (BitVec.access y 0))) : Bool)
        then (pure x)
        else (pure (0x00 : (BitVec 8)))) ^^^ ((← do
          if ((← (bit_to_bool (BitVec.access y 1))) : Bool)
          then (xt2 x)
          else (pure (0x00 : (BitVec 8)))) ^^^ ((← do
            if ((← (bit_to_bool (BitVec.access y 2))) : Bool)
            then (xt2 (← (xt2 x)))
            else (pure (0x00 : (BitVec 8)))) ^^^ (← do
            if ((← (bit_to_bool (BitVec.access y 3))) : Bool)
            then (xt2 (← (xt2 (← (xt2 x)))))
            else (pure (0x00 : (BitVec 8))))))))

def aes_mixcolumn_byte_fwd (so : (BitVec 8)) : SailM (BitVec 32) := do
  (pure ((← (gfmul so (0x3 : (BitVec 4)))) ++ (so ++ (so ++ (← (gfmul so (0x2 : (BitVec 4))))))))

def aes_mixcolumn_byte_inv (so : (BitVec 8)) : SailM (BitVec 32) := do
  (pure ((← (gfmul so (0xB : (BitVec 4)))) ++ ((← (gfmul so (0xD : (BitVec 4)))) ++ ((← (gfmul
              so (0x9 : (BitVec 4)))) ++ (← (gfmul so (0xE : (BitVec 4))))))))

def aes_mixcolumn_fwd (x : (BitVec 32)) : SailM (BitVec 32) := do
  let s0 : (BitVec 8) := (Sail.BitVec.extractLsb x 7 0)
  let s1 : (BitVec 8) := (Sail.BitVec.extractLsb x 15 8)
  let s2 : (BitVec 8) := (Sail.BitVec.extractLsb x 23 16)
  let s3 : (BitVec 8) := (Sail.BitVec.extractLsb x 31 24)
  let b0 ← (( do (pure ((← (xt2 s0)) ^^^ ((← (xt3 s1)) ^^^ (s2 ^^^ s3)))) ) : SailM (BitVec 8)
    )
  let b1 ← (( do (pure (s0 ^^^ ((← (xt2 s1)) ^^^ ((← (xt3 s2)) ^^^ s3)))) ) : SailM (BitVec 8)
    )
  let b2 ← (( do (pure (s0 ^^^ (s1 ^^^ ((← (xt2 s2)) ^^^ (← (xt3 s3)))))) ) : SailM (BitVec 8)
    )
  let b3 ← (( do (pure ((← (xt3 s0)) ^^^ (s1 ^^^ (s2 ^^^ (← (xt2 s3)))))) ) : SailM (BitVec 8)
    )
  (pure (b3 ++ (b2 ++ (b1 ++ b0))))

def aes_mixcolumn_inv (x : (BitVec 32)) : SailM (BitVec 32) := do
  let s0 : (BitVec 8) := (Sail.BitVec.extractLsb x 7 0)
  let s1 : (BitVec 8) := (Sail.BitVec.extractLsb x 15 8)
  let s2 : (BitVec 8) := (Sail.BitVec.extractLsb x 23 16)
  let s3 : (BitVec 8) := (Sail.BitVec.extractLsb x 31 24)
  let b0 ← (( do
    (pure ((← (gfmul s0 (0xE : (BitVec 4)))) ^^^ ((← (gfmul s1 (0xB : (BitVec 4)))) ^^^ ((← (gfmul
                s2 (0xD : (BitVec 4)))) ^^^ (← (gfmul s3 (0x9 : (BitVec 4)))))))) ) : SailM
    (BitVec 8) )
  let b1 ← (( do
    (pure ((← (gfmul s0 (0x9 : (BitVec 4)))) ^^^ ((← (gfmul s1 (0xE : (BitVec 4)))) ^^^ ((← (gfmul
                s2 (0xB : (BitVec 4)))) ^^^ (← (gfmul s3 (0xD : (BitVec 4)))))))) ) : SailM
    (BitVec 8) )
  let b2 ← (( do
    (pure ((← (gfmul s0 (0xD : (BitVec 4)))) ^^^ ((← (gfmul s1 (0x9 : (BitVec 4)))) ^^^ ((← (gfmul
                s2 (0xE : (BitVec 4)))) ^^^ (← (gfmul s3 (0xB : (BitVec 4)))))))) ) : SailM
    (BitVec 8) )
  let b3 ← (( do
    (pure ((← (gfmul s0 (0xB : (BitVec 4)))) ^^^ ((← (gfmul s1 (0xD : (BitVec 4)))) ^^^ ((← (gfmul
                s2 (0x9 : (BitVec 4)))) ^^^ (← (gfmul s3 (0xE : (BitVec 4)))))))) ) : SailM
    (BitVec 8) )
  (pure (b3 ++ (b2 ++ (b1 ++ b0))))

def aes_decode_rcon (r : (BitVec 4)) : SailM (BitVec 32) := do
  assert (zopz0zI_u r (0xA : (BitVec 4))) "riscv_types_kext.sail:87.18-87.19"
  let b__0 := r
  if ((b__0 == (0x0 : (BitVec 4))) : Bool)
  then (pure (0x00000001 : (BitVec 32)))
  else
    (do
      if ((b__0 == (0x1 : (BitVec 4))) : Bool)
      then (pure (0x00000002 : (BitVec 32)))
      else
        (do
          if ((b__0 == (0x2 : (BitVec 4))) : Bool)
          then (pure (0x00000004 : (BitVec 32)))
          else
            (do
              if ((b__0 == (0x3 : (BitVec 4))) : Bool)
              then (pure (0x00000008 : (BitVec 32)))
              else
                (do
                  if ((b__0 == (0x4 : (BitVec 4))) : Bool)
                  then (pure (0x00000010 : (BitVec 32)))
                  else
                    (do
                      if ((b__0 == (0x5 : (BitVec 4))) : Bool)
                      then (pure (0x00000020 : (BitVec 32)))
                      else
                        (do
                          if ((b__0 == (0x6 : (BitVec 4))) : Bool)
                          then (pure (0x00000040 : (BitVec 32)))
                          else
                            (do
                              if ((b__0 == (0x7 : (BitVec 4))) : Bool)
                              then (pure (0x00000080 : (BitVec 32)))
                              else
                                (do
                                  if ((b__0 == (0x8 : (BitVec 4))) : Bool)
                                  then (pure (0x0000001B : (BitVec 32)))
                                  else
                                    (do
                                      if ((b__0 == (0x9 : (BitVec 4))) : Bool)
                                      then (pure (0x00000036 : (BitVec 32)))
                                      else
                                        (internal_error "riscv_types_kext.sail" 99
                                          "Unexpected AES r"))))))))))

def sm4_sbox_table : (Vector (BitVec 8) 256) :=
  #v[(0x48 : (BitVec 8)), (0x39 : (BitVec 8)), (0xCB : (BitVec 8)), (0xD7 : (BitVec 8)), (0x3E : (BitVec 8)), (0x5F : (BitVec 8)), (0xEE : (BitVec 8)), (0x79 : (BitVec 8)), (0x20 : (BitVec 8)), (0x4D : (BitVec 8)), (0xDC : (BitVec 8)), (0x3A : (BitVec 8)), (0xEC : (BitVec 8)), (0x7D : (BitVec 8)), (0xF0 : (BitVec 8)), (0x18 : (BitVec 8)), (0x84 : (BitVec 8)), (0xC6 : (BitVec 8)), (0x6E : (BitVec 8)), (0xC5 : (BitVec 8)), (0x09 : (BitVec 8)), (0xF1 : (BitVec 8)), (0xB9 : (BitVec 8)), (0x65 : (BitVec 8)), (0x7E : (BitVec 8)), (0x77 : (BitVec 8)), (0x96 : (BitVec 8)), (0x0C : (BitVec 8)), (0x4A : (BitVec 8)), (0x97 : (BitVec 8)), (0x69 : (BitVec 8)), (0x89 : (BitVec 8)), (0xB0 : (BitVec 8)), (0xB4 : (BitVec 8)), (0xE5 : (BitVec 8)), (0xB8 : (BitVec 8)), (0x12 : (BitVec 8)), (0xD0 : (BitVec 8)), (0x74 : (BitVec 8)), (0x2D : (BitVec 8)), (0xBD : (BitVec 8)), (0x7B : (BitVec 8)), (0xCD : (BitVec 8)), (0xA5 : (BitVec 8)), (0x88 : (BitVec 8)), (0x31 : (BitVec 8)), (0xC1 : (BitVec 8)), (0x0A : (BitVec 8)), (0xD8 : (BitVec 8)), (0x5A : (BitVec 8)), (0x10 : (BitVec 8)), (0x1F : (BitVec 8)), (0x41 : (BitVec 8)), (0x5C : (BitVec 8)), (0xD9 : (BitVec 8)), (0x11 : (BitVec 8)), (0x7F : (BitVec 8)), (0xBC : (BitVec 8)), (0xDD : (BitVec 8)), (0xBB : (BitVec 8)), (0x92 : (BitVec 8)), (0xAF : (BitVec 8)), (0x1B : (BitVec 8)), (0x8D : (BitVec 8)), (0x51 : (BitVec 8)), (0x5B : (BitVec 8)), (0x6C : (BitVec 8)), (0x6D : (BitVec 8)), (0x72 : (BitVec 8)), (0x6A : (BitVec 8)), (0xFF : (BitVec 8)), (0x03 : (BitVec 8)), (0x2F : (BitVec 8)), (0x8E : (BitVec 8)), (0xFD : (BitVec 8)), (0xDE : (BitVec 8)), (0x45 : (BitVec 8)), (0x37 : (BitVec 8)), (0xDB : (BitVec 8)), (0xD5 : (BitVec 8)), (0x6F : (BitVec 8)), (0x4E : (BitVec 8)), (0x53 : (BitVec 8)), (0x0D : (BitVec 8)), (0xAB : (BitVec 8)), (0x23 : (BitVec 8)), (0x29 : (BitVec 8)), (0xC0 : (BitVec 8)), (0x60 : (BitVec 8)), (0xCA : (BitVec 8)), (0x66 : (BitVec 8)), (0x82 : (BitVec 8)), (0x2E : (BitVec 8)), (0xE2 : (BitVec 8)), (0xF6 : (BitVec 8)), (0x1D : (BitVec 8)), (0xE3 : (BitVec 8)), (0xB1 : (BitVec 8)), (0x8C : (BitVec 8)), (0xF5 : (BitVec 8)), (0x30 : (BitVec 8)), (0x32 : (BitVec 8)), (0x93 : (BitVec 8)), (0xAD : (BitVec 8)), (0x55 : (BitVec 8)), (0x1A : (BitVec 8)), (0x34 : (BitVec 8)), (0x9B : (BitVec 8)), (0xA4 : (BitVec 8)), (0x5D : (BitVec 8)), (0xAE : (BitVec 8)), (0xE0 : (BitVec 8)), (0xA1 : (BitVec 8)), (0x15 : (BitVec 8)), (0x61 : (BitVec 8)), (0xF9 : (BitVec 8)), (0xCE : (BitVec 8)), (0xF2 : (BitVec 8)), (0xF7 : (BitVec 8)), (0xA3 : (BitVec 8)), (0xB5 : (BitVec 8)), (0x38 : (BitVec 8)), (0xC7 : (BitVec 8)), (0x40 : (BitVec 8)), (0xD2 : (BitVec 8)), (0x8A : (BitVec 8)), (0xBF : (BitVec 8)), (0xEA : (BitVec 8)), (0x9E : (BitVec 8)), (0xC8 : (BitVec 8)), (0xC4 : (BitVec 8)), (0xA0 : (BitVec 8)), (0xE7 : (BitVec 8)), (0x02 : (BitVec 8)), (0x36 : (BitVec 8)), (0x4C : (BitVec 8)), (0x52 : (BitVec 8)), (0x27 : (BitVec 8)), (0xD3 : (BitVec 8)), (0x9F : (BitVec 8)), (0x57 : (BitVec 8)), (0x46 : (BitVec 8)), (0x00 : (BitVec 8)), (0xD4 : (BitVec 8)), (0x87 : (BitVec 8)), (0x78 : (BitVec 8)), (0x21 : (BitVec 8)), (0x01 : (BitVec 8)), (0x3B : (BitVec 8)), (0x7C : (BitVec 8)), (0x22 : (BitVec 8)), (0x25 : (BitVec 8)), (0xA2 : (BitVec 8)), (0xD1 : (BitVec 8)), (0x58 : (BitVec 8)), (0x63 : (BitVec 8)), (0x5E : (BitVec 8)), (0x0E : (BitVec 8)), (0x24 : (BitVec 8)), (0x1E : (BitVec 8)), (0x35 : (BitVec 8)), (0x9D : (BitVec 8)), (0x56 : (BitVec 8)), (0x70 : (BitVec 8)), (0x4B : (BitVec 8)), (0x0F : (BitVec 8)), (0xEB : (BitVec 8)), (0xF8 : (BitVec 8)), (0x8B : (BitVec 8)), (0xDA : (BitVec 8)), (0x64 : (BitVec 8)), (0x71 : (BitVec 8)), (0xB2 : (BitVec 8)), (0x81 : (BitVec 8)), (0x6B : (BitVec 8)), (0x68 : (BitVec 8)), (0xA8 : (BitVec 8)), (0x4F : (BitVec 8)), (0x85 : (BitVec 8)), (0xE6 : (BitVec 8)), (0x19 : (BitVec 8)), (0x3C : (BitVec 8)), (0x59 : (BitVec 8)), (0x83 : (BitVec 8)), (0xBA : (BitVec 8)), (0x17 : (BitVec 8)), (0x73 : (BitVec 8)), (0xF3 : (BitVec 8)), (0xFC : (BitVec 8)), (0xA7 : (BitVec 8)), (0x07 : (BitVec 8)), (0x47 : (BitVec 8)), (0xA6 : (BitVec 8)), (0x3F : (BitVec 8)), (0x8F : (BitVec 8)), (0x75 : (BitVec 8)), (0xFA : (BitVec 8)), (0x94 : (BitVec 8)), (0xDF : (BitVec 8)), (0x80 : (BitVec 8)), (0x95 : (BitVec 8)), (0xE8 : (BitVec 8)), (0x08 : (BitVec 8)), (0xC9 : (BitVec 8)), (0xA9 : (BitVec 8)), (0x1C : (BitVec 8)), (0xB3 : (BitVec 8)), (0xE4 : (BitVec 8)), (0x62 : (BitVec 8)), (0xAC : (BitVec 8)), (0xCF : (BitVec 8)), (0xED : (BitVec 8)), (0x43 : (BitVec 8)), (0x0B : (BitVec 8)), (0x54 : (BitVec 8)), (0x33 : (BitVec 8)), (0x7A : (BitVec 8)), (0x98 : (BitVec 8)), (0xEF : (BitVec 8)), (0x91 : (BitVec 8)), (0xF4 : (BitVec 8)), (0x50 : (BitVec 8)), (0x42 : (BitVec 8)), (0x9C : (BitVec 8)), (0x99 : (BitVec 8)), (0x06 : (BitVec 8)), (0x86 : (BitVec 8)), (0x49 : (BitVec 8)), (0x26 : (BitVec 8)), (0x13 : (BitVec 8)), (0x44 : (BitVec 8)), (0xAA : (BitVec 8)), (0xC3 : (BitVec 8)), (0x04 : (BitVec 8)), (0xBE : (BitVec 8)), (0x2A : (BitVec 8)), (0x76 : (BitVec 8)), (0x9A : (BitVec 8)), (0x67 : (BitVec 8)), (0x2B : (BitVec 8)), (0x05 : (BitVec 8)), (0x2C : (BitVec 8)), (0xFB : (BitVec 8)), (0x28 : (BitVec 8)), (0xC2 : (BitVec 8)), (0x14 : (BitVec 8)), (0xB6 : (BitVec 8)), (0x16 : (BitVec 8)), (0xB7 : (BitVec 8)), (0x3D : (BitVec 8)), (0xE1 : (BitVec 8)), (0xCC : (BitVec 8)), (0xFE : (BitVec 8)), (0xE9 : (BitVec 8)), (0x90 : (BitVec 8)), (0xD6 : (BitVec 8))]

def aes_sbox_fwd_table : (Vector (BitVec 8) 256) :=
  #v[(0x16 : (BitVec 8)), (0xBB : (BitVec 8)), (0x54 : (BitVec 8)), (0xB0 : (BitVec 8)), (0x0F : (BitVec 8)), (0x2D : (BitVec 8)), (0x99 : (BitVec 8)), (0x41 : (BitVec 8)), (0x68 : (BitVec 8)), (0x42 : (BitVec 8)), (0xE6 : (BitVec 8)), (0xBF : (BitVec 8)), (0x0D : (BitVec 8)), (0x89 : (BitVec 8)), (0xA1 : (BitVec 8)), (0x8C : (BitVec 8)), (0xDF : (BitVec 8)), (0x28 : (BitVec 8)), (0x55 : (BitVec 8)), (0xCE : (BitVec 8)), (0xE9 : (BitVec 8)), (0x87 : (BitVec 8)), (0x1E : (BitVec 8)), (0x9B : (BitVec 8)), (0x94 : (BitVec 8)), (0x8E : (BitVec 8)), (0xD9 : (BitVec 8)), (0x69 : (BitVec 8)), (0x11 : (BitVec 8)), (0x98 : (BitVec 8)), (0xF8 : (BitVec 8)), (0xE1 : (BitVec 8)), (0x9E : (BitVec 8)), (0x1D : (BitVec 8)), (0xC1 : (BitVec 8)), (0x86 : (BitVec 8)), (0xB9 : (BitVec 8)), (0x57 : (BitVec 8)), (0x35 : (BitVec 8)), (0x61 : (BitVec 8)), (0x0E : (BitVec 8)), (0xF6 : (BitVec 8)), (0x03 : (BitVec 8)), (0x48 : (BitVec 8)), (0x66 : (BitVec 8)), (0xB5 : (BitVec 8)), (0x3E : (BitVec 8)), (0x70 : (BitVec 8)), (0x8A : (BitVec 8)), (0x8B : (BitVec 8)), (0xBD : (BitVec 8)), (0x4B : (BitVec 8)), (0x1F : (BitVec 8)), (0x74 : (BitVec 8)), (0xDD : (BitVec 8)), (0xE8 : (BitVec 8)), (0xC6 : (BitVec 8)), (0xB4 : (BitVec 8)), (0xA6 : (BitVec 8)), (0x1C : (BitVec 8)), (0x2E : (BitVec 8)), (0x25 : (BitVec 8)), (0x78 : (BitVec 8)), (0xBA : (BitVec 8)), (0x08 : (BitVec 8)), (0xAE : (BitVec 8)), (0x7A : (BitVec 8)), (0x65 : (BitVec 8)), (0xEA : (BitVec 8)), (0xF4 : (BitVec 8)), (0x56 : (BitVec 8)), (0x6C : (BitVec 8)), (0xA9 : (BitVec 8)), (0x4E : (BitVec 8)), (0xD5 : (BitVec 8)), (0x8D : (BitVec 8)), (0x6D : (BitVec 8)), (0x37 : (BitVec 8)), (0xC8 : (BitVec 8)), (0xE7 : (BitVec 8)), (0x79 : (BitVec 8)), (0xE4 : (BitVec 8)), (0x95 : (BitVec 8)), (0x91 : (BitVec 8)), (0x62 : (BitVec 8)), (0xAC : (BitVec 8)), (0xD3 : (BitVec 8)), (0xC2 : (BitVec 8)), (0x5C : (BitVec 8)), (0x24 : (BitVec 8)), (0x06 : (BitVec 8)), (0x49 : (BitVec 8)), (0x0A : (BitVec 8)), (0x3A : (BitVec 8)), (0x32 : (BitVec 8)), (0xE0 : (BitVec 8)), (0xDB : (BitVec 8)), (0x0B : (BitVec 8)), (0x5E : (BitVec 8)), (0xDE : (BitVec 8)), (0x14 : (BitVec 8)), (0xB8 : (BitVec 8)), (0xEE : (BitVec 8)), (0x46 : (BitVec 8)), (0x88 : (BitVec 8)), (0x90 : (BitVec 8)), (0x2A : (BitVec 8)), (0x22 : (BitVec 8)), (0xDC : (BitVec 8)), (0x4F : (BitVec 8)), (0x81 : (BitVec 8)), (0x60 : (BitVec 8)), (0x73 : (BitVec 8)), (0x19 : (BitVec 8)), (0x5D : (BitVec 8)), (0x64 : (BitVec 8)), (0x3D : (BitVec 8)), (0x7E : (BitVec 8)), (0xA7 : (BitVec 8)), (0xC4 : (BitVec 8)), (0x17 : (BitVec 8)), (0x44 : (BitVec 8)), (0x97 : (BitVec 8)), (0x5F : (BitVec 8)), (0xEC : (BitVec 8)), (0x13 : (BitVec 8)), (0x0C : (BitVec 8)), (0xCD : (BitVec 8)), (0xD2 : (BitVec 8)), (0xF3 : (BitVec 8)), (0xFF : (BitVec 8)), (0x10 : (BitVec 8)), (0x21 : (BitVec 8)), (0xDA : (BitVec 8)), (0xB6 : (BitVec 8)), (0xBC : (BitVec 8)), (0xF5 : (BitVec 8)), (0x38 : (BitVec 8)), (0x9D : (BitVec 8)), (0x92 : (BitVec 8)), (0x8F : (BitVec 8)), (0x40 : (BitVec 8)), (0xA3 : (BitVec 8)), (0x51 : (BitVec 8)), (0xA8 : (BitVec 8)), (0x9F : (BitVec 8)), (0x3C : (BitVec 8)), (0x50 : (BitVec 8)), (0x7F : (BitVec 8)), (0x02 : (BitVec 8)), (0xF9 : (BitVec 8)), (0x45 : (BitVec 8)), (0x85 : (BitVec 8)), (0x33 : (BitVec 8)), (0x4D : (BitVec 8)), (0x43 : (BitVec 8)), (0xFB : (BitVec 8)), (0xAA : (BitVec 8)), (0xEF : (BitVec 8)), (0xD0 : (BitVec 8)), (0xCF : (BitVec 8)), (0x58 : (BitVec 8)), (0x4C : (BitVec 8)), (0x4A : (BitVec 8)), (0x39 : (BitVec 8)), (0xBE : (BitVec 8)), (0xCB : (BitVec 8)), (0x6A : (BitVec 8)), (0x5B : (BitVec 8)), (0xB1 : (BitVec 8)), (0xFC : (BitVec 8)), (0x20 : (BitVec 8)), (0xED : (BitVec 8)), (0x00 : (BitVec 8)), (0xD1 : (BitVec 8)), (0x53 : (BitVec 8)), (0x84 : (BitVec 8)), (0x2F : (BitVec 8)), (0xE3 : (BitVec 8)), (0x29 : (BitVec 8)), (0xB3 : (BitVec 8)), (0xD6 : (BitVec 8)), (0x3B : (BitVec 8)), (0x52 : (BitVec 8)), (0xA0 : (BitVec 8)), (0x5A : (BitVec 8)), (0x6E : (BitVec 8)), (0x1B : (BitVec 8)), (0x1A : (BitVec 8)), (0x2C : (BitVec 8)), (0x83 : (BitVec 8)), (0x09 : (BitVec 8)), (0x75 : (BitVec 8)), (0xB2 : (BitVec 8)), (0x27 : (BitVec 8)), (0xEB : (BitVec 8)), (0xE2 : (BitVec 8)), (0x80 : (BitVec 8)), (0x12 : (BitVec 8)), (0x07 : (BitVec 8)), (0x9A : (BitVec 8)), (0x05 : (BitVec 8)), (0x96 : (BitVec 8)), (0x18 : (BitVec 8)), (0xC3 : (BitVec 8)), (0x23 : (BitVec 8)), (0xC7 : (BitVec 8)), (0x04 : (BitVec 8)), (0x15 : (BitVec 8)), (0x31 : (BitVec 8)), (0xD8 : (BitVec 8)), (0x71 : (BitVec 8)), (0xF1 : (BitVec 8)), (0xE5 : (BitVec 8)), (0xA5 : (BitVec 8)), (0x34 : (BitVec 8)), (0xCC : (BitVec 8)), (0xF7 : (BitVec 8)), (0x3F : (BitVec 8)), (0x36 : (BitVec 8)), (0x26 : (BitVec 8)), (0x93 : (BitVec 8)), (0xFD : (BitVec 8)), (0xB7 : (BitVec 8)), (0xC0 : (BitVec 8)), (0x72 : (BitVec 8)), (0xA4 : (BitVec 8)), (0x9C : (BitVec 8)), (0xAF : (BitVec 8)), (0xA2 : (BitVec 8)), (0xD4 : (BitVec 8)), (0xAD : (BitVec 8)), (0xF0 : (BitVec 8)), (0x47 : (BitVec 8)), (0x59 : (BitVec 8)), (0xFA : (BitVec 8)), (0x7D : (BitVec 8)), (0xC9 : (BitVec 8)), (0x82 : (BitVec 8)), (0xCA : (BitVec 8)), (0x76 : (BitVec 8)), (0xAB : (BitVec 8)), (0xD7 : (BitVec 8)), (0xFE : (BitVec 8)), (0x2B : (BitVec 8)), (0x67 : (BitVec 8)), (0x01 : (BitVec 8)), (0x30 : (BitVec 8)), (0xC5 : (BitVec 8)), (0x6F : (BitVec 8)), (0x6B : (BitVec 8)), (0xF2 : (BitVec 8)), (0x7B : (BitVec 8)), (0x77 : (BitVec 8)), (0x7C : (BitVec 8)), (0x63 : (BitVec 8))]

def aes_sbox_inv_table : (Vector (BitVec 8) 256) :=
  #v[(0x7D : (BitVec 8)), (0x0C : (BitVec 8)), (0x21 : (BitVec 8)), (0x55 : (BitVec 8)), (0x63 : (BitVec 8)), (0x14 : (BitVec 8)), (0x69 : (BitVec 8)), (0xE1 : (BitVec 8)), (0x26 : (BitVec 8)), (0xD6 : (BitVec 8)), (0x77 : (BitVec 8)), (0xBA : (BitVec 8)), (0x7E : (BitVec 8)), (0x04 : (BitVec 8)), (0x2B : (BitVec 8)), (0x17 : (BitVec 8)), (0x61 : (BitVec 8)), (0x99 : (BitVec 8)), (0x53 : (BitVec 8)), (0x83 : (BitVec 8)), (0x3C : (BitVec 8)), (0xBB : (BitVec 8)), (0xEB : (BitVec 8)), (0xC8 : (BitVec 8)), (0xB0 : (BitVec 8)), (0xF5 : (BitVec 8)), (0x2A : (BitVec 8)), (0xAE : (BitVec 8)), (0x4D : (BitVec 8)), (0x3B : (BitVec 8)), (0xE0 : (BitVec 8)), (0xA0 : (BitVec 8)), (0xEF : (BitVec 8)), (0x9C : (BitVec 8)), (0xC9 : (BitVec 8)), (0x93 : (BitVec 8)), (0x9F : (BitVec 8)), (0x7A : (BitVec 8)), (0xE5 : (BitVec 8)), (0x2D : (BitVec 8)), (0x0D : (BitVec 8)), (0x4A : (BitVec 8)), (0xB5 : (BitVec 8)), (0x19 : (BitVec 8)), (0xA9 : (BitVec 8)), (0x7F : (BitVec 8)), (0x51 : (BitVec 8)), (0x60 : (BitVec 8)), (0x5F : (BitVec 8)), (0xEC : (BitVec 8)), (0x80 : (BitVec 8)), (0x27 : (BitVec 8)), (0x59 : (BitVec 8)), (0x10 : (BitVec 8)), (0x12 : (BitVec 8)), (0xB1 : (BitVec 8)), (0x31 : (BitVec 8)), (0xC7 : (BitVec 8)), (0x07 : (BitVec 8)), (0x88 : (BitVec 8)), (0x33 : (BitVec 8)), (0xA8 : (BitVec 8)), (0xDD : (BitVec 8)), (0x1F : (BitVec 8)), (0xF4 : (BitVec 8)), (0x5A : (BitVec 8)), (0xCD : (BitVec 8)), (0x78 : (BitVec 8)), (0xFE : (BitVec 8)), (0xC0 : (BitVec 8)), (0xDB : (BitVec 8)), (0x9A : (BitVec 8)), (0x20 : (BitVec 8)), (0x79 : (BitVec 8)), (0xD2 : (BitVec 8)), (0xC6 : (BitVec 8)), (0x4B : (BitVec 8)), (0x3E : (BitVec 8)), (0x56 : (BitVec 8)), (0xFC : (BitVec 8)), (0x1B : (BitVec 8)), (0xBE : (BitVec 8)), (0x18 : (BitVec 8)), (0xAA : (BitVec 8)), (0x0E : (BitVec 8)), (0x62 : (BitVec 8)), (0xB7 : (BitVec 8)), (0x6F : (BitVec 8)), (0x89 : (BitVec 8)), (0xC5 : (BitVec 8)), (0x29 : (BitVec 8)), (0x1D : (BitVec 8)), (0x71 : (BitVec 8)), (0x1A : (BitVec 8)), (0xF1 : (BitVec 8)), (0x47 : (BitVec 8)), (0x6E : (BitVec 8)), (0xDF : (BitVec 8)), (0x75 : (BitVec 8)), (0x1C : (BitVec 8)), (0xE8 : (BitVec 8)), (0x37 : (BitVec 8)), (0xF9 : (BitVec 8)), (0xE2 : (BitVec 8)), (0x85 : (BitVec 8)), (0x35 : (BitVec 8)), (0xAD : (BitVec 8)), (0xE7 : (BitVec 8)), (0x22 : (BitVec 8)), (0x74 : (BitVec 8)), (0xAC : (BitVec 8)), (0x96 : (BitVec 8)), (0x73 : (BitVec 8)), (0xE6 : (BitVec 8)), (0xB4 : (BitVec 8)), (0xF0 : (BitVec 8)), (0xCE : (BitVec 8)), (0xCF : (BitVec 8)), (0xF2 : (BitVec 8)), (0x97 : (BitVec 8)), (0xEA : (BitVec 8)), (0xDC : (BitVec 8)), (0x67 : (BitVec 8)), (0x4F : (BitVec 8)), (0x41 : (BitVec 8)), (0x11 : (BitVec 8)), (0x91 : (BitVec 8)), (0x3A : (BitVec 8)), (0x6B : (BitVec 8)), (0x8A : (BitVec 8)), (0x13 : (BitVec 8)), (0x01 : (BitVec 8)), (0x03 : (BitVec 8)), (0xBD : (BitVec 8)), (0xAF : (BitVec 8)), (0xC1 : (BitVec 8)), (0x02 : (BitVec 8)), (0x0F : (BitVec 8)), (0x3F : (BitVec 8)), (0xCA : (BitVec 8)), (0x8F : (BitVec 8)), (0x1E : (BitVec 8)), (0x2C : (BitVec 8)), (0xD0 : (BitVec 8)), (0x06 : (BitVec 8)), (0x45 : (BitVec 8)), (0xB3 : (BitVec 8)), (0xB8 : (BitVec 8)), (0x05 : (BitVec 8)), (0x58 : (BitVec 8)), (0xE4 : (BitVec 8)), (0xF7 : (BitVec 8)), (0x0A : (BitVec 8)), (0xD3 : (BitVec 8)), (0xBC : (BitVec 8)), (0x8C : (BitVec 8)), (0x00 : (BitVec 8)), (0xAB : (BitVec 8)), (0xD8 : (BitVec 8)), (0x90 : (BitVec 8)), (0x84 : (BitVec 8)), (0x9D : (BitVec 8)), (0x8D : (BitVec 8)), (0xA7 : (BitVec 8)), (0x57 : (BitVec 8)), (0x46 : (BitVec 8)), (0x15 : (BitVec 8)), (0x5E : (BitVec 8)), (0xDA : (BitVec 8)), (0xB9 : (BitVec 8)), (0xED : (BitVec 8)), (0xFD : (BitVec 8)), (0x50 : (BitVec 8)), (0x48 : (BitVec 8)), (0x70 : (BitVec 8)), (0x6C : (BitVec 8)), (0x92 : (BitVec 8)), (0xB6 : (BitVec 8)), (0x65 : (BitVec 8)), (0x5D : (BitVec 8)), (0xCC : (BitVec 8)), (0x5C : (BitVec 8)), (0xA4 : (BitVec 8)), (0xD4 : (BitVec 8)), (0x16 : (BitVec 8)), (0x98 : (BitVec 8)), (0x68 : (BitVec 8)), (0x86 : (BitVec 8)), (0x64 : (BitVec 8)), (0xF6 : (BitVec 8)), (0xF8 : (BitVec 8)), (0x72 : (BitVec 8)), (0x25 : (BitVec 8)), (0xD1 : (BitVec 8)), (0x8B : (BitVec 8)), (0x6D : (BitVec 8)), (0x49 : (BitVec 8)), (0xA2 : (BitVec 8)), (0x5B : (BitVec 8)), (0x76 : (BitVec 8)), (0xB2 : (BitVec 8)), (0x24 : (BitVec 8)), (0xD9 : (BitVec 8)), (0x28 : (BitVec 8)), (0x66 : (BitVec 8)), (0xA1 : (BitVec 8)), (0x2E : (BitVec 8)), (0x08 : (BitVec 8)), (0x4E : (BitVec 8)), (0xC3 : (BitVec 8)), (0xFA : (BitVec 8)), (0x42 : (BitVec 8)), (0x0B : (BitVec 8)), (0x95 : (BitVec 8)), (0x4C : (BitVec 8)), (0xEE : (BitVec 8)), (0x3D : (BitVec 8)), (0x23 : (BitVec 8)), (0xC2 : (BitVec 8)), (0xA6 : (BitVec 8)), (0x32 : (BitVec 8)), (0x94 : (BitVec 8)), (0x7B : (BitVec 8)), (0x54 : (BitVec 8)), (0xCB : (BitVec 8)), (0xE9 : (BitVec 8)), (0xDE : (BitVec 8)), (0xC4 : (BitVec 8)), (0x44 : (BitVec 8)), (0x43 : (BitVec 8)), (0x8E : (BitVec 8)), (0x34 : (BitVec 8)), (0x87 : (BitVec 8)), (0xFF : (BitVec 8)), (0x2F : (BitVec 8)), (0x9B : (BitVec 8)), (0x82 : (BitVec 8)), (0x39 : (BitVec 8)), (0xE3 : (BitVec 8)), (0x7C : (BitVec 8)), (0xFB : (BitVec 8)), (0xD7 : (BitVec 8)), (0xF3 : (BitVec 8)), (0x81 : (BitVec 8)), (0x9E : (BitVec 8)), (0xA3 : (BitVec 8)), (0x40 : (BitVec 8)), (0xBF : (BitVec 8)), (0x38 : (BitVec 8)), (0xA5 : (BitVec 8)), (0x36 : (BitVec 8)), (0x30 : (BitVec 8)), (0xD5 : (BitVec 8)), (0x6A : (BitVec 8)), (0x09 : (BitVec 8)), (0x52 : (BitVec 8))]

def sbox_lookup (x : (BitVec 8)) (table : (Vector (BitVec 8) 256)) : (BitVec 8) :=
  (GetElem?.getElem! table (255 -i (BitVec.toNat x)))

def aes_sbox_fwd (x : (BitVec 8)) : (BitVec 8) :=
  (sbox_lookup x aes_sbox_fwd_table)

def aes_sbox_inv (x : (BitVec 8)) : (BitVec 8) :=
  (sbox_lookup x aes_sbox_inv_table)

def aes_subword_fwd (x : (BitVec 32)) : (BitVec 32) :=
  ((aes_sbox_fwd (Sail.BitVec.extractLsb x 31 24)) ++ ((aes_sbox_fwd
        (Sail.BitVec.extractLsb x 23 16)) ++ ((aes_sbox_fwd (Sail.BitVec.extractLsb x 15 8)) ++ (aes_sbox_fwd
          (Sail.BitVec.extractLsb x 7 0)))))

def aes_subword_inv (x : (BitVec 32)) : (BitVec 32) :=
  ((aes_sbox_inv (Sail.BitVec.extractLsb x 31 24)) ++ ((aes_sbox_inv
        (Sail.BitVec.extractLsb x 23 16)) ++ ((aes_sbox_inv (Sail.BitVec.extractLsb x 15 8)) ++ (aes_sbox_inv
          (Sail.BitVec.extractLsb x 7 0)))))

def sm4_sbox (x : (BitVec 8)) : (BitVec 8) :=
  (sbox_lookup x sm4_sbox_table)

/-- Type quantifiers: c : Nat, 0 ≤ c ∧ c ≤ 3 -/
def aes_get_column (state : (BitVec 128)) (c : Nat) : (BitVec 32) :=
  (Sail.BitVec.extractLsb state ((32 *i c) +i 31) (32 *i c))

def aes_apply_fwd_sbox_to_each_byte (x : (BitVec 64)) : (BitVec 64) :=
  ((aes_sbox_fwd (Sail.BitVec.extractLsb x 63 56)) ++ ((aes_sbox_fwd
        (Sail.BitVec.extractLsb x 55 48)) ++ ((aes_sbox_fwd (Sail.BitVec.extractLsb x 47 40)) ++ ((aes_sbox_fwd
            (Sail.BitVec.extractLsb x 39 32)) ++ ((aes_sbox_fwd (Sail.BitVec.extractLsb x 31 24)) ++ ((aes_sbox_fwd
                (Sail.BitVec.extractLsb x 23 16)) ++ ((aes_sbox_fwd (Sail.BitVec.extractLsb x 15 8)) ++ (aes_sbox_fwd
                  (Sail.BitVec.extractLsb x 7 0)))))))))

def aes_apply_inv_sbox_to_each_byte (x : (BitVec 64)) : (BitVec 64) :=
  ((aes_sbox_inv (Sail.BitVec.extractLsb x 63 56)) ++ ((aes_sbox_inv
        (Sail.BitVec.extractLsb x 55 48)) ++ ((aes_sbox_inv (Sail.BitVec.extractLsb x 47 40)) ++ ((aes_sbox_inv
            (Sail.BitVec.extractLsb x 39 32)) ++ ((aes_sbox_inv (Sail.BitVec.extractLsb x 31 24)) ++ ((aes_sbox_inv
                (Sail.BitVec.extractLsb x 23 16)) ++ ((aes_sbox_inv (Sail.BitVec.extractLsb x 15 8)) ++ (aes_sbox_inv
                  (Sail.BitVec.extractLsb x 7 0)))))))))

/-- Type quantifiers: i : Nat, 0 ≤ i ∧ i ≤ 7 -/
def getbyte (x : (BitVec 64)) (i : Nat) : (BitVec 8) :=
  (Sail.BitVec.extractLsb x ((8 *i i) +i 7) (8 *i i))

def aes_rv64_shiftrows_fwd (rs2 : (BitVec 64)) (rs1 : (BitVec 64)) : (BitVec 64) :=
  ((getbyte rs1 3) ++ ((getbyte rs2 6) ++ ((getbyte rs2 1) ++ ((getbyte rs1 4) ++ ((getbyte rs2 7) ++ ((getbyte
                rs2 2) ++ ((getbyte rs1 5) ++ (getbyte rs1 0))))))))

def aes_rv64_shiftrows_inv (rs2 : (BitVec 64)) (rs1 : (BitVec 64)) : (BitVec 64) :=
  ((getbyte rs2 3) ++ ((getbyte rs2 6) ++ ((getbyte rs1 1) ++ ((getbyte rs1 4) ++ ((getbyte rs1 7) ++ ((getbyte
                rs2 2) ++ ((getbyte rs2 5) ++ (getbyte rs1 0))))))))

def aes_shift_rows_fwd (x : (BitVec 128)) : (BitVec 128) :=
  let ic3 : (BitVec 32) := (aes_get_column x 3)
  let ic2 : (BitVec 32) := (aes_get_column x 2)
  let ic1 : (BitVec 32) := (aes_get_column x 1)
  let ic0 : (BitVec 32) := (aes_get_column x 0)
  let oc0 : (BitVec 32) :=
    ((Sail.BitVec.extractLsb ic3 31 24) ++ ((Sail.BitVec.extractLsb ic2 23 16) ++ ((Sail.BitVec.extractLsb
            ic1 15 8) ++ (Sail.BitVec.extractLsb ic0 7 0))))
  let oc1 : (BitVec 32) :=
    ((Sail.BitVec.extractLsb ic0 31 24) ++ ((Sail.BitVec.extractLsb ic3 23 16) ++ ((Sail.BitVec.extractLsb
            ic2 15 8) ++ (Sail.BitVec.extractLsb ic1 7 0))))
  let oc2 : (BitVec 32) :=
    ((Sail.BitVec.extractLsb ic1 31 24) ++ ((Sail.BitVec.extractLsb ic0 23 16) ++ ((Sail.BitVec.extractLsb
            ic3 15 8) ++ (Sail.BitVec.extractLsb ic2 7 0))))
  let oc3 : (BitVec 32) :=
    ((Sail.BitVec.extractLsb ic2 31 24) ++ ((Sail.BitVec.extractLsb ic1 23 16) ++ ((Sail.BitVec.extractLsb
            ic0 15 8) ++ (Sail.BitVec.extractLsb ic3 7 0))))
  (oc3 ++ (oc2 ++ (oc1 ++ oc0)))

def aes_shift_rows_inv (x : (BitVec 128)) : (BitVec 128) :=
  let ic3 : (BitVec 32) := (aes_get_column x 3)
  let ic2 : (BitVec 32) := (aes_get_column x 2)
  let ic1 : (BitVec 32) := (aes_get_column x 1)
  let ic0 : (BitVec 32) := (aes_get_column x 0)
  let oc0 : (BitVec 32) :=
    ((Sail.BitVec.extractLsb ic1 31 24) ++ ((Sail.BitVec.extractLsb ic2 23 16) ++ ((Sail.BitVec.extractLsb
            ic3 15 8) ++ (Sail.BitVec.extractLsb ic0 7 0))))
  let oc1 : (BitVec 32) :=
    ((Sail.BitVec.extractLsb ic2 31 24) ++ ((Sail.BitVec.extractLsb ic3 23 16) ++ ((Sail.BitVec.extractLsb
            ic0 15 8) ++ (Sail.BitVec.extractLsb ic1 7 0))))
  let oc2 : (BitVec 32) :=
    ((Sail.BitVec.extractLsb ic3 31 24) ++ ((Sail.BitVec.extractLsb ic0 23 16) ++ ((Sail.BitVec.extractLsb
            ic1 15 8) ++ (Sail.BitVec.extractLsb ic2 7 0))))
  let oc3 : (BitVec 32) :=
    ((Sail.BitVec.extractLsb ic0 31 24) ++ ((Sail.BitVec.extractLsb ic1 23 16) ++ ((Sail.BitVec.extractLsb
            ic2 15 8) ++ (Sail.BitVec.extractLsb ic3 7 0))))
  (oc3 ++ (oc2 ++ (oc1 ++ oc0)))

def aes_subbytes_fwd (x : (BitVec 128)) : (BitVec 128) :=
  let oc0 : (BitVec 32) := (aes_subword_fwd (aes_get_column x 0))
  let oc1 : (BitVec 32) := (aes_subword_fwd (aes_get_column x 1))
  let oc2 : (BitVec 32) := (aes_subword_fwd (aes_get_column x 2))
  let oc3 : (BitVec 32) := (aes_subword_fwd (aes_get_column x 3))
  (oc3 ++ (oc2 ++ (oc1 ++ oc0)))

def aes_subbytes_inv (x : (BitVec 128)) : (BitVec 128) :=
  let oc0 : (BitVec 32) := (aes_subword_inv (aes_get_column x 0))
  let oc1 : (BitVec 32) := (aes_subword_inv (aes_get_column x 1))
  let oc2 : (BitVec 32) := (aes_subword_inv (aes_get_column x 2))
  let oc3 : (BitVec 32) := (aes_subword_inv (aes_get_column x 3))
  (oc3 ++ (oc2 ++ (oc1 ++ oc0)))

def aes_mixcolumns_fwd (x : (BitVec 128)) : SailM (BitVec 128) := do
  let oc0 ← (( do (aes_mixcolumn_fwd (aes_get_column x 0)) ) : SailM (BitVec 32) )
  let oc1 ← (( do (aes_mixcolumn_fwd (aes_get_column x 1)) ) : SailM (BitVec 32) )
  let oc2 ← (( do (aes_mixcolumn_fwd (aes_get_column x 2)) ) : SailM (BitVec 32) )
  let oc3 ← (( do (aes_mixcolumn_fwd (aes_get_column x 3)) ) : SailM (BitVec 32) )
  (pure (oc3 ++ (oc2 ++ (oc1 ++ oc0))))

def aes_mixcolumns_inv (x : (BitVec 128)) : SailM (BitVec 128) := do
  let oc0 ← (( do (aes_mixcolumn_inv (aes_get_column x 0)) ) : SailM (BitVec 32) )
  let oc1 ← (( do (aes_mixcolumn_inv (aes_get_column x 1)) ) : SailM (BitVec 32) )
  let oc2 ← (( do (aes_mixcolumn_inv (aes_get_column x 2)) ) : SailM (BitVec 32) )
  let oc3 ← (( do (aes_mixcolumn_inv (aes_get_column x 3)) ) : SailM (BitVec 32) )
  (pure (oc3 ++ (oc2 ++ (oc1 ++ oc0))))


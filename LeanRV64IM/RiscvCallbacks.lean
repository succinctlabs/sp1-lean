import LeanRV64IM.RiscvXlen
import LeanRV64IM.RiscvTypes

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

namespace LeanRV64IM.Functions

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
open extop_zbb
open extension
open exception
open ctl_result
open csrop
open cregidx
open cbop_zicbom
open bropw_zbb
open bropw_zba
open brop_zbs
open brop_zbkb
open brop_zbb
open brop_zba
open bop
open biop_zbs
open barrier_kind
open amoop
open agtype
open WaitReason
open TrapVectorMode
open SATPMode
open Register
open Privilege
open PmpAddrMatchType
open PTW_Error
open PTE_Check
open InterruptType
open Ext_PhysAddr_Check
open Ext_FetchAddr_Check
open Ext_DataAddr_Check
open Ext_ControlAddr_Check
open ExtStatus
open ExecutionResult
open ExceptionType
open Architecture
open AccessType

/-- Type quantifiers: x_2 : Nat, 0 < x_2 ∧ x_2 ≤ max_mem_access -/
def mem_write_callback (x_0 : String) (x_1 : (BitVec (if ( 64 = 32  : Bool) then 34 else 64))) (x_2 : Nat) (x_3 : (BitVec (8 * x_2))) : Unit :=
  ()

/-- Type quantifiers: x_2 : Nat, 0 < x_2 ∧ x_2 ≤ max_mem_access -/
def mem_read_callback (x_0 : String) (x_1 : (BitVec (if ( 64 = 32  : Bool) then 34 else 64))) (x_2 : Nat) (x_3 : (BitVec (8 * x_2))) : Unit :=
  ()

/-- Type quantifiers: x_1 : Nat, 0 ≤ x_1 ∧ x_1 < xlen -/
def mem_exception_callback (x_0 : (BitVec (if ( 64 = 32  : Bool) then 34 else 64))) (x_1 : Nat) : Unit :=
  ()

def pc_write_callback (x_0 : (BitVec 64)) : Unit :=
  ()

def xreg_full_write_callback (x_0 : String) (x_1 : regidx) (x_2 : (BitVec 64)) : Unit :=
  ()

def csr_full_write_callback (x_0 : String) (x_1 : (BitVec 12)) (x_2 : (BitVec 64)) : Unit :=
  ()

def csr_full_read_callback (x_0 : String) (x_1 : (BitVec 12)) (x_2 : (BitVec 64)) : Unit :=
  ()

def trap_callback (x_0 : Unit) : Unit :=
  ()

def csr_name_map_backwards (arg_ : String) : SailM (BitVec 12) := do
  match arg_ with
  | "misa" => (pure (0x301 : (BitVec 12)))
  | "mstatus" => (pure (0x300 : (BitVec 12)))
  | "mstatush" => (pure (0x310 : (BitVec 12)))
  | "mseccfg" => (pure (0x747 : (BitVec 12)))
  | "mseccfgh" => (pure (0x757 : (BitVec 12)))
  | "menvcfg" => (pure (0x30A : (BitVec 12)))
  | "menvcfgh" => (pure (0x31A : (BitVec 12)))
  | "senvcfg" => (pure (0x10A : (BitVec 12)))
  | "mie" => (pure (0x304 : (BitVec 12)))
  | "mip" => (pure (0x344 : (BitVec 12)))
  | "medeleg" => (pure (0x302 : (BitVec 12)))
  | "medelegh" => (pure (0x312 : (BitVec 12)))
  | "mideleg" => (pure (0x303 : (BitVec 12)))
  | "mcause" => (pure (0x342 : (BitVec 12)))
  | "mtval" => (pure (0x343 : (BitVec 12)))
  | "mscratch" => (pure (0x340 : (BitVec 12)))
  | "scounteren" => (pure (0x106 : (BitVec 12)))
  | "mcounteren" => (pure (0x306 : (BitVec 12)))
  | "mcountinhibit" => (pure (0x320 : (BitVec 12)))
  | "mvendorid" => (pure (0xF11 : (BitVec 12)))
  | "marchid" => (pure (0xF12 : (BitVec 12)))
  | "mimpid" => (pure (0xF13 : (BitVec 12)))
  | "mhartid" => (pure (0xF14 : (BitVec 12)))
  | "mconfigptr" => (pure (0xF15 : (BitVec 12)))
  | "sstatus" => (pure (0x100 : (BitVec 12)))
  | "sip" => (pure (0x144 : (BitVec 12)))
  | "sie" => (pure (0x104 : (BitVec 12)))
  | "sscratch" => (pure (0x140 : (BitVec 12)))
  | "scause" => (pure (0x142 : (BitVec 12)))
  | "stval" => (pure (0x143 : (BitVec 12)))
  | "tselect" => (pure (0x7A0 : (BitVec 12)))
  | "tdata1" => (pure (0x7A1 : (BitVec 12)))
  | "tdata2" => (pure (0x7A2 : (BitVec 12)))
  | "tdata3" => (pure (0x7A3 : (BitVec 12)))
  | "stvec" => (pure (0x105 : (BitVec 12)))
  | "sepc" => (pure (0x141 : (BitVec 12)))
  | "mtvec" => (pure (0x305 : (BitVec 12)))
  | "mepc" => (pure (0x341 : (BitVec 12)))
  | "pmpcfg0" => (pure (0x3A0 : (BitVec 12)))
  | "pmpcfg1" => (pure (0x3A1 : (BitVec 12)))
  | "pmpcfg2" => (pure (0x3A2 : (BitVec 12)))
  | "pmpcfg3" => (pure (0x3A3 : (BitVec 12)))
  | "pmpcfg4" => (pure (0x3A4 : (BitVec 12)))
  | "pmpcfg5" => (pure (0x3A5 : (BitVec 12)))
  | "pmpcfg6" => (pure (0x3A6 : (BitVec 12)))
  | "pmpcfg7" => (pure (0x3A7 : (BitVec 12)))
  | "pmpcfg8" => (pure (0x3A8 : (BitVec 12)))
  | "pmpcfg9" => (pure (0x3A9 : (BitVec 12)))
  | "pmpcfg10" => (pure (0x3AA : (BitVec 12)))
  | "pmpcfg11" => (pure (0x3AB : (BitVec 12)))
  | "pmpcfg12" => (pure (0x3AC : (BitVec 12)))
  | "pmpcfg13" => (pure (0x3AD : (BitVec 12)))
  | "pmpcfg14" => (pure (0x3AE : (BitVec 12)))
  | "pmpcfg15" => (pure (0x3AF : (BitVec 12)))
  | "pmpaddr0" => (pure (0x3B0 : (BitVec 12)))
  | "pmpaddr1" => (pure (0x3B1 : (BitVec 12)))
  | "pmpaddr2" => (pure (0x3B2 : (BitVec 12)))
  | "pmpaddr3" => (pure (0x3B3 : (BitVec 12)))
  | "pmpaddr4" => (pure (0x3B4 : (BitVec 12)))
  | "pmpaddr5" => (pure (0x3B5 : (BitVec 12)))
  | "pmpaddr6" => (pure (0x3B6 : (BitVec 12)))
  | "pmpaddr7" => (pure (0x3B7 : (BitVec 12)))
  | "pmpaddr8" => (pure (0x3B8 : (BitVec 12)))
  | "pmpaddr9" => (pure (0x3B9 : (BitVec 12)))
  | "pmpaddr10" => (pure (0x3BA : (BitVec 12)))
  | "pmpaddr11" => (pure (0x3BB : (BitVec 12)))
  | "pmpaddr12" => (pure (0x3BC : (BitVec 12)))
  | "pmpaddr13" => (pure (0x3BD : (BitVec 12)))
  | "pmpaddr14" => (pure (0x3BE : (BitVec 12)))
  | "pmpaddr15" => (pure (0x3BF : (BitVec 12)))
  | "pmpaddr16" => (pure (0x3C0 : (BitVec 12)))
  | "pmpaddr17" => (pure (0x3C1 : (BitVec 12)))
  | "pmpaddr18" => (pure (0x3C2 : (BitVec 12)))
  | "pmpaddr19" => (pure (0x3C3 : (BitVec 12)))
  | "pmpaddr20" => (pure (0x3C4 : (BitVec 12)))
  | "pmpaddr21" => (pure (0x3C5 : (BitVec 12)))
  | "pmpaddr22" => (pure (0x3C6 : (BitVec 12)))
  | "pmpaddr23" => (pure (0x3C7 : (BitVec 12)))
  | "pmpaddr24" => (pure (0x3C8 : (BitVec 12)))
  | "pmpaddr25" => (pure (0x3C9 : (BitVec 12)))
  | "pmpaddr26" => (pure (0x3CA : (BitVec 12)))
  | "pmpaddr27" => (pure (0x3CB : (BitVec 12)))
  | "pmpaddr28" => (pure (0x3CC : (BitVec 12)))
  | "pmpaddr29" => (pure (0x3CD : (BitVec 12)))
  | "pmpaddr30" => (pure (0x3CE : (BitVec 12)))
  | "pmpaddr31" => (pure (0x3CF : (BitVec 12)))
  | "pmpaddr32" => (pure (0x3D0 : (BitVec 12)))
  | "pmpaddr33" => (pure (0x3D1 : (BitVec 12)))
  | "pmpaddr34" => (pure (0x3D2 : (BitVec 12)))
  | "pmpaddr35" => (pure (0x3D3 : (BitVec 12)))
  | "pmpaddr36" => (pure (0x3D4 : (BitVec 12)))
  | "pmpaddr37" => (pure (0x3D5 : (BitVec 12)))
  | "pmpaddr38" => (pure (0x3D6 : (BitVec 12)))
  | "pmpaddr39" => (pure (0x3D7 : (BitVec 12)))
  | "pmpaddr40" => (pure (0x3D8 : (BitVec 12)))
  | "pmpaddr41" => (pure (0x3D9 : (BitVec 12)))
  | "pmpaddr42" => (pure (0x3DA : (BitVec 12)))
  | "pmpaddr43" => (pure (0x3DB : (BitVec 12)))
  | "pmpaddr44" => (pure (0x3DC : (BitVec 12)))
  | "pmpaddr45" => (pure (0x3DD : (BitVec 12)))
  | "pmpaddr46" => (pure (0x3DE : (BitVec 12)))
  | "pmpaddr47" => (pure (0x3DF : (BitVec 12)))
  | "pmpaddr48" => (pure (0x3E0 : (BitVec 12)))
  | "pmpaddr49" => (pure (0x3E1 : (BitVec 12)))
  | "pmpaddr50" => (pure (0x3E2 : (BitVec 12)))
  | "pmpaddr51" => (pure (0x3E3 : (BitVec 12)))
  | "pmpaddr52" => (pure (0x3E4 : (BitVec 12)))
  | "pmpaddr53" => (pure (0x3E5 : (BitVec 12)))
  | "pmpaddr54" => (pure (0x3E6 : (BitVec 12)))
  | "pmpaddr55" => (pure (0x3E7 : (BitVec 12)))
  | "pmpaddr56" => (pure (0x3E8 : (BitVec 12)))
  | "pmpaddr57" => (pure (0x3E9 : (BitVec 12)))
  | "pmpaddr58" => (pure (0x3EA : (BitVec 12)))
  | "pmpaddr59" => (pure (0x3EB : (BitVec 12)))
  | "pmpaddr60" => (pure (0x3EC : (BitVec 12)))
  | "pmpaddr61" => (pure (0x3ED : (BitVec 12)))
  | "pmpaddr62" => (pure (0x3EE : (BitVec 12)))
  | "pmpaddr63" => (pure (0x3EF : (BitVec 12)))
  | "vstart" => (pure (0x008 : (BitVec 12)))
  | "vxsat" => (pure (0x009 : (BitVec 12)))
  | "vxrm" => (pure (0x00A : (BitVec 12)))
  | "vcsr" => (pure (0x00F : (BitVec 12)))
  | "vl" => (pure (0xC20 : (BitVec 12)))
  | "vtype" => (pure (0xC21 : (BitVec 12)))
  | "vlenb" => (pure (0xC22 : (BitVec 12)))
  | "hpmcounter3" => (pure (0xC03 : (BitVec 12)))
  | "hpmcounter4" => (pure (0xC04 : (BitVec 12)))
  | "hpmcounter5" => (pure (0xC05 : (BitVec 12)))
  | "hpmcounter6" => (pure (0xC06 : (BitVec 12)))
  | "hpmcounter7" => (pure (0xC07 : (BitVec 12)))
  | "hpmcounter8" => (pure (0xC08 : (BitVec 12)))
  | "hpmcounter9" => (pure (0xC09 : (BitVec 12)))
  | "hpmcounter10" => (pure (0xC0A : (BitVec 12)))
  | "hpmcounter11" => (pure (0xC0B : (BitVec 12)))
  | "hpmcounter12" => (pure (0xC0C : (BitVec 12)))
  | "hpmcounter13" => (pure (0xC0D : (BitVec 12)))
  | "hpmcounter14" => (pure (0xC0E : (BitVec 12)))
  | "hpmcounter15" => (pure (0xC0F : (BitVec 12)))
  | "hpmcounter16" => (pure (0xC10 : (BitVec 12)))
  | "hpmcounter17" => (pure (0xC11 : (BitVec 12)))
  | "hpmcounter18" => (pure (0xC12 : (BitVec 12)))
  | "hpmcounter19" => (pure (0xC13 : (BitVec 12)))
  | "hpmcounter20" => (pure (0xC14 : (BitVec 12)))
  | "hpmcounter21" => (pure (0xC15 : (BitVec 12)))
  | "hpmcounter22" => (pure (0xC16 : (BitVec 12)))
  | "hpmcounter23" => (pure (0xC17 : (BitVec 12)))
  | "hpmcounter24" => (pure (0xC18 : (BitVec 12)))
  | "hpmcounter25" => (pure (0xC19 : (BitVec 12)))
  | "hpmcounter26" => (pure (0xC1A : (BitVec 12)))
  | "hpmcounter27" => (pure (0xC1B : (BitVec 12)))
  | "hpmcounter28" => (pure (0xC1C : (BitVec 12)))
  | "hpmcounter29" => (pure (0xC1D : (BitVec 12)))
  | "hpmcounter30" => (pure (0xC1E : (BitVec 12)))
  | "hpmcounter31" => (pure (0xC1F : (BitVec 12)))
  | "hpmcounter3h" => (pure (0xC83 : (BitVec 12)))
  | "hpmcounter4h" => (pure (0xC84 : (BitVec 12)))
  | "hpmcounter5h" => (pure (0xC85 : (BitVec 12)))
  | "hpmcounter6h" => (pure (0xC86 : (BitVec 12)))
  | "hpmcounter7h" => (pure (0xC87 : (BitVec 12)))
  | "hpmcounter8h" => (pure (0xC88 : (BitVec 12)))
  | "hpmcounter9h" => (pure (0xC89 : (BitVec 12)))
  | "hpmcounter10h" => (pure (0xC8A : (BitVec 12)))
  | "hpmcounter11h" => (pure (0xC8B : (BitVec 12)))
  | "hpmcounter12h" => (pure (0xC8C : (BitVec 12)))
  | "hpmcounter13h" => (pure (0xC8D : (BitVec 12)))
  | "hpmcounter14h" => (pure (0xC8E : (BitVec 12)))
  | "hpmcounter15h" => (pure (0xC8F : (BitVec 12)))
  | "hpmcounter16h" => (pure (0xC90 : (BitVec 12)))
  | "hpmcounter17h" => (pure (0xC91 : (BitVec 12)))
  | "hpmcounter18h" => (pure (0xC92 : (BitVec 12)))
  | "hpmcounter19h" => (pure (0xC93 : (BitVec 12)))
  | "hpmcounter20h" => (pure (0xC94 : (BitVec 12)))
  | "hpmcounter21h" => (pure (0xC95 : (BitVec 12)))
  | "hpmcounter22h" => (pure (0xC96 : (BitVec 12)))
  | "hpmcounter23h" => (pure (0xC97 : (BitVec 12)))
  | "hpmcounter24h" => (pure (0xC98 : (BitVec 12)))
  | "hpmcounter25h" => (pure (0xC99 : (BitVec 12)))
  | "hpmcounter26h" => (pure (0xC9A : (BitVec 12)))
  | "hpmcounter27h" => (pure (0xC9B : (BitVec 12)))
  | "hpmcounter28h" => (pure (0xC9C : (BitVec 12)))
  | "hpmcounter29h" => (pure (0xC9D : (BitVec 12)))
  | "hpmcounter30h" => (pure (0xC9E : (BitVec 12)))
  | "hpmcounter31h" => (pure (0xC9F : (BitVec 12)))
  | "mhpmevent3" => (pure (0x323 : (BitVec 12)))
  | "mhpmevent4" => (pure (0x324 : (BitVec 12)))
  | "mhpmevent5" => (pure (0x325 : (BitVec 12)))
  | "mhpmevent6" => (pure (0x326 : (BitVec 12)))
  | "mhpmevent7" => (pure (0x327 : (BitVec 12)))
  | "mhpmevent8" => (pure (0x328 : (BitVec 12)))
  | "mhpmevent9" => (pure (0x329 : (BitVec 12)))
  | "mhpmevent10" => (pure (0x32A : (BitVec 12)))
  | "mhpmevent11" => (pure (0x32B : (BitVec 12)))
  | "mhpmevent12" => (pure (0x32C : (BitVec 12)))
  | "mhpmevent13" => (pure (0x32D : (BitVec 12)))
  | "mhpmevent14" => (pure (0x32E : (BitVec 12)))
  | "mhpmevent15" => (pure (0x32F : (BitVec 12)))
  | "mhpmevent16" => (pure (0x330 : (BitVec 12)))
  | "mhpmevent17" => (pure (0x331 : (BitVec 12)))
  | "mhpmevent18" => (pure (0x332 : (BitVec 12)))
  | "mhpmevent19" => (pure (0x333 : (BitVec 12)))
  | "mhpmevent20" => (pure (0x334 : (BitVec 12)))
  | "mhpmevent21" => (pure (0x335 : (BitVec 12)))
  | "mhpmevent22" => (pure (0x336 : (BitVec 12)))
  | "mhpmevent23" => (pure (0x337 : (BitVec 12)))
  | "mhpmevent24" => (pure (0x338 : (BitVec 12)))
  | "mhpmevent25" => (pure (0x339 : (BitVec 12)))
  | "mhpmevent26" => (pure (0x33A : (BitVec 12)))
  | "mhpmevent27" => (pure (0x33B : (BitVec 12)))
  | "mhpmevent28" => (pure (0x33C : (BitVec 12)))
  | "mhpmevent29" => (pure (0x33D : (BitVec 12)))
  | "mhpmevent30" => (pure (0x33E : (BitVec 12)))
  | "mhpmevent31" => (pure (0x33F : (BitVec 12)))
  | "mhpmcounter3" => (pure (0xB03 : (BitVec 12)))
  | "mhpmcounter4" => (pure (0xB04 : (BitVec 12)))
  | "mhpmcounter5" => (pure (0xB05 : (BitVec 12)))
  | "mhpmcounter6" => (pure (0xB06 : (BitVec 12)))
  | "mhpmcounter7" => (pure (0xB07 : (BitVec 12)))
  | "mhpmcounter8" => (pure (0xB08 : (BitVec 12)))
  | "mhpmcounter9" => (pure (0xB09 : (BitVec 12)))
  | "mhpmcounter10" => (pure (0xB0A : (BitVec 12)))
  | "mhpmcounter11" => (pure (0xB0B : (BitVec 12)))
  | "mhpmcounter12" => (pure (0xB0C : (BitVec 12)))
  | "mhpmcounter13" => (pure (0xB0D : (BitVec 12)))
  | "mhpmcounter14" => (pure (0xB0E : (BitVec 12)))
  | "mhpmcounter15" => (pure (0xB0F : (BitVec 12)))
  | "mhpmcounter16" => (pure (0xB10 : (BitVec 12)))
  | "mhpmcounter17" => (pure (0xB11 : (BitVec 12)))
  | "mhpmcounter18" => (pure (0xB12 : (BitVec 12)))
  | "mhpmcounter19" => (pure (0xB13 : (BitVec 12)))
  | "mhpmcounter20" => (pure (0xB14 : (BitVec 12)))
  | "mhpmcounter21" => (pure (0xB15 : (BitVec 12)))
  | "mhpmcounter22" => (pure (0xB16 : (BitVec 12)))
  | "mhpmcounter23" => (pure (0xB17 : (BitVec 12)))
  | "mhpmcounter24" => (pure (0xB18 : (BitVec 12)))
  | "mhpmcounter25" => (pure (0xB19 : (BitVec 12)))
  | "mhpmcounter26" => (pure (0xB1A : (BitVec 12)))
  | "mhpmcounter27" => (pure (0xB1B : (BitVec 12)))
  | "mhpmcounter28" => (pure (0xB1C : (BitVec 12)))
  | "mhpmcounter29" => (pure (0xB1D : (BitVec 12)))
  | "mhpmcounter30" => (pure (0xB1E : (BitVec 12)))
  | "mhpmcounter31" => (pure (0xB1F : (BitVec 12)))
  | "mhpmcounter3h" => (pure (0xB83 : (BitVec 12)))
  | "mhpmcounter4h" => (pure (0xB84 : (BitVec 12)))
  | "mhpmcounter5h" => (pure (0xB85 : (BitVec 12)))
  | "mhpmcounter6h" => (pure (0xB86 : (BitVec 12)))
  | "mhpmcounter7h" => (pure (0xB87 : (BitVec 12)))
  | "mhpmcounter8h" => (pure (0xB88 : (BitVec 12)))
  | "mhpmcounter9h" => (pure (0xB89 : (BitVec 12)))
  | "mhpmcounter10h" => (pure (0xB8A : (BitVec 12)))
  | "mhpmcounter11h" => (pure (0xB8B : (BitVec 12)))
  | "mhpmcounter12h" => (pure (0xB8C : (BitVec 12)))
  | "mhpmcounter13h" => (pure (0xB8D : (BitVec 12)))
  | "mhpmcounter14h" => (pure (0xB8E : (BitVec 12)))
  | "mhpmcounter15h" => (pure (0xB8F : (BitVec 12)))
  | "mhpmcounter16h" => (pure (0xB90 : (BitVec 12)))
  | "mhpmcounter17h" => (pure (0xB91 : (BitVec 12)))
  | "mhpmcounter18h" => (pure (0xB92 : (BitVec 12)))
  | "mhpmcounter19h" => (pure (0xB93 : (BitVec 12)))
  | "mhpmcounter20h" => (pure (0xB94 : (BitVec 12)))
  | "mhpmcounter21h" => (pure (0xB95 : (BitVec 12)))
  | "mhpmcounter22h" => (pure (0xB96 : (BitVec 12)))
  | "mhpmcounter23h" => (pure (0xB97 : (BitVec 12)))
  | "mhpmcounter24h" => (pure (0xB98 : (BitVec 12)))
  | "mhpmcounter25h" => (pure (0xB99 : (BitVec 12)))
  | "mhpmcounter26h" => (pure (0xB9A : (BitVec 12)))
  | "mhpmcounter27h" => (pure (0xB9B : (BitVec 12)))
  | "mhpmcounter28h" => (pure (0xB9C : (BitVec 12)))
  | "mhpmcounter29h" => (pure (0xB9D : (BitVec 12)))
  | "mhpmcounter30h" => (pure (0xB9E : (BitVec 12)))
  | "mhpmcounter31h" => (pure (0xB9F : (BitVec 12)))
  | "mhpmcounter3h" => (pure (0xB83 : (BitVec 12)))
  | "mhpmcounter4h" => (pure (0xB84 : (BitVec 12)))
  | "mhpmcounter5h" => (pure (0xB85 : (BitVec 12)))
  | "mhpmcounter6h" => (pure (0xB86 : (BitVec 12)))
  | "mhpmcounter7h" => (pure (0xB87 : (BitVec 12)))
  | "mhpmcounter8h" => (pure (0xB88 : (BitVec 12)))
  | "mhpmcounter9h" => (pure (0xB89 : (BitVec 12)))
  | "mhpmcounter10h" => (pure (0xB8A : (BitVec 12)))
  | "mhpmcounter11h" => (pure (0xB8B : (BitVec 12)))
  | "mhpmcounter12h" => (pure (0xB8C : (BitVec 12)))
  | "mhpmcounter13h" => (pure (0xB8D : (BitVec 12)))
  | "mhpmcounter14h" => (pure (0xB8E : (BitVec 12)))
  | "mhpmcounter15h" => (pure (0xB8F : (BitVec 12)))
  | "mhpmcounter16h" => (pure (0xB90 : (BitVec 12)))
  | "mhpmcounter17h" => (pure (0xB91 : (BitVec 12)))
  | "mhpmcounter18h" => (pure (0xB92 : (BitVec 12)))
  | "mhpmcounter19h" => (pure (0xB93 : (BitVec 12)))
  | "mhpmcounter20h" => (pure (0xB94 : (BitVec 12)))
  | "mhpmcounter21h" => (pure (0xB95 : (BitVec 12)))
  | "mhpmcounter22h" => (pure (0xB96 : (BitVec 12)))
  | "mhpmcounter23h" => (pure (0xB97 : (BitVec 12)))
  | "mhpmcounter24h" => (pure (0xB98 : (BitVec 12)))
  | "mhpmcounter25h" => (pure (0xB99 : (BitVec 12)))
  | "mhpmcounter26h" => (pure (0xB9A : (BitVec 12)))
  | "mhpmcounter27h" => (pure (0xB9B : (BitVec 12)))
  | "mhpmcounter28h" => (pure (0xB9C : (BitVec 12)))
  | "mhpmcounter29h" => (pure (0xB9D : (BitVec 12)))
  | "mhpmcounter30h" => (pure (0xB9E : (BitVec 12)))
  | "mhpmcounter31h" => (pure (0xB9F : (BitVec 12)))
  | "scountovf" => (pure (0xDA0 : (BitVec 12)))
  | "seed" => (pure (0x015 : (BitVec 12)))
  | "cycle" => (pure (0xC00 : (BitVec 12)))
  | "time" => (pure (0xC01 : (BitVec 12)))
  | "instret" => (pure (0xC02 : (BitVec 12)))
  | "cycleh" => (pure (0xC80 : (BitVec 12)))
  | "timeh" => (pure (0xC81 : (BitVec 12)))
  | "instreth" => (pure (0xC82 : (BitVec 12)))
  | "mcycle" => (pure (0xB00 : (BitVec 12)))
  | "minstret" => (pure (0xB02 : (BitVec 12)))
  | "mcycleh" => (pure (0xB80 : (BitVec 12)))
  | "minstreth" => (pure (0xB82 : (BitVec 12)))
  | "mcyclecfg" => (pure (0x321 : (BitVec 12)))
  | "mcyclecfgh" => (pure (0x721 : (BitVec 12)))
  | "minstretcfg" => (pure (0x322 : (BitVec 12)))
  | "minstretcfgh" => (pure (0x722 : (BitVec 12)))
  | "stimecmp" => (pure (0x14D : (BitVec 12)))
  | "stimecmph" => (pure (0x15D : (BitVec 12)))
  | "satp" => (pure (0x180 : (BitVec 12)))
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def csr_name_write_callback (name : String) (value : (BitVec 64)) : SailM Unit := do
  let csr ← do (csr_name_map_backwards name)
  (pure (csr_full_write_callback name csr value))

def csr_id_write_callback (csr : (BitVec 12)) (value : (BitVec 64)) : SailM Unit := do
  let name ← do (csr_name_map_forwards csr)
  (pure (csr_full_write_callback name csr value))

def csr_name_read_callback (name : String) (value : (BitVec 64)) : SailM Unit := do
  let csr ← do (csr_name_map_backwards name)
  (pure (csr_full_read_callback name csr value))

def csr_id_read_callback (csr : (BitVec 12)) (value : (BitVec 64)) : SailM Unit := do
  let name ← do (csr_name_map_forwards csr)
  (pure (csr_full_read_callback name csr value))

def long_csr_write_callback (name : String) (name_high : String) (value : (BitVec 64)) : SailM Unit := do
  (csr_name_write_callback name (Sail.BitVec.extractLsb value (xlen -i 1) 0))


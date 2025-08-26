import LeanRV64IM.Flow
import LeanRV64IM.Prelude
import LeanRV64IM.RiscvXlen
import LeanRV64IM.RvfiDii
import LeanRV64IM.RiscvExtensions
import LeanRV64IM.RiscvTypes
import LeanRV64IM.RiscvRegs
import LeanRV64IM.RiscvSysRegs
import LeanRV64IM.RiscvPmpRegs
import LeanRV64IM.RiscvVextRegs
import LeanRV64IM.RiscvZihpm
import LeanRV64IM.RiscvSmcntrpmf
import LeanRV64IM.RiscvPlatform
import LeanRV64IM.RiscvVmemTlb
import LeanRV64IM.RiscvVmem
import LeanRV64IM.RiscvTerminationEnd

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

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg rvfi_instruction (← (undefined_RVFI_DII_Instruction_Packet ()))
  writeReg rvfi_inst_data (← (undefined_RVFI_DII_Execution_Packet_InstMetaData ()))
  writeReg rvfi_pc_data (← (undefined_RVFI_DII_Execution_Packet_PC ()))
  writeReg rvfi_int_data (← (undefined_RVFI_DII_Execution_Packet_Ext_Integer ()))
  writeReg rvfi_int_data_present (← (undefined_bool ()))
  writeReg rvfi_mem_data (← (undefined_RVFI_DII_Execution_Packet_Ext_MemAccess ()))
  writeReg rvfi_mem_data_present (← (undefined_bool ()))
  writeReg PC (← (undefined_bitvector 64))
  writeReg nextPC (← (undefined_bitvector 64))
  writeReg x1 (← (undefined_bitvector 64))
  writeReg x2 (← (undefined_bitvector 64))
  writeReg x3 (← (undefined_bitvector 64))
  writeReg x4 (← (undefined_bitvector 64))
  writeReg x5 (← (undefined_bitvector 64))
  writeReg x6 (← (undefined_bitvector 64))
  writeReg x7 (← (undefined_bitvector 64))
  writeReg x8 (← (undefined_bitvector 64))
  writeReg x9 (← (undefined_bitvector 64))
  writeReg x10 (← (undefined_bitvector 64))
  writeReg x11 (← (undefined_bitvector 64))
  writeReg x12 (← (undefined_bitvector 64))
  writeReg x13 (← (undefined_bitvector 64))
  writeReg x14 (← (undefined_bitvector 64))
  writeReg x15 (← (undefined_bitvector 64))
  writeReg x16 (← (undefined_bitvector 64))
  writeReg x17 (← (undefined_bitvector 64))
  writeReg x18 (← (undefined_bitvector 64))
  writeReg x19 (← (undefined_bitvector 64))
  writeReg x20 (← (undefined_bitvector 64))
  writeReg x21 (← (undefined_bitvector 64))
  writeReg x22 (← (undefined_bitvector 64))
  writeReg x23 (← (undefined_bitvector 64))
  writeReg x24 (← (undefined_bitvector 64))
  writeReg x25 (← (undefined_bitvector 64))
  writeReg x26 (← (undefined_bitvector 64))
  writeReg x27 (← (undefined_bitvector 64))
  writeReg x28 (← (undefined_bitvector 64))
  writeReg x29 (← (undefined_bitvector 64))
  writeReg x30 (← (undefined_bitvector 64))
  writeReg x31 (← (undefined_bitvector 64))
  writeReg cur_privilege (← (undefined_Privilege ()))
  writeReg cur_inst (← (undefined_bitvector 64))
  writeReg mie (← (undefined_Minterrupts ()))
  writeReg mip (← (undefined_Minterrupts ()))
  writeReg medeleg (← (undefined_Medeleg ()))
  writeReg mideleg (← (undefined_Minterrupts ()))
  writeReg mtvec (← (undefined_Mtvec ()))
  writeReg mcause (← (undefined_Mcause ()))
  writeReg mepc (← (undefined_bitvector 64))
  writeReg mtval (← (undefined_bitvector 64))
  writeReg mscratch (← (undefined_bitvector 64))
  writeReg scounteren (← (undefined_Counteren ()))
  writeReg mcounteren (← (undefined_Counteren ()))
  writeReg mcountinhibit (← (undefined_Counterin ()))
  writeReg mcycle (← (undefined_bitvector 64))
  writeReg mtime (← (undefined_bitvector 64))
  writeReg minstret (← (undefined_bitvector 64))
  writeReg minstret_increment (← (undefined_bool ()))
  writeReg stvec (← (undefined_Mtvec ()))
  writeReg sscratch (← (undefined_bitvector 64))
  writeReg sepc (← (undefined_bitvector 64))
  writeReg scause (← (undefined_Mcause ()))
  writeReg stval (← (undefined_bitvector 64))
  writeReg tselect (← (undefined_bitvector 64))
  writeReg vstart (← (undefined_bitvector 64))
  writeReg vl (← (undefined_bitvector 64))
  writeReg vtype (← (undefined_Vtype ()))
  writeReg pmpcfg_n (← (undefined_vector 64 (← (undefined_Pmpcfg_ent ()))))
  writeReg pmpaddr_n (← (undefined_vector 64 (← (undefined_bitvector 64))))
  writeReg vr0 (← (undefined_bitvector 65536))
  writeReg vr1 (← (undefined_bitvector 65536))
  writeReg vr2 (← (undefined_bitvector 65536))
  writeReg vr3 (← (undefined_bitvector 65536))
  writeReg vr4 (← (undefined_bitvector 65536))
  writeReg vr5 (← (undefined_bitvector 65536))
  writeReg vr6 (← (undefined_bitvector 65536))
  writeReg vr7 (← (undefined_bitvector 65536))
  writeReg vr8 (← (undefined_bitvector 65536))
  writeReg vr9 (← (undefined_bitvector 65536))
  writeReg vr10 (← (undefined_bitvector 65536))
  writeReg vr11 (← (undefined_bitvector 65536))
  writeReg vr12 (← (undefined_bitvector 65536))
  writeReg vr13 (← (undefined_bitvector 65536))
  writeReg vr14 (← (undefined_bitvector 65536))
  writeReg vr15 (← (undefined_bitvector 65536))
  writeReg vr16 (← (undefined_bitvector 65536))
  writeReg vr17 (← (undefined_bitvector 65536))
  writeReg vr18 (← (undefined_bitvector 65536))
  writeReg vr19 (← (undefined_bitvector 65536))
  writeReg vr20 (← (undefined_bitvector 65536))
  writeReg vr21 (← (undefined_bitvector 65536))
  writeReg vr22 (← (undefined_bitvector 65536))
  writeReg vr23 (← (undefined_bitvector 65536))
  writeReg vr24 (← (undefined_bitvector 65536))
  writeReg vr25 (← (undefined_bitvector 65536))
  writeReg vr26 (← (undefined_bitvector 65536))
  writeReg vr27 (← (undefined_bitvector 65536))
  writeReg vr28 (← (undefined_bitvector 65536))
  writeReg vr29 (← (undefined_bitvector 65536))
  writeReg vr30 (← (undefined_bitvector 65536))
  writeReg vr31 (← (undefined_bitvector 65536))
  writeReg vcsr (← (undefined_Vcsr ()))
  writeReg mhpmevent (← (undefined_vector 32 (← (undefined_HpmEvent ()))))
  writeReg mhpmcounter (← (undefined_vector 32 (← (undefined_bitvector 64))))
  writeReg mcyclecfg (← (undefined_CountSmcntrpmf ()))
  writeReg minstretcfg (← (undefined_CountSmcntrpmf ()))
  writeReg mtimecmp (← (undefined_bitvector 64))
  writeReg stimecmp (← (undefined_bitvector 64))
  writeReg htif_tohost (← (undefined_bitvector 64))
  writeReg htif_done (← (undefined_bool ()))
  writeReg htif_exit_code (← (undefined_bitvector 64))
  writeReg htif_cmd_write (← (undefined_bit ()))
  writeReg htif_payload_writes (← (undefined_bitvector 4))
  writeReg satp (← (undefined_bitvector 64))

def sail_model_init (x_0 : Unit) : SailM Unit := do
  writeReg misa (_update_Misa_MXL (Mk_Misa (zeros (n := 64))) (architecture_forwards RV64))
  writeReg mstatus (let mxl := (architecture_forwards RV64)
  (_update_Mstatus_UXL
    (_update_Mstatus_SXL (Mk_Mstatus (zeros (n := 64)))
      (if (((xlen != 32) && (hartSupports Ext_S)) : Bool)
      then mxl
      else (zeros (n := 2))))
    (if (((xlen != 32) && (hartSupports Ext_U)) : Bool)
    then mxl
    else (zeros (n := 2)))))
  writeReg mseccfg (← (legalize_mseccfg (Mk_Seccfg (zeros (n := 64))) (zeros (n := 64))))
  writeReg menvcfg (← (legalize_menvcfg (Mk_MEnvcfg (zeros (n := 64))) (zeros (n := 64))))
  writeReg senvcfg (← (legalize_senvcfg (Mk_SEnvcfg (zeros (n := 64))) (zeros (n := 64))))
  writeReg mvendorid (← (to_bits_checked (l := 32) (0 : Int)))
  writeReg mimpid (← (to_bits_checked (l := 64) (0 : Int)))
  writeReg marchid (← (to_bits_checked (l := 64) (0 : Int)))
  writeReg mhartid (← (to_bits_checked (l := 64) (0 : Int)))
  writeReg mconfigptr (zeros (n := 64))
  writeReg plat_ram_base (← (to_bits_checked (l := 64) (2147483648 : Int)))
  writeReg plat_ram_size (← (to_bits_checked (l := 64) (2147483648 : Int)))
  writeReg plat_rom_base (← (to_bits_checked (l := 64) (4096 : Int)))
  writeReg plat_rom_size (← (to_bits_checked (l := 64) (4096 : Int)))
  writeReg plat_clint_base (← (to_bits_checked (l := 64) (33554432 : Int)))
  writeReg plat_clint_size (← (to_bits_checked (l := 64) (786432 : Int)))
  writeReg tlb (vectorInit none)
  (initialize_registers ())

end LeanRV64IM.Functions

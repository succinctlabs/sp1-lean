import LeanRV32D.Main

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

noncomputable section

namespace LeanRV32D.Functions

open zvkfunct6
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
open word_width
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
open vext8funct6
open vext4funct6
open vext2funct6
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

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg rvfi_instruction (← (undefined_RVFI_DII_Instruction_Packet ()))
  writeReg rvfi_inst_data (← (undefined_RVFI_DII_Execution_Packet_InstMetaData ()))
  writeReg rvfi_pc_data (← (undefined_RVFI_DII_Execution_Packet_PC ()))
  writeReg rvfi_int_data (← (undefined_RVFI_DII_Execution_Packet_Ext_Integer ()))
  writeReg rvfi_int_data_present (← (undefined_bool ()))
  writeReg rvfi_mem_data (← (undefined_RVFI_DII_Execution_Packet_Ext_MemAccess ()))
  writeReg rvfi_mem_data_present (← (undefined_bool ()))
  writeReg PC (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg nextPC (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x1 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x2 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x3 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x4 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x5 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x6 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x7 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x8 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x9 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x10 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x11 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x12 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x13 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x14 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x15 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x16 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x17 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x18 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x19 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x20 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x21 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x22 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x23 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x24 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x25 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x26 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x27 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x28 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x29 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x30 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg x31 (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg cur_privilege (← (undefined_Privilege ()))
  writeReg cur_inst (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg mie (← (undefined_Minterrupts ()))
  writeReg mip (← (undefined_Minterrupts ()))
  writeReg medeleg (← (undefined_Medeleg ()))
  writeReg mideleg (← (undefined_Minterrupts ()))
  writeReg mtvec (← (undefined_Mtvec ()))
  writeReg mcause (← (undefined_Mcause ()))
  writeReg mepc (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg mtval (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg mscratch (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg scounteren (← (undefined_Counteren ()))
  writeReg mcounteren (← (undefined_Counteren ()))
  writeReg mcountinhibit (← (undefined_Counterin ()))
  writeReg mcycle (← (undefined_bitvector 64))
  writeReg mtime (← (undefined_bitvector 64))
  writeReg minstret (← (undefined_bitvector 64))
  writeReg minstret_increment (← (undefined_bool ()))
  writeReg stvec (← (undefined_Mtvec ()))
  writeReg sscratch (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg sepc (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg scause (← (undefined_Mcause ()))
  writeReg stval (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg tselect (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg vstart (← (undefined_bitvector 16))
  writeReg vl (← (undefined_bitvector ((2 ^i 2) *i 8)))
  writeReg vtype (← (undefined_Vtype ()))
  writeReg pmpcfg_n (← (undefined_vector 64 (← (undefined_Pmpcfg_ent ()))))
  writeReg pmpaddr_n (← (undefined_vector 64 (← (undefined_bitvector ((2 ^i 2) *i 8)))))
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
  writeReg float_result (← (undefined_bitvector 64))
  writeReg float_fflags (← (undefined_bitvector 64))
  writeReg f0 (← (undefined_bitvector (8 *i 8)))
  writeReg f1 (← (undefined_bitvector (8 *i 8)))
  writeReg f2 (← (undefined_bitvector (8 *i 8)))
  writeReg f3 (← (undefined_bitvector (8 *i 8)))
  writeReg f4 (← (undefined_bitvector (8 *i 8)))
  writeReg f5 (← (undefined_bitvector (8 *i 8)))
  writeReg f6 (← (undefined_bitvector (8 *i 8)))
  writeReg f7 (← (undefined_bitvector (8 *i 8)))
  writeReg f8 (← (undefined_bitvector (8 *i 8)))
  writeReg f9 (← (undefined_bitvector (8 *i 8)))
  writeReg f10 (← (undefined_bitvector (8 *i 8)))
  writeReg f11 (← (undefined_bitvector (8 *i 8)))
  writeReg f12 (← (undefined_bitvector (8 *i 8)))
  writeReg f13 (← (undefined_bitvector (8 *i 8)))
  writeReg f14 (← (undefined_bitvector (8 *i 8)))
  writeReg f15 (← (undefined_bitvector (8 *i 8)))
  writeReg f16 (← (undefined_bitvector (8 *i 8)))
  writeReg f17 (← (undefined_bitvector (8 *i 8)))
  writeReg f18 (← (undefined_bitvector (8 *i 8)))
  writeReg f19 (← (undefined_bitvector (8 *i 8)))
  writeReg f20 (← (undefined_bitvector (8 *i 8)))
  writeReg f21 (← (undefined_bitvector (8 *i 8)))
  writeReg f22 (← (undefined_bitvector (8 *i 8)))
  writeReg f23 (← (undefined_bitvector (8 *i 8)))
  writeReg f24 (← (undefined_bitvector (8 *i 8)))
  writeReg f25 (← (undefined_bitvector (8 *i 8)))
  writeReg f26 (← (undefined_bitvector (8 *i 8)))
  writeReg f27 (← (undefined_bitvector (8 *i 8)))
  writeReg f28 (← (undefined_bitvector (8 *i 8)))
  writeReg f29 (← (undefined_bitvector (8 *i 8)))
  writeReg f30 (← (undefined_bitvector (8 *i 8)))
  writeReg f31 (← (undefined_bitvector (8 *i 8)))
  writeReg fcsr (← (undefined_Fcsr ()))
  writeReg mcyclecfg (← (undefined_CountSmcntrpmf ()))
  writeReg minstretcfg (← (undefined_CountSmcntrpmf ()))
  writeReg mtimecmp (← (undefined_bitvector 64))
  writeReg stimecmp (← (undefined_bitvector 64))
  writeReg htif_tohost (← (undefined_bitvector 64))
  writeReg htif_done (← (undefined_bool ()))
  writeReg htif_exit_code (← (undefined_bitvector 64))
  writeReg htif_cmd_write (← (undefined_bit ()))
  writeReg htif_payload_writes (← (undefined_bitvector 4))
  writeReg satp (← (undefined_bitvector ((2 ^i 2) *i 8)))

def sail_model_init (x_0 : Unit) : SailM Unit := do
  writeReg misa (_update_Misa_MXL (Mk_Misa (zeros (n := 32))) (architecture_forwards RV32))
  writeReg mstatus (let mxl := (architecture_forwards RV32)
  (_update_Mstatus_UXL (_update_Mstatus_SXL (Mk_Mstatus (zeros (n := 64))) (zeros (n := 2)))
    (zeros (n := 2))))
  writeReg menvcfg (← (legalize_menvcfg (Mk_MEnvcfg (zeros (n := 64))) (zeros (n := 64))))
  writeReg senvcfg (← (legalize_senvcfg (Mk_SEnvcfg (zeros (n := 32)))
      (zeros (n := ((2 ^i 2) *i 8)))))
  writeReg mvendorid (← (to_bits_checked (l := 32) (0 : Int)))
  writeReg mimpid (← (to_bits_checked (l := ((2 ^i 2) *i 8)) (0 : Int)))
  writeReg marchid (← (to_bits_checked (l := ((2 ^i 2) *i 8)) (0 : Int)))
  writeReg mhartid (← (to_bits_checked (l := ((2 ^i 2) *i 8)) (0 : Int)))
  writeReg mconfigptr (zeros (n := ((2 ^i 2) *i 8)))
  writeReg plat_ram_base (← (to_bits_checked (l := 34) (2147483648 : Int)))
  writeReg plat_ram_size (← (to_bits_checked (l := 34) (2147483648 : Int)))
  writeReg plat_rom_base (← (to_bits_checked (l := 34) (4096 : Int)))
  writeReg plat_rom_size (← (to_bits_checked (l := 34) (4096 : Int)))
  writeReg plat_clint_base (← (to_bits_checked (l := 34) (33554432 : Int)))
  writeReg plat_clint_size (← (to_bits_checked (l := 34) (786432 : Int)))
  writeReg tlb (vectorInit none)
  writeReg hart_state (HART_ACTIVE ())
  (initialize_registers ())

end LeanRV32D.Functions

open LeanRV32D.Functions

def main (_ : List String) : IO UInt32 := do
  main_of_sail_main ⟨default, (), default, default, default, default⟩ (sail_model_init >=> sail_main)

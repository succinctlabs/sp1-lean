import LeanRV32D.RiscvTermination

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

def generate_dts (_ : Unit) : SailM String := do
  let clock_freq : Int := 1000000000
  let ram_base_hi ← do (pure (BitVec.toNat (shiftr (← readReg plat_ram_base) 32)))
  let ram_base_lo ← do
    (pure (BitVec.toNat (Sail.BitVec.extractLsb (← readReg plat_ram_base) 31 0)))
  let ram_size_hi ← do (pure (BitVec.toNat (shiftr (← readReg plat_ram_size) 32)))
  let ram_size_lo ← do
    (pure (BitVec.toNat (Sail.BitVec.extractLsb (← readReg plat_ram_size) 31 0)))
  let clint_base_hi ← do (pure (BitVec.toNat (shiftr (← readReg plat_clint_base) 32)))
  let clint_base_lo ← do
    (pure (BitVec.toNat (Sail.BitVec.extractLsb (← readReg plat_clint_base) 31 0)))
  let clint_size_hi ← do (pure (BitVec.toNat (shiftr (← readReg plat_clint_size) 32)))
  let clint_size_lo ← do
    (pure (BitVec.toNat (Sail.BitVec.extractLsb (← readReg plat_clint_size) 31 0)))
  let isa_string : String := "imafdc_zicntr_zihpm"
  (pure (HAppend.hAppend "/dts-v1/;
"
      (HAppend.hAppend "
"
        (HAppend.hAppend "/ {
"
          (HAppend.hAppend "  #address-cells = <2>;
"
            (HAppend.hAppend "  #size-cells = <2>;
"
              (HAppend.hAppend "  compatible = \"ucbbar,spike-bare-dev\";
"
                (HAppend.hAppend "  model = \"ucbbar,spike-bare\";
"
                  (HAppend.hAppend "  cpus {
"
                    (HAppend.hAppend "    #address-cells = <1>;
"
                      (HAppend.hAppend "    #size-cells = <0>;
"
                        (HAppend.hAppend "    timebase-frequency = <"
                          (HAppend.hAppend (Int.repr (Int.tdiv clock_freq plat_insns_per_tick))
                            (HAppend.hAppend ">;
"
                              (HAppend.hAppend "    CPU0: cpu@0 {
"
                                (HAppend.hAppend "      device_type = \"cpu\";
"
                                  (HAppend.hAppend "      reg = <0>;
"
                                    (HAppend.hAppend "      status = \"okay\";
"
                                      (HAppend.hAppend "      compatible = \"riscv\";
"
                                        (HAppend.hAppend "      riscv,isa = \""
                                          (HAppend.hAppend "rv"
                                            (HAppend.hAppend (Int.repr xlen)
                                              (HAppend.hAppend isa_string
                                                (HAppend.hAppend "\";
"
                                                  (HAppend.hAppend "      mmu-type = \"riscv,"
                                                    (HAppend.hAppend "sv32"
                                                      (HAppend.hAppend "\";
"
                                                        (HAppend.hAppend "      clock-frequency = <"
                                                          (HAppend.hAppend (Int.repr clock_freq)
                                                            (HAppend.hAppend ">;
"
                                                              (HAppend.hAppend
                                                                "      CPU0_intc: interrupt-controller {
"
                                                                (HAppend.hAppend
                                                                  "        #address-cells = <2>;
"
                                                                  (HAppend.hAppend
                                                                    "        #interrupt-cells = <1>;
"
                                                                    (HAppend.hAppend
                                                                      "        interrupt-controller;
"
                                                                      (HAppend.hAppend
                                                                        "        compatible = \"riscv,cpu-intc\";
"
                                                                        (HAppend.hAppend "      };
"
                                                                          (HAppend.hAppend "    };
"
                                                                            (HAppend.hAppend "  };
"
                                                                              (HAppend.hAppend
                                                                                "  memory@"
                                                                                (HAppend.hAppend
                                                                                  (String.drop
                                                                                    (Int.toHex
                                                                                      (BitVec.toNat
                                                                                        (← readReg plat_ram_base)))
                                                                                    2)
                                                                                  (HAppend.hAppend
                                                                                    " {
"
                                                                                    (HAppend.hAppend
                                                                                      "    device_type = \"memory\";
"
                                                                                      (HAppend.hAppend
                                                                                        "    reg = <"
                                                                                        (HAppend.hAppend
                                                                                          (Int.toHex
                                                                                            ram_base_hi)
                                                                                          (HAppend.hAppend
                                                                                            " "
                                                                                            (HAppend.hAppend
                                                                                              (Int.toHex
                                                                                                ram_base_lo)
                                                                                              (HAppend.hAppend
                                                                                                " "
                                                                                                (HAppend.hAppend
                                                                                                  (Int.toHex
                                                                                                    ram_size_hi)
                                                                                                  (HAppend.hAppend
                                                                                                    " "
                                                                                                    (HAppend.hAppend
                                                                                                      (Int.toHex
                                                                                                        ram_size_lo)
                                                                                                      (HAppend.hAppend
                                                                                                        ">;
"
                                                                                                        (HAppend.hAppend
                                                                                                          "  };
"
                                                                                                          (HAppend.hAppend
                                                                                                            "  soc {
"
                                                                                                            (HAppend.hAppend
                                                                                                              "    #address-cells = <2>;
"
                                                                                                              (HAppend.hAppend
                                                                                                                "    #size-cells = <2>;
"
                                                                                                                (HAppend.hAppend
                                                                                                                  "    compatible = \"ucbbar,spike-bare-soc\", \"simple-bus\";
"
                                                                                                                  (HAppend.hAppend
                                                                                                                    "    ranges;
"
                                                                                                                    (HAppend.hAppend
                                                                                                                      "    clint@"
                                                                                                                      (HAppend.hAppend
                                                                                                                        (String.drop
                                                                                                                          (Int.toHex
                                                                                                                            (BitVec.toNat
                                                                                                                              (← readReg plat_clint_base)))
                                                                                                                          2)
                                                                                                                        (HAppend.hAppend
                                                                                                                          " {
"
                                                                                                                          (HAppend.hAppend
                                                                                                                            "      compatible = \"riscv,clint0\";
"
                                                                                                                            (HAppend.hAppend
                                                                                                                              "      interrupts-extended = <&CPU0_intc 3 &CPU0_intc 7>;
"
                                                                                                                              (HAppend.hAppend
                                                                                                                                "      reg = <"
                                                                                                                                (HAppend.hAppend
                                                                                                                                  (Int.toHex
                                                                                                                                    clint_base_hi)
                                                                                                                                  (HAppend.hAppend
                                                                                                                                    " "
                                                                                                                                    (HAppend.hAppend
                                                                                                                                      (Int.toHex
                                                                                                                                        clint_base_lo)
                                                                                                                                      (HAppend.hAppend
                                                                                                                                        " "
                                                                                                                                        (HAppend.hAppend
                                                                                                                                          (Int.toHex
                                                                                                                                            clint_size_hi)
                                                                                                                                          (HAppend.hAppend
                                                                                                                                            " "
                                                                                                                                            (HAppend.hAppend
                                                                                                                                              (Int.toHex
                                                                                                                                                clint_size_lo)
                                                                                                                                              (HAppend.hAppend
                                                                                                                                                ">;
"
                                                                                                                                                (HAppend.hAppend
                                                                                                                                                  "    };
"
                                                                                                                                                  (HAppend.hAppend
                                                                                                                                                    "  };
"
                                                                                                                                                    (HAppend.hAppend
                                                                                                                                                      "  htif {
"
                                                                                                                                                      (HAppend.hAppend
                                                                                                                                                        "    compatible = \"ucb,htif0\";
"
                                                                                                                                                        (HAppend.hAppend
                                                                                                                                                          "  };
"
                                                                                                                                                          "};
"))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


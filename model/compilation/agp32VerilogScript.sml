open hardwarePreamble alignmentTheory alistTheory agp32ProcessorTheory translatorLib verilogPrintLib;

val _ = new_theory "agp32Verilog";

val _ = guess_lengths ();
val _ = prefer_num ();

local
 val module_def = agp32_def
 val abstract_fields = ["mem", "io_events", "interrupt_state"]
 val outputs = ["PC", "data_out", "interrupt_req", "command",
                "data_addr", "data_wdata", "data_wstrb"]
 val comms = ["data_out", "command", "data_addr", "data_wdata", "data_wstrb",
              "acc_arg", "acc_arg_ready", "acc_res", "acc_res_ready", "interrupt_req",
              "PC", "ID_PC", "EX_PC", "EX_imm", "EX_addrW", "EX_opc",
              "MEM_PC", "MEM_dataA", "MEM_dataB", "MEM_ALU_res",
              "MEM_SHIFT_res", "MEM_addrW", "MEM_opc",
              "WB_write_reg", "WB_addrW", "MEM_enable", "WB_enable"]
in
 val tstate = init_translator module_def
                              abstract_fields
                              comms

 val trans_thm = module2hardware tstate
                                 module_def
                                 abstract_fields
                                 outputs
                                 comms
end

val verilogstr =
 definition"agp32_v_def"
 |> REWRITE_RULE [definition"agp32_v_seqs_def", definition"agp32_v_combs_def", definition"agp32_v_decls_def"]
 |> concl
 |> rhs
 |> verilog_print "agp32_processor";

val _ = writeFile "agp32_processor.sv" verilogstr;

val _ = export_theory ();

open hardwarePreamble alignmentTheory alistTheory agp32StateTheory agp32ProcessorTheory translatorLib verilogPrintLib;

val _ = new_theory "agp32Verilog";

val _ = guess_lengths ();
val _ = prefer_num ();

val module_def = agp32_def;
val abstract_fields = ["mem", "io_events", "interrupt_state"];
val outputs = ["PC"];
val comms = ["PC", "data_out",
             "command", "data_addr", "data_wdata", "data_wstrb",
             "acc_arg", "acc_arg_ready",
             "acc_res", "acc_res_ready",
             "interrupt_req"];

val trans_thm = module2hardware module_def
                                abstract_fields
                                outputs
                                comms;

val verilogstr =
 definition"agp32_v_def"
 |> REWRITE_RULE [definition"agp32_v_seqs_def", definition"agp32_v_combs_def"]
 |> concl
 |> rhs
 |> verilog_print "agp32_processor";

val _ = writeFile "agp32_processor.sv" verilogstr;

val _ = export_theory ();
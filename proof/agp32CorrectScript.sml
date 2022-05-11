open hardwarePreamble translatorTheory translatorLib arithmeticTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory ag32Theory ag32ExtraTheory agp32RelationTheory;

val _ = new_theory "agp32Correct";

(* Special variables used in theorems:
   I: scheduling function.
   C: cache oracle.
 *)

val _ = prefer_num ();
val _ = guess_lengths ();

fun v2w_word_bit_list_cleanup tm =
  if is_var tm orelse is_const tm then
    raise UNCHANGED
  else if is_v2w tm andalso (is_list (rand tm)) then let
    val (arg, worddim) = dest_v2w tm
    val (arg, _) = dest_list arg
    val len = length arg
  in
    if len = 1 then
      raise UNCHANGED
    else let
      (* TODO: Fails on lists of non-dest_word_bit calls *)
      val (hindex, var) = arg |> hd |> dest_word_bit
      val (lindex, _) = arg |> last |> dest_word_bit
    in
      mk_eq (tm, mk_word_extract (hindex, lindex, var, mk_int_numeric_type len)) |> BBLAST_PROVE
    end
  end else if is_comb tm then
    COMB_CONV v2w_word_bit_list_cleanup tm
  else (* must be abs *)
    ABS_CONV v2w_word_bit_list_cleanup tm;

(* lemmas about the Silver ISA *)
Theorem ALU_state_eq_after:
  !func input1 input2 res a a'.
    ALU (func, input1, input2) a = (res, a') ==>
    a'.PC = a.PC /\ a'.MEM = a.MEM /\ a'.PC = a.PC /\ a'.R = a.R /\
    a'.data_in = a.data_in /\ a'.data_out = a.data_out /\ a'.io_events = a.io_events
Proof
  rw [ALU_def] >> Cases_on `func'` >> fs [] >> rw []
QED

Theorem ag32_data_in_unchanged:
  !a n. (FUNPOW Next n a).data_in = (FUNPOW Next (SUC n) a).data_in
Proof
  rw [FUNPOW_SUC] >>
  Q.ABBREV_TAC `a1 = FUNPOW Next n a` >>
  rw [Next_def] >>
  Q.ABBREV_TAC `i = (a1.MEM ((31 >< 2) a1.PC @@ (0w:word2) + 3w) @@
                     a1.MEM ((31 >< 2) a1.PC @@ (0w:word2) + 2w) @@
                     a1.MEM ((31 >< 2) a1.PC @@ (0w:word2) + 1w) @@
                     a1.MEM ((31 >< 2) a1.PC @@ (0w:word2)))` >>
  rw [Decode_def,boolify32_def] >> CONV_TAC v2w_word_bit_list_cleanup >>
  rw [Run_def,dfn'LoadUpperConstant_def,dfn'LoadConstant_def,
      dfn'Interrupt_def,incPC_def] >-
   (** JumpIfZero **)
   (rw [dfn'JumpIfZero_def] >>
    qpat_abbrev_tac `alu = ALU _ _` >>
    Cases_on `alu` >> rw [incPC_def] >>
    METIS_TAC [ALU_state_eq_after]) >-
   (** JumpIfNotZero **)
    (rw [dfn'JumpIfNotZero_def] >>
     qpat_abbrev_tac `alu = ALU _ _` >>
     Cases_on `alu` >> rw [incPC_def] >>
     METIS_TAC [ALU_state_eq_after]) >>
  Cases_on `DecodeReg_imm (v2w [word_bit 31 i],(30 >< 25) i)` >> rw [] >>
  (** Other instructions **)
  rw [dfn'Normal_def,norm_def,dfn'Shift_def,incPC_def,dfn'StoreMEM_def,
      dfn'StoreMEMByte_def,dfn'LoadMEM_def,dfn'LoadMEMByte_def,
      dfn'Out_def,dfn'In_def,dfn'Accelerator_def,dfn'Jump_def] >>
  qpat_abbrev_tac `alu = ALU _ _` >>
  Cases_on `alu` >> rw [] >>
  METIS_TAC [ALU_state_eq_after]
QED

Theorem agp32_Init_implies_Rel:
  !k fext fbits s a I.
    k >= 1 ==>
    k <= 5 ==>
    s = agp32 fext fbits ==>
    is_mem fext_accessor_circuit s fext ==>
    is_acc accelerator_f s ==>
    is_interrupt_interface fext_accessor_circuit s fext ==>
    Init (fext 0) (s 0) a ==>
    I(k,0) = 0 ==>
    Rel (fext 0) (s 0) k a 0
Proof
  rpt strip_tac >>
  fs [Init_def,Rel_def] >>
  Cases_on `k = 1` >-
   (fs [] >> cheat) >>
  Cases_on `k = 2` >-
   (fs [] >> cheat) >>
  Cases_on `k = 3` >-
   (fs [] >> cheat) >>
  Cases_on `k = 4` >-
   (fs [] >> cheat) >>
  Cases_on `k = 5` >-
   (fs [] >> cheat) >> fs []
QED

Theorem agp32_Rel_ag32_correct:
  !k fext fbits s a (t:num) I C.
    k >= 1 ==>
    k <= 5 ==>
    s = agp32 fext fbits ==>
    (!t. SC_self_mod (s t)) ==>
    is_mem fext_accessor_circuit s fext ==>
    is_acc accelerator_f s ==>
    is_interrupt_interface fext_accessor_circuit s fext ==>
    is_data_in fext ==>
    (* cache oracle can introduce hit/miss *)
    (!t. C (s t).data_addr (s t).data_wstrb (s t).data_wdata (s t).command (s t).PC <=> (fext t).ready) ==>
    Init (fext 0) (s 0) a ==>
    (** properties of scheduling function I **)
    (!t k. enable_stg k (s (SUC t)) ==> I(k,SUC t) = I(k,t) + 1) ==>
    I(k,0) = 0 ==>
    Rel (fext t) (s t) k a (I(k,t))
Proof
  rpt strip_tac >>
  Induct_on `t` >> fs [] >-
   METIS_TAC [agp32_Init_implies_Rel] >>
  Q.ABBREV_TAC `i = I'(k,t)` >>
  Cases_on `enable_stg k (s (SUC t))` >-
   (`I'(k, SUC t) = SUC i` by fs [] >> fs [Rel_def] >>
    Cases_on `k = 1` >-
     (** IF stage **)
     (fs [] >> rw [] >|[
         fs [GSYM ag32_data_in_unchanged,is_data_in_def],
         rw [agp32_def,mk_module_def] >> cheat,
         cheat]) >>
      cheat) >>
  cheat
QED

val _ = export_theory ();

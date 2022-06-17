open hardwarePreamble arithmeticTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax wordsExtraTheory ag32Theory ag32ExtraTheory;

val _ = new_theory "ag32Utilities";

(* lemmas about the Silver ISA *)
val _ = prefer_num ();
val _ = guess_lengths ();

(* this function is copied from the ag32 repo *)
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

(* self-defined tactics *)
val get_opc_from_decode_tac =
 (rpt GEN_TAC >> simp [Decode_def,boolify32_def] >>
  CONV_TAC v2w_word_bit_list_cleanup >>              
  qpat_abbrev_tac `dc = DecodeReg_imm (_,_)` >> rw [] >>
  Cases_on `dc` >> fs [] >>
  Q.ABBREV_TAC `op = (5 >< 0) (word_at_addr ag.MEM (align_addr ag.PC))` >>
  Cases_on_word_value `op` >> fs [] >>
  rw [opc_def,instr_def] >>
  fs [DecodeReg_imm_def,v2w_single_0w]);

Theorem ALU_state_eq_after:
  !func input1 input2 res a a'.
    ALU (func, input1, input2) a = (res, a') ==>
    a'.PC = a.PC /\ a'.MEM = a.MEM /\ a'.PC = a.PC /\ a'.R = a.R /\
    a'.data_in = a.data_in /\ a'.data_out = a.data_out /\ a'.io_events = a.io_events
Proof
  rw [ALU_def] >> Cases_on `func'` >> fs [] >> rw []
QED

(* data_in is unchanged *)
Theorem ag32_data_in_unchanged_next:
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

Theorem ag32_data_in_unchanged_all:
  !a n m. (FUNPOW Next n a).data_in = (FUNPOW Next m a).data_in
Proof
  rw [] >> Induct_on `n` >> Induct_on `m` >> rw [] >>
  METIS_TAC [ag32_data_in_unchanged_next]  
QED

(* ISA: opc is correct with respect to the Decode *)
(** if Deocde got Normal, then opc is 0w **)
Theorem ag32_Decode_Normal_opc_0w:
  !ag func wi a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Normal (func,wi,a,b) ==>
    opc ag = 0w
Proof
  get_opc_from_decode_tac
QED

(** if Deocde got Shift, then opc is 1w **)
Theorem ag32_Decode_Shift_opc_1w:
  !ag sh wi a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Shift (sh,wi,a,b) ==>
    opc ag = 1w
Proof
  get_opc_from_decode_tac
QED

(** if Deocde got StoreMEM, then opc is 2w **)
Theorem ag32_Decode_StoreMEM_opc_2w:
  !ag a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = StoreMEM (a,b) ==>
    opc ag = 2w
Proof
  get_opc_from_decode_tac
QED

(** if Deocde got StoreMEMByte, then opc is 3w **)
Theorem ag32_Decode_StoreMEMByte_opc_3w:
  !ag a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = StoreMEMByte (a,b) ==>
    opc ag = 3w
Proof
  get_opc_from_decode_tac
QED

(** if Deocde got LoadMEM, then opc is 4w **)
Theorem ag32_Decode_LoadMEM_opc_4w:
  !ag wi a.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = LoadMEM (wi,a) ==>
    opc ag = 4w
Proof
  get_opc_from_decode_tac
QED

(** if Deocde got LoadMEMByte, then opc is 5w **)
Theorem ag32_Decode_LoadMEMByte_opc_5w:
  !ag wi a.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = LoadMEMByte (wi,a) ==>
    opc ag = 5w
Proof
  get_opc_from_decode_tac
QED

(** if Deocde got Out, then opc is 6w **)
Theorem ag32_Decode_Out_opc_6w:
  !ag func wi a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Out (func,wi,a,b) ==>
    opc ag = 6w
Proof
  get_opc_from_decode_tac
QED

(** if Deocde got In, then opc is 7w **)
Theorem ag32_Decode_In_opc_7w:
  !ag c.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = In c ==>
    opc ag = 7w
Proof
  get_opc_from_decode_tac
QED

(** if Deocde got Acc, then opc is 8w **)
Theorem ag32_Decode_Acc_opc_8w:
  !ag wi a.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Accelerator (wi,a) ==>
    opc ag = 8w
Proof
  get_opc_from_decode_tac
QED

(** if Deocde got Jump, then opc is 9w **)
Theorem ag32_Decode_Jump_opc_9w:
  !ag func wi a.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Jump (func,wi,a) ==>
    opc ag = 9w
Proof
  get_opc_from_decode_tac
QED

(** if Deocde got JumpIfZero, then opc is 10w **)
Theorem ag32_Decode_JumpIfZero_opc_10w:
  !ag func wi a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = JumpIfZero (func,wi,a,b) ==>
    opc ag = 10w
Proof
  get_opc_from_decode_tac
QED

(** if Deocde got JumpIfNotZero, then opc is 11w **)
Theorem ag32_Decode_JumpIfNotZero_opc_11w:
  !ag func wi a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = JumpIfNotZero (func,wi,a,b) ==>
    opc ag = 11w
Proof
  get_opc_from_decode_tac
QED

(** if Deocde got Interrupt, then opc is 12w **)
Theorem ag32_Decode_Interrupt_opc_12w:
  !ag.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Interrupt ==>
    opc ag = 12w
Proof
  get_opc_from_decode_tac
QED

(** if Deocde got LoadConstant, then opc is 13w **)
Theorem ag32_Decode_LoadConstant_opc_13w:
  !ag w1 w2 w3.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = LoadConstant(w1,w2,w3) ==>
    opc ag = 13w
Proof
  get_opc_from_decode_tac
QED

(** if Deocde got LoadUpperConstant, then opc is 14w **)
Theorem ag32_Decode_LoadUpperConstant_opc_14w:
  !ag w1 w2.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = LoadUpperConstant(w1,w2) ==>
    opc ag = 14w
Proof
  rpt GEN_TAC >> simp [Decode_def,boolify32_def] >>
  CONV_TAC v2w_word_bit_list_cleanup >>              
  qpat_abbrev_tac `dc = DecodeReg_imm (_,_)` >> rw [] >-
   (rw [opc_def,instr_def] >>
    Q.ABBREV_TAC `i = word_at_addr ag.MEM (align_addr ag.PC)` >>
    fs [word_bit_def] >> FULL_BBLAST_TAC) >>
  Cases_on `dc` >> fs [] >>
  Q.ABBREV_TAC `op = (5 >< 0) (word_at_addr ag.MEM (align_addr ag.PC))` >>
  Cases_on_word_value `op` >> fs []
QED

val _ = export_theory ();

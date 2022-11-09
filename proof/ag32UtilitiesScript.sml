open hardwarePreamble arithmeticTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax wordsExtraTheory ag32Theory ag32ExtraTheory agp32EnvironmentTheory agp32RelationTheory;

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

val get_addrW_from_decode_tac =
 (rpt GEN_TAC >> simp [Decode_def,boolify32_def] >>
  CONV_TAC v2w_word_bit_list_cleanup >>              
  qpat_abbrev_tac `dc = DecodeReg_imm (_,_)` >> rw [] >>
  Cases_on `dc` >> fs [] >>
  Q.ABBREV_TAC `op = (5 >< 0) (word_at_addr ag.MEM (align_addr ag.PC))` >>
  Cases_on_word_value `op` >> fs [] >>
  rw [addrW_def,instr_def] >>
  fs [DecodeReg_imm_def] >>
  rename1 `vbit = 0w` >>
  Cases_on `vbit = 0w` >> fs []);

val get_data_simp_tac =
 (rpt GEN_TAC >> simp [Decode_def,boolify32_def] >>
  CONV_TAC v2w_word_bit_list_cleanup >>              
  qpat_abbrev_tac `dc = DecodeReg_imm (_,_)` >> rw [] >>
  Cases_on `dc` >> fs [] >>
  Q.ABBREV_TAC `op = (5 >< 0) (word_at_addr ag.MEM (align_addr ag.PC))` >>
  Cases_on_word_value `op` >> fs []);

val get_func_from_decode_tac =
 (simp [Decode_def,boolify32_def] >>
  CONV_TAC v2w_word_bit_list_cleanup >>              
  qpat_abbrev_tac `dc = DecodeReg_imm (_,_)` >> rw [] >>
  Cases_on `dc` >> fs [] >>
  Q.ABBREV_TAC `op = (5 >< 0) (word_at_addr ag.MEM (align_addr ag.PC))` >>
  Cases_on_word_value `op` >> fs [] >>
  Q.ABBREV_TAC `i = (word_at_addr ag.MEM (align_addr ag.PC))` >>
  Cases_on_word_value `(9 >< 6) i` >>
  fs [func_def,num2funcT_thm,instr_def]);


(* two lemmas about word concat and add *)
Theorem addr_add:
  !(w:word32).
    (31 >< 2) w @@ (0w:word2) + 1w = (31 >< 2) w @@ (1w:word2) /\
    (31 >< 2) w @@ (0w:word2) + 2w = (31 >< 2) w @@ (2w:word2) /\
    (31 >< 2) w @@ (0w:word2) + 3w = (31 >< 2) w @@ (3w:word2)
Proof
  BBLAST_TAC
QED

Theorem addr_concat:
  !(w1:word30) (w2:word2) (w3:word30) (w4:word2).
    (w1 @@ w2 = w3 @@ w4) <=> (w1 = w3 /\ w2 = w4)
Proof
  BBLAST_TAC
QED


(* unchanged items in ISA state after ALU updating *)
Theorem ALU_state_eq_after[local]:
  !func input1 input2 res a a'.
    ALU (func, input1, input2) a = (res, a') ==>
    a'.PC = a.PC /\ a'.MEM = a.MEM /\ a'.R = a.R /\
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

(** if opc is 2w, then Decode result is StoreMEM **)
Theorem ag32_opc_2w_Decode_StoreMEM:
  !ag.
    opc ag = 2w ==>
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) =
    StoreMEM (DecodeReg_imm (v2w [word_bit 23 (word_at_addr ag.MEM (align_addr ag.PC))],
                             (22 >< 17) (word_at_addr ag.MEM (align_addr ag.PC))),
              DecodeReg_imm (v2w [word_bit 16 (word_at_addr ag.MEM (align_addr ag.PC))],
                             (15 >< 10) (word_at_addr ag.MEM (align_addr ag.PC))))
Proof
  rw [opc_def,instr_def] >> simp [Decode_def,boolify32_def] >>
  CONV_TAC v2w_word_bit_list_cleanup >> fs [] >>
  rw [DecodeReg_imm_def] >>
  fs [v2w_single_0w]
QED

(** if Deocde got StoreMEMByte, then opc is 3w **)
Theorem ag32_Decode_StoreMEMByte_opc_3w:
  !ag a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = StoreMEMByte (a,b) ==>
    opc ag = 3w
Proof
  get_opc_from_decode_tac
QED

(** if opc is 3w, then Decode result is StoreMEMByte **)
Theorem ag32_opc_3w_Decode_StoreMEMByte:
  !ag.
    opc ag = 3w ==>
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) =
    StoreMEMByte (DecodeReg_imm (v2w [word_bit 23 (word_at_addr ag.MEM (align_addr ag.PC))],
                             (22 >< 17) (word_at_addr ag.MEM (align_addr ag.PC))),
                  DecodeReg_imm (v2w [word_bit 16 (word_at_addr ag.MEM (align_addr ag.PC))],
                                 (15 >< 10) (word_at_addr ag.MEM (align_addr ag.PC))))
Proof
  rw [opc_def,instr_def] >> simp [Decode_def,boolify32_def] >>
  CONV_TAC v2w_word_bit_list_cleanup >> fs [] >>
  rw [DecodeReg_imm_def] >>
  fs [v2w_single_0w]
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

(** if Deocde got ReservedInstr, then opc is not 0-14w **)
Theorem ag32_Decode_ReservedInstr_opc_15w:
  !ag.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = ReservedInstr ==>
    opc ag = 15w
Proof
  rpt GEN_TAC >> simp [Decode_def,boolify32_def] >>
  CONV_TAC v2w_word_bit_list_cleanup >>
  NTAC 2 (IF_CASES_TAC >- fs []) >>
  IF_CASES_TAC >-
   (Q.ABBREV_TAC `i = word_at_addr ag.MEM (align_addr ag.PC)` >>
    `~word_bit 31 i` by fs [] >>
    simp [opc_def,instr_def] >> fs [] >>
    `(23 >< 9) i <> 0w` by FULL_BBLAST_TAC >> rw []) >>
  NTAC 3 (IF_CASES_TAC >- fs []) >>
  qpat_abbrev_tac `dc = DecodeReg_imm (_,_)` >>
  Cases_on `dc` >> fs [] >-
   (simp [opc_def,instr_def] >> fs [DecodeReg_imm_def] >>
    Q.ABBREV_TAC `i = word_at_addr ag.MEM (align_addr ag.PC)` >>
    Cases_on `word_bit 31 i` >> fs [v2w_single]) >>
  NTAC 10 (IF_CASES_TAC >- fs []) >>
  simp [opc_def,instr_def] >> fs [DecodeReg_imm_def] >>
  Q.ABBREV_TAC `i = word_at_addr ag.MEM (align_addr ag.PC)` >>
  Cases_on `word_bit 31 i` >> fs [] >>
  `~((5 >< 0) i <+ 10w)` by FULL_BBLAST_TAC >> fs []
QED


(* Decode the func *)
(** if Decode got Normal(fAdd,_,_,_), the func is 0w **)
Theorem ag32_Decode_Normal_fAdd_func_0w:
  !ag wi a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Normal (fAdd,wi,a,b) ==>
    func ag = 0w
Proof
  rw [] >> `opc ag = 0w` by fs [ag32_Decode_Normal_opc_0w] >>
  UNDISCH_TAC ``Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Normal (fAdd,wi,a,b)`` >>
  get_func_from_decode_tac
QED

(** if Decode got Normal(fAddWithCarry,_,_,_), the func is 1w **)
Theorem ag32_Decode_Normal_fAddWithCarry_func_1w:
  !ag wi a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Normal (fAddWithCarry,wi,a,b) ==>
    func ag = 1w
Proof
  rw [] >> `opc ag = 0w` by fs [ag32_Decode_Normal_opc_0w] >>
  UNDISCH_TAC ``Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Normal (fAddWithCarry,wi,a,b)`` >>
  get_func_from_decode_tac
QED

(** if Decode got Normal(fSub,_,_,_), the func is 2w **)
Theorem ag32_Decode_Normal_fSub_func_2w:
  !ag wi a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Normal (fSub,wi,a,b) ==>
    func ag = 2w
Proof
  rw [] >> `opc ag = 0w` by fs [ag32_Decode_Normal_opc_0w] >>
  UNDISCH_TAC ``Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Normal (fSub,wi,a,b)`` >>
  get_func_from_decode_tac
QED

(** if Decode got Normal(f,_,_,_) and f is not fAdd or fAddWithCarry, the func is not 0w or 1w **)
Theorem ag32_Decode_Normal_func_not_0w_1w:
  !ag f wi a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Normal (f,wi,a,b) ==>
    f <> fAdd ==>
    f <> fAddWithCarry ==>
    (func ag <> 0w) /\ (func ag <> 1w)
Proof
  rw [] >> `opc ag = 0w` by fs [ag32_Decode_Normal_opc_0w] >>
  UNDISCH_TAC ``Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Normal (f,wi,a,b)`` >>
  get_func_from_decode_tac
QED

(** if Decode got Normal(f,_,_,_) and f is not fAdd, fAddWithCarry, fSub, the func is not 0/1/2w **)
Theorem ag32_Decode_Normal_func_not_0w_1w_2w:
  !ag f wi a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Normal (f,wi,a,b) ==>
    f <> fAdd ==>
    f <> fAddWithCarry ==>
    f <> fSub ==>
    (func ag <> 0w) /\ (func ag <> 1w) /\ (func ag <> 2w)
Proof
  rw [] >> `opc ag = 0w` by fs [ag32_Decode_Normal_opc_0w] >>
  UNDISCH_TAC ``Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Normal (f,wi,a,b)`` >>
  get_func_from_decode_tac
QED

(** if Decode got Out(fAdd,_,_,_), the func is 0w **)
Theorem ag32_Decode_Out_fAdd_func_0w:
  !ag wi a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Out (fAdd,wi,a,b) ==>
    func ag = 0w
Proof
  rw [] >> `opc ag = 6w` by fs [ag32_Decode_Out_opc_6w] >>
  UNDISCH_TAC ``Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Out (fAdd,wi,a,b)`` >>
  get_func_from_decode_tac
QED

(** if Decode got Out(fAddWithCarry,_,_,_), the func is 1w **)
Theorem ag32_Decode_Out_fAddWithCarry_func_1w:
  !ag wi a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Out (fAddWithCarry,wi,a,b) ==>
    func ag = 1w
Proof
  rw [] >> `opc ag = 6w` by fs [ag32_Decode_Out_opc_6w] >>
  UNDISCH_TAC ``Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Out (fAddWithCarry,wi,a,b)`` >>
  get_func_from_decode_tac
QED

(** if Decode got Out(fSub,_,_,_), the func is 2w **)
Theorem ag32_Decode_Out_fSub_func_2w:
  !ag wi a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Out (fSub,wi,a,b) ==>
    func ag = 2w
Proof
  rw [] >> `opc ag = 6w` by fs [ag32_Decode_Out_opc_6w] >>
  UNDISCH_TAC ``Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Out (fSub,wi,a,b)`` >>
  get_func_from_decode_tac
QED

(** if Decode got Out(f,_,_,_) and f is not fAdd or fAddWithCarry, the func is not 0w or 1w **)
Theorem ag32_Decode_Out_func_not_0w_1w:
  !ag f wi a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Out (f,wi,a,b) ==>
    f <> fAdd ==>
    f <> fAddWithCarry ==>
    (func ag <> 0w) /\ (func ag <> 1w)
Proof
  rw [] >> `opc ag = 6w` by fs [ag32_Decode_Out_opc_6w] >>
  UNDISCH_TAC ``Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Out (f,wi,a,b)`` >>
  get_func_from_decode_tac
QED

(** if Decode got Out(f,_,_,_) and f is not fAdd/fAddWithCarry/fSub, the func is not 0/1/2w **)
Theorem ag32_Decode_Out_func_not_0w_1w_2w:
  !ag f wi a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Out (f,wi,a,b) ==>
    f <> fAdd ==>
    f <> fAddWithCarry ==>
    f <> fSub ==>
    (func ag <> 0w) /\ (func ag <> 1w) /\ (func ag <> 2w)
Proof
  rw [] >> `opc ag = 6w` by fs [ag32_Decode_Out_opc_6w] >>
  UNDISCH_TAC ``Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Out (f,wi,a,b)`` >>
  get_func_from_decode_tac
QED

(** if Decode got Jump(fAdd,_,_), the func is 0w **)
Theorem ag32_Decode_Jump_fAdd_func_0w:
  !ag wi a.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Jump (fAdd,wi,a) ==>
    func ag = 0w
Proof
  rw [] >> `opc ag = 9w` by fs [ag32_Decode_Jump_opc_9w] >>
  UNDISCH_TAC ``Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Jump (fAdd,wi,a)`` >>
  get_func_from_decode_tac
QED

(** if Decode got Jump(fAddWithCarry,_,_), the func is 1w **)
Theorem ag32_Decode_Jump_fAddWithCarry_func_1w:
  !ag wi a.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Jump (fAddWithCarry,wi,a) ==>
    func ag = 1w
Proof
  rw [] >> `opc ag = 9w` by fs [ag32_Decode_Jump_opc_9w] >>
  UNDISCH_TAC ``Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Jump (fAddWithCarry,wi,a)`` >>
  get_func_from_decode_tac
QED

(** if Decode got Jump(fSub,_,_), the func is 2w **)
Theorem ag32_Decode_Jump_fSub_func_2w:
  !ag wi a.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Jump (fSub,wi,a) ==>
    func ag = 2w
Proof
  rw [] >> `opc ag = 9w` by fs [ag32_Decode_Jump_opc_9w] >>
  UNDISCH_TAC ``Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Jump (fSub,wi,a)`` >>
  get_func_from_decode_tac
QED

(** if Decode got Jump(f,_,_) and f is not fAdd or fAddWithCarry, the func is not 0w or 1w **)
Theorem ag32_Decode_Jump_func_not_0w_1w:
  !ag f wi a.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Jump (f,wi,a) ==>
    f <> fAdd ==>
    f <> fAddWithCarry ==>
    (func ag <> 0w) /\ (func ag <> 1w)
Proof
  rw [] >> `opc ag = 9w` by fs [ag32_Decode_Jump_opc_9w] >>
  UNDISCH_TAC ``Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Jump (f,wi,a)`` >>
  get_func_from_decode_tac
QED

(** if Decode got Jump(f,_,_) and f is not fAdd/fAddWithCarry/fSub, the func is not 0/1/2w **)
Theorem ag32_Decode_Jump_func_not_0w_1w_2w:
  !ag f wi a.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Jump (f,wi,a) ==>
    f <> fAdd ==>
    f <> fAddWithCarry ==>
    f <> fSub ==>
    (func ag <> 0w) /\ (func ag <> 1w) /\ (func ag <> 2w)
Proof
  rw [] >> `opc ag = 9w` by fs [ag32_Decode_Jump_opc_9w] >>
  UNDISCH_TAC ``Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Jump (f,wi,a)`` >>
  get_func_from_decode_tac
QED

(** if Decode got JumpIfZero(fAdd,_,_,_), the func is 0w **)
Theorem ag32_Decode_JumpIfZero_fAdd_func_0w:
  !ag wi a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = JumpIfZero (fAdd,wi,a,b) ==>
    func ag = 0w
Proof
  rw [] >> `opc ag = 10w` by fs [ag32_Decode_JumpIfZero_opc_10w] >>
  UNDISCH_TAC ``Decode (word_at_addr ag.MEM (align_addr ag.PC)) = JumpIfZero (fAdd,wi,a,b)`` >>
  get_func_from_decode_tac
QED

(** if Decode got JumpIfZero(fAddWithCarry,_,_), the func is 1w **)
Theorem ag32_Decode_JumpIfZero_fAddWithCarry_func_1w:
  !ag wi a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = JumpIfZero (fAddWithCarry,wi,a,b) ==>
    func ag = 1w
Proof
  rw [] >> `opc ag = 10w` by fs [ag32_Decode_JumpIfZero_opc_10w] >>
  UNDISCH_TAC ``Decode (word_at_addr ag.MEM (align_addr ag.PC)) = JumpIfZero (fAddWithCarry,wi,a,b)`` >>
  get_func_from_decode_tac
QED

(** if Decode got JumpIfZero(fSub,_,_), the func is 2w **)
Theorem ag32_Decode_JumpIfZero_fSub_func_2w:
  !ag wi a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = JumpIfZero (fSub,wi,a,b) ==>
    func ag = 2w
Proof
  rw [] >> `opc ag = 10w` by fs [ag32_Decode_JumpIfZero_opc_10w] >>
  UNDISCH_TAC ``Decode (word_at_addr ag.MEM (align_addr ag.PC)) = JumpIfZero (fSub,wi,a,b)`` >>
  get_func_from_decode_tac
QED

(** if Decode got JumpIfZero(f,_,_,_) and f is not fAdd or fAddWithCarry,
    the func is not 0w or 1w **)
Theorem ag32_Decode_JumpIfZero_func_not_0w_1w:
  !ag f wi a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = JumpIfZero (f,wi,a,b) ==>
    f <> fAdd ==>
    f <> fAddWithCarry ==>
    (func ag <> 0w) /\ (func ag <> 1w)
Proof
  rw [] >> `opc ag = 10w` by fs [ag32_Decode_JumpIfZero_opc_10w] >>
  UNDISCH_TAC ``Decode (word_at_addr ag.MEM (align_addr ag.PC)) = JumpIfZero (f,wi,a,b)`` >>
  get_func_from_decode_tac
QED

(** if Decode got JumpIfZero(f,_,_,_) and f is not fAdd/fAddWithCarry/fSub,
    the func is not 0/1/2w **)
Theorem ag32_Decode_JumpIfZero_func_not_0w_1w_2w:
  !ag f wi a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = JumpIfZero (f,wi,a,b) ==>
    f <> fAdd ==>
    f <> fAddWithCarry ==>
    f <> fSub ==>
    (func ag <> 0w) /\ (func ag <> 1w) /\ (func ag <> 2w)
Proof
  rw [] >> `opc ag = 10w` by fs [ag32_Decode_JumpIfZero_opc_10w] >>
  UNDISCH_TAC ``Decode (word_at_addr ag.MEM (align_addr ag.PC)) = JumpIfZero (f,wi,a,b)`` >>
  get_func_from_decode_tac
QED

(** if Decode got JumpIfNotZero(fAdd,_,_,_), the func is 0w **)
Theorem ag32_Decode_JumpIfNotZero_fAdd_func_0w:
  !ag wi a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = JumpIfNotZero (fAdd,wi,a,b) ==>
    func ag = 0w
Proof
  rw [] >> `opc ag = 11w` by fs [ag32_Decode_JumpIfNotZero_opc_11w] >>
  UNDISCH_TAC ``Decode (word_at_addr ag.MEM (align_addr ag.PC)) = JumpIfNotZero (fAdd,wi,a,b)`` >>
  get_func_from_decode_tac
QED

(** if Decode got JumpIfNotZero(fAddWithCarry,_,_), the func is 1w **)
Theorem ag32_Decode_JumpIfNotZero_fAddWithCarry_func_1w:
  !ag wi a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = JumpIfNotZero (fAddWithCarry,wi,a,b) ==>
    func ag = 1w
Proof
  rw [] >> `opc ag = 11w` by fs [ag32_Decode_JumpIfNotZero_opc_11w] >>
  UNDISCH_TAC ``Decode (word_at_addr ag.MEM (align_addr ag.PC)) = JumpIfNotZero (fAddWithCarry,wi,a,b)`` >>
  get_func_from_decode_tac
QED

(** if Decode got JumpIfNotZero(fSub,_,_), the func is 2w **)
Theorem ag32_Decode_JumpIfNotZero_fSub_func_2w:
  !ag wi a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = JumpIfNotZero (fSub,wi,a,b) ==>
    func ag = 2w
Proof
  rw [] >> `opc ag = 11w` by fs [ag32_Decode_JumpIfNotZero_opc_11w] >>
  UNDISCH_TAC ``Decode (word_at_addr ag.MEM (align_addr ag.PC)) = JumpIfNotZero (fSub,wi,a,b)`` >>
  get_func_from_decode_tac
QED

(** if Decode got JumpIfNotZero(f,_,_,_) and f is not fAdd or fAddWithCarry,
    the func is not 0w or 1w **)
Theorem ag32_Decode_JumpIfNotZero_func_not_0w_1w:
  !ag f wi a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = JumpIfNotZero (f,wi,a,b) ==>
    f <> fAdd ==>
    f <> fAddWithCarry ==>
    (func ag <> 0w) /\ (func ag <> 1w)
Proof
  rw [] >> `opc ag = 11w` by fs [ag32_Decode_JumpIfNotZero_opc_11w] >>
  UNDISCH_TAC ``Decode (word_at_addr ag.MEM (align_addr ag.PC)) = JumpIfNotZero (f,wi,a,b)`` >>
  get_func_from_decode_tac
QED

(** if Decode got JumpIfNotZero(f,_,_,_) and f is not fAdd/fAddWithCarry/fSub,
    the func is not 0/1/2w **)
Theorem ag32_Decode_JumpIfNotZero_func_not_0w_1w_2w:
  !ag f wi a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = JumpIfNotZero (f,wi,a,b) ==>
    f <> fAdd ==>
    f <> fAddWithCarry ==>
    f <> fSub ==>
    (func ag <> 0w) /\ (func ag <> 1w) /\ (func ag <> 2w)
Proof
  rw [] >> `opc ag = 11w` by fs [ag32_Decode_JumpIfNotZero_opc_11w] >>
  UNDISCH_TAC ``Decode (word_at_addr ag.MEM (align_addr ag.PC)) = JumpIfNotZero (f,wi,a,b)`` >>
  get_func_from_decode_tac
QED


(* decode the addrW *)
(** Acc **)
Theorem ag32_Decode_Acc_addrW[local]:
  !ag wi a.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Accelerator (wi,a) ==>
    addrW ag = wi
Proof
  get_addrW_from_decode_tac
QED

(** In **)
Theorem ag32_Decode_In_addrW[local]:
  !ag c.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = In c ==>
    addrW ag = c
Proof
  get_addrW_from_decode_tac
QED

(** Jump **)
Theorem ag32_Decode_Jump_addrW[local]:
  !ag a f wi.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Jump (f,wi,a) ==>
    addrW ag = wi
Proof
  get_addrW_from_decode_tac
QED

(** LoadConstant **)
Theorem ag32_Decode_LoadConstant_addrW[local]:
  !ag w1 w2 w3.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = LoadConstant (w1,w2,w3) ==>
    addrW ag = w1
Proof
  get_addrW_from_decode_tac
QED

(** LoadUpperConstant **)
Theorem ag32_Decode_LoadUpperConstant_addrW[local]:
  !ag w1 w2.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = LoadUpperConstant (w1,w2) ==>
    addrW ag = w1
Proof
  get_addrW_from_decode_tac
QED

(** LoadMEM **)
Theorem ag32_Decode_LoadMEM_addrW[local]:
  !ag wi a.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = LoadMEM (wi,a) ==>
    addrW ag = wi
Proof
  get_addrW_from_decode_tac
QED

(** LoadMEMByte **)
Theorem ag32_Decode_LoadMEMByte_addrW[local]:
  !ag wi a.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = LoadMEMByte (wi,a) ==>
    addrW ag = wi
Proof
  get_addrW_from_decode_tac
QED

(** Normal **)
Theorem ag32_Decode_Normal_addrW[local]:
  !ag func wi a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Normal (func,wi,a,b) ==>
    addrW ag = wi
Proof
  get_addrW_from_decode_tac >>
  rename1 `v2w v1 = 0w` >>
  Cases_on `v2w v1 :word1 = 0w` >> fs []
QED

(** Out **)
Theorem ag32_Decode_Out_addrW[local]:
  !ag func wi a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Out (func,wi,a,b) ==>
    addrW ag = wi
Proof
  get_addrW_from_decode_tac
QED

(** Shift **)
Theorem ag32_Decode_Shift_addrW[local]:
  !ag sh wi a b.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Shift (sh,wi,a,b) ==>
    addrW ag = wi
Proof
  get_addrW_from_decode_tac
QED

(* decode the dataA *)
(** Normal **)
Theorem ag32_Decode_Normal_dataA:
  !ag a b f wi.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Normal (f,wi,a,b) ==>
    (dataA ag = ri2word a ag)
Proof
  get_data_simp_tac >>
  rw [dataA_def,instr_def]
QED

(** Out **)
Theorem ag32_Decode_Out_dataA:
  !ag a b f wi.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Out (f,wi,a,b) ==>
    (dataA ag = ri2word a ag)
Proof
  get_data_simp_tac >>
  rw [dataA_def,instr_def]
QED

(** Jump **)
Theorem ag32_Decode_Jump_dataA:
  !ag a f wi.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Jump (f,wi,a) ==>
    dataA ag = ri2word a ag
Proof
  get_data_simp_tac >>
  rw [dataA_def,instr_def]
QED

(** JumpIfNotZero **)
Theorem ag32_Decode_JumpIfNotZero_dataA:
  !ag a b f wi.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = JumpIfNotZero (f,wi,a,b) ==>
    (dataA ag = ri2word a ag)
Proof
  get_data_simp_tac >>
  rw [dataA_def,instr_def]
QED

(** JumpIfZero **)
Theorem ag32_Decode_JumpIfZero_dataA:
  !ag a b f wi.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = JumpIfZero (f,wi,a,b) ==>
    (dataA ag = ri2word a ag)
Proof
  get_data_simp_tac >>
  rw [dataA_def,instr_def]
QED


(** dataB **)
(** Normal **)
Theorem ag32_Decode_Normal_dataB:
  !ag a b f wi.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Normal (f,wi,a,b) ==>
    (dataB ag = ri2word b ag)
Proof
  get_data_simp_tac >>
  rw [dataB_def,instr_def]
QED

(** Out **)
Theorem ag32_Decode_Out_dataB:
  !ag a b f wi.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = Out (f,wi,a,b) ==>
    (dataB ag = ri2word b ag)
Proof
  get_data_simp_tac >>
  rw [dataB_def,instr_def]
QED

(** JumpIfNotZero **)
Theorem ag32_Decode_JumpIfNotZero_dataB:
  !ag a b f wi.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = JumpIfNotZero (f,wi,a,b) ==>
    (dataB ag = ri2word b ag)
Proof
  get_data_simp_tac >>
  rw [dataB_def,instr_def]
QED

(** JumpIfZero **)
Theorem ag32_Decode_JumpIfZero_dataB:
  !ag a b f wi.
    Decode (word_at_addr ag.MEM (align_addr ag.PC)) = JumpIfZero (f,wi,a,b) ==>
    (dataB ag = ri2word b ag)
Proof
  get_data_simp_tac >>
  rw [dataB_def,instr_def]
QED


(* if the current instr does not jump, the next pc = current pc + 4w *)
Theorem ag32_not_isJump_isa_Next_PC:
  !ag.
    ~isJump_isa ag ==>
    ag.PC + 4w = (Next ag).PC
Proof
  rw [Next_def,isJump_isa_def] >> rw [GSYM word_at_addr_def,GSYM align_addr_def] >>
  Cases_on `Decode (word_at_addr ag.MEM (align_addr ag.PC))` >-
   (PairCases_on `p` >> rw [Run_def,dfn'Accelerator_def,incPC_def]) >-
   rw [Run_def,dfn'In_def,incPC_def] >-
   rw [Run_def,dfn'Interrupt_def,incPC_def] >-
   (** Jump **)
   (PairCases_on `p` >> fs [ag32_Decode_Jump_opc_9w]) >-
   (** JumpIfNotZero **)
   (PairCases_on `p` >>
    `opc ag = 11w` by fs [ag32_Decode_JumpIfNotZero_opc_11w] >>
    fs [Run_def,dfn'JumpIfNotZero_def,ALU_res_def,ALU_input1_def,ALU_input2_def] >>
    UNDISCH_TAC ``Decode (word_at_addr ag.MEM (align_addr ag.PC)) = JumpIfNotZero (p0,p1,p2,p3)`` >> 
    simp [Decode_def,boolify32_def] >>
    CONV_TAC v2w_word_bit_list_cleanup >>
    qpat_abbrev_tac `dc = DecodeReg_imm (_,_)` >> rw [] >-
     (fs [func_def,instr_def,dataA_def,dataB_def] >>
      qpat_abbrev_tac `alu = ALU (_,_,_)` >>
      Cases_on `alu ag` >> fs [incPC_def,Abbr `alu`] >> METIS_TAC [ALU_state_eq_after]) >>
    Cases_on `dc` >> fs [] >>
    Q.ABBREV_TAC `op = (5 >< 0) (word_at_addr ag.MEM (align_addr ag.PC))` >>
    Cases_on_word_value `op` >> fs []) >-
   (** JumpIfZero **)
   (PairCases_on `p` >>
    `opc ag = 10w` by fs [ag32_Decode_JumpIfZero_opc_10w] >>
    fs [Run_def,dfn'JumpIfZero_def,ALU_res_def,ALU_input1_def,ALU_input2_def] >>
    UNDISCH_TAC ``Decode (word_at_addr ag.MEM (align_addr ag.PC)) = JumpIfZero (p0,p1,p2,p3)`` >> 
    simp [Decode_def,boolify32_def] >>
    CONV_TAC v2w_word_bit_list_cleanup >>
    qpat_abbrev_tac `dc = DecodeReg_imm (_,_)` >> rw [] >-
     (fs [func_def,instr_def,dataA_def,dataB_def] >>
      qpat_abbrev_tac `alu = ALU (_,_,_)` >>
      Cases_on `alu ag` >> fs [incPC_def,Abbr `alu`] >> METIS_TAC [ALU_state_eq_after]) >>
    Cases_on `dc` >> fs [] >>
    Q.ABBREV_TAC `op = (5 >< 0) (word_at_addr ag.MEM (align_addr ag.PC))` >>
    Cases_on_word_value `op` >> fs []) >-
   (PairCases_on `p` >> rw [Run_def,dfn'LoadConstant_def,incPC_def]) >-
   (PairCases_on `p` >> rw [Run_def,dfn'LoadMEM_def,incPC_def]) >-
   (PairCases_on `p` >> rw [Run_def,dfn'LoadMEMByte_def,incPC_def]) >-
   (PairCases_on `p` >> rw [Run_def,dfn'LoadUpperConstant_def,incPC_def]) >-
   (PairCases_on `p` >> rw [Run_def,dfn'Normal_def,norm_def,incPC_def,ALU_def] >>
    Cases_on `p0` >> rw []) >-
   (PairCases_on `p` >> rw [Run_def,dfn'Out_def,norm_def,incPC_def,ALU_def] >>
    Cases_on `p0` >> rw []) >-
   fs [ag32_Decode_ReservedInstr_opc_15w] >-
   (PairCases_on `p` >> rw [Run_def,dfn'Shift_def,incPC_def]) >-
   (PairCases_on `p` >> rw [Run_def,dfn'StoreMEM_def,incPC_def]) >> 
   PairCases_on `p` >> rw [Run_def,dfn'StoreMEMByte_def,incPC_def]
QED


(* word_at_addr and mem_update *)
Theorem word_at_addr_not_changed_after_mem_update:
  !mem adr adr' wdata wstrb.
    align_addr adr <> align_addr adr' ==>
    word_at_addr (mem_update mem (align_addr adr) wdata wstrb) (align_addr adr') =
    word_at_addr mem (align_addr adr')
Proof
  rw [mem_update_def] >>
  fs [word_at_addr_def,align_addr_def,combinTheory.APPLY_UPDATE_THM] >>
  fs [addr_add,addr_concat]
QED


(* word_at_addr is unchanged after a memory write *)
Theorem word_at_addr_not_changed_after_write_mem:
  !adr n a.
    is_wrMEM_isa (FUNPOW Next (n-1) a) ==>
    align_addr (dataB (FUNPOW Next (n-1) a)) <> (align_addr adr) ==>
    word_at_addr (FUNPOW Next (n-1) a).MEM (align_addr adr) =
    word_at_addr (FUNPOW Next n a).MEM (align_addr adr)
Proof
  Cases_on `n` >> rw [FUNPOW_SUC] >>
  Q.ABBREV_TAC `a0 = FUNPOW Next n' a` >>
  fs [is_wrMEM_isa_def] >-
   ((** StoreMem **)
   Cases_on `opc a0 = 2w` >> fs [] >>
   rw [Next_def,Run_def] >>
   rw [GSYM word_at_addr_def,GSYM align_addr_def] >>
   `Decode (word_at_addr a0.MEM (align_addr a0.PC)) =
   StoreMEM (DecodeReg_imm (v2w [word_bit 23 (word_at_addr a0.MEM (align_addr a0.PC))],
                            (22 >< 17) (word_at_addr a0.MEM (align_addr a0.PC))),
             DecodeReg_imm (v2w [word_bit 16 (word_at_addr a0.MEM (align_addr a0.PC))],
                            (15 >< 10) (word_at_addr a0.MEM (align_addr a0.PC))))`
     by fs [ag32_opc_2w_Decode_StoreMEM] >>
   fs [dataB_def] >>
   qpat_abbrev_tac `da = DecodeReg_imm (_,_)` >>
   qpat_abbrev_tac `db = DecodeReg_imm (_,_)` >>
   rw [dfn'StoreMEM_def,incPC_def] >>
   rw [word_at_addr_def] >> fs [align_addr_def] >> fs [combinTheory.APPLY_UPDATE_THM] >>
   rw [addr_add,addr_concat]) >>
  Cases_on `opc a0 = 3w` >> fs [] >>
  rw [Next_def,Run_def] >>
  rw [GSYM word_at_addr_def,GSYM align_addr_def] >>
  `Decode (word_at_addr a0.MEM (align_addr a0.PC)) =
  StoreMEMByte (DecodeReg_imm (v2w [word_bit 23 (word_at_addr a0.MEM (align_addr a0.PC))],
                               (22 >< 17) (word_at_addr a0.MEM (align_addr a0.PC))),
                DecodeReg_imm (v2w [word_bit 16 (word_at_addr a0.MEM (align_addr a0.PC))],
                               (15 >< 10) (word_at_addr a0.MEM (align_addr a0.PC))))`
    by fs [ag32_opc_3w_Decode_StoreMEMByte] >>
  fs [dataB_def] >>
  qpat_abbrev_tac `da = DecodeReg_imm (_,_)` >>
  qpat_abbrev_tac `db = DecodeReg_imm (_,_)` >>
  rw [dfn'StoreMEMByte_def,incPC_def] >>
  rw [word_at_addr_def] >> fs [align_addr_def] >> fs [combinTheory.APPLY_UPDATE_THM] >>
  `ri2word db a0 = (31 >< 2) (ri2word db a0) @@ (1 >< 0) (ri2word db a0)` by BBLAST_TAC >>
  `(31 >< 2) (ri2word db a0) <> (31 >< 2) adr` by fs [addr_concat] >>
  simp [addr_add] >> METIS_TAC [addr_concat]
QED

(* if the instr is a not write operation, then fetched value is not affected *)
Theorem word_at_addr_not_changed_after_normal_instrs:
  !adr n a.
    ~is_wrMEM_isa (FUNPOW Next (n-1) a) ==>
    word_at_addr (FUNPOW Next (n-1) a).MEM adr =
    word_at_addr (FUNPOW Next n a).MEM adr
Proof
  Cases_on `n` >> rw [FUNPOW_SUC] >>
  Q.ABBREV_TAC `a0 = FUNPOW Next n' a` >>
  fs [is_wrMEM_isa_def] >>
  rw [Next_def,GSYM word_at_addr_def,GSYM align_addr_def] >>
  Cases_on `Decode (word_at_addr a0.MEM (align_addr a0.PC))` >-
   (PairCases_on `p` >> rw [Run_def,dfn'Accelerator_def,incPC_def]) >-
   (rw [Run_def,dfn'In_def,incPC_def]) >-
   (rw [Run_def,dfn'Interrupt_def,incPC_def]) >-
   (PairCases_on `p` >> rw [Run_def,dfn'Jump_def,ALU_def] >> Cases_on `p0` >> fs []) >-
   (PairCases_on `p` >> rw [Run_def,dfn'JumpIfNotZero_def,incPC_def] >>
    qpat_abbrev_tac `alu = ALU _ _` >>
    Cases_on `alu` >> rw [] >>
    METIS_TAC [ALU_state_eq_after]) >-
   (PairCases_on `p` >> rw [Run_def,dfn'JumpIfZero_def,incPC_def] >>
    qpat_abbrev_tac `alu = ALU _ _` >>
    Cases_on `alu` >> rw [] >>
    METIS_TAC [ALU_state_eq_after]) >-
   (PairCases_on `p` >> rw [Run_def,dfn'LoadConstant_def,incPC_def]) >-
   (PairCases_on `p` >> rw [Run_def,dfn'LoadMEM_def,incPC_def]) >-
   (PairCases_on `p` >> rw [Run_def,dfn'LoadMEMByte_def,incPC_def]) >-
   (PairCases_on `p` >> rw [Run_def,dfn'LoadUpperConstant_def,incPC_def]) >-
   (PairCases_on `p` >> rw [Run_def,dfn'Normal_def,norm_def,incPC_def] >>
    qpat_abbrev_tac `alu = ALU _ _` >>
    Cases_on `alu` >> rw [] >>
    METIS_TAC [ALU_state_eq_after]) >-
   (PairCases_on `p` >> rw [Run_def,dfn'Out_def,norm_def,incPC_def] >>
    qpat_abbrev_tac `alu = ALU _ _` >>
    Cases_on `alu` >> rw [] >>
    METIS_TAC [ALU_state_eq_after]) >-
   rw [Run_def] >-
   (PairCases_on `p` >> rw [Run_def,dfn'Shift_def,incPC_def]) >-
   (PairCases_on `p` >> fs [ag32_Decode_StoreMEM_opc_2w]) >>
   PairCases_on `p` >> fs [ag32_Decode_StoreMEMByte_opc_3w]
QED


(* Given the self-modified condition, 3 instrs' fetched values after an instr are not affected. *)
Theorem SC_self_mod_isa_not_affect_fetched_instr:
  !a i j.
    SC_self_mod_isa a ==>
    i > j ==>
    i < j + 4 ==>
    word_at_addr (FUNPOW Next (i-1) a).MEM (align_addr (FUNPOW Next (i-1) a).PC)  =
    word_at_addr (FUNPOW Next j a).MEM (align_addr (FUNPOW Next (i-1) a).PC)
Proof
  rw [SC_self_mod_isa_def] >>
  `i = j + 1 \/ i = j + 2 \/ i = j + 3` by fs [] >> rw [] >-
   (Q.ABBREV_TAC `n' = j + 1` >>
    `j = n' - 1` by fs [Abbr `n'`] >> fs [] >>
    Cases_on `is_wrMEM_isa (FUNPOW Next (n'-1) a)` >-
     (`n'+1 > n' /\ n'+1 < n'+4` by rw [] >>
      `align_addr (FUNPOW Next (n'+1-1) a).PC <>
       align_addr (dataB (FUNPOW Next (n'−1) a))` by fs [] >>
      fs [word_at_addr_not_changed_after_write_mem]) >>
    fs [word_at_addr_not_changed_after_normal_instrs]) >>
  Q.ABBREV_TAC `n' = j + 1` >>
  `n' <> 0` by fs [Abbr `n'`] >>
  `j = n' - 1` by fs [Abbr `n'`] >> fs [] >>
  Cases_on `is_wrMEM_isa (FUNPOW Next (n'-1) a)` >-
   (`n'+2 > n' /\ n'+2 < n'+4` by rw [] >>
    `align_addr (FUNPOW Next (n'+2-1) a).PC <>
     align_addr (dataB (FUNPOW Next (n'−1) a))` by fs [] >>
    `word_at_addr (FUNPOW Next (n' − 1) a).MEM
     (align_addr (FUNPOW Next (n' + 1) a).PC) =
    word_at_addr (FUNPOW Next n' a).MEM
     (align_addr (FUNPOW Next (n' + 1) a).PC)`                        
      by fs [word_at_addr_not_changed_after_write_mem] >> fs [] >>
    Q.ABBREV_TAC `n'' = n' + 1` >>
    `n' = n'' - 1` by fs [Abbr `n''`] >> fs [] >>
    Cases_on `is_wrMEM_isa (FUNPOW Next (n''-1) a)` >-
     (`n''+1 > n'' /\ n''+1 < n''+4` by rw [] >>
      `align_addr (FUNPOW Next (n''+1-1) a).PC <>
       align_addr (dataB (FUNPOW Next (n''−1) a))` by fs [] >>
      fs [word_at_addr_not_changed_after_write_mem]) >>
    fs [word_at_addr_not_changed_after_normal_instrs]) >>
  `word_at_addr (FUNPOW Next (n' − 1) a).MEM
   (align_addr (FUNPOW Next (n' + 1) a).PC) =
  word_at_addr (FUNPOW Next n' a).MEM
  (align_addr (FUNPOW Next (n' + 1) a).PC)`                        
   by fs [word_at_addr_not_changed_after_normal_instrs] >> fs [] >>
  Q.ABBREV_TAC `n'' = n' + 1` >>          
  `n' = n'' - 1` by fs [Abbr `n''`] >> fs [] >>
  Cases_on `is_wrMEM_isa (FUNPOW Next (n''-1) a)` >-
    (`n''+1 > n'' /\ n''+1 < n''+4` by rw [] >>
     `align_addr (FUNPOW Next (n''+1-1) a).PC <>
     align_addr (dataB (FUNPOW Next (n''−1) a))` by fs [] >>
    fs [word_at_addr_not_changed_after_write_mem]) >>
  fs [word_at_addr_not_changed_after_normal_instrs]          
QED

(** similiar theorem as above but for j-1 **)
Theorem SC_self_mod_isa_not_affect_fetched_instr_extra:
  !a i j.
    SC_self_mod_isa a ==>
    i > j ==>
    i < j + 4 ==>
    word_at_addr (FUNPOW Next (i-1) a).MEM (align_addr (FUNPOW Next (i-1) a).PC) =
    word_at_addr (FUNPOW Next (j-1) a).MEM (align_addr (FUNPOW Next (i-1) a).PC)
Proof
  rw [SC_self_mod_isa_def] >>
  `i = j + 1 \/ i = j + 2 \/ i = j + 3` by fs [] >> rw [] >-
   (Cases_on `is_wrMEM_isa (FUNPOW Next (j-1) a)` >-
     (`align_addr (FUNPOW Next (j+1-1) a).PC <>
       align_addr (dataB (FUNPOW Next (j−1) a))` by fs [] >>
      fs [word_at_addr_not_changed_after_write_mem]) >>
    fs [word_at_addr_not_changed_after_normal_instrs]) >-
   (Cases_on `is_wrMEM_isa (FUNPOW Next (j-1) a)` >-
     (`j+2 > j /\ j+2 < j+4` by rw [] >>
      `align_addr (FUNPOW Next (j+2-1) a).PC <>
       align_addr (dataB (FUNPOW Next (j−1) a))` by fs [] >>
      `word_at_addr (FUNPOW Next (j − 1) a).MEM (align_addr (FUNPOW Next (j + 1) a).PC) =
      word_at_addr (FUNPOW Next j a).MEM (align_addr (FUNPOW Next (j + 1) a).PC)`
        by fs [word_at_addr_not_changed_after_write_mem] >> fs [] >>
      Q.ABBREV_TAC `j' = j + 1` >>
      `j = j' - 1` by fs [Abbr `j'`] >> fs [] >>
      Cases_on `is_wrMEM_isa (FUNPOW Next (j'-1) a)` >-
       (`j'+1 > j /\ j'+1 < j+4` by rw [] >>
        `align_addr (FUNPOW Next (j'+1-1) a).PC <>
         align_addr (dataB (FUNPOW Next (j'−1) a))` by fs [] >>
        fs [word_at_addr_not_changed_after_write_mem]) >>
      fs [word_at_addr_not_changed_after_normal_instrs]) >>
    `word_at_addr (FUNPOW Next (j − 1) a).MEM (align_addr (FUNPOW Next (j + 1) a).PC) =
    word_at_addr (FUNPOW Next j a).MEM (align_addr (FUNPOW Next (j + 1) a).PC)`                        
      by fs [word_at_addr_not_changed_after_normal_instrs] >> fs [] >>
    Q.ABBREV_TAC `j' = j + 1` >>
    `j = j' - 1` by fs [Abbr `j'`] >> fs [] >>
    Cases_on `is_wrMEM_isa (FUNPOW Next (j'-1) a)` >-
     (`j'+1 > j' /\ j'+1 < j'+4` by rw [] >>
      `align_addr (FUNPOW Next (j'+1-1) a).PC <>
       align_addr (dataB (FUNPOW Next (j'−1) a))` by fs [] >>
      fs [word_at_addr_not_changed_after_write_mem]) >>
    fs [word_at_addr_not_changed_after_normal_instrs]) >>
  Cases_on `is_wrMEM_isa (FUNPOW Next (j-1) a)` >-
   (`j+3 > j /\ j+3 < j+4` by rw [] >>
    `align_addr (FUNPOW Next (j+3-1) a).PC <> align_addr (dataB (FUNPOW Next (j−1) a))` by fs [] >>
    `word_at_addr (FUNPOW Next (j − 1) a).MEM (align_addr (FUNPOW Next (j + 2) a).PC) =
    word_at_addr (FUNPOW Next j a).MEM (align_addr (FUNPOW Next (j + 2) a).PC)`
      by fs [word_at_addr_not_changed_after_write_mem] >> fs [] >>
    Q.ABBREV_TAC `j' = j + 1` >>
    `j' <> 0` by fs [Abbr `j'`] >>
    `j = j' - 1` by fs [Abbr `j'`] >> fs [] >>
    Cases_on `is_wrMEM_isa (FUNPOW Next (j'-1) a)` >-
     (`j'+2 > j' /\ j'+2 < j'+4` by rw [] >>
      `align_addr (FUNPOW Next (j'+2-1) a).PC <> align_addr (dataB (FUNPOW Next (j'−1) a))` by fs [] >>
      `word_at_addr (FUNPOW Next (j' − 1) a).MEM (align_addr (FUNPOW Next (j' + 1) a).PC) =
      word_at_addr (FUNPOW Next j' a).MEM (align_addr (FUNPOW Next (j' + 1) a).PC)`
        by fs [word_at_addr_not_changed_after_write_mem] >> fs [] >>
      Q.ABBREV_TAC `j'' = j' + 1` >>
      `j' = j'' - 1` by fs [Abbr `j''`] >> fs [] >>
      Cases_on `is_wrMEM_isa (FUNPOW Next (j''-1) a)` >-
       (`j''+1 > j'' /\ j''+1 < j''+4` by rw [] >>
        `align_addr (FUNPOW Next (j''+1-1) a).PC <>
         align_addr (dataB (FUNPOW Next (j''−1) a))` by fs [] >>
        fs [word_at_addr_not_changed_after_write_mem]) >>
      fs [word_at_addr_not_changed_after_normal_instrs]) >>
    `word_at_addr (FUNPOW Next (j' − 1) a).MEM (align_addr (FUNPOW Next (j' + 1) a).PC) =
    word_at_addr (FUNPOW Next j' a).MEM (align_addr (FUNPOW Next (j' + 1) a).PC)`
      by fs [word_at_addr_not_changed_after_normal_instrs] >> fs [] >>
    Q.ABBREV_TAC `j'' = j' + 1` >>
    `j' = j'' - 1` by fs [Abbr `j''`] >> fs [] >>
    Cases_on `is_wrMEM_isa (FUNPOW Next (j''-1) a)` >-
     (`j''+1 > j'' /\ j''+1 < j''+4` by rw [] >>
      `align_addr (FUNPOW Next (j''+1-1) a).PC <>
       align_addr (dataB (FUNPOW Next (j''−1) a))` by fs [] >>
      fs [word_at_addr_not_changed_after_write_mem]) >>
    fs [word_at_addr_not_changed_after_normal_instrs]) >>
  `word_at_addr (FUNPOW Next (j − 1) a).MEM (align_addr (FUNPOW Next (j + 2) a).PC) =
  word_at_addr (FUNPOW Next j a).MEM (align_addr (FUNPOW Next (j + 2) a).PC)`
    by fs [word_at_addr_not_changed_after_normal_instrs] >> fs [] >>
  Q.ABBREV_TAC `j' = j + 1` >>
  `j' <> 0` by fs [Abbr `j'`] >>
  `j = j' - 1` by fs [Abbr `j'`] >> fs [] >>
  Cases_on `is_wrMEM_isa (FUNPOW Next (j'-1) a)` >-
   (`j'+2 > j' /\ j'+2 < j'+4` by rw [] >>
    `align_addr (FUNPOW Next (j'+2-1) a).PC <> align_addr (dataB (FUNPOW Next (j'−1) a))` by fs [] >>
    `word_at_addr (FUNPOW Next (j' − 1) a).MEM (align_addr (FUNPOW Next (j' + 1) a).PC) =
    word_at_addr (FUNPOW Next j' a).MEM (align_addr (FUNPOW Next (j' + 1) a).PC)`
      by fs [word_at_addr_not_changed_after_write_mem] >> fs [] >>
    Q.ABBREV_TAC `j'' = j' + 1` >>
    `j' = j'' - 1` by fs [Abbr `j''`] >> fs [] >>
    Cases_on `is_wrMEM_isa (FUNPOW Next (j''-1) a)` >-
     (`j''+1 > j'' /\ j''+1 < j''+4` by rw [] >>
      `align_addr (FUNPOW Next (j''+1-1) a).PC <>
       align_addr (dataB (FUNPOW Next (j''−1) a))` by fs [] >>
      fs [word_at_addr_not_changed_after_write_mem]) >>
    fs [word_at_addr_not_changed_after_normal_instrs]) >>
    `word_at_addr (FUNPOW Next (j' − 1) a).MEM (align_addr (FUNPOW Next (j' + 1) a).PC) =
    word_at_addr (FUNPOW Next j' a).MEM (align_addr (FUNPOW Next (j' + 1) a).PC)`
      by fs [word_at_addr_not_changed_after_normal_instrs] >> fs [] >>
    Q.ABBREV_TAC `j'' = j' + 1` >>
    `j' = j'' - 1` by fs [Abbr `j''`] >> fs [] >>
    Cases_on `is_wrMEM_isa (FUNPOW Next (j''-1) a)` >-
     (`j''+1 > j'' /\ j''+1 < j''+4` by rw [] >>
      `align_addr (FUNPOW Next (j''+1-1) a).PC <>
       align_addr (dataB (FUNPOW Next (j''−1) a))` by fs [] >>
      fs [word_at_addr_not_changed_after_write_mem]) >>
  fs [word_at_addr_not_changed_after_normal_instrs]
QED


(* correctness of ISA help funcations imm/flag/data for ports A/B/W *)
(** data port A **)
Theorem dataA_correct_rewrite_flag_imm_reg_data:
  !a.
    dataA a = if v2w [flagA a] = (0w:word1) then reg_dataA a else immA a
Proof
  rw [dataA_def,flagA_def,reg_dataA_def,immA_def,instr_def,DecodeReg_imm_def,ri2word_def,addrA_def]
QED

(** data port B **)
Theorem dataB_correct_rewrite_flag_imm_reg_data:
  !a.
    dataB a = if v2w [flagB a] = (0w:word1) then reg_dataB a else immB a
Proof
  rw [dataB_def,flagB_def,reg_dataB_def,immB_def,instr_def,DecodeReg_imm_def,ri2word_def,addrB_def]
QED

(** data port W **)
Theorem dataW_correct_rewrite_flag_imm_reg_data:
  !a.
    dataW a = if v2w [flagW a] = (0w:word1) then reg_dataW a else immW a
Proof
  rw [dataW_def,flagW_def,reg_dataW_def,immW_def,instr_def,DecodeReg_imm_def,ri2word_def,addrW_def]
QED


(** register data is unchanged after an instruction **)
Theorem reg_adr_update_isa_not_change_data:
  !a nop adr.
    ~reg_adr_update_isa nop a adr ==>
    nop <> NONE ==>
    (FUNPOW Next (THE nop - 1) a).R adr = (FUNPOW Next (THE nop) a).R adr
Proof
  rw [reg_adr_update_isa_def] >> fs [] >>
  Cases_on `nop` >> fs [] >>
  Cases_on `x = 0` >> fs [] >>
  `x = SUC (x-1)` by rw [] >>
  `FUNPOW Next x a = FUNPOW Next (SUC (x-1)) a` by METIS_TAC [] >>
  rw [FUNPOW_SUC] >>
  qpat_abbrev_tac `a1 = FUNPOW _ _  _` >>
  rw [Next_def,GSYM word_at_addr_def,GSYM align_addr_def] >>
  Cases_on `Decode (word_at_addr a1.MEM (align_addr a1.PC))` >-
   (PairCases_on `p` >> rw [Run_def,dfn'Accelerator_def,incPC_def] >>
    Cases_on `addrW a1 = adr` >> fs [] >-
     (fs [reg_iswrite_def,ag32_Decode_Acc_opc_8w]) >>
    `addrW a1 = p0` by fs [ag32_Decode_Acc_addrW] >>
    EVAL_TAC >> fs []) >-
   (rw [Run_def,dfn'In_def,incPC_def] >>
    Cases_on `addrW a1 = adr` >> fs [] >-
     (fs [reg_iswrite_def,ag32_Decode_In_opc_7w]) >>
    `addrW a1 = c` by fs [ag32_Decode_In_addrW] >>
    EVAL_TAC >> fs []) >-
   (rw [Run_def,dfn'Interrupt_def,incPC_def]) >-
   (PairCases_on `p` >> fs [Run_def,dfn'Jump_def,ALU_def] >>
    Cases_on `addrW a1 = adr` >> fs [] >-
     (fs [reg_iswrite_def,ag32_Decode_Jump_opc_9w]) >>
    `addrW a1 = p1` by fs [ag32_Decode_Jump_addrW] >>
    Cases_on `p0` >> EVAL_TAC >> fs []) >-
   (PairCases_on `p` >> fs [Run_def,dfn'JumpIfNotZero_def,incPC_def] >>
    qpat_abbrev_tac `alu = ALU _ _` >>
    Cases_on `alu` >> rw [] >>
    METIS_TAC [ALU_state_eq_after]) >-
   (PairCases_on `p` >> rw [Run_def,dfn'JumpIfZero_def,incPC_def] >>
    qpat_abbrev_tac `alu = ALU _ _` >>
    Cases_on `alu` >> rw [] >>
    METIS_TAC [ALU_state_eq_after]) >-
   (PairCases_on `p` >> fs [Run_def,dfn'LoadConstant_def,incPC_def] >>
    Cases_on `addrW a1 = adr` >> fs [] >-
     (fs [reg_iswrite_def,ag32_Decode_LoadConstant_opc_13w]) >>
    `addrW a1 = p0` by fs [ag32_Decode_LoadConstant_addrW] >>
    EVAL_TAC >> fs []) >-
   (PairCases_on `p` >> rw [Run_def,dfn'LoadMEM_def,incPC_def] >>
    Cases_on `addrW a1 = adr` >> fs [] >-
     (fs [reg_iswrite_def,ag32_Decode_LoadMEM_opc_4w]) >>
    `addrW a1 = p0` by fs [ag32_Decode_LoadMEM_addrW] >>
    EVAL_TAC >> fs []) >-
   (PairCases_on `p` >> rw [Run_def,dfn'LoadMEMByte_def,incPC_def] >>
    Cases_on `addrW a1 = adr` >> fs [] >-
     (fs [reg_iswrite_def,ag32_Decode_LoadMEMByte_opc_5w]) >>
    `addrW a1 = p0` by fs [ag32_Decode_LoadMEMByte_addrW] >>
    EVAL_TAC >> fs []) >-
   (PairCases_on `p` >> rw [Run_def,dfn'LoadUpperConstant_def,incPC_def] >>
    Cases_on `addrW a1 = adr` >> fs [] >-
     (fs [reg_iswrite_def,ag32_Decode_LoadUpperConstant_opc_14w]) >>
    `addrW a1 = p0` by fs [ag32_Decode_LoadUpperConstant_addrW] >>
    EVAL_TAC >> fs []) >-
   (PairCases_on `p` >> rw [Run_def,dfn'Normal_def,norm_def,incPC_def] >>
    qpat_abbrev_tac `alu = ALU _ _` >>
    Cases_on `alu` >> rw [] >>
    Cases_on `addrW a1 = adr` >> fs [] >-
     (fs [reg_iswrite_def,ag32_Decode_Normal_opc_0w]) >>
    `addrW a1 = p1` by fs [ag32_Decode_Normal_addrW] >>
    EVAL_TAC >> fs [] >>
    METIS_TAC [ALU_state_eq_after]) >-
   (PairCases_on `p` >> rw [Run_def,dfn'Out_def,norm_def,incPC_def] >>
    qpat_abbrev_tac `alu = ALU _ _` >>
    Cases_on `alu` >> rw [] >>
    Cases_on `addrW a1 = adr` >> fs [] >-
     (fs [reg_iswrite_def,ag32_Decode_Out_opc_6w]) >>
    `addrW a1 = p1` by fs [ag32_Decode_Out_addrW] >>
    EVAL_TAC >> fs [] >>
    METIS_TAC [ALU_state_eq_after]) >-
   rw [Run_def] >-
   (PairCases_on `p` >> rw [Run_def,dfn'Shift_def,incPC_def] >>
    Cases_on `addrW a1 = adr` >> fs [] >-
     (fs [reg_iswrite_def,ag32_Decode_Shift_opc_1w]) >>
    `addrW a1 = p1` by fs [ag32_Decode_Shift_addrW] >>
    EVAL_TAC >> fs []) >-
   (PairCases_on `p` >> rw [Run_def,dfn'StoreMEM_def,incPC_def]) >>
  PairCases_on `p` >> rw [Run_def,dfn'StoreMEMByte_def,incPC_def]
QED

val _ = export_theory ();

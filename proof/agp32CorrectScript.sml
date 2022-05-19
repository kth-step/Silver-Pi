open hardwarePreamble translatorTheory translatorLib arithmeticTheory dep_rewrite blastLib bitstringSyntax fcpSyntax listSyntax wordsSyntax agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory ag32Theory ag32ExtraTheory ag32UtilitiesTheory agp32RelationTheory agp32UpdateTheory;

val _ = new_theory "agp32Correct";

(* Special variables used in theorems:
   I: scheduling function.
   C: cache oracle.
 *)

val _ = prefer_num ();
val _ = guess_lengths ();

(* Init relation implies Rel at cycle 0 *)
Theorem agp32_Init_implies_Rel:
  !k fext fbits s a I.
    k >= 1 ==>
    k <= 5 ==>
    s = agp32 fext fbits ==>
    I(k,0) = 0 ==>
    Init (fext 0) (s 0) a ==>
    Rel (fext 0) (s 0) I 0 a 0
Proof
  rpt strip_tac >>
  fs [Init_def,Rel_def] >> rw [] >-
   cheat >>
  fs [enable_stg_def] >> fs []
QED

(* correctness of the pipelined Silver concerning the ISA *)
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
    Rel (fext t) (s t) I t a (I(k,t))
Proof
  Induct_on `t` >>
  rpt strip_tac >-
   METIS_TAC [agp32_Init_implies_Rel] >>
  `Rel (fext t) (s t) I' t a (I' (k,t))` by METIS_TAC [] >>
  Q.ABBREV_TAC `i = I'(k,t)` >> 
  Cases_on `enable_stg k (s (SUC t))` >-
   (`I'(k, SUC t) = SUC i` by fs [] >> fs [Rel_def] >>
    Cases_on `k = 1` >-
     (** IF stage **)
     (fs [] >> rw [] >-
       fs [GSYM ag32_data_in_unchanged,is_data_in_def] >>
      `I'(1,SUC t) <> I'(2,SUC t)` by cheat >> fs [] >>
      `I'(1,SUC t) <> I'(3,SUC t)` by cheat >> fs [] >>
      `I'(1,SUC t) <> I'(4,SUC t)` by cheat >> fs [] >>
      `I'(1,SUC t) <> I'(5,SUC t)` by cheat >> fs [] >>
      rw [IF_Rel_def] >>
      `?s s'. (agp32 fext fbits (SUC t)).IF.IF_instr =
      (IF_instr_update (fext (SUC t)) s s').IF.IF_instr`
        by rw [agp32_IF_instr_updated_by_IF_instr_update] >>
      rw [IF_instr_update_def,instr_def] >> cheat) >>
    cheat) >>
  cheat
QED

val _ = export_theory ();

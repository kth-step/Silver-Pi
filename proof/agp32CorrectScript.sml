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
  !fext fbits s a I.
    s = agp32 fext fbits ==>
    (!k.I(k,0) = 0) ==>
    Init (fext 0) (s 0) a ==>
    Rel I (fext 0) (s 0) a 0
Proof
  rpt strip_tac >>
  fs [Init_def,Rel_def] >> rw [] >-
   cheat >>
  fs [enable_stg_def] >> fs []
QED

(* correctness of the pipelined Silver concerning the ISA *)
Theorem agp32_Rel_ag32_correct:
  !fext fbits s a (t:num) I C.
    s = agp32 fext fbits ==>
    (!t. SC_self_mod (s t)) ==>
    is_mem fext_accessor_circuit s fext ==>
    is_acc accelerator_f s ==>
    is_interrupt_interface fext_accessor_circuit s fext ==>
    is_data_in fext ==>
    (* cache oracle can introduce hit/miss *)
    (!t. C (s t).data_addr (s t).data_wstrb (s t).data_wdata (s t).command (s t).PC
         <=> (fext t).ready) ==>
    Init (fext 0) (s 0) a ==>
    (** properties of scheduling function I **)
    (!k.I(k,0) = 0) ==>
    (!t k. enable_stg k (s (SUC t)) ==> I(k,SUC t) = I(k,t) + 1) ==>
    Rel I (fext t) (s t) a t
Proof
  Induct_on `t` >>
  rpt strip_tac >-
   METIS_TAC [agp32_Init_implies_Rel] >>
  `Rel I' (fext t) (s t) a t` by METIS_TAC [] >>
  fs [Rel_def] >> rw [] >-
   (** data_in **)
   fs [is_data_in_def,ag32_data_in_unchanged_all] >-
   (** carryflag **)
   (Cases_on `enable_stg 3 (agp32 fext fbits (SUC t))` >-
    (** EX stage is enabled **)
     (`I'(3,SUC t) = SUC (I'(3,t))` by fs [] >>
      rw [FUNPOW_SUC] >>
      Q.ABBREV_TAC `ai = FUNPOW Next (I' (3,t)) a` >>
      rw [Next_def,GSYM word_at_addr_def,GSYM align_addr_def] >>
      Cases_on `Decode (word_at_addr ai.MEM (align_addr ai.PC))` >-
       ((** Accelerator **)
       PairCases_on `p` >> rw [Run_def,dfn'Accelerator_def,incPC_def] >>
       cheat) >>
      cheat) >>
    cheat) >-
   (** overflow flag **)
   cheat >-
   (** PC when jump **)
   cheat >-
   (** PC when not jump **)
   cheat >-
   (** memory **)
   cheat >-
   (** data_out **)
   cheat >-
   (** registers **)
   cheat >-
   (** invisiable regs in IF **)
   (rw [IF_Rel_def] >-
    (** IF_instr when memory is ready **)
    (`?s s'. (agp32 fext fbits (SUC t)).IF.IF_instr =
     (IF_instr_update (fext (SUC t)) s s').IF.IF_instr`
       by rw [agp32_IF_instr_updated_by_IF_instr_update] >>
     rw [IF_instr_update_def,instr_def] >> cheat) >>
    (** IF_instr when not ready **)
    cheat) >>
  cheat         
QED

val _ = export_theory ();

open hardwarePreamble agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory ag32Theory ag32ExtraTheory agp32RelationTheory;

val _ = new_theory "agp32Correct";

(* Special variables used in theorems:
   I: scheduling function.
   C: cache oracle.
 *)

val _ = prefer_num ();
val _ = guess_lengths ();

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
  !(k:num) fext fbits s a (t:num) i I C.
    k >= 1 ==>
    k <= 5 ==>
    s = agp32 fext fbits ==>
    (!t. SC_self_mod (s t)) ==>
    is_mem fext_accessor_circuit s fext ==>
    is_acc accelerator_f s ==>
    is_interrupt_interface fext_accessor_circuit s fext ==>
    (* cache oracle can introduce hit/miss *)
    (!t. C (s t).data_addr (s t).data_wstrb (s t).data_wdata (s t).command (s t).PC <=> (fext t).ready) ==>
    Init (fext 0) (s 0) a ==>
    (** properties of scheduling function I **)
    (!t k. enable_stg k (s t) ==> I(k,t) = I(k,t-1) + 1) ==>
    I(k,0) = 0 ==>
    I(k,t) = i ==>
    Rel (fext t) (s t) k a i
Proof
  rpt strip_tac >>
  Induct_on `t` >>
  rpt strip_tac >-
   METIS_TAC [agp32_Init_implies_Rel] >>
  fs [Init_def,Rel_def] >>
  Cases_on `k = 1` >-
   (** IF stage **)
   (fs [] >> rw [] >> cheat) >>
  cheat
QED

val _ = export_theory ();

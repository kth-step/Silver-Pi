open hardwarePreamble agp32StateTheory agp32EnvironmentTheory agp32ProcessorTheory ag32Theory ag32ExtraTheory agp32RelationTheory;

val _ = new_theory "agp32Correct";

val _ = prefer_num ();
val _ = guess_lengths ();

(* I: scheduling function
   C: cache oracle
 *)
Theorem agp32_Rel_ag32_correct:
  !(k:num) fext fbits s a (t:num) i I C.
    s = agp32 fext fbits ==>
    SC_self_mod (s t) ==>
    is_mem fext_accessor_circuit s fext ==>
    is_acc accelerator_f s ==>
    is_interrupt_interface fext_accessor_circuit s fext ==>
    (* cache oracle can introduce hit/miss *)
    (C (s t).data_addr (s t).data_wstrb (s t).data_wdata (s t).command (s t).PC <=> (fext t).ready) ==>
    Init (fext 0) (s 0) a ==>
    (** properties of scheduling function I **)
    (enable_stg k (s t) ==> I(k,t) = I(k-1,t) - 1) ==>
    I(k,t) = i ==>
    Rel (fext t) (s t) k a i
Proof
  REPEAT STRIP_TAC >> cheat
QED

val _ = export_theory ();

Require Export LBool LNat LTerm Nat.
Require Import LTactics.

(** * Extracted Functions *)

(** ** Extracted equality of encoded terms *)

Fixpoint term_eqb s t :=
  match s,t with
  | var n, var m => eqb n m
  | app s1 t1, app s2 t2 => andb (term_eqb s1 s2) (term_eqb t1 t2)
  | lam s',lam t' => term_eqb s' t'
  | _,_ => false
  end.

Instance term_term_eqb : computable term_eqb.
Proof.
  extract.
Defined.

Lemma term_eqb_spec : forall x y1 : term, reflect (x = y1) (term_eqb x y1).
Proof with try (constructor;congruence).
  induction x;cbn; destruct y1...
  -destruct (Nat.eqb_spec n n0)...
  -destruct (IHx1 y1_1)...
   destruct (IHx2 y1_2)...
  -destruct (IHx y1)...
Qed.  

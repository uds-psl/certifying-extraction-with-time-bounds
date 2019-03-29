Require Export LTactics GenEncode.
Require Import Shared.Numbers.

Require Import Nat LBool.
(** ** Encoding of natural numbers *)

Run TemplateProgram (tmGenEncode "nat_enc" nat).
(* Next Obligation. register_proc. Qed. *)
(* Next Obligation. register_inj. Qed. *)
(* Next Obligation. extract match. Qed. *)
Hint Resolve nat_enc_correct : Lrewrite.

Instance termT_S : computableTime S (fun _ _ => (1,tt)).
Proof.
  extract constructor.
  solverec.
Defined.

Instance termT_pred : computableTime pred (fun _ _ => (4,tt)).
Proof.
  extract.
  solverec.
Defined.
  
(* Instance term_plus : computable add. *)
(* Proof. *)
(*   extract. *)
(* Defined. *)

Instance termT_plus' : computableTime add (fun x xT => (5,(fun y yT => (10*x+3,tt)))).
Proof.
  extract. fold add.
  solverec.
Defined.

(* Instance term_mult : computable mult. *)
(* Proof. *)
(*   extract. *)
(* Qed. *)

Instance termT_mult : computableTime mult (fun x xT => (5,(fun y yT => (x * (10 * y) + 17*x + 3,tt)))).
Proof.
  extract.
  solverec.
Defined.

(* Instance term_leb : computable leb. *)
(* Proof. *)
(*   extract. *)
(* Defined. *)

Instance termT_leb : computableTime leb (fun x xT => (5,(fun y yT => (x*12 + 3,tt)))).
Proof.
  extract.
  solverec.
Defined.

(* Instance term_nat_eqb : computable Nat.eqb. *)
(* Proof. *)
(*   extract. *)
(* Defined. *)

Instance termT_nat_eqb: computableTime Nat.eqb (fun x xT => (5,(fun y yT => ((min x y)*15 + 8,tt)))).
Proof.
  extract.
  solverec.
Defined.

(* Notice that we have those two properties as well, just by registering nat_enc:
But for consistency, we do not use them*)
(* Lemma nat_enc_injective : injective nat_enc. *)
(* Proof. *)
(*   exact inj_enc. *)
(* Abort. *)

(* now some more encoding-related properties:*)

Fixpoint nat_unenc (s : term) :=
  match s with
  | lam (lam #1) => Some 0
  | lam (lam (app #0 s)) => match nat_unenc s with Some n => Some (S n) | x=>x end
  | _ => None
  end.

Lemma unenc_correct m : (nat_unenc (nat_enc m)) = Some m.
Proof.
  induction m; simpl; now try rewrite IHm.
Qed.

Lemma unenc_correct2 t n : nat_unenc t = Some n -> nat_enc n = t.
Proof with try solve [Coq.Init.Tactics.easy].
  revert n. eapply (size_induction (f := size) (p := (fun t => forall n, nat_unenc t = Some n -> nat_enc n = t))). clear t. intros t IHt n H.
  destruct t. easy. easy.
  destruct t. easy. easy.
  destruct t. 3:easy.
  -destruct n0. easy. destruct n0. 2:easy. inv H. easy.
  -destruct t1. 2-3:easy. destruct n0. 2:easy. simpl in H. destruct (nat_unenc t2) eqn:A.
   +apply IHt in A;simpl;try omega. destruct n. inv H. simpl. congruence.
   +congruence.
Qed.

Lemma dec_enc t : dec (exists n, t = nat_enc n).
Proof.
  destruct (nat_unenc t) eqn:H.
  - left. exists n. now eapply unenc_correct2 in H.
  - right. intros [n A]. rewrite A in H. rewrite unenc_correct in H. inv H.
Qed.



(* This is an example for an function in which the run-time of the fix itself is not constant (in add, the fix on the first argument always returns an function in ~5 steps)*)
(* Instance termT_testId : computableTime (fix f x := *)
(*                                             match x with *)
(*                                               0 => 0 *)
(*                                             | S x => S (f x) *)
(*                                             end). *)
(* Proof. *)
(*   extract. *)
(*   eexists (fun x xT => (x*9+7,tt)). *)
(*   abstract (repeat (cbn;intros;intuition;try destruct _;try ring_simplify)). *)
(* Defined. *)

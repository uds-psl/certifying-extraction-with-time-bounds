Require Export L.
Require Import Reflection ComputableTime mixedTactics.

(** ** Symbolic simplification for L*)

(** *** Lproc *)

(** This module provides tactics fLproc and Lproc that solve goals of the form [lambda s] or [proc s] or [closed s] for L-terms [s]. *)

Hint Resolve rho_lambda rho_cls : LProc.

Lemma proc_closed p : proc p -> closed p.
Proof.
  firstorder intuition.
Qed.

Lemma proc_lambda p : proc p -> lambda p.
Proof.
  firstorder intuition.
Qed.


Ltac fLproc :=intros;
              lazymatch goal with
              | [ |- proc _ ] => split;fLproc
              | [ |- lambda ?s ] => eexists; reflexivity || fail "Prooving 'lambda " s " ' by computation failed. It is either not a fixed term, some used identifier is opaqie or the goal does not hold"
              | [ |- closed ?s ] => vm_compute; reflexivity || fail "Prooving 'closed " s " ' by computation failed. It is either not a fixed term, some used identifier is opaque or the goal does not hold"
              end.

Ltac Lproc' :=
  lazymatch goal with
  | |- lambda (match ?c with _ => _ end) => destruct c;now repeat Lproc'
  | |- lambda (@enc ?t ?H ?x) => exact (proc_lambda (@proc_enc t H x))
  | |- lambda (@ext ?X ?tt ?x ?H) => exact (proc_lambda (@proc_ext X tt x H))
  | |- lambda (@extT ?X ?tt ?x _ ?H) => exact (proc_lambda (@proc_extT X tt x _ H))
  (*| |- lambda (@ext_ext ?X ?x ?H) => exact (proc_lambda (@proc_extT X tt x _))*)
  | H:computes _ _ ?s _ |- lambda ?s => simple eapply proc_lambda;exact (computesProc H)
  | |- lambda _ => (apply proc_lambda;(trivial with nocore LProc || tauto)) || tauto || (eexists;reflexivity)
  | |- rClosed ?phi _ => solve [apply rClosed_decb_correct;[assumption|vm_compute;reflexivity]]
  | |- L.closed _ => apply closed_dcl
  | |- bound _  (match ?c with _ => _ end) => destruct c;now repeat Lproc'
  | |- bound _ (L.var _) => solve [constructor;omega]
  | |- bound _ (L.app _ _) => constructor
  | |- bound _ (L.lam _) => constructor
  | |- bound _ (rho ?s) => apply rho_dcls
  | H:computes _ _ ?s |- bound ?k ?s =>  exact (closed_dcl_x k (proc_closed (computesProc H)))
  | |- bound ?k (@ext ?X ?tt ?x ?H) =>
    exact (closed_dcl_x k (proc_closed (@proc_ext X tt x H)))
            | |- bound ?k (@extT ?X ?tt ?x _ ?H) =>
    exact (closed_dcl_x k (proc_closed (@proc_extT X tt x _ H)))
  (*| |- bound ?k (@extT ?X ?tt ?x ?H) =>
      exact (closed_dcl_x k (proc_closed (@extT_proc X tt x H)))*)
  | |- bound ?k (@enc ?t ?H ?x) =>
    exact (closed_dcl_x k (proc_closed (@proc_enc t H x)))
  | |- bound _ ?s => refine (closed_dcl_x _ _); (trivial with LProc || (apply proc_closed;trivial with LProc || tauto) || tauto )
  end.


(* early abort for speed!*)

Ltac Lproc :=
  match goal with
  (*| |- _ (match ?x with _ => _ end) => fail 1;(destruct x;Lproc || fail 1)*)

  | |- proc (app _ _) => fail 1
  | |- proc _ => split;[|now Lproc];Lproc
  | |- proc ?s => fail 1 (*000 "Lproc tactic not applicable for proc" s *)

  | |- closed _ => try now (repeat Lproc')
  | |- closed ?s => fail 1 (*000 "Lproc tactic not applicable for closed" s *)

  | |- lambda (app _ _) => fail 1
  | |- lambda _ => Lproc'
  | |- lambda ?s => fail 1 (*000 "Lproc tactic not applicable for lambda" s*)
  end.

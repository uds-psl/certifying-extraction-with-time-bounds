Require Import Seval LBool LOptions LTactics Nat.

(** * Case Study 1: Universal L-term *)

(* ** Encoding for natural numers *)

Run TemplateProgram (tmGenEncode "nat_enc" nat).
Hint Resolve nat_enc_correct : Lrewrite.

Instance termT_S : computableTime S (fun _ _ => (1,tt)).
Proof. extract constructor. solverec. Qed.

(** ** Encoding for L-terms *)

Run TemplateProgram (tmGenEncode "term_enc" term).
Hint Resolve term_enc_correct : Lrewrite.
  
(* register the non-constant constructors *)
Instance term_var : computableTime var (fun n _ => (1, tt)).
Proof. extract constructor. solverec. Qed.

Instance term_app : computableTime app (fun s1 _ => (1, (fun s2 _ => (1, tt)))).
Proof. extract constructor. solverec. Qed.

Instance term_lam : computableTime lam (fun s _ => (1, tt)).
Proof. extract constructor. solverec. Qed.

(** ** Extracted equality on natural numbers **)
Instance termT_nat_eqb: computableTime Nat.eqb (fun x xT => (5,(fun y yT => ((min x y)*15 + 8,tt)))).
Proof. extract. solverec. Qed.

(** ** Extracted substitution **)

Instance term_substT :
  computableTime subst (fun s _ => (5, (fun n _ => (1, (fun t _ => ( 15 * n * size s + 43 * (size s) ^ 2 + 13, tt)))))).
Proof. extract. solverec. Qed.

(** ** Extracted step-indexed L-interpreter *)

Instance term_eva : computable eva.
Proof. extract. Qed.

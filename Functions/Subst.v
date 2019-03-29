Require Import LTactics Equality LNat.
(** ** Extracted substitution on terms *)

Instance term_substT :
  computableTime subst (fun s _ => (5, (fun n _ => (1, (fun t _ => ( 15 * n * size s + 43 * (size s) ^ 2 + 13, tt)))))).
Proof.
  extract. solverec.
Qed.

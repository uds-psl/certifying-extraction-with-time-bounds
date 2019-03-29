Require Import LTactics LTactics GenEncode.
Require Export LNat LTerm.

(** ** Extracted encoding of natural numbers *)

Instance term_nat_enc : computable nat_enc.
Proof.
  extract.   
Defined.

(** ** Extracted term encoding *)

Instance term_term_enc : computable term_enc.
Proof.
  extract.
Qed.

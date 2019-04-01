Require Export L.
Require Import LTactics GenEncode.
(** ** Encoding of booleans *)

Run TemplateProgram (tmGenEncode "bool_enc" bool).
(* For each encoding, Lrewrite must contain an lemma that solves goals like "encode b s t >* match ...end". The database Lrewrite also calls Lproc to discharge the other assumptions *)
Hint Resolve bool_enc_correct : Lrewrite.

Instance term_negb : computableTime negb (fun _ _ => (3,tt)).
Proof.
  extract.
  solverec.
Qed.

Instance term_andb : computableTime andb (fun _ _ => (1,fun _ _ => (3,tt))).
Proof.
  extract.
  solverec.
Qed.

Instance term_orb : computableTime orb (fun _ _ => (1,fun _ _ => (3,tt))).
Proof.
  extract.
  solverec.
Qed.


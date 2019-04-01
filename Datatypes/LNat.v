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
Qed.

Instance termT_pred : computableTime pred (fun _ _ => (4,tt)).
Proof.
  extract.
  solverec.
Qed.

Instance termT_plus : computableTime add (fun x xT => (5,(fun y yT => (10*x+3,tt)))).
Proof.
  extract. fold add.
  solverec.
Qed.

Instance termT_mult : computableTime mult (fun x xT => (5,(fun y yT => (x * (10 * y) + 17*x + 3,tt)))).
Proof.
  extract.
  solverec.
Qed.

Instance termT_leb : computableTime leb (fun x xT => (5,(fun y yT => (x*12 + 3,tt)))).
Proof.
  extract.
  solverec.
Qed.

Instance termT_nat_eqb: computableTime Nat.eqb (fun x xT => (5,(fun y yT => ((min x y)*15 + 8,tt)))).
Proof.
  extract.
  solverec.
Qed.

Require Import LTactics LBool GenEncode.

(** ** Encoding of option type *)
Section Fix_X.
  Variable X:Type.
  Variable intX : registered X.
  
  
  Run TemplateProgram (tmGenEncode "option_enc" (option X)).
  Hint Resolve option_enc_correct : Lrewrite.
  
  (* now we must register the non-constant constructors*)
  
  Global Instance term_Some : computableTime (@Some X) (fun _ _ => (1,tt)).
  Proof.
    extract constructor.
    solverec.
  Qed.

End Fix_X.

Hint Resolve option_enc_correct : Lrewrite.

Section option_eqb.

  Variable X : Type.
  Variable eqb : X -> X -> bool.
  Variable spec : forall x y, reflect (x = y) (eqb x y).

  Definition option_eqb (A B : option X) := 
    match A,B with
    | None,None => true
    | Some x, Some y => eqb x y
    | _,_ => false
    end.

  Lemma option_eqb_spec A B : reflect (A = B) (option_eqb A B).
  Proof.
    destruct A, B; try now econstructor. cbn.
    destruct (spec x x0); econstructor; congruence.
  Qed.
End option_eqb.

Section int.

  Variable X:Type.
  Context {HX : registered X}.

  Global Instance term_option_eqb : computableTime (@option_eqb X) (fun eqb eqbT => (1, fun a _ => (1,fun b _ => (match a,b with Some a, Some b => callTime2 eqbT a b + 10 | _,_ => 8 end,tt)))).
  Proof.
    extract. solverec.
  Qed.

End int.

Definition isSome {T} (u : option T) := match u with Some _ => true | _ => false end.

Instance term_isSome {T} `{registered T} : computable (@isSome T).
Proof.
  extract.
Qed.

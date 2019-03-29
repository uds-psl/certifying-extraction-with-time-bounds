Require Import LTactics LBool LNat LOptions LProd GenEncode.
Require Export List Shared.Lists.Filter Datatypes.

(** ** Encoding of lists *)

Section Fix_X.
  Variable (X:Type).
  Context {intX : registered X}.

  Run TemplateProgram (tmGenEncode "list_enc" (list X)).  
  Hint Resolve list_enc_correct : Lrewrite.
  
  (* now we must register the non-constant constructors*)
  
  Global Instance termT_cons : computableTime (@cons X) (fun a aT => (1,fun A AT => (1,tt))).
  Proof.
    extract constructor.
    solverec.
  Defined.

  (* Lemma list_enc_correct (A:list X) (s t:term): proc s -> proc t -> enc A s t >(2) match A with nil => s | cons a A' => t (enc a) (enc (A')) end. *)
  (* Proof. *)
  (*   extract match.  *)
  (* Qed. *)
  

  Global Instance termT_append : computableTime (@List.app X) (fun A _ => (5,fun B _ => (length A * 15 +3,tt))).
  Proof.
    extract.
    solverec.
  Defined.

  Global Instance term_filter: computableTime (@filter X) (fun p pT => (1,fun l _ => (fold_right (fun x res => 14 + res + fst (pT x tt)) 7 l ,tt))).
  Proof using intX.
    change (filter (A:=X)) with ((fun (f : X -> bool) =>
                                    fix filter (l : list X) : list X := match l with
                                                                        | [] => []
                                                                        | x :: l0 => (fun r => if f x then x :: r else r) (filter l0)
                                                                        end)).
    extract.
    solverec.
  Defined.

  Global Instance term_filter_notime: computable (@filter X).
  pose (t:= extT (@filter X)). hnf in t. 
    computable using t.
  Defined.

  Global Instance term_nth : computableTime (@nth X) (fun n _ => (5,fun l lT => (1,fun d _ => (n*18+7,tt)))). 
  Proof.
    extract.
    solverec.
  Defined.

  Fixpoint inb eqb (x:X) (A: list X) :=
    match A with
      nil => false
    | a::A' => orb (eqb a x) (inb eqb x A')
    end.

  Variable X_eqb : X -> X -> bool.
  Hypothesis X_eqb_spec : (forall (x y:X), Bool.reflect (x=y) (X_eqb x y)).

  Lemma inb_spec: forall x A, Bool.reflect (In x A) (inb X_eqb x A).
  Proof using X_eqb_spec.
    intros x A. induction A.
    -constructor. tauto.
    -simpl. destruct (X_eqb_spec a x).
     +constructor. tauto.
     +inv IHA. destruct (X_eqb_spec a x).
      *constructor. tauto.
      *constructor. tauto.
      *constructor. tauto.
  Defined.

  Global Instance term_inb: computableTime inb (fun eq eqT => (5,fun x _ => (1,fun l _ =>
                                        (fold_right (fun x' res => callTime2 eqT x' x
                                                                + res + 15) 3 l ,tt)))).
  Proof.
    extract.
    solverec. 
  Defined.

  Global Instance term_inb_notime: computable inb.
  Proof.
    extract.
  Defined.

  Definition pos_nondec  :=
    fix pos_nondec (eqb: X -> X -> bool) (s : X) (A : list X) {struct A} : option nat :=
      match A with
      | [] => None
      | a :: A0 =>
        if eqb s a
        then Some 0
        else match pos_nondec eqb s A0 with
             | Some n => Some (S n)
             | None => None
             end
      end.

  Lemma pos_nondec_spec (x:X) `{eq_dec X} A: pos_nondec X_eqb x A = pos x A.
  Proof using X_eqb_spec.
    induction A;[reflexivity|];cbn.
    rewrite IHA. destruct (X_eqb_spec x a); repeat (destruct _; try congruence).
  Defined.

  Global Instance term_pos_nondec:
    computable pos_nondec.
  Proof.
    extract.
  Defined.

End Fix_X.

Hint Resolve list_enc_correct : Lrewrite.
  
Instance term_map (X Y:Type) (Hx : registered X) (Hy:registered Y): computableTime (@map X Y) (fun f fT => (1,fun l _ => (fold_right (fun x res => fst (fT x tt) + res + 11) 7 l,tt))).
Proof.
  extract.
  solverec.
Defined.

Instance term_map_noTime (X Y:Type) (Hx : registered X) (Hy:registered Y): computable (@map X Y).
Proof.
  extract.
Defined.

Instance term_nth_error (X:Type) (Hx : registered X): computable (@nth_error X).
Proof.
  extract.
Defined.

Instance term_elAt (X:Type) (Hx : registered X) : computable (@elAt X).
Proof.
  unfold elAt. exact _.
Defined.

Instance term_rev (X : Type) (Hx : registered X) : computable (@rev X).
Proof.
  extract.
Defined.

Section list_eqb.

  Variable X : Type.
  Variable eqb : X -> X -> bool.
  Variable spec : forall x y, reflect (x = y) (eqb x y).

  Fixpoint list_eqb A B :=
    match A,B with
    | nil,nil => true
    | a::A',b::B' => eqb a b && list_eqb A' B'
    | _,_ => false
    end.

  Lemma list_eqb_spec A B : reflect (A = B) (list_eqb A B).
  Proof.
    revert B; induction A; intros; destruct B; cbn in *; try now econstructor.
    destruct (spec a x), (IHA B); cbn; econstructor; congruence.
  Qed.

End list_eqb.
Section int.

  Context {X : Type}.
  Context {HX : registered X}.

  Fixpoint list_eqbTime (eqbT: timeComplexity (X -> X -> bool)) (A B:list X) :=
    match A,B with
      a::A,b::B => callTime2 eqbT a b + 22 + list_eqbTime eqbT A B
    | _,_ => 9
    end.
  
  Global Instance term_list_eqb : computableTime (list_eqb (X:=X))
                                                   (fun _ eqbT => (1,(fun A _ => (5,fun B _ => (list_eqbTime eqbT A B,tt))))).
  Proof.
    extract.
    solverec.                                                                                             
  Defined.

  Definition list_eqbTime_leq (eqbT: timeComplexity (X -> X -> bool)) (A B:list X) k:
    (forall a b, callTime2 eqbT a b <= k)
    -> list_eqbTime eqbT A B <= length A * (k+22) + 9.
  Proof.
    intros H'. induction A in B|-*.
    -cbn. omega.
    -destruct B.
     {cbn. intuition. }
     cbn - [callTime2]. setoid_rewrite IHA.
     rewrite H'. ring_simplify. intuition.
  Qed.             
  
End int.

Section list_prod.

  Context {X Y : Type}.
  Context {HX : registered X} {HY : registered Y}.
  
  Global Instance term_list_prod : computable (@list_prod X Y).
  Proof.
    unfold list_prod.
    change (computable
              (fix list_prod (l : list X) (l' : list Y) {struct l} : list (X * Y) :=
                 match l with
                 | [] => []
                 | x :: t => map (pair x) l' ++ list_prod t l'
                 end)).
    extract.
  Qed.

End list_prod.
  

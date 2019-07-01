Require Import LOptions LBool LTactics.
Require LNat Datatypes.Lists.
Require Import ComputableTactics.

Section demo.

(** for further examples of usage see LBool/LNat/Lists/Option/Encoding etc*)

Definition unit_enc := fun (x:unit) => I.

Instance register_unit : registered  unit.
Proof.
  register unit_enc. 
Defined.

(** example for automated higher-order-extraction *)

Definition on0 (f:nat->nat->nat) := f 0 0.

Instance term_on0 : computable on0.
Proof.
  extract. 
Qed.

Lemma test_Some_nat : computable (@Some nat).
Proof.
  extract.
Qed.

(** *** Interactive Demo *)
(** This file shows the inner working of the tactic that shows the correctness of our extracted terms, [[cstep]] *)

Section PaperExample.

  (** Examples of the internal working of tactics that proof the correctness lemmata *)

  Import ComputableTactics.
  Import ComputableTactics.Intern.

  Example correctness_example: computable orb.
  extractAs s.
  (** The term is in context: [s := (lam (lam ((1 (int_ext true)) 0)) : extracted orb) : extracted orb] *)
  
  computable_using_noProof s.
  (** Goal: [computes (! bool ~> ! bool ~> ! bool) (fun b1 b2 : bool => if b1 then true else b2) (lam (lam ((1 (ext true)) 0)))] *)
  
  cstep.
  (** Goal: [  computes (! bool ~> ! bool) (fun b2 : bool => if x then true else b2) (lam (((enc x) (ext true)) 0))] *)
  
  cstep.
  (** Goal: [  computes (! bool) (if x then true else x0) (if x then enc true else enc x0)] *)
  
  cstep.
  (** Subgoal 1: [ computes (! bool) true (enc true) ]
      Subgoal 2: [ computes (! bool) x0 (enc x0)] **)
  
  all:cstep.
  Qed.


  (** Coming up with the conditions for the time bound *)
  Goal forall fT, computableTime orb fT.
    intros.
    extractAs s.
    computable_using_noProof s.
    cstep.
    cstep. (* Note that the second goal got more specific *)
    cstep. (* Note that the second goal got more specific *)
    cstep.
    1,2:cstep. (* Note that the hole in the second goal got filled with True*)
    solverec.
  Abort.  

  (** Finding the Time Bound *)

  (** We use an polymorphic, opaque wrapper for [0] as an "marker": *)
  Print cnst.
  
  Goal computableTime orb (fun _ _ => (cnst "c1",fun _ _ => (cnst "c2",tt))).
    extract. solverec. (* Now the solution is clear *)
  Abort.

  Goal computableTime orb (fun _ _ => (1,fun _ _ => (3,tt))).
    extract. solverec.
  Abort.
  
  Import Datatypes.LNat.
  
  Goal computable Nat.add.
    unfold Nat.add.
    extractAs s.
    computable_using_noProof s.
    cstep.
    all:cstep.
    all:cstep.
  Qed.

  Goal computable (fix f (x y z : nat) := y + match y with |  S (S y) => S (f x y z) | _ => 0 end).
    extractAs s.
    computable_using_noProof s.
    cstep.
    all:cstep.
    all:cstep.
    all:cstep.
  Qed.

  
  
  Lemma supported3 : computable (fun (b:bool) => if b then (fix f x := match x with S x => f x | 0 => 0 end) else S).
    extractAs s.
    computable_using_noProof s.
    cstep.
    cstep.
    all:cstep.
    all:cstep.
  Qed.


  (* this is due to https://github.com/coq/coq/issues/9761 *)
  Lemma unsupported : computable (fix f (y : nat) {struct y}:= match y with | S (S y) => f y | _ => S end).
    extractAs s.
    computable_using_noProof s.
    repeat cstep.
    Fail Guarded.
  Abort.

    (* this is due to https://github.com/coq/coq/issues/9761 *)
  Lemma workarround : let f := (fix f (z y : nat) {struct y}:= match y with | S (S y) => f z y | _ => S z end) in computable (fun y z => f z y).
    intros f. assert (computable f) by (unfold f;extract).
    extract.
  Qed.

  Lemma unsupported2 :  computable 10.
    extract. (* not true*) Fail reflexivity. 
  Abort.
  (* not a problem inside a function*)
  Goal computable (fun n : nat => 10).
    extract.
  Qed.

  

  Import Datatypes.Lists.
  Remove Hints term_map : typeclass_instances. 

  Example correct_recursive A B  (Rx : registered A)  (Ry: registered B):
    computable (@map A B).
    extractAs s.
    computable_using_noProof s.
    cstep;rename x into f.
    (** Goal: [computes (! list A ~> ! list B) (fix map (l : list A) : list B := match l with
                                                                    | [] => []
                                                                    | a :: t => f a :: map t
                                                                    end)
            (rho (lam (lam ((O (ext [])) (lam (lam (((ext cons) ((ext f) 1)) (3 0))))))))] *)

    (** Here the magic happens: *)
    cstep.
    (** New assumption (fix, so only to be called on smaller arguments):
   [IHP : forall x0 : list A,
        True ->
        True ->
        {v : term &
        computesExp (! list B) ((fix map (l : list A) : list B := match l with
                                                                  | [] => []
                                                                  | a :: t => f a :: map t
                                                                  end) x0) (P (enc x0)) v} ] *)
    (** Subgoal 1: [computes (! list B) [] (enc [])] *) 
    (** Subgoal 2: [computes (! list B) (x a :: (fix map (l0 : list A) : list B := match l0 with
                                                                | [] => []
                                                                | a0 :: t => x a0 :: map t
                                                                end) l)
   (enc (x a :: (fix map (l0 : list A) : list B := match l0 with
                                                   | [] => []
                                                   | a0 :: t => x a0 :: map t
                                                   end) l))] *)
    all:cstep.
  Qed.

  (* coming up with the condition, with intemrediate steps *)

  Example comeUp_timebound_withInternalTactics A B (Rx : registered A)  (Ry: registered B):
    computableTime (@map A B) (fun f fT => (cnst "c",fun xs _ => (cnst ("f",xs),tt))).
    extractAs s.
    computable_using_noProof s.
    cstep.
    cstep.
    repeat cstep.
  Abort.
  
  (** coming up with the time bound *)

  Lemma comeUp_timebound A B (Rx : registered A)  (Ry: registered B):
    computableTime (@map A B) (fun f fT => (cnst "c",fun xs _ => (cnst ("f",xs),tt))).
    extract. solverec.
    (** Subgoal 1: [1 <= cnst "c"] *)
    (** Subgoal 2: [7 <= cnst ("f", [])] *)
    (** Subgoal 3: [fst (xT a tt) + cnst ("f", l) + 11 <= cnst ("f", a :: l) ] *)
  Abort.

  Lemma term_map (X Y:Type) (Hx : registered X) (Hy:registered Y):
    computableTime (@map X Y)
                   (fun f fT => (1,fun l _ => (fold_right (fun x res => fst (fT x tt) + res + 11) 7 l,tt))).
  Proof.
    extract.
    solverec.
  Qed.

  End PaperExample. 


  Instance term_nat_eqb : computable Nat.eqb.
  Proof.
    extract. fold Nat.eqb. repeat ComputableTactics.Intern.cstep. 
  Defined.

End demo.

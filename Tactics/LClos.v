Require Export L.

(** **** Closure calculus *)

Inductive Comp : Type :=
| CompVar (x:nat)
| CompApp (s : Comp) (t : Comp) : Comp
| CompClos (s : term) (A : list Comp) : Comp.                      

Coercion CompApp : Comp >-> Funclass.

Inductive lamComp : Comp -> Prop := lambdaComp s A: lamComp (CompClos (lam s) A).

Inductive validComp : Comp -> Prop :=
| validCompApp s t : validComp s -> validComp t -> validComp (s t)
| validCompClos (s : term) (A : list Comp) :
     (forall a, a el A -> validComp a) -> (forall a, a el A -> lamComp a) -> bound (length A) s -> validComp (CompClos s A).

Hint Constructors Comp lamComp validComp.

Definition validEnv A := forall a, a el A -> validComp a (*/\ lamComp a)*).

Definition validEnv' A := forall a, a el A -> closed a.

Hint Unfold validEnv validEnv'.

Lemma validEnv_cons a A : validEnv (a::A) <-> ((validComp a) /\ validEnv A).
Proof.
  unfold validEnv. simpl. split. auto. intros [? ?] a' [eq|el']; subst;auto.
Qed.

Lemma validEnv'_cons a A : validEnv' (a::A) <-> (closed a /\ validEnv' A).
Proof.
  unfold validEnv'. simpl. intuition. now subst.
Qed.

Ltac inv_validComp :=
  match goal with
    | H : validComp (CompApp _ _) |- _ => inv H
    | H : validComp (CompClos _ _)   |- _ => inv H
  end.
  
Definition Comp_ind_deep'
           (P : Comp -> Prop)
           (Pl : list Comp -> Prop)
           (IHVar : forall x : nat, P (CompVar x))
           (IHApp : forall s : Comp, P s -> forall t : Comp, P t -> P (s t))
           (IHClos : forall (s : term) (A : list Comp),
                       Pl A -> P (CompClos s A))
           (IHNil : Pl nil)
           (IHCons : forall (a:Comp) (A : list Comp),
                       P a -> Pl A -> Pl (a::A))
           (x:Comp) : P x :=
  (fix f c : P c:=
     match c with
       | CompVar x => IHVar x
       | CompApp s t => IHApp s (f s) t (f t)
       | CompClos s A => IHClos s A 
         ((fix g A : Pl A := 
            match A with
                [] => IHNil
              | a::A => IHCons a A (f a) (g A)
            end) A)
     end) x
.

Definition Comp_ind_deep
           (P : Comp -> Prop)
           (IHVar : forall x : nat, P (CompVar x))
           (IHApp : forall s : Comp, P s -> forall t : Comp, P t -> P (s t))
           (IHClos : forall (s : term) (A : list Comp),
                       (forall a, a el A -> P a) -> P (CompClos s A)) : forall x, P x.
Proof.
  apply Comp_ind_deep' with (Pl:=fun A => (forall a, a el A -> P a));auto.
  intros. inv H1;auto. 
Qed.

Fixpoint substList (s:term) (x:nat) (A: list term): term := 
  match s with
    | var n => if Dec (x>n) then var n else nth (n-x) A (var n)
    | app s t => (substList s x A) (substList t x A)
    | lam s => lam (substList s (S x) A)
  end.
  

Fixpoint deClos (s:Comp) : term := 
  match s with
    | CompVar x => var x
    | CompApp s t => (deClos s) (deClos t)
    | CompClos s A => substList s 0 (map deClos A)
  end.

(* Reduction *)

Reserved Notation "s '>[(' l ')]' t" (at level 50, format "s  '>[(' l ')]'  t").

Inductive CPow : nat -> Comp -> Comp -> Prop :=
| CPowRefl (s:Comp) : s >[(0)] s                                                      
| CPowTrans (s t u:Comp) i j : s >[(i)] t -> t >[(j)] u -> s >[(i+j)] u
| CPowAppL (s s' t :Comp) l: s >[(l)] s' -> (s t) >[(l)] (s' t)                                  
| CPowAppR (s t t':Comp) l: t >[(l)] t' -> (s t) >[(l)] (s t')
| CPowApp  (s t:term) (A:list Comp) :
    CompClos (s t) A >[(0)] (CompClos s A) (CompClos t A)
| CPowVar (x:nat) (A:list Comp):
    CompClos (var x) A >[(0)] nth x A (CompVar x)
| CPowVal (s t:term) (A B:list Comp):
    lambda t -> (CompClos (lam s) A) (CompClos t B) >[(1)] (CompClos s ((CompClos t B)::A))
where "s  '>[(' l ')]'  t" := (CPow l s t)  : LClos.

Open Scope LClos.

Ltac inv_CompStep :=
  match goal with
    | H : (CompApp _ _) >(_) CompClos _ _ |- _ => inv H
    | H : (CompClos _ _) >(_) CompApp _ _ |- _ => inv H
  end.

Hint Constructors CPow.

Lemma CPow_congL n s s' t :
  s >[(n)] s' ->  s t >[(n)] s' t.
Proof.
  induction 1;eauto.
Qed.

Lemma CPow_congR n (s t t' : Comp) :
  t >[(n)] t' ->  s t >[(n)] s t'.
Proof.
  induction 1;eauto.
Qed.

Lemma CPow_trans s t u i j k : s >[(i)] t -> t >[(j)] u -> i + j = k -> s >[(k)] u.
Proof.
  intros. subst. eauto.
Qed.


Instance CPow'_App_properR n:
  Proper (eq ==> (CPow n) ==> (CPow n)) CompApp.
Proof.
  intros ? ? -> ? ?  ?. now eapply CPow_congR. 
Qed.

Lemma substList_bound x s A: bound x s -> substList s x A = s.
Proof.
  revert x;induction s;intros;simpl.
  -inv H. decide (x>n);tauto.
  -inv H. now rewrite IHs1,IHs2.
  -inv H. rewrite IHs;auto. 
Qed.

Lemma substList_closed s A x: closed s -> substList s x A = s.
Proof.
  intros. apply substList_bound. destruct x. now apply closed_dcl. eapply bound_gt;[rewrite <- closed_dcl|];auto. omega.
Qed.

Lemma substList_var' y x A: y >= x -> substList (var y) x A = nth (y-x) A (var y).
Proof.
  intros ge. simpl. decide (x>y). omega. auto. 
Qed.

Lemma substList_var y A: substList (var y) 0 A = nth y A (var y).
Proof.
  rewrite substList_var'. f_equal. omega. omega.
Qed.

Lemma substList_is_bound y A s: validEnv' A -> bound (y+|A|) (s) -> bound y (substList s y A).
Proof.
  intros vA. revert y. induction s;intros y dA.
  -apply closed_k_bound. intros k u ge. simpl. decide (y>n). 
   +simpl. destruct (Nat.eqb_spec n k). omega. auto.
   +inv dA. assert (n-y<|A|) by omega. now rewrite (vA _ (nth_In A n H)).
  -inv dA. simpl. constructor;auto.
  -simpl. constructor. apply IHs. now inv dA.
Qed.

Lemma substList_closed' A s: validEnv' A -> bound (|A|) (s) -> closed (substList s 0 A).
Proof.
  intros. rewrite closed_dcl. apply substList_is_bound;auto.
Qed.



Lemma deClos_valComp a: validComp a -> closed (deClos a).
Proof.
  intros va. induction va;simpl.
  -now apply app_closed.
  -apply substList_closed'. intros a ain. rewrite in_map_iff in ain. destruct ain as [a' [eq a'in]];subst. now apply H0. now rewrite map_length.
Qed.

Lemma deClos_validEnv A : validEnv A -> validEnv' (map deClos A).
Proof.
  intros vA. induction A;simpl.
  -unfold validEnv'. simpl. tauto.
  -rewrite validEnv'_cons.  apply validEnv_cons in vA as [ca cA]. split;auto. apply deClos_valComp; auto.
Qed.

Hint Resolve deClos_validEnv.

Lemma subst_substList x s t A: validEnv' A -> subst (substList s (S x) A) x t = substList s x (t::A).
Proof.
  revert x;induction s;simpl;intros x cl.
  -decide (S x > n);simpl. decide (x>n); destruct (Nat.eqb_spec n x);try omega;try tauto. subst. now rewrite minus_diag. decide (x>n). omega. destruct (n-x) eqn: eq. omega. assert (n2=n-S x) by omega. subst n2. destruct (nth_in_or_default (n-S x) A n).
   + apply cl in i. now rewrite i.
   +rewrite e. simpl. destruct (Nat.eqb_spec n x). omega. auto. 
  -now rewrite IHs1,IHs2.
  -now rewrite IHs.
Qed.

Lemma validComp_step s t l: validComp s -> s >[(l)] t -> validComp t.
Proof with repeat (subst || firstorder).
  intros vs R. induction R;repeat inv_validComp...
  -inv H3. constructor...
  -inv H3. apply H1. apply nth_In. omega.
  -inv H8. constructor;auto;intros a [?|?];subst;auto.
Qed.

Hint Resolve validComp_step.

Lemma deClos_correct l s t : validComp s -> s >[(l)] t -> deClos s >(l) deClos t.
Proof with repeat (cbn in * || eauto 10 using star || congruence || omega || subst).
  intros cs R.
  induction R...
  -eapply pow_trans;eauto.
  -inv cs;apply pow_step_congL...
  -inv cs;apply pow_step_congR...
  -rewrite <- minus_n_O. rewrite <-map_nth with (f:=deClos)...
  -inv H. inv cs. inv H1. eexists;split... rewrite <- subst_substList... 
Qed.


Lemma substList_nil s x: substList s x [] = s.
Proof.
  revert x. induction s;intros;simpl.
  -decide (x>n). reflexivity. now destruct(n-x).
  -congruence.
  -congruence.
Qed.

Lemma validComp_closed s: closed s -> validComp (CompClos s []).
Proof.
  intros cs. constructor;simpl;try tauto. now apply closed_dcl.
Qed.

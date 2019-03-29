Require Export ARS.
Require Export Shared.Base Shared.Bijection MoreBase.

Hint Constructors ARS.star : cbv.

(** * The call-by-value lambda calculus L *)

(** ** Syntax   *)

Inductive term : Type :=
| var (n : nat) : term
| app (s : term) (t : term) : term
| lam (s : term).

Notation "'#' v" := (var v) (at level 1).
(* Notation "(λ  s )" := (lam s) (right associativity, at level 0).  *)

Instance term_eq_dec : eq_dec term.
Proof.
  intros s t; unfold dec; repeat decide equality.
Defined.

Definition term_eq_dec_proc s t := if Dec (s = t) then true else false.

Hint Resolve term_eq_dec.

(** Notation using binders *)

Inductive hoas : Type := hv (n : nat) | ha (s t : hoas) | hl (f : nat -> hoas) | hter (t : term).

Fixpoint TH n s :=
  match s with
  | hv m => var (n - m - 1)
  | ha s t => app (TH n s) (TH n t)
  | hl f => lam (TH (S n) (f n))
  | hter t => t
  end.

(* Fixpoint H L s := *)
(*   match s with *)
(*   | var n => hv (nth n L 0) *)
(*   | app s t => ha (H L s) (H L t) *)
(*   | lam s => hl (fun x => H (x :: L) s) *)
(*   end. *)

Definition convert:=TH 0.
Coercion convert : hoas >-> term.

Coercion var : nat >-> term.

Coercion hv : nat >-> hoas.
Coercion ha : hoas >-> Funclass.

Coercion app : term >-> Funclass. 

(* Use Eval simpl in (term) when defining an term using convert.
This converts while defining and therefore makes all later steps faster.
See "important terms" below

Also: remember to give the type of combinators explicitly becuase we want to use the coercion!
(e.g. "Definition R:term := ..." )*) 

Arguments convert /.

Notation "'λ' x .. y , p" := (hl (fun x => .. (hl (fun y => p)) ..))
  (at level 100, x binder, right associativity,
   format "'[' 'λ'  '/  ' x  ..  y ,  '/  ' p ']'").

Notation "'!!' s" := (hter s) (at level 0).
Coercion hter : term >-> hoas.

(** Important terms *)

Definition r : term := Eval simpl in λ r f, f (λ x , r r f x). 
Definition R : term := r r.

Definition rho s : term := Eval simpl in λ x, r r s x. 

Definition I : term := Eval simpl in λ x, x.
Definition K : term := Eval simpl in λ x y, x.

Definition omega : term := Eval simpl in λ x , x x.
Definition Omega : term := omega omega.

(**  Substitution *)

Fixpoint subst (s : term) (k : nat) (u : term) :=
  match s with
      | var n => if Nat.eqb n k then u else (var n)
      | app s t => app (subst s k u) (subst t k u)
      | lam s => lam (subst s (S k) u)
  end.

(** Important definitions *)

Definition closed s := forall n u, subst s n u = s.

Definition lambda s := exists t, s = lam t.

Definition proc s := closed s /\ lambda s.

Lemma lambda_lam s : lambda (lam s).
Proof.
  exists s; reflexivity.
Qed.

Hint Resolve lambda_lam.

Instance lambda_dec s : dec (lambda s).
Proof.
  destruct s;[right;intros C;inv C;congruence..|left;eexists;eauto].
Defined.


(** Size of terms *)

Fixpoint size (t : term) :=
  match t with
  | var n => 1 + n
  | app s t => 1+ size s + size t
  | lam s => 1 + size s
  end.

Fixpoint size' (t : term) :=
  match t with
  | var n => 0
  | app s t => 1+ size' s + size' t
  | lam s => 1 + size' s
  end.

(** Alternative definition of closedness *)

Inductive bound : nat -> term -> Prop :=
  | dclvar k n : k > n -> bound k (var n)
  | dclApp k s t : bound k s -> bound k t -> bound k (s t)
  | dcllam k s : bound (S k) s -> bound k (lam s).

Lemma bound_closed_k s k u : bound k s -> subst s k u = s.
Proof with eauto.
  intros H; revert u; induction H; intros u; simpl.
  - destruct (Nat.eqb_spec n k)... omega.
  - rewrite IHbound1, IHbound2...
  - f_equal...
Qed.

Lemma bound_ge k s : bound k s -> forall m, m >= k -> bound m s.
Proof.
  induction 1; intros m Hmk; econstructor; eauto. 
  - omega.
  - eapply IHbound. omega.
Qed.

Lemma bound_gt k s : bound k s -> forall m, m > k -> bound m s.
Proof.
  intros. apply (bound_ge H). omega.
Qed.

Lemma bound_closed s k u : bound 0 s -> subst s k u = s.
Proof.
  intros H. destruct k.
  - eapply bound_closed_k. eassumption.
  - eapply bound_gt in H. eapply bound_closed_k. eassumption. omega.
Qed.

Lemma closed_k_bound k s : (forall n u, n >= k -> subst s n u = s) -> bound k s.
Proof.
  revert k. induction s; intros k H.
  - econstructor. specialize (H n (#(S n))). simpl in H.
    decide (n >= k) as [Heq | Heq].
    + destruct (Nat.eqb_spec n n); [injection (H Heq)|]; omega. 
    + omega.
  - econstructor; [eapply IHs1 | eapply IHs2]; intros n u Hnk;
    injection (H n u Hnk); congruence.
  - econstructor. eapply IHs. intros n u Hnk.
    destruct n. omega.
    injection (H n u). tauto. omega.
Qed.

Lemma closed_dcl s : closed s <-> bound 0 s.
Proof.
  split.
  -eauto using closed_k_bound.
  -unfold closed. eauto using bound_closed.
Qed.

Lemma closed_app (s t : term) : closed (s t) -> closed s /\ closed t.
Proof.
  intros cls. rewrite closed_dcl in cls. inv cls. split; rewrite closed_dcl; eassumption.
Qed.

Lemma app_closed (s t : term) : closed s -> closed t -> closed (s t).
Proof.
  intros H H' k u. simpl. now rewrite H, H'.
Qed.

Instance bound_dec k s : dec (bound k s).
Proof with try ((left; econstructor; try omega; tauto) || (right; inversion 1; try omega; tauto)).
  revert k; induction s; intros k.
  - destruct (le_lt_dec n k) as [Hl | Hl]... destruct (le_lt_eq_dec _ _ Hl)...
  - destruct (IHs1 k), (IHs2 k)...
  - induction k.
    + destruct (IHs 1)...
    + destruct (IHs (S (S k)))...
Defined.

Instance closed_dec s : dec (closed s).
Proof.
  decide (bound 0 s);[left|right];now rewrite closed_dcl.
Defined.

(* This already works! *)
Lemma proc_dec s : dec (proc s).
Proof.
  exact _.
Qed.


(** ** Reduction *)

Reserved Notation "s '>>' t" (at level 50).

Inductive step : term -> term -> Prop :=
| stepApp  s t     : app (lam s) (lam t) >> subst s 0 (lam t)
| stepAppR s t  t' : t >> t' -> app s t >> app s t'
| stepAppL s s' t  : s >> s' -> app s t >> app s' t
where "s '>>' t" := (step s t).

Hint Constructors step.

Ltac inv_step :=
  match goal with
    | H : step (lam _) _ |- _ => inv H
    | H : step (var _) _ |- _ => inv H
    | H : star step (lam _) _ |- _ => inv H
    | H : star step (var _) _ |- _ => inv H
  end.

Lemma closed_subst s t k : bound (S k) s -> bound k t -> bound k (subst s k t).
Proof.
  revert k t; induction s; intros k t cls_s cls_t; simpl; inv cls_s; eauto 6 using bound, bound_gt.
  destruct (Nat.eqb_spec n k); eauto. econstructor.  omega.
Qed.
  
Lemma closed_step s t : s >> t -> closed s -> closed t.
Proof.
  rewrite !closed_dcl; induction 1; intros cls_s; inv cls_s; eauto using bound.
  inv H2. eauto using closed_subst.
Qed.

Lemma comb_proc_red s : closed s -> proc s \/ exists t, s >> t.
Proof with try tauto.
  intros cls_s. induction s.
  - eapply closed_dcl in cls_s. inv cls_s. omega.
  - eapply closed_app in cls_s. destruct IHs1 as [[C [t A]] | A], IHs2 as [[D [t' B]] | B]...
    + right. subst. eexists. eauto.
    + right; subst. firstorder; eexists. eapply stepAppR. eassumption.
    + right; subst. firstorder; eexists. eapply stepAppL. eassumption.
    + right. subst. firstorder. eexists. eapply stepAppR. eassumption.
  - left. split. eassumption. firstorder.
Qed.

Goal forall s, closed s -> ((~ exists t, s >> t) <-> proc s).
Proof.
  intros s cls_s. split.
  destruct (comb_proc_red cls_s).
  - eauto.
  - tauto.
  - destruct 1 as [? [? ?]]. subst. destruct 1 as [? B]. inv B.
Qed.

(** Properties of the reduction relation *)

Theorem uniform_confluence : uniform_confluent step.
Proof with repeat inv_step; eauto using step.
  intros s; induction s; intros t1 t2 step_s_t1 step_s_t2; try now inv step_s_t2.
  inv step_s_t1.
  - inv step_s_t2; try eauto; inv_step.
  - inv step_s_t2...
    + destruct (IHs2 _ _ H2 H3).
      * left. congruence.
      * right. destruct H as [u [A B]]...
    + right... 
  - inv step_s_t2...
    + right...
    + destruct (IHs1 _ _ H2 H3).
      * left. congruence.
      * right. destruct H as [u [A B]]... 
Qed.

Notation "s '>(' l ')' t" := (pow step l s t) (at level 50, format "s  '>(' l ')'  t").
Arguments pow: simpl never.

Lemma confluence : confluent step.
Proof.
  intros x y z x_to_y x_to_z.
  eapply star_pow in x_to_y. destruct x_to_y as [n x_to_y].
  eapply star_pow in x_to_z. destruct x_to_z as [m x_to_z].
  destruct (parametrized_confluence uniform_confluence x_to_y x_to_z) as
      [k [l [u [_ [_ [C [D _]]]]]]].
  exists u. split; eapply star_pow; eexists; eassumption.
Qed.

Lemma step_Lproc s v :
  lambda v -> (lam s) v >> subst s 0 v.
Proof.
  intros [t lamv].
  rewrite lamv.
  repeat econstructor.
Qed.

(** Properties of the reflexive, transitive closure of reduction *)

Notation "s '>*' t" := (star step s t) (at level 50).

Instance star_PreOrder : PreOrder (star step).
Proof.
  constructor; hnf.
  - eapply starR.
  - eapply star_trans. 
Defined.

Lemma step_star s s':
  s >> s' -> s >* s'.
Proof.
  eauto using star. 
Qed.

Instance step_star_subrelation : subrelation step (star step).
Proof.
  cbv. apply step_star.
Defined.

Lemma star_trans_l s s' t :
  s >* s' -> s t >* s' t.
Proof.
  induction 1; eauto using star, step. 
Qed.

Lemma star_trans_r (s s' t:term):
  s >* s' -> t s >* t s'.
Proof.
  induction 1; eauto using star, step.
Qed.

Instance star_step_app_proper :
  Proper ((star step) ==> (star step) ==> (star step)) app.
Proof.
  cbv. intros s s' A t t' B.
  etransitivity. apply (star_trans_l _ A). now apply star_trans_r.
Defined.

Lemma closed_star s t: s >* t -> closed s -> closed t.
Proof.
  intros R. induction R;eauto using closed_step. 
Qed.

Instance star_closed_proper :
  Proper ((star step) ==> Basics.impl) closed.
Proof.
  exact closed_star.
Defined.

(**  Properties of star: *)

Instance pow_step_congL k:
  Proper ((pow step k) ==> eq ==> (pow step k)) app.
Proof.
  intros s t R u ? <-. revert s t R u.
  induction k;cbn in *;intros ? ? R ?. congruence. destruct R as [s' [R1 R2]].
  exists (s' u). firstorder.
Defined.

Instance pow_step_congR k:
  Proper (eq ==>(pow step k) ==> (pow step k)) app.
Proof.
  intros s ? <- t u R. revert s t u R.
  induction k;cbn in *;intros ? ? ? R. congruence. destruct R as [t' [R1 R2]].
  exists (s t'). firstorder.
Defined.

(** Equivalence *)

Reserved Notation "s '==' t" (at level 50).

Inductive equiv : term -> term -> Prop :=
  | eqStep s t : step s t -> s == t
  | eqRef s : s == s
  | eqSym s t : t == s -> s == t
  | eqTrans s t u: s == t -> t == u -> s == u
where "s '==' t" := (equiv s t).

Hint Immediate eqRef.


(** Properties of the equivalence relation *)

Instance equiv_Equivalence : Equivalence equiv.
Proof.
  constructor; hnf.
  - apply eqRef.
  - intros. eapply eqSym. eassumption.
  - apply eqTrans.
Qed.

Lemma equiv_ecl s t : s == t <-> ecl step s t.
Proof with eauto using ecl, equiv.
  split; induction 1...
  - eapply ecl_sym... 
  - eapply ecl_trans... 
Qed.

Lemma church_rosser s t : s == t -> exists u, s >* u /\ t >* u.
Proof.
  rewrite equiv_ecl. eapply confluent_CR, confluence.
Qed.

Lemma star_equiv s t :
  s >* t -> s == t.
Proof.
  induction 1.
  - reflexivity.
  - eapply eqTrans. econstructor; eassumption. eassumption.
Qed.
Hint Resolve star_equiv.

Instance star_equiv_subrelation : subrelation (star step) equiv.
Proof.
  cbv. apply star_equiv.
Qed.

Instance step_equiv_subrelation : subrelation step equiv.
Proof.
  cbv. intros ? ? H. apply star_equiv, step_star. assumption.
Qed.

(*
Lemma equiv_lambda' s t : s == (lam t) -> s >* (lam t).
Proof.
  intros H. destruct (church_rosser H) as [u [A B]]; repeat inv_step; eassumption.
Qed.*)

Lemma equiv_lambda s t : lambda t -> s == t -> s >* t.
Proof.
  intros H eq. destruct (church_rosser eq) as [u [A B]]. inv B. assumption. inv H. inv H0.
Qed.

Lemma eqStarT s t u : s >* t -> t == u -> s == u.
Proof.
  eauto using equiv.
Qed.

Lemma eqApp s s' u u' : s == s' -> u == u' -> s u == s' u'.
Proof with eauto using equiv, step.
  intros H; revert u u'; induction H; intros z z' H'...
  - eapply eqTrans. eapply eqStep. eapply stepAppL. eassumption.
    induction H'...
  - induction H'...   
Qed.

Instance equiv_app_proper :
  Proper (equiv ==> equiv ==> equiv) app.
Proof.
  cbv. intros s s' A t t' B.
  eapply eqApp; eassumption.
Qed.


(** Definition of convergence *)

Definition converges s := exists t, s == t /\ lambda t.

Lemma converges_equiv s t : s == t -> (converges s <-> converges t).
Proof.
  intros H; split; intros [u [A lu]]; exists u;split;try assumption; rewrite <- A.
  - symmetry. eassumption.
  - eassumption.
Qed.

Instance converges_proper :
  Proper (equiv ==> iff) converges.
Proof.
  intros s t H. now eapply converges_equiv.
Qed.
(*
Lemma eq_lam s t : lambda s -> lambda t -> lam s == lam t <-> s = t.
Proof.
  split.
  - intros H. eapply equiv_lambda in H; repeat inv_step; reflexivity.
  - intros []. reflexivity.
Qed.  

Lemma unique_normal_forms' (s t t' : term) : s == lam t -> s == lam t' -> lam t = lam t'.
Proof.
  intros Ht Ht'. rewrite Ht in Ht'. eapply eq_lam in Ht'. congruence.
Qed.*)

Lemma unique_normal_forms (s t : term) : lambda s -> lambda t ->  s == t -> s = t.
Proof.
  intros ls lt. intros H. apply equiv_lambda in H;try assumption. inv ls. inv H. reflexivity. inv H0.
Qed.

(** Eta expansion *)

Lemma Eta (s : term ) t : closed s -> lambda t -> (lam (s #0)) t == s t.
Proof.  intros cls_s lam_t. eapply star_equiv, starC; eauto using step_Lproc. simpl. rewrite cls_s. reflexivity.
Qed.

(** Useful lemmas *)

Lemma pow_trans s t u i j: pow step i s t -> pow step j t u -> pow step (i+j) s u.
Proof.
  intros. subst. apply pow_add. now exists t.
Qed.

Instance pow_star_subrelation i: subrelation (pow step i) (star step).
Proof.
  intros ? ? ?.
  eapply pow_star;eauto.
Qed.

(** Definition of evaluation *)

Definition eval s t := s >* t /\ lambda t.
Notation "s '⇓' t" := (eval s t) (at level 51).
Hint Unfold eval.

Instance eval_star_subrelation : subrelation eval (star step).
Proof.
  now intros ? ? [].
Qed.

Instance reduce_eval_proper : Proper (Basics.flip (star step) ==> eq ==> Basics.impl) eval.
Proof.
  repeat intro. subst. unfold Basics.flip in H. destruct H1. split. etransitivity. eassumption. assumption. assumption.
Defined.

Instance equiv_eval_proper: Proper (equiv ==> eq ==> Basics.impl) eval.
Proof.
  repeat intro;subst. destruct H1. split;try auto. apply equiv_lambda. auto. now rewrite <- H0, H.
Qed.

Definition evalIn i s t := s >(i) t /\ lambda t.

Notation "s '⇓(' l ')' t" := (evalIn l s t) (at level 50, format "s  '⇓(' l ')'  t").

Definition redLe l s t := exists i , i <= l /\ pow step i s t.
Notation "s '>(<=' l ')' t" := (redLe l s t) (at level 50, format "s  '>(<=' l ')'  t").

Definition evalLe l s t := s >(<=l) t /\ lambda t.
Notation "s '⇓(<=' l ')' t" := (evalLe l s t) (at level 50, format "s  '⇓(<=' l ')'  t").

Instance evalLe_eval_subrelation i: subrelation (evalLe i) eval.
Proof.
  intros ? ? [[? []] ?]. split. eapply pow_star_subrelation. all:eauto. 
Qed.

Instance evalIn_evalLe_subrelation i: subrelation (evalIn i) (evalLe i).
Proof.
  intros s t (R & lt). split;[now exists i|trivial]. 
Qed.

Instance pow_redLe_subrelation i: subrelation (pow step i) (redLe i).
Proof.
  intros s t R. now exists i. 
Qed.

Instance evalLe_redLe_subrelation i: subrelation (evalLe i) (redLe i).
Proof.
  now intros ? ? [].
Qed.

Instance redLe_star_subrelation i: subrelation (redLe i) (star step).
Proof.
  intros ? ? (j & leq & R). now rewrite R. 
Qed.

Instance le_redLe_proper: Proper (le ==> eq ==> eq ==> Basics.impl) redLe.
Proof.
  intros ? ? ? ? ? -> ? ? -> (i&lt&R).
  exists i. split. omega. tauto.
Qed.

Instance le_evalLe_proper: Proper (le ==> eq ==> eq ==> Basics.impl) evalLe.
Proof.
  intros ? ? H' ? ? -> ? ? -> [H p].
  split. 2:tauto. now rewrite <- H'.
Qed.

Lemma evalIn_trans s t u i j :
  s >(i) t -> t ⇓(j) u -> s ⇓(i+j) u.
Proof.
  intros R1 [R2 lam].
  split; eauto using pow_trans.  
Defined.

Lemma redLe_trans s t u i j :
  s >(<=i) t -> t >(<=j) u -> s >(<=i+j) u.
Proof.
  intros [i' [? R1]] [j' [? R2]].
  exists (i'+j'). split. omega. apply pow_add. hnf; eauto.
Qed.

Lemma redLe_trans_eq s t u i j k :
  i+j=k ->  s >(<=i) t -> t >(<=j) u -> s >(<=k) u.
Proof.
  intros;subst;eauto using redLe_trans.  
Qed.

Lemma evalLe_trans s t u i j :
  s >(<=i) t -> t ⇓(<=j) u -> s ⇓(<=i+j) u.
Proof.
  intros R1 [R2 lam].
  split; eauto using redLe_trans.  
Defined.

Instance pow0_refl : Reflexive (pow step 0).
Proof.
  intro. reflexivity.
Qed.

Instance redLe_refl : Reflexive (redLe 0).
Proof.
  intro. eexists; split;reflexivity.  
Qed.

(* Helpfull Lemmas*)

Lemma pow_trans_lam' t v s k j:
  lambda v -> pow step j t v -> pow step k t s  -> j>=k /\ pow step (j-k) s v.
Proof.
  intros lv A B.
  destruct (parametrized_confluence uniform_confluence A B) 
     as [m' [l [u [m_le_Sk [l_le_n [C [D E]]]]]]].
  cut (m' = 0).
  -intros ->. split. omega. replace (j-k) with l by omega. hnf in C. subst v. tauto. 
  -destruct m'; eauto. destruct C. destruct H. inv lv. inv H.
Qed.

Lemma evalLe_trans_rev t v s k j:
  evalLe j t v -> pow step k t s  -> j>=k /\ evalLe (j-k) s v.
Proof.
  intros [(i&lti&R) lv] B.
  edestruct (pow_trans_lam' lv R B). split. omega. split. 2:tauto. eexists;split. 2:eauto. omega. 
Qed.

Lemma pow_trans_lam t v s k n :
  lambda v -> pow step n t v -> pow step (S k) t s  -> exists m, m < n /\ pow step m s v.
Proof.
  intros H1 H2 H3. edestruct (pow_trans_lam' H1 H2 H3) as (H'1&H'2). do 2 eexists. 2:eassumption. omega.
Qed.

Lemma powSk t t' s : t >> t' -> t' >* s -> exists k, pow step (S k) t s.
Proof.
  intros A B.
  eapply star_pow in B. destruct B as [n B]. exists n.
  unfold pow. simpl. econstructor. unfold pow in B. split; eassumption.
Qed.

(* Properties of rho *)



Lemma rho_dcls n s : bound (S n) s -> bound n (rho s).
Proof.
  unfold rho,r. intros H. repeat (apply dcllam || apply dclApp || apply dclvar);try assumption;try omega.
Qed.

Lemma closed_dcl_x x s: closed s -> bound x s.
Proof.
  intros. apply (@bound_ge 0). now apply closed_dcl. omega.
Qed.
Lemma rho_cls s : closed s -> closed (rho s).
Proof.
  intros. rewrite closed_dcl.  apply rho_dcls. now apply closed_dcl_x. 
Qed.

Lemma rho_lambda s : lambda (rho s).
Proof.
  eexists. reflexivity.
Qed.

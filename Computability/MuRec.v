Require Export LNat LBool LTactics Computability.

Section MuRecursor.

Variable P : term.
Hypothesis P_proc : proc P.
Hint Resolve P_proc : LProc.

Hypothesis dec'_P : forall (n:nat), (exists (b:bool), P (ext n) == ext b ).

Lemma dec_P : forall n:nat, {b:bool | P (ext n) == ext b}.
  intros. eapply lcomp_comp.
  -apply bool_enc_inv_correct.
  -apply dec'_P.
Qed.

Definition mu' := Eval cbn -[enc] in rho (λ mu P n, (P n) (!!K n) (λ Sn, mu P Sn) (!!(ext S) n)).

Lemma mu'_proc : proc mu'.
  unfold mu'; Lproc. 
Qed.

Hint Resolve mu'_proc : LProc.

Lemma mu'_n_false n: P (ext n)  == ext false -> mu' P (ext n) >* mu' P (ext (S n)).
Proof.
  intros R. apply equiv_lambda in R;[|Lproc]. recStep mu'. unfold K. Lsimpl. 
Qed.

Lemma mu'_0_false n: (forall n', n' < n -> P (ext n')  == ext false) -> mu' P (ext 0) >* mu' P (ext n).
Proof.
  intros H. induction n.
  -reflexivity.
  -rewrite IHn. 
   +apply mu'_n_false. apply H. omega.
   +intros. apply H. omega. 
Qed.

Lemma mu'_n_true (n:nat): P (ext n)  == ext true -> mu' P (ext n) == ext n.
Proof.
  intros R. recStep mu'. Lsimpl. rewrite R. unfold K.  Lsimpl.
Qed.

Lemma mu'_sound v n: proc v -> mu' P (ext (n:nat)) == v ->
                     (forall n', n' < n -> P (ext n') == ext false) ->
                     exists n0, n0 >= n /\ P (ext n0) == ext true /\ v == ext n0
                                /\ forall n', n' < n0 -> P (ext (n':nat)) == ext false.
Proof.
  intros pv. intros R. apply equiv_lambda in R;try Lproc. apply star_pow in R. destruct R as [k R]. revert n R. apply complete_induction with (x:=k);clear k;intros k. intros IH n R H.
  specialize (dec_P n).
  destruct (dec_P n) as [[] eq].
  -exists n;intuition. apply pow_star in R. apply star_equiv in R. rewrite <- R. now rewrite mu'_n_true.
  -assert (R':=mu'_n_false eq). apply star_pow in R'. destruct R' as [k' R'].
   destruct (parametrized_confluence uniform_confluence R R') as [x [l [u [le1 [le2 [R1 [R2 eq']]]]]]]. destruct x.
   +inv R1. apply IH in R2 as [n0 [ge1 [Rn0 [eq0 H0]]]].
    *exists n0. repeat split;try assumption;omega.
    *decide (l=k);[|omega]. subst l. assert (k'=0) by omega. subst k'. inv R'. apply inj_enc in H1. omega.
    *intros. decide (n'=n). subst. tauto.  apply H. omega.
   +destruct R1 as [? [C _]]. destruct pv as [_ [v']]. subst v. inv C.
Qed.
  

Lemma mu'_complete n0 : P (ext n0) == ext true
                        -> (forall n', n' < n0 -> P (ext n') == ext false)
                        -> mu' P (ext 0) == ext n0.
Proof.
  intros. rewrite mu'_0_false with (n:=n0);try tauto.
  -recStep mu'. Lsimpl. rewrite H. unfold K. Lsimpl. 
Qed.

(* the mu combinator:*)


Definition mu :term := Eval cbn in λ P, mu' P (ext 0).

Lemma mu_proc : proc mu.
  unfold mu. Lproc. 
Qed.

Hint Resolve mu_proc : LProc.

Lemma mu_sound v : lambda v -> mu P == v -> exists n, v = ext n /\ P (ext n) == ext true /\ (forall n', n' < n -> P (ext n') == ext false).
Proof.
  unfold mu. intros lv R. standardizeHypo 100. apply mu'_sound in R.
  -destruct R as [n ?]. exists n. intuition. apply unique_normal_forms;try Lproc. assumption.
  -split;[|Lproc]. apply equiv_lambda in R;auto. apply closed_star in R;Lproc.
  -intros. omega.
Qed.

Lemma mu_complete (n:nat) : P (ext n) == ext true -> exists n0:nat, mu P == ext n0. 
Proof.
  remember 0 as n0.
  assert (forall n':nat, n'< n-(n-n0) -> P (ext n') == ext false) by (intros;omega).
  assert ((n-n0)+n0=n) by omega. remember (n-n0) as k. clear Heqk Heqn0 H0 n0. induction k.
  -simpl in *. subst. intros. eexists. unfold mu. Lsimpl. apply mu'_complete;eauto. intros. apply H. omega. 
  -intros. destruct (dec_P (n-S k)) as [y P'].
   destruct y.
   +eexists. unfold mu. Lsimpl. apply mu'_complete. exact P'. exact H.
   +apply IHk. intros. decide (n' = n - (S k)).
     *subst. exact P'.
     *apply H. omega.
     *assumption.
Qed.

End MuRecursor.

Hint Resolve mu'_proc : LProc.
Hint Resolve mu_proc : LProc.


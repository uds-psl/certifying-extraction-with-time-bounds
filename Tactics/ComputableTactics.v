Require Import Shared.Bijection Template.All Strings.Ascii StringBase Lproc Computable Lsimpl mixedTactics.
Require Export Ring Arith Lia.

(** ** Tactics proving correctness *)
Module Intern.
  
Ltac visibleHead t :=
  match t with
    ?h _ => visibleHead h
  | _ => t
  end.

Ltac fold_encs :=
  match goal with
    x:_ |- _ =>
    revert x;fold_encs;intros x;
    let H := fresh "H" in
    try (assert (H:@enc _ _ x= @enc _ _ x) by reflexivity;
         try (unfold enc in H at 1; cbn in H;rewrite !H);clear H)
  | _ => idtac
  end.


Ltac recRem P:=
  match goal with
  | |- context[rho ?s] =>
    let rP := fresh "rP" in
    set (rP:=s);
    assert (proc rP);[unfold rP;solve [Lproc]|
                      set (P := rho rP);
                      assert (proc P);[unfold P;solve [Lproc]|]]
  end.

Ltac recStepInit P:=
   lazymatch eval lazy [P] in P with
   | rho ?rP =>
     lazymatch goal with
     | |- evalLe _ _ _ => 
       let rec loop := 
           lazymatch goal with
           | |- ARS.pow step _ (app P _) _ =>unfold P;apply rho_correctPow;now Lproc
           | |- ARS.pow step _ (app _ _) _ => eapply pow_step_congL;[loop|reflexivity]
           end
       in
       eapply evalLe_trans;[apply pow_redLe_subrelation;loop|fold P; unfold rP]
     | |- evalIn _ _ _ =>
       let rec loop := 
           lazymatch goal with
           | |- ARS.pow step _ (app P _) _ =>unfold P;apply rho_correctPow;now Lproc
           | |- ARS.pow step _ (app _ _) _ => eapply pow_step_congL;[loop|reflexivity]
           end
       in
       eapply evalIn_trans;[loop|fold P; unfold rP]
     | |- eval _ _ =>
       let rec loop := 
           lazymatch goal with
           | |- ARS.star step (app P _) _ =>unfold P;apply rho_correct;now Lproc
           | |- ARS.star step (app _ _) _ => eapply star_step_app_proper;[loop|reflexivity]
           end
       in
       eapply eval_helper;[loop|fold P; unfold rP]
     end
   end.


Ltac recStepUnnamed :=
  match goal with
    [ P := rho _ |- ?G ] => recStepInit P
  end.


Ltac destructRefine :=
  lazymatch goal with
    |- ?R ?s _ =>
    match s with
    | context C [match ?x with _ => _ end]=>
      let t := type of x in
      refine (_:R _ ((fun y:t => ltac:(destruct y)) x));
      (* refine index if applicable*)
      lazymatch R with
        (?R' ?i) => tryif is_evar i then
          refine (_:R' ((fun (y:t) (*(_ : x=y)*) => ltac:(destruct y)) x )_ _)
        else idtac
      | _ => idtac
      end;
      lazymatch goal with
       | |- ?R2 ?i ?s ?t =>
         let i':= eval cbn zeta in i in
             refine (_:R2 i' s t) + match goal with |- ?G => let G' := constr:(R2 i' s t) in idtac "could not refine" G "with" G' end
       | _ => idtac
      end;
      destruct x
    end
  end.

Ltac extractCorrectCrush :=
  repeat(repeat destructRefine;Lsimpl).

Ltac shelveIfUnsolved msg:= first[let n:= numgoals in guard n=0|
                                  match goal with
                                    |- ?G => idtac "Could not solve some subgoal("msg"):";idtac G;shelve
                                  end].

Ltac ugly_fix_fix IH n :=
  (* we must destruct to allow the fix to reduce...*)
  lazymatch eval cbn in n with
    0 => fix IH 1
  | 1 => fix IH 4
  | 2 => fix IH 7
  | 3 => fix IH 10
  | _ => let m := eval cbn in (1+3*n) in
            fail 1000 "please add '| "n" => fix IH"m"'" " in the definition of Ltac-tactic ugly_fix_fix!"
  end.

Ltac ugly_fix_fix2 IH n :=
  (* we must destruct to allow the fix to reduce...*)
  lazymatch eval cbn in n with
    0 => fix IH 1
  | 1 => fix IH 5
  | 2 => fix IH 9
  | 3 => fix IH 13
  | _ => let m := eval cbn in (1+4*n) in
            fail 1000 "please add '| "n" => fix IH"m"'" " in the definition of Ltac-tactic ugly_fix_fix2!"
  end.
 
Ltac intro_to_assumed x :=
  lazymatch goal with
    H : Lock _ |- _  =>
    let tx := type of x in
    revert x;unlock H;revert H;
    refine (_ : (forall (x:tx), _:Prop) -> _);
    intros H x;specialize (H x);lock H
  end.

Ltac split_assumed :=
  lazymatch goal with
    H : Lock _ |- _  =>
    unlock H;
    split;[eapply proj1 in H|eapply proj2 in H];lock H
  end.

Ltac clean_assumed :=
  repeat
    lazymatch goal with
      H : Lock (_/\_) |- ?G  =>
      unlock H; apply proj2 in H;lock H
    end.

Ltac is_assumed_add :=
  lazymatch goal with
    H : Lock _ |- ?G  =>
    unlock H; refine (proj1 H);shelve
  end.

Ltac is_assumed :=
  lazymatch goal with
    H : Lock _ |- ?G  =>
    unlock H; refine H;shelve
  end.

Ltac close_assumed :=
  lazymatch goal with
    H : Lock _ |- ?G  =>unlock H;assert True by exact H
  end.

(* a non-recursive step*)
Ltac cstep :=
  let x := fresh "x" in
  lazymatch goal with
  | |- computes _ _ (match ?x with _ => _ end)=> destruct x
  | |- computes (TyArr ?tt1 ?tt2) ?f ?intF=>
    let fRep := constr:(ltac:(quote_term f (fun x => exact x))) in
    lazymatch fRep with
      (* a potentially recursive step *)
      Ast.tFix (_::_::_) => fail 1000 "mutual recursion not supported"
    | Ast.tFix [BasicAst.mkdef _ _ _(*<-dtype*) _(*<-dbody*) ?recArg(*<-recArg*)] 0 =>
      (let P := fresh "P" in
      recRem P;
      eapply computesExpStart;[solve [Lproc]|];
      let n:= (eval cbn in (S recArg)) in
      let rec step n:=
          (lazymatch n with
           |  S ?n =>
              eexists;
              eapply computesExpStep;[try recStep P;extractCorrectCrush;shelveIfUnsolved "pos5"|Lproc;shelveIfUnsolved "pos6"|];
              let x := fresh "x" in  
              let xInt := fresh x "Int" in
              let xInts := fresh x "Ints" in
              intros x xInt xInts;
              change xInt with (@ext _ _ x (Build_computable xInts));
              lazymatch type of xInts with
                computes (@TyB _ ?reg) _ _ =>
                rewrite (ext_is_enc (Build_computable xInts)) in *;
                clear xInt xInts;assert (xInt:True) by constructor; assert (xInts:True) by constructor
              | computes (TyArr _ _) _ _ => idtac
              end;
              step n;
              revert x xInt xInts
           | 0 => idtac
           end) in
      step n;
        let IH := fresh "IH" P in
        ugly_fix_fix IH recArg;
          let rec loop n := (* destruct the struct-recursive argument*)
              lazymatch n with
                0 => intros [] ? ?
              | S ?n' => intros ? ? ?;loop n'
              end in
          loop recArg;
          eexists;
          (split;[try recStep P;extractCorrectCrush;shelveIfUnsolved "pos7"|]))

    (* a non-recursive function *)
    | _=>
      let xInt := fresh x "Int" in
      let xNorm := fresh x "Norm" in
      let xInts := fresh x "Ints" in
      let vProc := fresh "vProc" in
      eapply computesTyArr;[try Lproc;shelveIfUnsolved "pos1"|idtac];
      intros x xInt xInts;
      change xInt with (@ext _ _ x (Build_computable xInts));
      lazymatch tt1 with
        TyB _ => rewrite (ext_is_enc (Build_computable xInts)) in *;
                clear xInt xInts;assert (xInt:True) by constructor; assert (xInts:True) by constructor
      | _ => idtac
      end;
      eexists;split;[extractCorrectCrush;shelveIfUnsolved "pos2" | intros vProc]
    end

  | |- computes (TyB _) _ _=> apply computesTyB

  (* with time bounds: *)                                
  | H : Lock _ |- computesTime _ _ (match ?x with _ => _ end) _=>
    let t := type of x in
    unlock H;revert H;(refine (_: ((fun z:t => ltac:(destruct z):Prop) x) -> _);intros H;lock H);
    destruct x
  | H:Lock _ |- computesTime (TyArr ?tt1 ?tt2) ?f ?intF ?T=>
    let fRep := constr:(ltac:(quote_term f (fun x => exact x))) in
    lazymatch fRep with
      Ast.tFix (_::_::_) => fail 1000 "mutual recursion not supported"
    | Ast.tFix [BasicAst.mkdef _ _ _(*<-dtype*) _(*<-dbody*) ?recArg(*<-recArg*)] 0 =>
      let P := fresh "P" in
      let H' := fresh H "'" in
      recRem P;
      eapply computesTimeExpStart;[solve [Lproc]|];
      let n:= (eval cbn in (S recArg)) in
      let rec step n:=
          (lazymatch n with
           |  S ?n' =>
              eexists;
              let x := fresh "x" in  
              let xInt := fresh x "Int" in
              let xT := fresh x "T" in
              let xInts := fresh x "Ints" in
              (refine (computesTimeExpStep (fT:=fun x xT => _) _ _ _ _) ;
               [|try recStepUnnamed;extractCorrectCrush;shelveIfUnsolved "pos8"|Lproc;shelveIfUnsolved "pos9"|]);
              [try reflexivity;is_assumed_add|];clean_assumed;
              (*simple notypeclasses refine (_:computes (_ ~> _) _ _ (fun x xInt xNorm => (_,_)));try exact tt;shelve_unifiable;*) 
              intros x xInt xT; intro_to_assumed x;intro_to_assumed xT;intro xInts;
              change xInt with (@extT _ _ x _ (Build_computableTime xInts));
              lazymatch type of xInts with
                computesTime (@TyB _ ?reg) _ _ _=>
                rewrite (extT_is_enc (Build_computableTime xInts)) in *;
                destruct xT;
                clear xInt xInts;assert (xInt:True) by constructor; assert (xInts:True) by constructor; assert (xT:True) by constructor
              | computesTime (TyArr _ _) _ _ _=> idtac
              end;
              step n';
              revert x xInt xT xInts
           | 0 => idtac
           end) in
      step n;
        
      let IH := fresh "IH" P in
      ugly_fix_fix2 IH recArg;
        let rec loop n := (* destruct the struct-recursive argument*)
            (clean_assumed;
             let x := fresh "x" in
             let xT := fresh x "T" in
             intros x ? xT ? ;
             let tx := type of x in
             let txT := type of xT in
             unlock H; revert H;refine (_ : (forall (x:_) (xT:_) , (_ :Prop)) -> _ );
             intros H;specialize (H x xT);lock H;
             lazymatch n with
               0 => unlock H;revert H;(refine (_: ((fun z:tx => ltac:(destruct z):Prop) x) -> _);intros H;lock H);
                   eexists (ltac:(destruct x));destruct x;(split;unlock H;
                   [
                     lazymatch goal with
                       |- evalLe ?k _ _ =>
                       refine (le_evalLe_proper _ eq_refl eq_refl _);[refine (proj1 H);shelve|apply proj2 in H;lock H];
                       try recStepUnnamed;extractCorrectCrush;shelveIfUnsolved "pos10"
                     end
                    |apply proj2 in H;lock H])
             | S ?n' => loop n'
             end ) in
        loop recArg
    (* non-recursive function*)
    |  _ =>
      let xInt := fresh x "Int" in
      let xNorm := fresh x "Norm" in
      let xInts := fresh x "Time" in
      let xInts := fresh x "Ints" in
      let xT := fresh x "T" in
      let vProc := fresh "vProc" in
      (*simple notypeclasses refine (_:computes (tt1 ~> tt2) _ _ (fun x xInt xNorm => (_,_)));try exact tt;shelve_unifiable;*)
      eapply computesTimeTyArr_helper with (time := fun x xT => _);[try Lproc;shelveIfUnsolved "pos3"|];
      intros x xT;intro_to_assumed x;intro_to_assumed xT;
      split_assumed;[now is_assumed|];
      intros xInt xInts;
      change xInt with (@extT _ _ x _ (Build_computableTime xInts));
      lazymatch tt1 with
        TyB _ => rewrite (extT_is_enc (Build_computableTime xInts)) in *;
                clear xInt xInts;assert (xInt:True) by constructor; assert (xInts:True) by constructor
      | _ => idtac
      end;
      eexists;split;[extractCorrectCrush;shelveIfUnsolved "pos4"| intros vProc]
    end
  (* complexity: *)

  | H : Lock _ |- computesTime (TyB _) _ _ ?tt=> close_assumed; destruct tt;apply computesTimeTyB                                                                                       
  | |- computesTime _ _ _ _ =>
    match goal with
    |  H : Lock _ |- _ => fail 1
    | |- _ => 
      refine (computesTimeIfStart (P:= fun fT => _) _ _);
      [let H := fresh "H" in
       let fT := fresh "fT" in
       intros fT H; lock H|] (* introduce the assumptions for the recurence equations to be collected *)
    end
end.

Ltac computable_match:=
  intros;
  lazymatch goal with
  | |- ?R ?lhs ?rhs =>
    lazymatch lhs with 
    | context C [@enc _ ?reg ?x] =>
      induction x;
      let encf := (eval hnf in (@enc _ reg)) in
      change (@enc _ reg) with encf;
      cbn -[enc];
      repeat change encf with (@enc _ reg);
      fold_encs;
      Lsimpl
    end
  end.

Ltac infer_instances :=
  repeat match goal with
         | [ |- context [ int_ext ?t ] ] => first [change (int_ext t) with (ext t) | fail 3 "Could not fold int-instance for " t]
         | [ |- context [ extT ?t ] ] => first [change (extT t) with (ext t) | fail 3 "Could not fold int-instance for " t]
         end.


Ltac infer_instancesT :=
  repeat match goal with
         | [ |- context [ int_ext ?t ] ] => first [change (int_ext t) with (extT t) | fail 3 "Could not fold extT-instance for " t]
         | [ |- context [ ext ?t ] ] => first [change (ext t) with (extT t) | fail 3 "Could not fold extT-instance for " t]
         end.


Ltac computable_prepare t :=
  let h := visibleHead t in
  tryif is_const h then unfold h else idtac.

Ltac computable_using_noProof Lter:=
  lazymatch goal with
  | [ |- computable ?t ] =>
    eexists Lter;unfold Lter;
    let t' := eval hnf in t in
        let h := visibleHead t' in
        try unfold h;computable_prepare t;infer_instances
  | [ |- computableTime ?t _] =>
    eexists Lter;unfold Lter;
    let t' := (eval hnf in t) in
    let h := visibleHead t' in
    try unfold h; computable_prepare t; infer_instancesT
  end.


Ltac extractAs s :=
  lazymatch goal with
  | [ |- computable ?t ] =>
    (run_template_program (tmExtract None t)
                         (fun e =>  pose (s:= ( e : extracted t))))
  | [ |- computableTime ?t _] =>
    (run_template_program (tmExtract None t)
                         (fun e => pose (s:= ( e : extracted t))))
  end.


Ltac extractThis t s :=
    (run_template_program (tmExtract None t)
                         (fun e =>  pose (s:= ( e : extracted t)))).

End Intern.

Import Intern.

Ltac register_inj :=   abstract (intros x; induction x; destruct 0;simpl; intros eq; try (injection eq || discriminate eq);intros;f_equal;auto;try apply inj_enc;try easy).

Ltac register_proc :=
  unfold enc_f;
  (((induction 0 || intros);
    cbn; fold_encs;Lproc
                        )).

Ltac register encf :=   refine (@mk_registered _ encf _ _);[
                          (((induction 0 || intros);(let f := visibleHead encf in unfold f;cbn [f]);
                            fold_encs;Lproc
                        )) | try register_inj].


Tactic Notation "computable" "using" open_constr(Lter) :=
  computable_using_noProof Lter;repeat cstep.

Tactic Notation "computable" "instead" open_constr(t) :=
  let s := fresh "s" in
  extractThis t s; computable using s.
      
Tactic Notation "computable" "infer" :=
  lazymatch goal with
  | [ |- computable ?t ] =>
    let e := constr:(int_ext t) in let e' := eval unfold int_ext in e in computable using e'
  | [ |- computableTime ?t _] =>
    let e := constr:(int_ext t) in let e' := eval unfold int_ext in e in computable using e'
  end.

Tactic Notation "extract" :=
    let term := fresh "used_term" in
    extractAs term;computable using term.


Tactic Notation "extract" "constructor":=
  let term := fresh "used_term" in
        lazymatch goal with
        | [ |- computable ?t ] =>
          run_template_program (tmExtractConstr' None t)
                                 (fun e =>  pose (term:= ( e : extracted t)); computable using term)
        | [ |- computableTime ?t _] =>
          run_template_program (tmExtractConstr' None t)
                               (fun e =>  pose (term:= ( e : extracted t)); computable using term)
          
   end.

Tactic Notation "extract" "match" := computable_match.

Local Ltac solverecTry :=       cbn [timeComplexity] in *;
                                (repeat (intros; intuition idtac;
                                         repeat match goal with
                                                | t:unit |- _ =>
                                                  destruct t
                                                end;
                                         try (let H:= fresh "H" in destruct _ eqn:H);cbn -[mult plus];try ring_simplify);try lia).
Ltac solverec :=   try abstract (solverecTry);solverecTry.


Lemma cast_computable X Y `{registered Y} (cast : X -> Y) (Hc : injective cast) :
  let _ := registerAs cast Hc in
  computable cast.
Proof.
  cbn.
  pose (t:=lam 0).
  computable using t.
Defined.

Notation "'computableTime' f" := (@computableTime _ ltac:(let t:=type of f in refine (_ : TT t);exact _) f) (at level 0,only parsing).

Lemma cast_computableTime X Y `{registered Y} (cast : X -> Y) (Hc : injective cast):
  let _ := registerAs cast Hc in
  computableTime cast (fun _ _ => (1,tt)).
Proof.
  cbn.
  pose (t:=lam 0).
  computable using t.
  solverec.
Defined.


Ltac computable_casted_result :=
  match goal with
    |- @computable _ _ _ => 
    simple notypeclasses refine (cast_registeredAs _ _);
    [ | | | |
      cbn - [registerAs];reflexivity| ];
    cbn
  | |- @ComputableTime.computableTime _ _ _ _=>
    simple notypeclasses refine (cast_registeredAs_TimeComplexity _ _);
    [ | | | |
      cbn - [registerAs];reflexivity| ];
    cbn
  end.

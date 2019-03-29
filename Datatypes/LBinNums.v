Require Import L.Tactics.LTactics.
Require Import BinNums.

Require Import LUnit LBool.


Section BinPos.
  Import BinPos.Pos.

  Run TemplateProgram (tmGenEncode "positive_enc" positive).
  Hint Resolve positive_enc_correct : Lrewrite.
  
  Global Instance termT_Pos_xI : computableTime xI (fun x _ => (1,tt)).
  extract constructor. solverec.
  Qed.

  Global Instance termT_Pos_xO : computableTime xO (fun x _ => (1,tt)).
  extract constructor. solverec.
  Qed.

  Global Instance termT_Pos_succ : computableTime succ (fun x _ => (size_nat x*11,tt)).
  extract. solverec.
  Qed.

  Fixpoint addC (c:bool) (x : positive) {struct x}: positive -> positive:=
    ((if c then  
      fun _ => match x with
      | p~1 => fun y => match y with
                    | q~1 => fun _ => (addC true p q)~1
                    | q~0 => fun _ => (addC true p q)~0
                    | 1 => fun _ =>(succ p)~1
                    end tt
      | p~0 => fun y => match y with
                    | q~1 => fun _ => (addC true p q)~0
                    | q~0 => fun _ => (addC false p q)~1
                    | 1 => fun _ => (succ p)~0
                    end tt
      | 1 => fun y => match y with
                  | q~1 => fun _ => (succ q)~1
                  | q~0 => fun _ => (succ q)~0
                  | 1 => fun _ => 3
                  end tt
      end
    else
      fun _ => match x with
      | p~1 => fun y => match y with
                    | q~1 => fun _ => (addC true p q)~0
                    | q~0 => fun _ => (addC false p q)~1
                    | 1 => fun _ =>(succ p)~0
                    end tt
      | p~0 => fun y => match y with
                    | q~1 => fun _ => (addC false p q)~1
                    | q~0 => fun _ => (addC false p q)~0
                    | 1 => fun _ => p~1
                    end tt
      | 1 => fun y => match y with
                  | q~1 => fun _ => (succ q)~0
                  | q~0 => fun _ => q~1
                  | 1 => fun _ => 2
                  end tt
       end) tt)%positive.

  Lemma addC_ext_eq : extEq addC (fun b => if b then add_carry else add).
  Proof.
    intros b x y. induction x in b,y|-*;destruct b,y;cbn;try rewrite !IHx. all:reflexivity.
  Qed.

  Global Instance termT_Pos_addC: computableTime addC (fun b _ => (5%nat,fun x _ => (11%nat,fun y _ => (12*(size_nat x + size_nat y),tt)))).
  extract. solverec.
  Qed.

  Global Instance termT_Pos_add: computableTime Pos.add (fun x _ => (17%nat,fun y _ => (12*(size_nat x + size_nat y),tt))).
  Proof.
    eapply computableTimeExt with (x:= (fun x => addC false x)).
    -hnf;repeat intro;eapply addC_ext_eq.
    -extract. solverec.
  Qed.

End BinPos.
Hint Resolve positive_enc_correct : Lrewrite.


Run TemplateProgram (tmGenEncode "N_enc" N).
Hint Resolve N_enc_correct : Lrewrite.

Instance termT_N_NPos : computableTime Npos (fun x _ => (1,tt)).
  extract constructor. solverec.
Qed.

Import N.
Instance termT_N_add: computableTime N.add (fun x _ => (1,fun y _ => (12*(N.size_nat x + N.size_nat y) + 25 ,tt))).
extract. solverec.
Qed.

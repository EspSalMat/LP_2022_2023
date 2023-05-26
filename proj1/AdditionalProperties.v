(* ################################################################# *)
(** * Additional Properties 

      It might be a good idea to read the relevant book chapters/sections before or as you
      develop your solution. The properties below are discussed and some of them proved
      for the original Imp formulation.
*)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From FirstProject Require Import Maps Imp Interpreter RelationalEvaluation.
Set Default Goal Selector "!".


(**
  3.2. TODO: Prove all the properties below that are stated without proof.
             Add a succint comment before each property explaining the property in your own words.
*)

(* ################################################################# *)
(** * Property of the Step-Indexed Interpreter *)

(*
  If interpreting a program giving i1 as the maximum number of steps executes properly and returns
  Some, it will also return that with any i2 greater or equal to i1.
*)
Theorem ceval_step_more: forall i1 i2 st st' res c,
i1 <= i2 ->
ceval_step st c i1 = Some (st', res) ->
ceval_step st c i2 = Some (st', res).
Proof.
  induction i1 as [|i1']; intros i2 st st' res c Hle Hceval.
  - simpl in Hceval. discriminate Hceval.
  - destruct i2 as [|i2']; inversion Hle; assert (Hle': i1' <= i2') by lia; destruct c; try assumption.
    -- rewrite <- H0. assumption. 
    -- simpl in Hceval. simpl. destruct (beval st b).
      --- apply IHi1'; try lia. assumption.
      --- rewrite <- H0. assumption.
    -- rewrite <- H0. assumption.
    -- simpl in Hceval. simpl. destruct (ceval_step st c1 i1') eqn:Heqst1'o.
      --- destruct p. assert (ceval_step st c1 i2' = Some(s, r)).
        ---- apply (IHi1' i2'); assumption.
        ---- rewrite H1. destruct r.
          ----- apply IHi1'; try lia. assumption.
          ----- assumption. 
      --- discriminate Hceval.
    -- simpl in Hceval. simpl. destruct (beval st b); apply (IHi1' i2') in Hceval; assumption.
    -- simpl in Hceval. simpl. destruct (beval st b); try assumption. destruct (ceval_step st c i1') eqn: Heqst1'o.
      --- destruct p. assert (ceval_step st c i2' = Some(s, r)).
        ---- apply (IHi1' i2'); assumption.
        ---- rewrite H1. destruct r.
          ----- apply IHi1'; try lia. assumption.
          ----- assumption.
      --- discriminate Hceval.
Qed.


(* ################################################################# *)
(** * Relational vs. Step-Indexed Evaluation *)

(** As for arithmetic and boolean expressions, we'd hope that
    the two alternative definitions of evaluation would actually
    amount to the same thing in the end.  This section shows that this
    is the case. *)

Theorem ceval_step__ceval: forall c st st' res,
    (exists i, ceval_step st c i = Some (st', res)) ->
    st =[ c ]=> st' / res.
Proof.
intros c st st' res H.
inversion H as [i E].
clear H.
generalize dependent res.
generalize dependent st'.
generalize dependent st.
generalize dependent c.
induction i as [| i' ].

- intros c st st' res H. discriminate.
- intros c st st' res H. destruct c; inversion H; subst; clear H.
  -- apply E_Skip.
  -- apply E_Break.
  -- apply E_Asgn. reflexivity.
  -- destruct (ceval_step st c1 i') eqn:Heqr1.
    --- destruct p, r.
      ---- apply E_SeqContinue with s; apply IHi'; assumption.
      ---- inversion H1. apply E_SeqBreak. apply IHi'. rewrite H0 in Heqr1. assumption.
    --- discriminate H1.
  -- destruct (beval st b) eqn:Heqb.
    --- apply E_IfTrue; try assumption. apply IHi'. assumption.
    --- apply E_IfFalse; try assumption. apply IHi'. assumption.
  -- destruct (beval st b) eqn:Heqb; assert (res = SContinue).
    --- destruct (ceval_step st c i') eqn:Heqr1.
      ---- destruct p, r.
        ----- apply while_continue with (b := b) (c := c) (st:=s) (st':=st'). apply IHi'. assumption.
        ----- inversion H1. reflexivity.
      ---- discriminate H1.
    --- destruct (ceval_step st c i') eqn:Heqr1.
      ---- destruct p, r; destruct res; try discriminate H.
        ----- apply E_WhileTrueContinue with s; try assumption; try apply IHi'; try assumption.
        ----- apply E_WhileTrueBreak.
          ------ assumption.
          ------ apply IHi'. inversion H1. rewrite <- H2. assumption.
      ---- discriminate H1.
    --- destruct (ceval_step st c i') eqn:Heqr1.
      ---- destruct p, r; inversion H1; reflexivity.
      ---- inversion H1. reflexivity.
    --- rewrite H. rewrite H in H1. inversion H1. apply E_WhileFalse. rewrite <- H2. assumption.
Qed.

(** 
  TODO: For the following proof, you'll need [ceval_step_more] in a
  few places, as well as some basic facts about [<=] and [plus]. *)

Theorem ceval__ceval_step: forall c st st' res,
    st =[ c ]=> st' / res ->
    exists i, ceval_step st c i = Some (st', res).
Proof.
  intros c st st' res Hce.
  induction Hce.
  - exists 1. simpl. reflexivity.
  - exists 1. simpl. reflexivity.
  - exists 1. simpl. rewrite H. reflexivity.
  - inversion IHHce as [i1 H1]. exists (S i1). simpl. rewrite H. assumption.
  - inversion IHHce as [i1 H1]. exists (S i1). simpl. rewrite H. assumption.
  - inversion IHHce as [i1 H1]. exists (S i1). simpl. rewrite H1. reflexivity.
  - inversion IHHce1 as [i1 H1]. inversion IHHce2 as [i2 H2]. exists (S (i1 + i2)). apply ceval_step_more with (i2 := i1 + i2) in H1.
    -- apply ceval_step_more with (i2 := i1 + i2) in H2.
      --- simpl. rewrite H1. assumption.
      --- lia.
    -- lia.
  - exists 1. simpl. rewrite H. reflexivity.
  - inversion IHHce as [i1 H1]. exists (S i1). simpl. rewrite H. rewrite H1. reflexivity. 
  - inversion IHHce1 as [i1 H1]. inversion IHHce2 as [i2 H2]. exists (S (i1 + i2)). apply ceval_step_more with (i2 := i1 + i2) in H1.
    -- apply ceval_step_more with (i2 := i1 + i2) in H2.
      --- simpl. rewrite H. rewrite H1. assumption.
      --- lia.
    -- lia.
Qed. 



(* Note that with the above properties, we can say that both semantics are equivalent! *)

Theorem ceval_and_ceval_step_coincide: forall c st st' res,
    st =[ c ]=> st' / res
<-> exists i, ceval_step st c i = Some (st', res).
Proof.
intros c st st'.
split. 
 - apply ceval__ceval_step. 
 - apply ceval_step__ceval.
Qed.


(* ################################################################# *)
(** * Determinism of Evaluation Again *)

(** Using the fact that the relational and step-indexed definition of
  evaluation are the same, we can give a short proof that the
  evaluation _relation_ is deterministic. *)

(* TODO: Write/explain the following proof in natural language, 
         using your own words. *)

(*
  First we use the ceval__ceval_step theorem, which allows us to replace the relational
  notation with calls to the step indexed interpreter ceval_step, stating that a natural number i
  exists that makes the function return Some.

  We do this when we write "apply ceval__ceval_step in He1" and "apply ceval__ceval_step in He2".

  We extract the i and the property from each "exists" of both hypotheses. This is done using
  "inversion He1 as [i1 E1]" and "inversion He2 as [i2 E2]".

  Then we use the above theorem ceval_step_more, which states that any i2 greater or equal to i1
  will return Some, if i1 returns Some. With this we can make it use (i1 + i2), since both are natural
  numbers their sum will be greater than both. We do this again and basically we will have ...
*)

Theorem ceval_deterministic' : forall c st st1 st2 res1 res2,
   st =[ c ]=> st1 / res1 ->
   st =[ c ]=> st2 / res2 ->
   st1 = st2.
Proof.
intros c st st1 st2 res1 res2 He1 He2.
apply ceval__ceval_step in He1.
apply ceval__ceval_step in He2.
inversion He1 as [i1 E1].
inversion He2 as [i2 E2].
apply ceval_step_more with (i2 := i1 + i2) in E1.
 - apply ceval_step_more with (i2 := i1 + i2) in E2.
  -- rewrite E1 in E2. inversion E2. reflexivity.
  -- lia. 
 - lia.  
 Qed.

(** * Imp: Simple Imperative Programs *)

(** Taken from the chapter Imp:
  https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html

    It might be a good idea to read the chapter before or as you
    develop your solution.
*)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From FirstProject Require Import Maps Imp.
Set Default Goal Selector "!".

(** Next, we need to define the behavior of [break].  Informally,
    whenever [break] is executed in a sequence of commands, it stops
    the execution of that sequence and signals that the innermost
    enclosing loop should terminate.  (If there aren't any
    enclosing loops, then the whole program simply terminates.)  The
    final state should be the same as the one in which the [break]
    statement was executed.

    One important point is what to do when there are multiple loops
    enclosing a given [break]. In those cases, [break] should only
    terminate the _innermost_ loop. Thus, after executing the
    following...

       X := 0;
       Y := 1;
       while 0 <> Y do
         while true do
           break
         end;
         X := 1;
         Y := Y - 1
       end

    ... the value of [X] should be [1], and not [0].

    One way of expressing this behavior is to add another parameter to
    the evaluation relation that specifies whether evaluation of a
    command executes a [break] statement: *)

Inductive result : Type :=
  | SContinue
  | SBreak.

Reserved Notation "st '=[' c ']=>' st' '/' s"
     (at level 40, c custom com at level 99, st' constr at next level).

(** Intuitively, [st =[ c ]=> st' / s] means that, if [c] is started in
    state [st], then it terminates in state [st'] and either signals
    that the innermost surrounding loop (or the whole program) should
    exit immediately ([s = SBreak]) or that execution should continue
    normally ([s = SContinue]).

    The definition of the "[st =[ c ]=> st' / s]" relation is very
    similar to the one we gave above for the regular evaluation
    relation ([st =[ c ]=> st']) -- we just need to handle the
    termination signals appropriately:

    - If the command is [skip], then the state doesn't change and
      execution of any enclosing loop can continue normally.

    - If the command is [break], the state stays unchanged but we
      signal a [SBreak].

    - If the command is an assignment, then we update the binding for
      that variable in the state accordingly and signal that execution
      can continue normally.

    - If the command is of the form [if b then c1 else c2 end], then
      the state is updated as in the original semantics of Imp, except
      that we also propagate the signal from the execution of
      whichever branch was taken.

    - If the command is a sequence [c1 ; c2], we first execute
      [c1].  If this yields a [SBreak], we skip the execution of [c2]
      and propagate the [SBreak] signal to the surrounding context;
      the resulting state is the same as the one obtained by
      executing [c1] alone. Otherwise, we execute [c2] on the state
      obtained after executing [c1], and propagate the signal
      generated there.

    - Finally, for a loop of the form [while b do c end], the
      semantics is almost the same as before. The only difference is
      that, when [b] evaluates to true, we execute [c] and check the
      signal that it raises.  If that signal is [SContinue], then the
      execution proceeds as in the original semantics. Otherwise, we
      stop the execution of the loop, and the resulting state is the
      same as the one resulting from the execution of the current
      iteration.  In either case, since [break] only terminates the
      innermost loop, [while] signals [SContinue]. *)

Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st,
      st =[ CSkip ]=> st / SContinue
  | E_Break : forall st,
      st =[ CBreak ]=> st / SBreak
  | E_Asgn : forall st a x n,
      aeval st a = n ->
      st =[ CAsgn x a ]=> (x !-> n; st) / SContinue
  | E_IfTrue : forall st st' b c1 c2 res,
      beval st b = true ->
      st =[ c1 ]=> st' / res ->
      st =[ CIf b c1 c2 ]=> st' / res
  | E_IfFalse : forall st st' b c1 c2 res,
      beval st b = false ->
      st =[ c2 ]=> st' / res ->
      st =[ CIf b c1 c2 ]=> st' / res
  | E_SeqBreak : forall st st' c1 c2,
      st  =[ c1 ]=> st' / SBreak ->
      st  =[ CSeq c1 c2 ]=> st' / SBreak
  | E_SeqContinue: forall st st' st'' c1 c2 res,
      st   =[ c1 ]=> st'  / SContinue ->
      st'  =[ c2 ]=> st'' / res ->
      st   =[ CSeq c1 c2 ]=> st'' / res
  | E_WhileFalse : forall st b c,
      beval st b = false ->
      st =[ CWhile b c ]=> st / SContinue
  | E_WhileTrueBreak : forall st st' b c,
      beval st b = true ->
      st  =[ c ]=> st' / SBreak ->
      st  =[ CWhile b c ]=> st' / SContinue
  | E_WhileTrueContinue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' / SContinue ->
      st' =[ CWhile b c ]=> st'' / SContinue ->
      st  =[ CWhile b c ]=> st'' / SContinue

  where "st '=[' c ']=>' st' '/' s" := (ceval c st s st').


(* The theorem means that when evaluating a sequence that starts with a break, 
   the state of the program remains unchanged. *)
Theorem break_ignore : forall c st st' s,
     st =[ break; c ]=> st' / s ->
     st = st'.
Proof.
  intros.
  inversion H; subst.
  - inversion H5. subst. reflexivity.
  - inversion H2.
Qed.


(* The theorem means that when evaluating a while loop, it will always signal the inner most loop 
   to continue the execution. 
*)
Theorem while_continue : forall b c st st' s,
  st =[ while b do c end ]=> st' / s ->
  s = SContinue.
Proof.
  intros.
  inversion H; reflexivity.
Qed.


(* The theorem means that when evaluating a while loop, if the body of the loop signals the loop to break the execution, 
   the state resulting from the execution of the loop is the same as the state resulting from the
   execution of the body of the loop.
*)
Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  st =[ c ]=> st' / SBreak ->
  st =[ while b do c end ]=> st' / SContinue.
Proof.
  intros.
  apply E_WhileTrueBreak with (st := st) (st' := st'); assumption.
Qed.


(* The theorem means that when evaluating a sequence, if both instructions signal the inner most context to continue the execution,
   the state resulting from the execution of the sequence is the same as the state resulting from the execution of the second instruction,
   executed on the state resulting from the execution of the first instruction.
*)
Theorem seq_continue : forall c1 c2 st st' st'',
  st =[ c1 ]=> st' / SContinue ->
  st' =[ c2 ]=> st'' / SContinue ->
  st =[ c1 ; c2 ]=> st'' / SContinue.
Proof.
  intros.
  apply E_SeqContinue with (st := st) (st' := st') (st'' := st''); assumption.
Qed.


(* The theorem means that when evaluating a sequence, if the first instruction signals the inner most context to break the execution,
   the state resulting from the execution of the sequence is the same as the state resulting from the execution of the first instruction,
   independently of the second instruction.
*)
Theorem seq_stops_on_break : forall c1 c2 st st',
  st =[ c1 ]=> st' / SBreak ->
  st =[ c1 ; c2 ]=> st' / SBreak.
Proof.
  intros.
  apply E_SeqBreak with (st := st) (st' := st'). assumption.
Qed.


(* The theorem means that when evaluating a while loop, if after its execution the condition 
   still evaluates to true, the last execution body of the loop must have signaled the loop
   to break the execution.
*)
Theorem while_break_true : forall b c st st',
  st =[ while b do c end ]=> st' / SContinue ->
  beval st' b = true ->
  exists st'', st'' =[ c ]=> st' / SBreak.
Proof.
  intros.
  remember <{ while b do c end  }> as loop eqn:Hloop.
  induction H; inversion Hloop; subst.
  - rewrite H in H0. discriminate.
  - exists st. assumption.
  - apply IHceval2; try reflexivity. assumption.
Qed.

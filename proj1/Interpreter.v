(** * An Evaluation Function for Imp *)


(** Taken from the chapter Imp:
  https://softwarefoundations.cis.upenn.edu/lf-current/ImpCEvalFun.html

    It might be a good idea to read the chapter before or as you
    develop your solution.
*)

From Coq Require Import Lia.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.PeanoNat.
Import Nat.
From Coq Require Import Arith.EqNat.
From FirstProject Require Import Imp Maps.

(* Let's import the result datatype from the relational evaluation file *)
From FirstProject Require Import RelationalEvaluation.

(** We can improve the readability of this version by introducing a
    bit of auxiliary notation to hide the plumbing involved in
    repeatedly matching against optional states. *)

Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).

Fixpoint ceval_step (st : state) (c : com) (i : nat): option (state*result) :=
  match i with
  | O => None
  | S i' => match c with
            | <{ skip }> => Some (st, SContinue)
            | <{ break }> => Some (st, SBreak)
            | <{ x := y }> => Some ((x !-> (aeval st y) ; st), SContinue)
            | <{ x ; y }> => LETOPT res <== (ceval_step st x i') IN
                            match res with
                              | (st', SContinue) => ceval_step st' y i'
                              | (st', SBreak) => Some (st', SBreak)
                            end
            | <{ if x then y else z end }> => if beval st x then
                                                ceval_step st y i'
                                                else ceval_step st z i'
            | <{ while x do y end }> => if beval st x then
                                          LETOPT res <== ceval_step st y i' IN
                                              match res with
                                                | (st', SContinue) => ceval_step st' c i'
                                                | (st', SBreak) => Some (st', SContinue)
                                              end
                                          else Some (st, SContinue)
           end
end.

(* The following definition is taken from the book and it can be used to
   test the step-indexed interpreter. *)
Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None    => None
  | Some (st, _) => Some (st X, st Y, st Z)
  end.

Example example_test_ceval :
     test_ceval empty_st

     <{ X := 2;
        if (X <= 1)
        then Y := 3
        else Z := 4
        end }>

     = Some (2, 0, 4).
Proof. reflexivity. Qed.

(*
  The theorem menas that evaluating a sequence that begins with a break followed by a skip 
  or a sequence that begins with a break followed by any other instruction will lead to the same outcome.
  When evaluating a break instruction it will signal SBreak, signaling that the inner most loop should terminate.
  When evaluating a sequence and the first instruction signals an SBreak, the sequence will also signal an SBreak 
  and the second intruction will not be applied, not changing the state of the program.
  Because of that, any sequence that with a break instruction as the first instruction will return the same state
  and signal SBreak, regardless of the second instruction.
*)
Theorem equivalence1: forall st c,
(exists i0,
forall i1, i1>=i0 ->
ceval_step st <{ break; c }> i1
=
ceval_step st <{ break; skip }> i1
).
Proof.
  intros. exists 0. intros.
  repeat (destruct i1; try lia; try reflexivity).
Qed.

(*
  The theorem menas that evaluating evaluating a skip or a sequence that begins with a break will lead to different outcomes.
  In both cases the computation won't change the state of the program.
  However, the skip instruction will signal SContinue and break will signal SBreak to signal that the inner most loop should terminate,
  resulting in different outcomes.
*)
Theorem inequivalence1: forall st c,
(exists i0,
forall i1, i1>=i0 ->
ceval_step st <{ break; c }> i1
<>
ceval_step st <{ skip }> i1
).
Proof.
  intros. exists 1. intros.
  repeat (destruct i1; try lia; try discriminate).
Qed.

Theorem p1_equivalent_p2: forall st,
  (exists i0,
    forall i1, i1>=i0 ->
      ceval_step st p1 i1 = ceval_step st p2 i1
  ).
Proof.
  intros. exists 6. intros.
  repeat (destruct i1; try lia; try reflexivity).
Qed.

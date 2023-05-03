(* Lecture 2 *)

Definition succ (n:nat): nat := n + 1.

Definition succ_implicit n := n + 1.

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Check monday.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Compute next_weekday friday.

Compute next_weekday (next_weekday friday).

Definition next_weekday' (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | _ => monday
  end.

(* Natural numbers *)
Require Import Coq.Unicode.Utf8.

Module MyNat.
  Inductive nat : Type :=
    | O : nat
    | S : nat → nat.
End MyNat.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Compute plus 3 2.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Fixpoint beq_nat' (n m:nat) : bool :=
  match n,m with
    | O, O => true
    | O, S m' => false
    | S n', O => false
    | S n', S m' => beq_nat' n' m'
  end.

Fixpoint beq_nat'' (n m:nat) : bool :=
  match n,m with
    | O, O => true
    | S n', S m' => beq_nat'' n' m'
    | _, _ => false
  end.

(* Exercise 1 *)
Fixpoint leb (n m: nat) :  bool :=
  match n, m with
    | O, _ => true
    | _, O => false
    | S n', S m' => leb n' m'
  end.

Compute leb 9 6.
Compute leb 5 7.
Compute leb 6 6.

Definition isZero (n : nat) : bool :=
  if (beq_nat n 0) then true else false.

Definition my_if :=
  if (leb 0 42) then 1 else 0.
Check my_if.

(* Structured data *)
Inductive natprod : Type :=
  | pair : nat → nat → natprod.
Check (pair 3 5).

Definition fst (p: natprod) : nat :=
  match p with
    | pair n1 n2 => n1
  end.

Definition snd (p: natprod) : nat :=
  match p with
    | pair n1 n2 => n2
  end.

Compute snd (pair 3 5).

Notation "( x , y )" := (pair x y).

Check (3,5).

Definition swap_pair (p : natprod) : natprod :=
  match p with
    | (m,n) => (n,m)
  end.

Compute swap_pair (3,5).

Lemma swap_twice: forall (m n: nat),
    swap_pair (swap_pair (m, n)) = (m, n).
Proof. intros. simpl. reflexivity. Qed.

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Fixpoint length (l: natlist) : nat :=
  match l with
    | nil => 0
    | cons _ t => 1 + length t
  end.

Compute length mylist.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42
  | a :: l' => match beq_nat n O with
               | true => a
               | false => nth_bad l' (pred n)
               end
  end.

Inductive natoption : Type :=
  | Some : nat → natoption
  | None : natoption.

(* Some things might be missing *)

Module Polymorphic.
  Inductive list (X:Type) : Type :=
    | nil : list X
    | cons : X → list X → list X.

  Check list.
  Check (nil nat).
  Check nil nat.
  Check nil bool.
  Check cons.
  Check cons nat.
  Check cons bool.
  Check (cons nat 3 (nil nat)).

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.


Fixpoint repeat' X x count : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat' X x count')
  end.

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat'' _ x count')
  end.

Arguments nil {X}.
Arguments cons {X} _ _.

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat''' x count')
  end.

Compute repeat''' 32 4.
End Polymorphic.

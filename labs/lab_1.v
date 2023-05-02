(* Lab Session 1 *)

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.


(* Ex 1.1 *)
Definition week_to_nat (d: day): nat :=
  match d with
    | monday => 2
    | tuesday => 3
    | wednesday => 4
    | thursday => 5
    | friday => 6
    | saturday => 7
    | sunday => 1
  end.

(* Ex 1.2 *)
Compute week_to_nat monday.
Compute week_to_nat tuesday.
Compute week_to_nat wednesday.
Compute week_to_nat thursday.
Compute week_to_nat friday.
Compute week_to_nat saturday.
Compute week_to_nat sunday.

(* Ex 1.3 *)
Definition is_weekend (d: day): bool :=
  match d with
    | saturday => true
    | sunday => true
    | _ => false
  end.

Compute is_weekend monday.
Compute is_weekend sunday.

(* Ex 2.1 *)
Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1: bool) (b2: bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

(* Ex 2.2 *)
Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb2: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb4: (orb false false) = false.
Proof. simpl. reflexivity. Qed.

(* Ex 2.3 *)
Notation "~ x" := (negb x).
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Compute ~false || (true && false).

(* Ex 2.4 *)
Definition xor (b1: bool) (b2: bool): bool := (b1 || b2) && ~ (b1 && b2).

Example test_xor1: (xor true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_xor2: (xor true true) = false.
Proof. simpl. reflexivity. Qed.

Example test_xor3: (xor false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_xor4: (xor false false) = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground.
  (* Ex 3.1 *)
  (*Inductive nat : Type :=
    | O : nat
    | S : nat -> nat.*)

  Check (S (S (S (S O)))).

  (* Ex 3.2 *)
  Definition minustwo (n : nat) : nat :=
    match n with
      | O => O
      | S O => O
      | S (S n') => n'
    end.

  Compute minustwo (S (S (S O))).

  (* Ex 3.3 *)
  Fixpoint evenb (n: nat): bool :=
    match n with
      | O => true
      | S O => false
      | S (S n') => evenb n'
    end.

  Fixpoint oddb (n: nat): bool :=
    match n with
      | O => false
      | S O => true
      | S (S n') => oddb n'
    end.

  (* Ex 3.4 *)
  Definition oddb' (n: nat): bool := ~ evenb(n).

  (* Ex 3.5 *)
  Fixpoint plus (n1: nat) (n2: nat): nat :=
    match n1 with
      | O => n2
      | S n' => plus n' (S n2)
    end.

  Compute plus (S (S (S O))) (S (S O)).

  Fixpoint mult (n1: nat) (n2: nat): nat :=
    match n1 with
      | O => O
      | S n' => plus (n2) (mult n' n2)
    end.

  Compute mult (S (S O)) (S (S (S O))).

  Fixpoint exp (n1: nat) (n2: nat): nat :=
    match n2 with
      | O => S O
      | S n' => mult (n1) (exp n1 n')
    end.

  Compute exp (S (S O)) (S (S O)).

  (* 3.6
       plus 3 2
     = plus 2 3
     = plus 1 4
     = plus 0 5
     = 5
  *)

  (* Ex 3.7 *)
  Fixpoint minus (n1: nat) (n2: nat): nat :=
    match n1 with
      | O => O
      | S n' =>
          match n2 with
            | O => n1
            | S n'' => minus n' n''
          end
      end.

  Compute minus (S (S (S O))) (S (S O)).

  (* Ex 3.7 *)
  Fixpoint factorial (n: nat): nat :=
    match n with
      | O => S O
      | S n' => mult n (factorial n')
    end.


  Compute factorial (S (S (S O))).

  Notation "x (+) y" := (plus x y)
    (at level 50, left associativity)
    : nat_scope.

  Notation "x $ y" := (mult x y)
    (at level 40, left associativity)
    : nat_scope.

  Notation "x (^) y" := (exp x y)
    (at level 40, left associativity)
    : nat_scope.

  Notation "x (-) y" := (minus x y)
    (at level 50, left associativity)
    : nat_scope.

  Notation "x !" := (factorial x)
    (at level 40, left associativity)
    : nat_scope.

  Compute (S O) (+) (S O).
  Compute (S (S O)) $ (S (S (S O))).
  Compute (S (S O)) (^) (S (S (S O))).
  Compute 100 (-) 30.
  Compute 5!.
End NatPlayground.

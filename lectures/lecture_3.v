(* Lecture 3 *)

Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.Unicode.Utf8.

Definition doit3times {X: Type} (f: X -> X) (n: X) : X :=
  f (f (f n)).

Check doit3times.

Definition f1 (n: nat) := n + 1.

Compute doit3times f1 0.

Fixpoint filter {X: Type} (test: X -> bool) (l: list X)
                : (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t)
                        else filter test t
  end.

Fixpoint is_odd(n: nat): bool :=
  match n with
    | O => false
    | S O => true
    | S (S n') => is_odd n'
  end.

Definition countoddmembers (l: list nat) : nat :=
  length (filter is_odd l).

Compute countoddmembers [1; 3; 4; 5; 6; 8].

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. simpl. reflexivity. Qed.

Require Import Coq.Arith.PeanoNat.

Definition remove_smaller_than (n: nat) (l: list nat) : list nat :=
  filter (fun n' => n <=? n') l.

Compute remove_smaller_than 3 [1;2;3;4;5] = [3;4;5].

Fixpoint map {X Y: Type} (f:X→Y) (l:list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Compute map (fun x => x + 3) [2;0;2] = [5;3;5].
Compute map is_odd [1;2;3].

Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.
Compute fold plus [1;2;3;4] 0 = 1 + (2 + (3 + (4 + 0))).

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros pombo.
  (* intros pode receber como argumento o nome a dar às variáveis na prova *)
  simpl.
  reflexivity.
Qed.

Theorem plus_1_l : ∀ n:nat, 1 + n = S n.
Proof. trivial. Qed.

Theorem plus_id_example : ∀ n m:nat,
  n = m →
  n + n = m + m.
Proof.
  intros n m H.
  simpl.
  rewrite <- H.
  reflexivity.
Qed.

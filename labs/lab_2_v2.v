Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(* Ex 2.15 *)
Set Implicit Arguments.
Section ListFunctions.
  Variable T : Type.
  Variable U : Type.

 (* Ex 2.1 *)
  Definition tl (l: list T) : list T :=
    match l with
      | [] => []
      | h :: t => t
    end.

 (* Ex 2.2 *)
  Fixpoint removelast (l: list T) : list T :=
    match l with
      | [] => []
      | [h] => []
      | h :: t => h :: removelast t
    end.


 (* Ex 2.3 *)
  Fixpoint firstn (n: nat) (l: list T) : list T :=
    match l, n with
      | _, O => []
      | [], _ => []
      | h :: l', S n' => h :: firstn n' l'
    end.

 (* Ex 2.4 *)
  Fixpoint skipn (l: list T) (n: nat) : list T :=
    match l, n with
      | _, O => l
      | [], _ => []
      | h :: l', S n' => skipn l' n'
    end.

 (* Ex 2.5 *)
  Fixpoint last (l: list T) : option T :=
    match l with
      | [] => None
      | [h] => Some h
      | h :: t => last t
    end.

 (* Ex 2.6 *)
  Fixpoint seq (start: nat) (len: nat) : list nat :=
    match start, len with
      | _, O => []
      | i, S len' => i :: seq (S i) len'
    end.

 (* Ex 2.7 *)
  Fixpoint split (l: list (prod T U)) : prod (list T) (list U) :=
    match l with
      | [] => ([], [])
      | (x, y) :: t =>
          let (lx, ly) := split t in (x :: lx, y :: ly)
    end.

 (* Ex 2.8 *)
  Fixpoint append (l1 l2: list T) : list T :=
    match l1, l2 with
      | [], l2' => l2'
      | h :: l1', l2' => h :: append l1' l2'
    end.

 (* Ex 2.9 *)
  Fixpoint rev' (l1 l2: list T) : list T :=
    match l1, l2 with
      | [], l2' => l2'
      | h :: l1', l2' => rev' l1' (h :: l2')
    end.

  Definition rev (l: list T) : list T :=
    rev' l [].

 (* Ex 2.10 *)
  Fixpoint existsb (f: T -> bool) (l: list T) : bool :=
    match l with
      | [] => false
      | h :: l' => (f h) || (existsb f l')
    end.

 (* Ex 2.11 *)
  Fixpoint forallb (f: T -> bool) (l: list T) : bool :=
    match l with
      | [] => true
      | h :: l' => (f h) && (forallb f l')
    end.

  (* Ex 2.12 *)
  Fixpoint find (f: T -> bool) (l: list T) : option T :=
    match l with
      | [] => None
      | h :: l' => if f h then Some h else find f l'
    end.

 (* Ex 2.13 *)
  Fixpoint partition (f: T -> bool) (l: list T) : prod (list T) (list T) :=
    match l with
      | [] => ([], [])
      | h :: l' => let (l1, l2) := partition f l' in
                if f h then (h :: l1, l2) else (l1, h :: l2)
    end.

 (* Ex 2.14 *)
  Fixpoint list_prod' (x: T) (ly: list U) : list (prod T U) :=
    match ly with
      | [] => []
      | y :: ly' => (x, y) :: list_prod' x ly'
    end.

  Fixpoint list_prod (lx: list T) (ly: list U) : list (prod T U) :=
    match lx with
      | [] => []
      | x :: lx' => (list_prod' x ly) ++ (list_prod lx' ly)
    end.
End ListFunctions.

Compute removelast [].
Compute removelast [2].
Compute removelast [2; 3].
Compute removelast [2; 3; 4].

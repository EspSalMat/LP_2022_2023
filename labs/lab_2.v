(* Lab Session 2 *)

Module ExerciseOne.
  Inductive mumble : Type :=
    | a : mumble
    | b : mumble -> nat -> mumble
    | c : mumble.

  Inductive grumble (X:Type) : Type :=
    | d : mumble -> grumble X
    | e : X -> grumble X.

  (*Check d (b a 5).*)
  Check d mumble (b a 5).
  Check d bool (b a 5).
  (*Check e bool 5. *)
  Check e bool true.
  Check e mumble (b c 0).
  (* Check e bool (b c 0). *)
  Check c. (* Este não tem erros, mas não é de um tipo grumble X *)
End ExerciseOne.

Require Import Coq.Lists.List.
Import ListNotations.

(* Ex 2.1 *)
Definition tl {T: Type} (l: list T) : list T :=
  match l with
    | [] => []
    | h :: t => t
  end.

(* Ex 2.2 *)
Fixpoint removelast {T: Type} (l: list T) : list T :=
  match l with
    | [] => []
    | [h] => []
    | h :: t => h :: removelast t
  end.

Compute removelast [].
Compute removelast [2].
Compute removelast [2; 3].
Compute removelast [2; 3; 4].

(* Ex 2.3 *)
Fixpoint firstn {T: Type} (n: nat) (l: list T) : list T :=
  match l, n with
    | _, O => []
    | [], _ => []
    | h :: l', S n' => h :: firstn n' l'
  end.

Compute firstn 1 [].
Compute firstn 1 [2].
Compute firstn 1 [2; 3].
Compute firstn 2 [2; 3; 4].

(* Ex 2.4 *)
Fixpoint skipn {T: Type} (l: list T) (n: nat) : list T :=
  match l, n with
    | _, O => l
    | [], _ => []
    | h :: l', S n' => skipn l' n'
  end.

Compute skipn [] 1.
Compute skipn [2] 1.
Compute skipn [2; 3] 1.
Compute skipn [2; 3; 4] 2.

(* Ex 2.5 *)
Fixpoint last {T: Type} (l: list T) : option T :=
  match l with
    | [] => None
    | [h] => Some h
    | h :: t => last t
  end.

Compute last [].
Compute last [2].
Compute last [2; 3].
Compute last [2; 3; 4].

(* Ex 2.6 *)
Fixpoint seq (start: nat) (len: nat) : list nat :=
  match start, len with
    | _, O => []
    | i, S len' => i :: seq (S i) len'
  end.

Compute seq 1 10.
Compute seq 3 4.

(* Ex 2.7 *)
Fixpoint split {T U: Type} (l: list (prod T U)) : prod (list T) (list U) :=
  match l with
    | [] => ([], [])
    | (x, y) :: t =>
        let (lx, ly) := split t in (x :: lx, y :: ly)
  end.

Compute split [(1,true);(2,false);(3,true)].

(* Ex 2.8 *)
Fixpoint append {T: Type} (l1 l2: list T) : list T :=
  match l1, l2 with
    | [], l2' => l2'
    | h :: l1', l2' => h :: append l1' l2'
  end.

Compute append [1;2;3] [4;5;6].

(* Ex 2.9 *)
Fixpoint rev' {T: Type} (l1 l2: list T) : list T :=
  match l1, l2 with
    | [], l2' => l2'
    | h :: l1', l2' => rev' l1' (h :: l2')
  end.

Definition rev {T: Type} (l: list T) : list T :=
  rev' l [].

Compute rev [1;2;3].

(* Ex 2.10 *)
Require Import Coq.Arith.PeanoNat.

Fixpoint existsb {T: Type} (f: T -> bool) (l: list T) : bool :=
  match l with
    | [] => false
    | h :: l' => (f h) || (existsb f l')
  end.

Compute existsb (fun e => e <=? 3) [2;4;5].

(* Ex 2.11 *)
Fixpoint forallb {T: Type} (f: T -> bool) (l: list T) : bool :=
  match l with
    | [] => true
    | h :: l' => (f h) && (forallb f l')
  end.

Compute forallb (fun e => e <=? 3) [2;4;5].
Compute forallb (fun e => e <=? 3) [2;1;2].

(* Ex 2.12 *)
Fixpoint find {T: Type} (f: T -> bool) (l: list T) : option T :=
  match l with
    | [] => None
    | h :: l' => if f h then Some h else find f l'
  end.

Compute find (fun e => e <=? 3) [6;4;1;3;7].

(* Ex 2.13 *)
Fixpoint partition {T: Type} (f: T -> bool) (l: list T) : prod (list T) (list T) :=
  match l with
    | [] => ([], [])
    | h :: l' => let (l1, l2) := partition f l' in
               if f h then (h :: l1, l2) else (l1, h :: l2)
  end.

Compute partition (fun e => e <=? 3) [2;4;5;1;9].

(* Ex 2.14 *)
Fixpoint list_prod' {T U: Type} (x: T) (ly: list U) : list (prod T U) :=
  match ly with
    | [] => []
    | y :: ly' => (x, y) :: list_prod' x ly'
  end.

Fixpoint list_prod {T U: Type} (lx: list T) (ly: list U) : list (prod T U) :=
  match lx with
    | [] => []
    | x :: lx' => (list_prod' x ly) ++ (list_prod lx' ly)
  end.

Compute list_prod [1; 2] [true; false].

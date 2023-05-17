(* Lab Session 5 *)
Require Import String.
Open Scope string_scope.
Require Import Coq.Unicode.Utf8.
Require Import Coq.Arith.PeanoNat.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Bool.Bool.

Definition map (X: Type) := string -> X.
Definition empty {X: Type} (def: X) : map X :=
  fun x => def.
Definition update {X: Type} (m: map X) (n: string) (v: X) : map X :=
  fun n' => if n' =? n then v else m n'.

Notation "x 'IS' v 'AND' m" := (update m x v) (at level 100, v at next level, right associativity).
Notation "'WITH' v" := (empty v) (at level 100, right associativity).

Definition apply_option {A B C : Type} (f:A → B → C) (o1: option A) (o2: option B) :
  option C :=
  match o1,o2 with
    | None,_ => None
    |_, None => None
    | Some a, Some b => Some (f a b)
  end.

Inductive arith : Type :=
  | Const (n : nat)
  | Var (x : string)
  | Plus (e1 e2 : arith)
  | Times (e1 e2 : arith).

Inductive bexpr : Type :=
  | GreaterThan (e1 e2 : arith)
  | Equal (e1 e2 : arith)
  | Not (e : bexpr)
  | And (e1 e2 : bexpr)
  | True
  | False.

Inductive cmd : Type :=
  | Skip
  | Assign (x : string) (e : arith)
  | Sequence (c1 c2 : cmd)
  | IfThen (b : bexpr) (c1 c2 : cmd)
  | Repeat (e : arith) (body : cmd).

Definition x := "X".
Definition y := "Y".
Definition z := "Z".

(* Notations *)
Coercion Var: string >-> arith.
Coercion Const: nat >-> arith.

Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y"   := (Plus x y) (in custom com at level 50, left associativity).
Notation "x * y"   := (Times x y) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := True (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := False (in custom com at level 0).
Notation "x > y"   := (GreaterThan x y) (in custom com at level 70, no associativity).
Notation "x = y"   := (Equal x y) (in custom com at level 70, no associativity).
Notation "x && y"  := (And x y) (in custom com at level 80, left associativity).
Notation "'~' b"   := (Not b) (in custom com at level 75, right associativity).

Notation "'skip'"  := Skip (in custom com at level 0) : com_scope.
Notation "x := y"  := (Assign x y)
          (in custom com at level 0, x constr at level 0, y at level 85, no associativity) : com_scope.
Notation "x ; y" := (Sequence x y)
          (in custom com at level 90, right associativity) : com_scope.
Notation "'repeat' x 'do' y 'end'" :=
         (Repeat x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (IfThen x y z)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.

Open Scope com_scope.

Fixpoint aeval (a: arith) (st: map nat) : nat :=
  match a with
    | <{ a1 + a2 }> => (aeval a1 st) + (aeval a2 st)
    | <{ a1 * a2 }> => (aeval a1 st) * (aeval a2 st)
    | Const n => n
    | Var x => st x
  end.

Fixpoint beval (b: bexpr) (st: map nat) : bool :=
  match b with
    | <{ a1 > a2 }>   => Nat.leb (aeval a2 st)  (aeval a1 st)
    | <{ a1 = a2 }>   => Nat.eqb (aeval a2 st)  (aeval a1 st)
    | <{ ~ b' }> => negb (beval b' st)
    | <{ b1 && b2 }>   => (beval b1 st) && (beval b2 st)
    | <{ true }> => true
    | <{ false }> => false
  end.

(*Inductive cmd : Type :=
  | Skip
  | Assign (x : string) (e : arith)
  | Sequence (c1 c2 : cmd)
  | Repeat (e : arith) (body : cmd).
*)

Fixpoint self_compose {A: Type} (f: A -> A) (n: nat) : A -> A :=
  match n with
    | O => fun x => x
    | S n' => fun x => self_compose f n' (f x)
  end.

Fixpoint exec (c: cmd) (st: map nat) : map nat :=
  match c with
    | <{ skip }> => st
    | <{ v := a }> => v IS (aeval a st) AND st
    | <{ c1; c2 }> => exec c2 (exec c1 st)
    | <{ if b then c1 else c2 end }> => if (beval b st) then exec c1 st else exec c2 st
    | <{ repeat a do c' end }> => self_compose (exec c') (aeval a st) st
  end.

Definition p := <{
x := 10;
if x > 5 then
   x := 3
else
   x := 15
end
}>.
Compute (exec p (empty 0)) x.

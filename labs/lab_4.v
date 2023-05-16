(* Lab Session 4 *)
Require Import String.
Open Scope string_scope.
Require Import Coq.Unicode.Utf8.
Require Import Lia.
Require Import Coq.Program.Wf.

(* Exercise 1 *)
Module ExerciseOne.
Inductive arith : Type :=
  | Const (n : nat)
  | Var (x : string)
  | Plus (e1 e2 : arith)
  | Times (e1 e2 : arith).

(* 1.1 *)
Fixpoint size (ast: arith) : nat :=
  match ast with
    | Const _ => 1
    | Var _ => 1
    | Plus e1 e2 => 1 + size e1 + size e2
    | Times e1 e2 => 1 + size e1 + size e2
  end.

Fixpoint depth (ast: arith) : nat :=
  match ast with
    | Const _ => 1
    | Var _ => 1
    | Plus e1 e2 => 1 + (max (depth e1) (depth e2))
    | Times e1 e2 => 1 + (max (depth e1) (depth e2))
  end.

Definition my_ast1 := Times (Plus (Const 1) (Var "x")) (Const 8).
Compute size my_ast1.

(* 1.2 *)
Theorem depth_le_size : ∀ ast, depth ast ≤ size ast.
Proof.
  induction ast; simpl; lia.
Qed.

(* 1.3 *)
Fixpoint commuter (ast: arith) : arith :=
  match ast with
    | Plus e1 e2 => Plus (commuter e2) (commuter e1)
    | Times e1 e2 => Times (commuter e2) (commuter e1)
    | other => other
  end.

Compute commuter my_ast1.

(* 1.4.1 *)
(* O tamanho de qualquer ast é igual ao da ast espelhada *)
Theorem size_commuter : ∀ e, size (commuter e) = size e.
Proof.
  induction e; simpl; lia.
Qed.

(* 1.4.2 *)
(* A profundidade de qualquer ast é igual à da ast espelhada *)
Theorem depth_commuter : ∀ e, depth (commuter e) = depth e.
Proof.
  induction e; simpl; lia.
Qed.

(* 1.4.3 *)
(* A espelhada da espelhada é a própria ast *)
Theorem commuter_inverse : ∀ e, commuter (commuter e) = e.
Proof.
  induction e; simpl; try reflexivity.
  - rewrite IHe1. rewrite IHe2. reflexivity.
  - rewrite IHe1. rewrite IHe2. reflexivity.
Qed.

(* 1.5 *)
Fixpoint substitute (e1: arith) (v: string) (e2: arith) : arith :=
  match e1 with
    | Var n => if string_dec n v then e2 else e1
    | Plus e1' e2' => Plus (substitute e1' v e2) (substitute e2' v e2)
    | Times e1' e2' => Times (substitute e1' v e2) (substitute e2' v e2)
    | o => o
  end.

Compute substitute my_ast1 "x" (Const 6).
Compute substitute (Plus (Var "x") (Var "y")) "x" (Const 42)
        = (Plus (Const 42) (Var "y")).

(* 1.6.1 *)
(*
  A profundidade depois de substituir uma variável é menor ou igual à
  soma das profundidas da origina e da substituições
*)
Theorem substitute_depth : ∀ replaceThis withThis inThis,
        depth (substitute inThis replaceThis withThis)
        ≤ depth inThis + depth withThis.
Proof.
  intros var_name var_value ast.
  induction ast; simpl; try destruct (string_dec x var_name); simpl; lia.
Qed.

(* 1.6.2 *)
(* Substituir a variável por ela própria não faz nada *)
Theorem substitute_self : ∀ replaceThis inThis,
    substitute inThis replaceThis (Var replaceThis) = inThis.
Proof.
  intros var_name ast.
  induction ast.
  - simpl. reflexivity.
  - simpl. destruct (string_dec x var_name).
    -- rewrite e. reflexivity.
    -- reflexivity.
  - simpl. rewrite IHast1. rewrite IHast2. reflexivity.
  - simpl. rewrite IHast1. rewrite IHast2. reflexivity.
Qed.

(* 1.6.3 *)
(* não interessa a ordem em que se faz as duas funções *)
Theorem substitute_commuter : ∀ replaceThis withThis inThis,
    commuter (substitute inThis replaceThis withThis)
  = substitute (commuter inThis) replaceThis (commuter withThis).
Proof.
  intros var_name var_value ast.
  induction ast.
  - simpl. reflexivity.
  - simpl. destruct (string_dec x var_name).
    -- reflexivity.
    -- simpl. reflexivity.
  - simpl. rewrite IHast1. rewrite IHast2. reflexivity.
  - simpl. rewrite IHast1. rewrite IHast2. reflexivity.
Qed.

(* 1.7 *)
Definition tmap (X: Type) := string -> X.
Definition empty_tmap {X: Type} (def: X) : tmap X :=
  fun x => def.
Definition tmap_add {X: Type} (m: tmap X) (n: string) (v: X) : tmap X :=
  fun n' => if n' =? n then v else m n'.

Definition pmap (X: Type) := tmap (option X).
Definition empty_pmap {X: Type} : pmap X :=
  fun x => None.
Definition pmap_add {X: Type} (m: pmap X) (n: string) (v: X) : pmap X :=
  fun n' => if n' =? n then Some v else m n'.

Fixpoint eval (e: arith) (vars: pmap nat) : option nat :=
  match e with
    | Const n => Some n
    | Var x => vars x
    | Plus e1 e2 => match eval e1 vars, eval e2 vars with
                     | None, _ => None
                     | _, None => None
                     | Some v1, Some v2 => Some (v1 + v2)
                   end

    | Times e1 e2 => match eval e1 vars, eval e2 vars with
                     | None, _ => None
                     | _, None => None
                     | Some v1, Some v2 => Some (v1 * v2)
                   end
  end.

Fixpoint eval' (e: arith) (vars: tmap nat) : nat :=
  match e with
    | Const n => n
    | Var x => vars x
    | Plus e1 e2 => eval' e1 vars + eval' e2 vars
    | Times e1 e2 => eval' e1 vars * eval' e2 vars
  end.

Compute eval my_ast1 empty_pmap.
Compute eval my_ast1 (pmap_add (empty_pmap) "x" 2).

Compute eval' my_ast1 (empty_tmap 0).
Compute eval' my_ast1 (tmap_add (empty_tmap 0) "x" 2).
End ExerciseOne.

(* Exercise 2 *)
Module ExerciseTwo.
  (* 2.1 *)
  Inductive arith : Type :=
    | Const (n : nat)
    | Var (x : string)
    | LetIn (x : string) (e1 e2 : arith)
    | Plus (e1 e2 : arith)
    | Times (e1 e2 : arith).

  Fixpoint depth (ast: arith) : nat :=
    match ast with
      | Const _ => 1
      | Var _ => 1
      | LetIn _ e1 e2 => 1 + (max (depth e1) (depth e2))
      | Plus e1 e2 => 1 + (max (depth e1) (depth e2))
      | Times e1 e2 => 1 + (max (depth e1) (depth e2))
    end.

  (* 2.2 *)
  Definition my_ast1 := LetIn "x" (Const 1) (LetIn "y" (Const 2) (Plus (Var "x") (Var "y"))).
  Definition my_ast2 := LetIn "x" (Const 1) (LetIn "y" (Const 2) (Plus (Var "x") (Times (Var "y") (Var "z")))).
  Definition my_ast3 := LetIn "x" (Const 2) (LetIn "y" (Times (Const 2) (Var "x")) (Plus (Var "y") (Const 5))).

  (* 2.3 *)
  Fixpoint substitute (e1: arith) (v: string) (e2: arith) : arith :=
    match e1 with
      | Var n => if string_dec n v then e2 else e1
      | Plus e1' e2' => Plus (substitute e1' v e2) (substitute e2' v e2)
      | Times e1' e2' => Times (substitute e1' v e2) (substitute e2' v e2)
      (*| LetIn n e1' e2' => LetIn n (substitute e1' v e2) (substitute e2' v e2)*)
      | LetIn n e1' e2' => if n =? v then LetIn n (substitute e1' v e2) e2'
                          else LetIn n (substitute e1' v e2) (substitute e2' v e2)
      | o => o
    end.

  Compute substitute my_ast1 "x" (Const 1).

  (* 2.4 *)
  (* Copiei esta função auxiliar das soluções porque ajuda a meter o código mais clean *)
  Definition apply_option {A B C : Type} (f:A → B → C) (o1: option A) (o2: option B) :
    option C :=
    match o1,o2 with
    | None,_ => None
    |_, None => None
    | Some a, Some b => Some (f a b)
    end.

  Program Fixpoint eval (e: arith) {measure (depth e)}: option nat :=
    match e with
      | Const n => Some n
      | Var _ => None
      | LetIn n e1 e2 => eval (substitute e2 n e1)
      | Plus e1 e2 => apply_option plus (eval e1) (eval e2)
      | Times e1 e2 => apply_option mult (eval e1) (eval e2)
    end.
  Admit Obligations.

  Compute eval my_ast1.
  Compute eval my_ast2.
  Compute eval (LetIn "z" (Const 3) my_ast2).
  Compute eval my_ast3.
End ExerciseTwo.

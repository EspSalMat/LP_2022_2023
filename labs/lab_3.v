(* Lab Session 3 *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Require Import Coq.Unicode.Utf8.

Require Import Lia.

(* Ex 1.1 *)
Definition partition {X: Type} (f: X -> bool) (l: list X) : prod (list X) (list X) :=
  let f' := fun x => negb (f x) in (filter f l, filter f' l).

Compute partition (fun x => x <? 5) [1; 2; 3; 5; 9; 4; 6].

(* Ex 1.2 *)
Definition list_prod {X Y: Type} (l1: list X) (l2: list Y) : list (prod X Y) :=
  fold_right (fun x y => x ++ y) [] (map (fun x => map (fun y => (x, y)) l2) l1).

Compute list_prod [1; 2; 3] [4; 5; 6].

(* Ex 1.3 *)
Definition length {X: Type} (l: list X) : nat :=
  fold_right (fun x y => y + 1) 0 l.

Compute length [1; 2; 3].

(* Ex 1.4 *)
Definition map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
  fold_right (fun x y => (f x) :: y) [] l.

Compute map (fun x => 2 * x) [1; 2; 3].

(* Ex 1.5 *)
Definition filter {X: Type} (f: X -> bool) (l: list X) : list X :=
  let f' := fun x y => if (f x) then x :: y else y in
    fold_right f' [] l.

Compute filter (fun x => x <=? 2) [1; 2; 3].

(* Ex 1.6 *)
Definition forallb {X: Type} (f: X -> bool) (l: list X) : bool :=
  fold_right (fun x y => andb x y) true (map f l).

Compute forallb (fun x => x <=? 2) [1; 2; 3].
Compute forallb (fun x => x <=? 2) [1; 2].

(* Ex 2.1 *)
Theorem thm_simpl1: forall a b c:nat,
    a = 0 -> b*(a+b) = b*b.
Proof.
  intros a b c H.
  rewrite H.
  simpl.
  reflexivity.
Qed.

(* Ex 2.2 *)
Theorem thm_simpl2: forall (a b c d:nat) (f: nat -> nat -> nat),
    a=b -> c=d -> (forall x y, f x y = f y x) -> f a c = f d b.

Proof.
  intros a b c d f H1 H2 H3.
  rewrite H1. rewrite H2.
  rewrite H3.
  reflexivity.
Qed.

(* Ex 2.3 *)
Theorem identity_fn_applied_twice :
  ∀ (f : bool → bool),
  (∀ (x : bool), f x = x) →
  ∀ (b : bool), f (f b) = b.

Proof.
  intros.
  rewrite H.
  rewrite H.
  reflexivity.
Qed.

(* Ex 2.4 *)
Theorem negation_fn_applied_twice :
  ∀ (f : bool → bool),
  (∀ (x : bool), f x = negb x) →
  ∀ (b : bool), f (f b) = b.

Proof.
  intros.
  rewrite H.
  rewrite H.
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Module ExerciseThree.
  Inductive btree (X: Type) : Type :=
    | empty : btree X
    | node : X -> btree X -> btree X -> btree X.
  Arguments empty {X}.
  Arguments node {X} _ _ _.

  Definition leaf {X: Type} (x: X) : btree X := node x empty empty.
  Definition node' {X: Type} (x: X) (t: btree X) : btree X := node x t empty.

  Definition my_tree := node 9 (leaf 4) (leaf 3).
  Definition my_tree' := node 9 (node' 4 (node' 7 (node 11 (leaf 6) (leaf 2)))) (leaf 3).

  (* Ex 3.1 *)
  Fixpoint nodes {X: Type} (t: btree X) : nat :=
    match t with
      | empty => 0
      | node _ l r => 1 + (nodes l) + (nodes r)
    end.

  Compute nodes my_tree.
  Compute nodes my_tree'.

  (* Ex 3.2 *)
  Definition is_leaf {X: Type} (t: btree X) :=
    match t with
      | node _ empty empty => true
      | _ => false
    end.

  Fixpoint leaves {X: Type} (t: btree X) : nat :=
    let x' := if (is_leaf t) then 1 else 0 in
      match t with
        | empty => 0
        | node _ l r => x' + (leaves l) + (leaves r)
      end.

  Compute leaves my_tree.
  Compute leaves my_tree'.

  (* Ex 3.3 *)
  Fixpoint flatten {X: Type} (t: btree X) : list X :=
    match t with
      | empty => []
      | node x l r => x :: (flatten l) ++ (flatten r)
    end.

  Compute flatten my_tree.
  Compute flatten my_tree'.

  (* Ex 3.4 *)
  Fixpoint height {X: Type} (t: btree X) : nat :=
    match t with
      | empty => 0
      | node _ l r => 1 + max (height l) (height r)
    end.

  Compute height my_tree.
  Compute height my_tree'.

  (* Ex 3.5 *)
  (* DISCLAIMER: Preciso de aprender indução ainda. *)
  Theorem height_leq_nodes: ∀ {X: Type} (t: btree X), height t <= nodes t.
  Proof.
    intros. induction t.
    - reflexivity.
    - simpl. lia.
  Qed.


  (* Ex 3.6 *)
  Fixpoint maxTree (t: btree nat) : nat :=
    match t with
      | empty => 0
      | node x l r => max x (max (maxTree l) (maxTree r))
    end.

  Compute maxTree my_tree.
  Compute maxTree my_tree'.

  (* Ex 3.7 *)
  Fixpoint subTrees {X: Type} (t: btree X) : list (btree X) :=
    match t with
      | empty => []
      | node _ l r => l :: r :: subTrees l ++ subTrees r
    end.

  Compute subTrees my_tree.
  Compute subTrees my_tree'.

  (* Ex 3.8 *)
  Fixpoint mapBtree {X Y: Type} (f: X->Y) (t: btree X) : btree Y :=
    match t with
      | empty => empty
      | node x l r => node (f x) (mapBtree f l) (mapBtree f r)
    end.

  Compute mapBtree (fun x => x*2) my_tree.


  (* Ex 3.9 *)
  Fixpoint foldBtree {X Y: Type} (f: X->Y->Y->Y) (acc: Y) (t: btree X) : Y :=
    match t with
      | empty => acc
      | node x l r => f x (foldBtree f acc l) (foldBtree f acc r)
    end.

  Compute foldBtree (fun x ly ry => x + ly + ry) 0 my_tree.
  Compute foldBtree (fun x ly ry => x + ly + ry) 0 my_tree'.

  (* Ex 3.10 *)
  Definition nodes' {X: Type} (t: btree X) : nat :=
    foldBtree (fun x y y' => y + y' + 1) 0 t.

  Compute nodes' my_tree = nodes my_tree.
  Compute nodes' my_tree' = nodes my_tree'.

  Definition height' {X: Type} (t: btree X) : nat :=
    foldBtree (fun x y y' => 1 + (max y y')) 0 t.

  Compute height' my_tree = height my_tree.
  Compute height' my_tree' = height my_tree'.

  Definition flatten' {X: Type} (t: btree X) : list X :=
    foldBtree (fun x y y' => x :: y ++ y') [] t.

  Compute flatten' my_tree = flatten my_tree.

  Definition maxTree' (t: btree nat) : nat :=
    foldBtree (fun x y y' => max x (max y y')) 0 t.

  Compute maxTree' my_tree = maxTree my_tree.

  Definition mapBtree' {X Y: Type} (f: X->Y) (t: btree X) : btree Y :=
    foldBtree (fun x l r => node (f x) l r) empty t.

  Compute mapBtree' (fun x => x*2) my_tree.

  (* Ex 3.11 *)
  Lemma mapfusion: ∀ {X Y Z: Type} (f: Y → Z) (g: X → Y) tree,
    mapBtree f (mapBtree g tree) = mapBtree (fun x => f (g x)) tree.
  Proof.
    intros. induction tree.
    - simpl. reflexivity.
    - simpl. rewrite <- IHtree1. rewrite <- IHtree2. reflexivity.
  Qed.
End ExerciseThree.

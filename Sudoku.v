(* SUDOKU *)

Require Import Coq.Init.Datatypes.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Import ListNotations.

(** HELPER DATATYPES **)
(* Nat Pair *)
Definition pair := (nat * nat)%type.

(* Nat Multiset *)
Definition value := nat.
Definition multiset := nat -> nat.

(* Equality *)
Fixpoint eqNat (n1 : nat) (n2 : nat) :=
  match n1, n2 with
  | O, O => true
  | S m1, S m2 => eqNat m1 m2
  | _, _ => false
  end.

Definition eqp (p1 : pair) (p2 : pair) :=
  match p1, p2 with
  | (x1, y1), (x2, y2) => (eqNat x1 x2) && (eqNat y1 y2)
  end.

Infix "==" := eqNat  (at level 100) : eq_scope.
Infix "=p=" := eqp (at level 100) : eq_scope.

Open Scope eq_scope.

Definition empty : multiset :=
   fun x => 0.
Definition union (a b : multiset) : multiset :=
   fun x => a x + b x.
Definition singleton (v: nat) : multiset :=
   fun x => if x == v then 1 else 0.

Definition Sudoku := pair -> nat.

Definition blank : Sudoku := (fun _ => 0).

Definition update (xy : pair) (entry : nat) (grid : Sudoku) : Sudoku :=
  fun p => if eqp p xy then entry else grid xy.

(* THINK OF A BETTER NOTATION

Notation "[]" := empty.

Notation "p '[' n ']' s" := (update p n s)
                              (at level 100, s at next level, right associativity).

Example p1 : pair := (1, 1).

Example trivial : Sudoku := (1,2)[3]((1,1)[2][]). *)

Definition one_thru_nine : list nat := [1; 2; 3; 4; 5; 6; 7; 8; 9].

Fixpoint row_helper (puzzle : Sudoku) (row : nat) (counter : list nat) (acc : multiset) : multiset :=
  match counter with
  | [] => acc
  | i :: t => if (puzzle (row, i)) == 0 then row_helper puzzle row t acc
            else union (singleton (puzzle (row, i))) (row_helper puzzle row t acc)
  end.                        

Fixpoint row (puzzle : Sudoku) (row : nat) : multiset :=
  row_helper puzzle row one_thru_nine empty.

(* Parallel function for column and similar idea but nuanced for box to come. *)

Fixpoint column_helper (puzzle : Sudoku) (col : nat) (counter : list nat) (acc : multiset) : multiset :=
  match counter with
  | [] => acc
  | i :: t => if (puzzle (i, col)) == 0 then column_helper puzzle col t acc
            else union (singleton (puzzle (i, col))) (row_helper puzzle col t acc)
  end.       

Fixpoint column (puzzle : Sudoku) (column : nat) : multiset :=
  column_helper puzzle column one_thru_nine empty.

(**                BOX NUMBERS
                 -----------------
                |     |     |     |
                |  1  |  2  |  3  |
                |     |     |     |        
                |-----------------|
                |     |     |     |
                |  4  |  5  |  6  |
                |     |     |     |        
                |-----------------|
                |     |     |     |
                |  7  |  8  |  9  |
                |     |     |     |        
                 -----------------               **)

Definition box_pairs : list pair := [ (1,1); (1,2); (1,3); (2,1); (2,2); (2,3);
                                        (3,1); (3,2); (3,3) ].

Definition pair_addition (pair1 pair2 : pair) : pair :=
  match pair1, pair2 with
  | (a, b), (c, d) => (a + c, b + d)
  end.                       

Infix "+p" := pair_addition (at level 100).

Fixpoint box_helper (puzzle : Sudoku) (pairList : list pair) (acc: multiset) :
  multiset :=
  match pairList with
  | [] => acc
  | h :: t => if (puzzle h) == 0 then box_helper puzzle t acc
            else union (singleton (puzzle h)) (box_helper puzzle t acc)
  end.

Fixpoint box (puzzle : Sudoku) (box : nat) : multiset :=
  box_helper puzzle (map (pair_addition (3*(div (box-1) 3),3*(modulo (box-1) 3))) box_pairs) empty.

(* Makes sure no element of the multiset range 1-9 has multiplicity greater than    1.
 *)
Definition set_consistent (set : multiset) : bool :=
  fold_left (fun b i => b && (set i <=? 1)) one_thru_nine true.

(* Makes sure all elements of the multiset range 1-9 has multiplicity exactly 1.
 *)
Definition set_complete (set : multiset) : bool :=
  fold_left (fun b i => b && (set i == 1)) one_thru_nine true.

Definition rows_consistent (puzzle : Sudoku) : bool :=
  fold_left (fun b i => b && (set_consistent (row puzzle i))) one_thru_nine true.

Definition cols_consistent (puzzle : Sudoku) : bool :=
  fold_left (fun b i => b && (set_consistent (column puzzle i))) one_thru_nine true.

Definition boxes_consistent (puzzle : Sudoku) : bool :=
  fold_left (fun b i => b && (set_consistent (box puzzle i))) one_thru_nine true.

Definition sudoku_consistent (puzzle : Sudoku) : bool :=
  (rows_consistent puzzle) && (cols_consistent puzzle)
                           && (boxes_consistent puzzle).

Definition rows_complete (puzzle : Sudoku) : bool :=
  fold_left (fun b i => b && (set_complete (row puzzle i))) one_thru_nine true.

Definition cols_complete (puzzle : Sudoku) : bool :=
  fold_left (fun b i => b && (set_complete (column puzzle i))) one_thru_nine true.

Definition boxes_complete (puzzle : Sudoku) : bool :=
  fold_left (fun b i => b && (set_complete (box puzzle i))) one_thru_nine true.

Definition sudoku_complete (puzzle : Sudoku) : bool :=
  (rows_complete puzzle) && (cols_complete puzzle)
                           && (boxes_complete puzzle).

(* ABOVE AS PROPOSITIONS *)
Definition P_set_consistent (set : multiset) : Prop :=
  fold_left (fun b i => b /\ (set i <= 1)) one_thru_nine True.

Definition P_set_complete (set : multiset) : Prop  :=
  fold_left (fun b i => b /\ (set i = 1)) one_thru_nine True.

Definition P_rows_consistent (puzzle : Sudoku) : Prop :=
  fold_left (fun b i => b /\ (P_set_consistent (row puzzle i))) one_thru_nine True.

Definition P_cols_consistent (puzzle : Sudoku) : Prop :=
  fold_left (fun b i => b /\ (P_set_consistent (column puzzle i))) one_thru_nine True.

Definition P_boxes_consistent (puzzle : Sudoku) : Prop :=
  fold_left (fun b i => b /\ (P_set_consistent (box puzzle i))) one_thru_nine True.

Definition P_sudoku_consistent (puzzle : Sudoku) : Prop :=
  (P_rows_consistent puzzle) /\ (P_cols_consistent puzzle)
                           /\ (P_boxes_consistent puzzle).

Definition P_rows_complete (puzzle : Sudoku) : Prop :=
  fold_left (fun b i => b /\ (P_set_complete (row puzzle i))) one_thru_nine True.

Definition P_cols_complete (puzzle : Sudoku) : Prop :=
  fold_left (fun b i => b /\ (P_set_complete (column puzzle i))) one_thru_nine True.

Definition P_boxes_complete (puzzle : Sudoku) : Prop :=
  fold_left (fun b i => b /\ (P_set_complete (box puzzle i))) one_thru_nine True.

Definition P_sudoku_complete (puzzle : Sudoku) : Prop :=
  (P_rows_complete puzzle) /\ (P_cols_complete puzzle)
                           /\ (P_boxes_complete puzzle).


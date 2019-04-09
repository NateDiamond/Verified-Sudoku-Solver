(* SUDOKU *)

Require Import Coq.Init.Datatypes.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
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

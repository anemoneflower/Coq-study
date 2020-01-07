
(*** Days of the Week ***)

(* Define new type named day *)
Inductive day : Type :=
| monday
| tuesday
| wednesday
| sunday.

(* Write function that operate on days *)
Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => sunday
  | sunday => monday
  end.


(* Use command Compute *)
Compute (next_weekday monday).

Compute (next_weekday (next_weekday tuesday)).

(* Example
   1. makes assertion
   2. gives the assertion a name that can be used to refer to it later *)
Example test_next_weekday:
  (next_weekday (next_weekday sunday)) = tuesday.
(* Make coq to verify above example *)
Proof. simpl. reflexivity. Qed.

(*** Booleans ***)

(* Define new type named bool *)
Inductive bool : Type :=
| true
| false.

(* Write functions over booleans *)
Definition negb (b: bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1: bool) (b2: bool) :bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1: bool) (b2: bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

(* Notation command defines a new symbolic notation for an existing definition. *)
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.







   

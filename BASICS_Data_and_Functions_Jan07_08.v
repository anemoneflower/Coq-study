
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


(* Ex nandb *)
Definition nandb (b1: bool) (b2: bool) : bool :=
  match b1 with
  | true => negb b2
  | false => true
  end.
Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.


(* Ex andb3 *)
Definition andb3 (b1: bool) (b2: bool) (b3: bool) : bool :=
  match b1 with
  | true => andb b2 b3
  | false => false
  end.
Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.


(*** Types ***)

(* Check command print the type of an expression *)
Check true.
Check (negb true).
Check negb.

(* Type definition, where one of the constructors takes and argument *)
Inductive rgb : Type :=
| red
| green
| blue.

Inductive color : Type :=
| black
| white
| primary (p : rgb).

(* Define functions on colors using pattern matching *)
Definition monochrome (c: color) : bool :=
  match c with
  | black => true
  | white => true
  | primary q => false
  end.
Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

         
(*** Tuples ***)
(* A single constructor with multiple parameters can be used to create a tuple type. *)
Inductive bit : Type :=
| B0
| B1.
Inductive nybble : Type :=
| bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0).

(* The bits constructor acts as a wrapper for its contents. Unwrapping can be done by pattern-matching, as in the all_zero function which tests a nybble to see if all its bits are 0. *)
Definition all_zero (nb : nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | (bits _ _ _ _) => false
  end.
Compute (all_zero (bits B1 B1 B0 B0)).
Compute (all_zero (bits B0 B0 B0 B0)).

(*** Numbers ***)
(* Module allows an inner module does not interfere with the one from stand library *)
Module NatPlayground. (* This ends when we call End NatPlayground *)

  (* O represents zero. S represents natural number n *)
  (* O is a natural number (note that this is the letter "O," not the numeral "0").
     S can be put in front of a natural number to yield another one — if n is a natural number, then S n is too.) *)
  Inductive nat : Type :=
  | O
  | S (n: nat).

  Inductive nat' : Type :=
  | stop
  | tick (foo : nat').

  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n' (* if n has the form S n' for some n', then return n' *)
    end.
End NatPlayground.

Check (S (S (S (S O)))).

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.
Compute (minustwo 4).

Check S.
Check pred.
Check minustwo.
   
(* use Fixpoint to define recursive function *)
Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S ( S n') => evenb n'
  end.

Definition oddb (n: nat) : bool := negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.


Module NatPlayground2.
  Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.
  Compute (plus 3 2).

  Fixpoint mult (n m :nat) : nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m)
    end.
  Example test_mult1: (mult 3 3) = 9.
  Proof. simpl. reflexivity. Qed.

  Fixpoint minus (n m :nat) : nat :=
    match n, m with
    | 0, _ => 0
    | S _ , 0 => n
    | S n', S m' => minus n' m'
    end.
End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

(* Ex factorial *)
Fixpoint factorial (n: nat) : nat :=
  match n with
  | O => 1
  | S n' => mult n (factorial n')
  end.
Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.
Check ((0 + 1) + 1).

Fixpoint eqb (n m :nat) : bool :=
  match n with
  | O => match m with
        | O => true
        | S m' => false
        end
  | S n' => match m with
           | O => false
           | S m' => eqb n' m'
           end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

(* Ex ltb *)
Definition ltb (n m :nat) : bool :=
  match leb n m with
  | true => match eqb n m with
           | true => false
           | false => true
           end
  | false => false
  end.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.
                   

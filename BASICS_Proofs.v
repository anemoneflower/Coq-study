(*** Proof by Simiplification ***)
(* use simpl to simplify both sides of the equation *)
(* use reflexivity to check that both sides contain identical values. *)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

(* reflexivity can perform some simplification automatically when checking that two sides are equal *)
Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

(* reflexivity
   - tries "unfolding" defined terms, replacing them with their right-hand sides.
     if reflexivity succeeds, the whole goal is finished and we don't need to look at whatever expanded expressions reflexivity has created by all this simplification and unfolding.

   simpl
   - used in situations where we may have to read and understand the new goal that it creates, so we would not want it blindly expanding definitions and leaving the goal in a messy state.
 *)

(* Example, Theorem, Lemma, Fact, Remark
   - difference is mostly a matter of style.
   - pretty much the same thing to Coq. *)

(* intros n : Suppose n is some number... / moves n from the quantifier in the goal to a context of current assumptions. *)

(* tatic : command that is used between Proof and Qed to guide the process of checking some claim we are making. ex> intros, simpl, reflexivity *)

Theorem plus_l_l : forall n:nat, 1+n = S n.
Proof.
  intros n. reflexivity. Qed.
Theorem mult_0_l : forall n:nat, 0*n=0.
Proof.
  intros n. reflexivity. Qed.

(*** Proof by Rewriting ***)
Theorem plus_id_example : forall n m :nat,
  n = m ->
  n + n = m + m.
Proof.
  (* move both quantifiers into the context *)
  intros n m.
  (* move the hypothesis into the context *)
  intros H.
  (* rewrite the goal using the hypothesis *)
  rewrite -> H.
  reflexivity. Qed.

(* EX> plus id exercise *)
Theorem plus_id_exercise : forall n m o : nat,
    n=m -> m=o -> n+m = m+o.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite -> H1.
  rewrite <- H2.
  reflexivity. Qed.

Theorem mult_0_plus : forall n m : nat,
    (0 + n) * m=n*m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity. Qed.


(* EX> mult S 1 *)
Theorem mult_S_1 : forall n m : nat,
    m = S n ->
    m * (1+n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  rewrite <- plus_l_l.
  reflexivity. Qed.


(*** Proof by Case Analysis ***)
(* from previous file *)
Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m'=> eqb n' m'
            end
  end.
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
(* ------------------ *)

(* destruct generates two subgoals, which we must then prove, separately, in order to get Coq to accept the theorem. *)
Theorem plus_1_neq_0 : forall n : nat,
    (n + 1) =? 0  = false.
Proof.
  (* The annotation "as [| n']" is called an intro pattern. It tells Coq what variable names to introduce in each subgoal. In general, what goes between the square brackets is a list of lists of names, separated by |. In this case, the first component is empty, since the O constructor is nullary (it doesn't have any arguments). The second component gives a single name, n', since S is a unary constructor. *)
  (* The eqn:E annotation tells destruct to give the name E to this equation. *)
  intros n. destruct n as [| n'] eqn: E.
  (*The - signs are called bullets, and they mark the parts of the proof that correspond to each generated subgoal. *)
  - reflexivity.
  - reflexivity.
Qed.

Theorem negb_involutive: forall b: bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  -reflexivity.
  -reflexivity. Qed.

(* It is sometimes useful to invoke destruct inside  a subgoal. In this case, we use different kinds of bullets to mark goals on different "levels" *)

(*def. from previous file *)
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  Qed.

(* We can also use * or curly braces *)
Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. }}
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. }}
  Qed.

(* curly braces allow us to reuse the same bullet shapes at multiple levels in a proof *)
Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
Qed.

Theorem plus_1_neq_0' : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity. Qed.

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* Ex> andb true elim2 *)
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c. destruct b eqn:Eb.
  - simpl. destruct c eqn:Ec.
    + simpl. reflexivity.
    + intros H. rewrite -> H. reflexivity.
  - simpl. destruct c eqn:Ec.
    + reflexivity.
    + intros H. rewrite -> H. reflexivity.  
  Qed.

(* Ex> zero nbeq plus 1 *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  O =? (n+1) = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
  Qed.











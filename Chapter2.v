(* https://softwarefoundations.cis.upenn.edu/lf-current/Induction.html *)
(* Exercise numbers have nothing to do with exercises from the book *)
(* Exercise 2.1*)

Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite -> IH. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [|n' IHn].
  - induction m as [|m' IHm].
    +  reflexivity.
    + rewrite <- IHm. simpl. reflexivity.
  - induction m as [|m' IHm].
    + simpl. rewrite <- IHn. reflexivity.
    + simpl. rewrite -> IHn. reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  induction n as [|n' IH].
  -   induction m as [|m' IH'].
    + reflexivity.
    + simpl. rewrite <- IH'. simpl. reflexivity.
  - intros m. simpl. rewrite -> IH. induction m as [|m' IH'].
    + simpl. reflexivity.
    + simpl. rewrite <- IH'. reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  induction n as [|n' IH].
  - reflexivity.
  - intros m p. simpl. rewrite -> IH. reflexivity.
Qed.

(* Did not complete Exercise 2.2 *)

(* Exercise 2.3 *)
Fixpoint eqb (n m : nat) : bool :=
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

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* Exercise 2.4 *)

Fixpoint even (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => even n'
  end.

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).

Proof.
  induction n as [|n IH].
  - reflexivity.
  - rewrite -> IH. destruct (even n) eqn:E.
    + simpl. rewrite E. reflexivity.
    + simpl. rewrite E. reflexivity.
Qed.

(* Exercise 2.5 *)
(*
Theorem n + m = m + n holds for any natural number n, m 
Proof:
  First, we show show that m+n=m when n = 0 (Trivial)
  Then we show that m+n=m when m = 0 (Trivial)
  Then, we show that m+n'=n'+m for some number n'
  Finally we show that m'+n=n+m' for some number m'
  
  These two last follow from IH and definition of +.
  Qed.
*)
 
(* Exercise 2.6 *)
Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin)
.

Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 n => B1 n
  | B1 n => B0 (incr n)
  end.

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. simpl. reflexivity. Qed.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => 0
  | B0 n => 2 * bin_to_nat n
  | B1 n => 2 * bin_to_nat n + 1
  end.

Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Proof. simpl. reflexivity. Qed.

Example test_bin_incr5 : bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr6 : bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.

(* Missing rest *)

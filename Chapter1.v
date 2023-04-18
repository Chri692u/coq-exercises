(* https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html *)
(* Exercise 1.1 *) (* Exercise numbers are not related to anything in the book *)
Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 && b2 with
    | true => false
    | false => true
  end.

Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.

Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

(* Exercise 1.2 *)
Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match (b1 && b2) && b3 with
    | true => true
    | false => false
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.

(* Exercise 1.3 *)
Fixpoint factorial (n:nat) : nat := 
  match n with
    | O => S 0
    | S n' => n * factorial n'
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.  

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.

(* Exercise 1.4 *)
Fixpoint ltb (n m : nat) : bool :=
  match n with
    | O => 
      match m with
        | O => false
        | S _ => true
      end
    | S n' => 
      match m with
        | O => false
        | S m' => ltb n' m'
      end
  end. 

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.

Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.

Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

(* Exercise 1.5*)
Theorem plus_id_exercise: forall n m o : nat, 
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros h0 h1.
  rewrite h0.
  rewrite h1.
  reflexivity.
Qed.

(* Exercise 1.6 *)
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.

Proof.
  intros b c.
   destruct c as [|c'] eqn:C.
  - rewrite <- C. simpl. reflexivity.
  - destruct b as [|b'] eqn:B.
  + intros H. rewrite <- H. reflexivity.
  + intros H. rewrite <- H. simpl. reflexivity.
Qed.

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

Theorem zero_nbeq_plus_1 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros [|n].
  - reflexivity. 
  - reflexivity.
Qed.

(* Exercise 1.7 *)
Theorem identity_fn_applied_twice : forall (f : bool -> bool),
  (forall (x : bool), f x = x) -> forall (b : bool), f (f b) = b.
Proof.
  intros f x b.
  rewrite -> x. rewrite -> x.
  reflexivity.
Qed.

(* Exercise 1.8 *)
Theorem neg_fn_applied_twice : forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) -> forall (b : bool), f(f b) = b.
Proof.
  intros f x b.
  destruct b as [|b'] eqn:B.
  - rewrite -> x. rewrite -> x. reflexivity.
  - rewrite -> x. rewrite -> x. reflexivity.
Qed.
(* Do not modify the following line: (From the book)*)
(* Definition manual_grade_for_negation_fn_applied_twice : option (nat*string) := None. *)

(* Exercise 1.9 *)
Inductive letter : Type := | A | B | C | D | F.

Inductive modifier : Type := | Plus | Natural | Minus.

Inductive grade : Type := Grade (l:letter) (m:modifier).

Inductive comparison : Set :=
  | Eq : comparison (* "equal" *)
  | Lt : comparison (* "less than" *)
  | Gt : comparison. (* "greater than" *)

Definition letter_comparison (l1 l2 : letter) : comparison :=
  match l1, l2 with
  | A, A => Eq
  | A, _ => Gt
  | B, A => Lt
  | B, B => Eq
  | B, _ => Gt
  | C, (A | B) => Lt
  | C, C => Eq
  | C, _ => Gt
  | D, (A | B | C) => Lt
  | D, D => Eq
  | D, _ => Gt
  | F, (A | B | C | D) => Lt
  | F, F => Eq
  end.

Theorem letter_comparison_Eq : forall l,
  letter_comparison l l = Eq.
Proof.
  intros l. destruct l eqn:L.
  all: reflexivity.
Qed.

(* Exercise 1.10 *)
Definition modifier_comparison (m1 m2 : modifier) : comparison :=
  match m1, m2 with
  | Plus, Plus => Eq
  | Plus, _ => Gt
  | Natural, Plus => Lt
  | Natural, Natural => Eq
  | Natural, _ => Gt
  | Minus, (Plus | Natural) => Lt
  | Minus, Minus => Eq
  end.

Definition grade_comparison (g1 g2 : grade) : comparison :=
  match g1, g2 with
  | Grade l m, Grade l' m' => match (letter_comparison l l') with
    | Eq => modifier_comparison m m'
    | Gt => Gt
    | Lt => Lt
    end
  end.

Example test_grade_comparison1 :
  (grade_comparison (Grade A Minus) (Grade B Plus)) = Gt.
Proof. simpl. reflexivity. Qed.
Example test_grade_comparison2 :
  (grade_comparison (Grade A Minus) (Grade A Plus)) = Lt.
Proof. simpl. reflexivity. Qed.
Example test_grade_comparison3 :
  (grade_comparison (Grade F Plus) (Grade F Plus)) = Eq.
Proof. simpl. reflexivity. Qed.
Example test_grade_comparison4 :
  (grade_comparison (Grade B Minus) (Grade C Plus)) = Gt.
Proof. simpl. reflexivity. Qed.


(* Exercise 1.10 *)
Definition lower_grade (g : grade) : grade :=
  match g with
  | Grade g' Plus => Grade g' Natural
  | Grade g' Natural => Grade g' Minus
  | Grade g' Minus => match g' with
    | A => Grade B Plus
    | B => Grade C Plus
    | C => Grade D Plus
    | D => Grade F Plus
    | F => Grade F Minus
    end
  end.

Example lower_grade_A_Plus :
  lower_grade (Grade A Plus) = (Grade A Natural).
Proof. reflexivity. Qed.
Example lower_grade_A_Natural :
  lower_grade (Grade A Natural) = (Grade A Minus).
Proof. reflexivity. Qed.
Example lower_grade_A_Minus :
  lower_grade (Grade A Minus) = (Grade B Plus).
Proof. reflexivity. Qed.
Example lower_grade_B_Plus :
  lower_grade (Grade B Plus) = (Grade B Natural).
Proof. reflexivity. Qed.
Example lower_grade_F_Natural :
  lower_grade (Grade F Natural) = (Grade F Minus).
Proof. reflexivity. Qed.
Example lower_grade_twice :
  lower_grade (lower_grade (Grade B Minus)) = (Grade C Natural).
Proof. reflexivity. Qed.
Example lower_grade_thrice :
  lower_grade (lower_grade (lower_grade (Grade B Minus))) = (Grade C Minus).
Proof. reflexivity. Qed.

Theorem lower_grade_F_Minus : lower_grade (Grade F Minus) = (Grade F Minus).
Proof. simpl. reflexivity. Qed.

Theorem lower_grade_lowers : forall (g : grade),
  grade_comparison (Grade F Minus) g = Lt ->
  grade_comparison (lower_grade g) g = Lt.
Proof.
  intros g H.
  destruct g.
  destruct l.
  - destruct m.
  all : reflexivity.
  - destruct m. 
  all : reflexivity.
  - destruct m.
  all : reflexivity.
  - destruct m.
  all : reflexivity.
  - destruct m.
  + reflexivity.
  + reflexivity.
  + rewrite <- H. reflexivity.
Qed.

(* 3 Missing *)

Inductive Nat := O : Nat | S : Nat -> Nat.

Definition one := S O.
Definition two := S one.
Definition three := S two.
Definition four := S three.
Definition five := S four.

Fixpoint eq_Nat (n m : Nat) :=
  match n, m with
  | O, O       => true
  | O, S _     => false
  | S _, O     => false 
  | S n', S m' => eq_Nat n' m'
  end.

Compute eq_Nat O O.
Compute eq_Nat one O.
Compute eq_Nat one one.
Compute eq_Nat one four.
Compute eq_Nat five four.
Compute eq_Nat five five.

Fixpoint add (m n : Nat) : Nat :=
  match m with
  | O => n
  | S m' => S (add m' n)
  end.

Compute add one one.
Compute add one five.
Compute add five one.
Compute add five O.
Compute add O five.

Fixpoint max (m n : Nat) : Nat :=
  match m with
  | O => n
  | S m' => match n with
            | O => m
            | S n' => S (max m' n')
            end
  end.

Compute max one two.
Compute max O one.
Compute max one O.
Compute max four five.
Compute max five four.

(*EX1*)

Fixpoint le_Nat (m n : Nat) : bool :=
 match m with
 | O => true
 | S m' => match n with
           | O => false
           | S n' => le_Nat m' n'
           end
end.

Compute le_Nat O O. (* true *)
Compute le_Nat O one. (* true *)
Compute le_Nat one O. (* false *)
Compute le_Nat one one. (* true *)
Compute le_Nat one five. (* true *)
Compute le_Nat five one. (* false *)
Compute le_Nat five four. (* false *)
Compute le_Nat five five. (* true *)

(*EX2*)

Lemma le_then_O :
  forall n,
    le_Nat n O = true ->
    n = O.
Proof.
   intros n.
   intros H0.
   destruct n as [|n'].
   -trivial.
   -simpl in H0. inversion H0.
Qed.

(*EX3*)
Lemma le_refl:
  forall x,
    le_Nat x x = true.
Proof.
    intros x. induction x.
    -simpl. trivial.
    -simpl. apply IHx.
Qed.

Lemma le_Trans :
  forall m n p,
    le_Nat m n = true ->
    le_Nat n p = true ->
    le_Nat m p = true.
Proof.
    induction m.
    -simpl. trivial.
    -destruct n as [|n'].
    --destruct p as [|p']. 
    ---simpl. intros H0. inversion H0.
    ---simpl. intros H0. inversion H0.
    --destruct p as[|p'].
    ---simpl. intros H0 H1. inversion H1.
    ---simpl. apply IHm.
Qed.

(*EX4*)
Lemma le_Mai_Mic_Decat_x_plus_y :
  forall x y,
    le_Nat x (add x y) = true.
Proof.
    intros. induction x.
    -simpl. trivial.
    -simpl. apply IHx.
Qed.

(*EX5*)
Lemma le_Mai_Mic_Decat_cu_z :
  forall x y z,
  le_Nat x y = true -> le_Nat x (add y z) =true.
Proof.
intros. induction x. 
-trivial.
-
Qed.

(*EX6*)
Lemma Aia_cu_Maxim :
  forall x y,
  le_Nat x y = true -> max x y = y.
Proof.
Qed.

(*EX7*)
Lemma Aia_cu_Maxim_dar_invers :
  forall x y,
  le_Nat x y = false -> max x y = x.
Proof.
induction x.
- simpl. intros n H1. inversion H1.
Qed.
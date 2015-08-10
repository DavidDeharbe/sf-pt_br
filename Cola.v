(** * Programação Funcional em Coq: Cola *)
 
(** ** Booleans *)

Inductive bool : Type := true : bool | false : bool.

Definition negb (b:bool) : bool := 
  match b with true => false | false => true end.

Definition andb (b1:bool) (b2:bool) : bool := 
  match b1 with true => b2  | false => false end.

Definition orb (b1:bool) (b2:bool) : bool := 
  match b1 with true => true | false => b2 end.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof. Admitted.

Theorem identity_fn_applied_twice : 
  forall (f : bool -> bool), 
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof. Admitted.

Theorem andb_eq_orb : 
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof. Admitted.

(** ** Numbers *)

Module Playground1.
Inductive nat : Type := O : nat | S : nat -> nat.
End Playground1.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with O => m | S n' => S (plus n' m) end.

Fixpoint mult (n m : nat) : nat :=
  match n with O => O | S n' => plus m (mult n' m) end.

Fixpoint minus (n m:nat) : nat :=
  match n, m with O , _    => O | S _ , O    => n | S n', S m' => minus n' m' end.

Fixpoint exp (base power : nat) : nat :=
  match power with O => S O | S p => mult base (exp base p) end.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with O => true | S m' => false end
  | S n' => match m with O => false | S m' => beq_nat n' m' end
  end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with O => false | S m' => ble_nat n' m' end
  end.


Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof. Admitted.

Theorem plus_n_O : forall n, n + 0 = n.

Theorem plus_1_l : forall n:nat, 1 + n = S n. 
Proof. Admitted.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof. Admitted.

Theorem plus_id_example : forall n m:nat,
  n = m -> n + n = m + m.
Proof. Admitted.
Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof. Admitted.

Theorem mult_S_1 : forall n m : nat,
  m = S n -> m * (1 + n) = m * m.
Proof. Admitted.

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof. Admitted.

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof. Admitted.

Theorem plus_0_r_firsttry : forall n:nat,  n + 0 = n.
Proof. Admitted.

Theorem minus_diag : forall n, minus n n = 0.
Proof. Admitted.

Theorem mult_0_plus' : forall n m : nat, (0 + n) * m = n * m.
Proof. Admitted.

Theorem mult_0_r : forall n:nat, n * 0 = 0.
Proof. Admitted.

Theorem plus_n_Sm : forall n m : nat, S (n + m) = n + (S m).
Proof. Admitted.

Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof. Admitted.

Theorem plus_assoc : forall n m p : nat, n + (m + p) = (n + m) + p.
Proof. Admitted.



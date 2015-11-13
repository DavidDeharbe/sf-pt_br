Require Export Imp.

Definition Assertion := state -> Prop.

Definition as1 : Assertion := fun st => st X = 3.
Definition as2 : Assertion := fun st => st X <= st Y.
Definition as3 : Assertion :=
  fun st => st X = 3 \/ st X <= st Y.
Definition as4 : Assertion :=
  fun st => st Z * st Z <= st X /\
            ~ (((S (st Z)) * (S (st Z))) <= st X).
Definition as5 : Assertion := fun st => True.
Definition as6 : Assertion := fun st => False.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" :=
  (assert_implies P Q) (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P ->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

Definition hoare_triple
           (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st',
       c / st || st' ->
       P st ->
       Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  apply H. Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~(P st)) ->
  {{P}} c {{Q}}.
Proof. intros.
unfold hoare_triple.
intros.
unfold not in H.
apply H in H1.
inversion H1. Qed.

Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (update st X (aeval st a)).

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X ::= a) {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption. Qed.

Example assn_sub_example :
  {{(fun st => st X = 3) [X |-> ANum 3]}}
  (X ::= (ANum 3))
  {{fun st => st X = 3}}.
Proof.
  apply hoare_asgn. Qed.

Example assn_sub_ex1 :
{{ (fun st => st X <= 5) [X |-> APlus (AId X) (ANum 1) ]}}
(X ::= APlus (AId X) (ANum 1))
{{ fun st => st X <= 5}}.
Proof. apply hoare_asgn. Qed.

Lemma update_shadow_st :
    (forall {X Y: Type} {f g : X -> Y},
     (forall (x: X), f x = g x) -> f = g) ->
  forall x1 x2 id st,
   (update (update st id x1) id x2) = (update st id x2).
Proof.
intros.
apply H.
intros.
apply update_shadow.
Qed.

Theorem hoare_asgn_fwd :
  (forall {X Y: Type} {f g : X -> Y},
     (forall (x: X), f x = g x) -> f = g) ->
  forall m a P,
  {{fun st => P st /\ st X = m}}
    X ::= a
  {{fun st => P (update st X m) /\ st X = aeval (update st X m) a }}.
Proof.
  intros functional_extensionality m a P.
unfold hoare_triple.
intros.
split.
inversion H.
subst.
rewrite update_shadow_st.
inversion H0.
assert (st = update st X m).
apply functional_extensionality.
intros x.
unfold update.
destruct (eq_id_dec X x).
rewrite e in H2. apply H2.
reflexivity. rewrite <- H3. apply H1.
intros.
apply functional_extensionality.
intros.
apply H1.
inversion H0. inversion H. subst. simpl in H.
inversion H0. rewrite -> H.
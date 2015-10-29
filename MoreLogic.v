(** * MoreLogic: Elementos Adicionais de Lógica em Coq *)

Require Export "Prop".

(* ############################################################ *)
(** * Quantificação Existencial *)

(** [Claudia]Another critical logical connective is _existential
    quantification_.  We can express it with the following
    definition: *)

Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.

(** [Dalay]That is, [ex] is a family of propositions indexed by a type [X]
    and a property [P] over [X].  In order to give evidence for the
    assertion "there exists an [x] for which the property [P] holds"
    we must actually name a _witness_ -- a specific value [x] -- and
    then give evidence for [P x], i.e., evidence that [x] has the
    property [P]. 

*)


(** *** *)
(** [Diego]Coq's [Notation] facility can be used to introduce more
    familiar notation for writing existentially quantified
    propositions, exactly parallel to the built-in syntax for
    universally quantified propositions.  Instead of writing [ex nat
    ev] to express the proposition that there exists some number that
    is even, for example, we can write [exists x:nat, ev x].  (It is
    not necessary to understand exactly how the [Notation] definition
    works.) *)

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

(** *** *)
(** [Francisco]We can use the usual set of tactics for
    manipulating existentials.  For example, to prove an
    existential, we can [apply] the constructor [ex_intro].  Since the
    premise of [ex_intro] involves a variable ([witness]) that does
    not appear in its conclusion, we need to explicitly give its value
    when we use [apply]. *)

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness:=2). 
  reflexivity.  Qed.

(** [Renan]Note that we have to explicitly give the witness. *)

(** *** *)
(**Ou, no lugar de escrever [apply ex_intro with (witness:=e)] todas as vezes, podemos 
usar o atalho conveniente [exists e] que significa a mesma coisa. *)

Example exists_example_1' : exists n, n + (n * n) = 6.
Proof.
  exists 2. 
  reflexivity.  Qed.

(** *** *)
(** [Claudia]Conversely, if we have an existential hypothesis in the
    context, we can eliminate it with [inversion].  Note the use
    of the [as...] pattern to name the variable that Coq
    introduces to name the witness value and get evidence that
    the hypothesis holds for the witness.  (If we don't
    explicitly choose one, Coq will just call it [witness], which
    makes proofs confusing.) *)
  
Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H as [m Hm]. 
  exists (2 + m).  
  apply Hm.  Qed. 


(** [Dalay]Here is another example of how to work with existentials. *)
Lemma exists_example_3 : 
  exists (n:nat), even n /\ beautiful n.
Proof.
(* REALIZADO EM SALA *)
  exists 8.
  split.
  unfold even. simpl. reflexivity.
  apply b_sum with (n:=3) (m:=5).
  apply b_3. apply b_5.
Qed.

(** **** Exercício: nível 1, opcional (english_exists)  *)
(** [Diego]In English, what does the proposition 
      ex nat (fun n => beautiful (S n))
]] 
    mean? *)

(* PREENCHER *)

(*
*)
(** **** Exercício: nível 1 (dist_not_exists)  *)
(** [Francisco]Prove that "[P] holds for all [x]" implies "there is no [x] for
    which [P] does not hold." *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof. 
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 3, opcional (not_exists_dist)  *)
(** [Renan](The other direction of this theorem requires the classical "law
    of the excluded middle".) *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 2 (dist_exists_or)  *)
(** Prove que a quantificação existencial é distribuída sobre a disjunção *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
   (* PREENCHER *) Admitted.
(** [] *)

(* ###################################################### *)
(** * Booleanos Portadores de Evidência *)

(** [Claudia]So far we've seen two different forms of equality predicates:
    [eq], which produces a [Prop], and the type-specific forms, like
    [beq_nat], that produce [boolean] values.  The former are more
    convenient to reason about, but we've relied on the latter to let
    us use equality tests in _computations_.  While it is
    straightforward to write lemmas (e.g. [beq_nat_true] and
    [beq_nat_false]) that connect the two forms, using these lemmas
    quickly gets tedious. *)

(** *** *)
(** [Dalay]It turns out that we can get the benefits of both forms at once by
    using a construct called [sumbool]. *)

Inductive sumbool (A B : Prop) : Set :=
 | left : A -> sumbool A B 
 | right : B -> sumbool A B.

Notation "{ A } + { B }" :=  (sumbool A B) : type_scope.

(** [Diego]Think of [sumbool] as being like the [boolean] type, but instead
    of its values being just [true] and [false], they carry _evidence_
    of truth or falsity. This means that when we [destruct] them, we
    are left with the relevant evidence as a hypothesis -- just as
    with [or].  (In fact, the definition of [sumbool] is almost the
    same as for [or].  The only difference is that values of [sumbool]
    are declared to be in [Set] rather than in [Prop]; this is a
    technical distinction that allows us to compute with them.) *)

(** *** *)

(** [Francisco]Here's how we can define a [sumbool] for equality on [nat]s *)

Theorem eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  (* REALIZADO EM SALA *)
  intros n.
  induction n as [|n'].
  Case "n = 0".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      left. reflexivity.
    SCase "m = S m'".
      right. intros contra. inversion contra.
  Case "n = S n'".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      right. intros contra. inversion contra.
    SCase "m = S m'". 
      destruct IHn' with (m := m') as [eq | neq].
      left. apply f_equal.  apply eq.
      right. intros Heq. inversion Heq as [Heq']. apply neq. apply Heq'.
Defined. 
  
(** [Renan]Read as a theorem, this says that equality on [nat]s is decidable:
    that is, given two [nat] values, we can always produce either
    evidence that they are equal or evidence that they are not.  Read
    computationally, [eq_nat_dec] takes two [nat] values and returns a
    [sumbool] constructed with [left] if they are equal and [right] if
    they are not; this result can be tested with a [match] or, better,
    with an [if-then-else], just like a regular [boolean].  (Notice
    that we ended this proof with [Defined] rather than [Qed].  The
    only difference this makes is that the proof becomes
    _transparent_, meaning that its definition is available when Coq
    tries to do reductions, which is important for the computational
    interpretation.) *) 

(** *** *)
(** Abaixo um exemplo simples ilustrando as vantagens da forma [sumbool]. *)

Definition override' {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
  fun (k':nat) => if eq_nat_dec k k' then x else f k'.

Theorem override_same' : forall (X:Type) x1 k1 k2 (f : nat->X),
  f k1 = x1 -> 
  (override' f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f. intros Hx1.
  unfold override'.
  destruct (eq_nat_dec k1 k2).   (* observe what appears as a hypothesis *)
  Case "k1 = k2".
    rewrite <- e.
    symmetry. apply Hx1.
  Case "k1 <> k2". 
    reflexivity.  Qed.

(** [Claudia]Compare this to the more laborious proof (in MoreCoq.v) for the
    version of [override] defined using [beq_nat], where we had to use
    the auxiliary lemma [beq_nat_true] to convert a fact about
    booleans to a Prop. *)

(** **** Exercício: nível 1 (override_shadow')  *)
Theorem override_shadow' : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  (override' (override' f k1 x2) k1 x1) k2 = (override' f k1 x1) k2.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)





(* ####################################################### *)
(** * Exercícios Adicionais *)

(** **** Exercício: nível 3 (all_forallb)  *)
(** [Dalay]Inductively define a property [all] of lists, parameterized by a
    type [X] and a property [P : X -> Prop], such that [all X P l]
    asserts that [P] is true for every element of the list [l]. *)

Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
  (* PREENCHER *)
.

(** [Diego]Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Poly]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

(** [Francisco]Using the property [all], write down a specification for [forallb],
    and prove that it satisfies the specification. Try to make your 
    specification as precise as possible.

    [Renan]Are there any important properties of the function [forallb] which
    are not captured by your specification? *)

(* PREENCHER *)
(** [] *)

(** **** Exercício: nível 4, avançado (filter_challenge)  *)
(** Um dos principais propósitos do Coq é provar que os programas correspondem às suas 
especificações. Para este fim, provemos que nossa definição de [filter] está de acordo 
com uma especificação. Aqui está a especificação, escrita informalmente em português.

    [Claudia]Suppose we have a set [X], a function [test: X->bool], and a list
    [l] of type [list X].  Suppose further that [l] is an "in-order
    merge" of two lists, [l1] and [l2], such that every item in [l1]
    satisfies [test] and no item in [l2] satisfies test.  Then [filter
    test l = l1].

    [Dalay]A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example, 
    [1,4,6,2,3]
    is an in-order merge of
    [1,6,2]
    and
    [4,3].
    Your job is to translate this specification into a Coq theorem and
    prove it.  (Hint: You'll need to begin by defining what it means
    for one list to be a merge of two others.  Do this with an
    inductive relation, not a [Fixpoint].)  *)

(* PREENCHER *)
(** [] *)

(** **** Exercício: nível 5, avançado, opcional (filter_challenge_2)  *)
(** [Diego]A different way to formally characterize the behavior of [filter]
    goes like this: Among all subsequences of [l] with the property
    that [test] evaluates to [true] on all their members, [filter test
    l] is the longest.  Express this claim formally and prove it. *)

(* PREENCHER *)
(** [] *)

(** **** Exercício: nível 4, avançado (no_repeats)  *)
(** [Francisco]The following inductively defined proposition... *)

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

(** [Renan]...gives us a precise way of saying that a value [a] appears at
    least once as a member of a list [l]. 

	Para aquecer, é mostrado a seguir dois lemas a serem provados sobre [appears_in].
*)

Lemma appears_in_app : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  (* PREENCHER *) Admitted.

Lemma app_appears_in : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  (* PREENCHER *) Admitted.


(** [Claudia]Now use [appears_in] to define a proposition [disjoint X l1 l2],
    which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in common. *)

(* PREENCHER *)

(** [Dalay]Next, use [appears_in] to define an inductive proposition
    [no_repeats X l], which should be provable exactly when [l] is a
    list (with elements of type [X]) where every member is different
    from every other.  For example, [no_repeats nat [1,2,3,4]] and
    [no_repeats bool []] should be provable, while [no_repeats nat
    [1,2,1]] and [no_repeats bool [true,true]] should not be.  *)

(* PREENCHER *)

(** [Diego]Finally, state and prove one or more interesting theorems relating
    [disjoint], [no_repeats] and [++] (list append).  *)

(* PREENCHER *)
(** [] *)

(** **** Exercício: nível 3 (nostutter)  *)
(** [Francisco]Formulating inductive definitions of predicates is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help at all.

    [Renan]We say that a list of numbers "stutters" if it repeats the same
    number consecutively.  The predicate "[nostutter mylist]" means
    that [mylist] does not stutter.  Formulate an inductive definition
    for [nostutter].  (This is different from the [no_repeats]
    predicate in the exercise above; the sequence [1;4;1] repeats but
    does not stutter.) *)

Inductive nostutter:  list nat -> Prop :=
 (* PREENCHER *)
.

(** 
Tenha certeza de que cada um desses testes sejam bem-sucedidos, mas você é livre para 
mudar a prova se a que lhe for dada não funcionar para você. A sua definição pode ser 
diferente da minha e ainda assim ser correta, talvez precisando, sendo este o caso, que 
os exemplos tenham provas diferentes.

    [Dalay]The suggested proofs for the examples (in comments) use a number
    of tactics we haven't talked about, to try to make them robust
    with respect to different possible ways of defining [nostutter].
    You should be able to just uncomment and use them as-is, but if
    you prefer you can also prove each example with more basic
    tactics.  *)

Example test_nostutter_1:      nostutter [3;1;4;1;5;6].
(* PREENCHER *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_2:  nostutter [].
(* PREENCHER *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_3:  nostutter [5].
(* PREENCHER *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
(* PREENCHER *) Admitted.
(* 
  Proof. intro.
  repeat match goal with 
    h: nostutter _ |- _ => inversion h; clear h; subst 
  end.
  contradiction H1; auto. Qed.
*)
(** [] *)

(** **** Exercício: nível 4, avançado (pigeonhole principle)  *)
(** [Diego]The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some 
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** [Francisco]First a pair of useful lemmas (we already proved these for lists
    of naturals, but not for arbitrary lists). *)

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof. 
  (* PREENCHER *) Admitted.

Lemma appears_in_app_split : forall (X:Type) (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  (* PREENCHER *) Admitted.

(** [Renan]Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  (* PREENCHER *)
.

(** Agora temos aqui uma maneira de formalizar o princípio da casa dos pombos. A lista 
[l2] representa uma lista de rótulos da casa dos pombos e a lista [l1] representa os 
rótulos atribuídos a uma lista de itens: se houver mais itens que rótulos, pelo menos 
dois itens precisam ter o mesmo rótulo. Esta prova é muito mais fácil se você usar a 
hipótese [excluded_middle] para mostrar que [appears_in] é decidível, isto é, [forall x
    l, (appears_in x l) \/ ~ (appears_in x l)]. Entretanto também possível realizar a 
    prova _sem_ precisar assumir que [appears_in] é decidível: se você conseguir avançar 
    desta forma então não será mais necessária a hipótese [excluded_middle].*)

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X), 
   excluded_middle -> 
   (forall x, appears_in x l1 -> appears_in x l2) -> 
   length l2 < length l1 -> 
   repeats l1.  
Proof.
   intros X l1. induction l1 as [|x l1'].
  (* PREENCHER *) Admitted.
(** [] *)

(* PREENCHER *)

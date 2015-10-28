(** * Prop: Proposições e Evidência *)

Require Export Logic.

(* ####################################################### *)
(** * Proposições Definidas Indutivamente *)

(** [Claudia] In chapter [Basics] we defined a _function_ [evenb] that tests a
    number for evenness, yielding [true] if so.  We can use this
    function to define the _proposition_ that some number [n] is
    even: *)

Definition even (n:nat) : Prop := 
  evenb n = true.

(** [Dalay] That is, we can define "[n] is even" to mean "the function [evenb]
    returns [true] when applied to [n]."  

    Note que aqui temos dado um nome para
    uma proposição utilizando uma [Definition], assim como temos dado
    nomes para expressões de outros tipos. Ela não é fundamentalmente um
    novo tipo de proposição;  Ela ainda é apenas uma igualdade. *)

(** [Francisco] Another alternative is to define the concept of evenness
    directly.  Instead of going via the [evenb] function ("a number is
    even if a certain computation yields [true]"), we can say what the
    concept of evenness means by giving two different ways of
    presenting _evidence_ that a number is even. *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).


(** [Renan] The first line declares that [ev] is a proposition -- or,
    more formally, a family of propositions "indexed by" natural
    numbers.  (That is, for each number [n], the claim that "[n] is
    even" is a proposition.)  Such a family of propositions is
    often called a _property_ of numbers.  

    [Vitor] The last two lines declare the two ways to give evidence that a
    number [m] is even.  First, [0] is even, and [ev_0] is evidence
    for this.  Second, if [m = S (S n)] for some [n] and we can give
    evidence [e] that [n] is even, then [m] is also even, and [ev_SS n
    e] is the evidence.
*)


(** **** Exercício: nível 1 (double_even)  *)

Theorem double_even : forall n,
  ev (double n).
Proof.
  (* PREENCHER *) Admitted.
(** [] *)



(* ##################################################### *)

(** [Claudia] For [ev], we had already defined [even] as a function (returning a
   boolean), and then defined an inductive relation that agreed with
   it. However, we don't necessarily need to think about propositions
   first as boolean functions, we can start off with the inductive
   definition.
*)

(** [Dalay] As another example of an inductively defined proposition, let's
    define a simple property of natural numbers -- we'll call it
    "[beautiful]." *)

(** Informalmente, um número é [beautiful] se ele é [0], [3], [5], ou a
    soma de dois números [beautiful].  

    [Francisco] More pedantically, we can define [beautiful] numbers by giving four
    rules:

       - Rule [b_0]: The number [0] is [beautiful].
       - Rule [b_3]: The number [3] is [beautiful]. 
       - Rule [b_5]: The number [5] is [beautiful]. 
       - Rule [b_sum]: If [n] and [m] are both [beautiful], then so is
         their sum. *)

(** [Renan] We will see many definitions like this one during the rest
    of the course, and for purposes of informal discussions, it is
    helpful to have a lightweight notation that makes them easy to
    read and write.  _Inference rules_ are one such notation: *)
(**
                              -----------                               (b_0)
                              beautiful 0
                              
                              ------------                              (b_3)
                              beautiful 3

                              ------------                              (b_5)
                              beautiful 5    

                       beautiful n     beautiful m
                       ---------------------------                      (b_sum)
                              beautiful (n+m)   
*)

(** *** *)
(** [Vitor] Each of the textual rules above is reformatted here as an
    inference rule; the intended reading is that, if the _premises_
    above the line all hold, then the _conclusion_ below the line
    follows.  For example, the rule [b_sum] says that, if [n] and [m]
    are both [beautiful] numbers, then it follows that [n+m] is
    [beautiful] too.  If a rule has no premises above the line, then
    its conclusion holds unconditionally.

    [Claudia]These rules _define_ the property [beautiful].  That is, if we
    want to convince someone that some particular number is [beautiful],
    our argument must be based on these rules.  For a simple example,
    suppose we claim that the number [5] is [beautiful].  To support
    this claim, we just need to point out that rule [b_5] says so.
    Or, if we want to claim that [8] is [beautiful], we can support our
    claim by first observing that [3] and [5] are both [beautiful] (by
    rules [b_3] and [b_5]) and then pointing out that their sum, [8],
    is therefore [beautiful] by rule [b_sum].  This argument can be
    expressed graphically with the following _proof tree_: *)
(**
         ----------- (b_3)   ----------- (b_5)
         beautiful 3         beautiful 5
         ------------------------------- (b_sum)
                   beautiful 8   
*)
(** *** *)
(** 
    [Dalay] Of course, there are other ways of using these rules to argue that
    [8] is [beautiful], for instance:
         ----------- (b_5)   ----------- (b_3)
         beautiful 5         beautiful 3
         ------------------------------- (b_sum)
                   beautiful 8   
*)

(** **** Exercício: nível 1 (varieties_of_beauty)  *)
(** Existem quantas maneiras diferentes para mostrar que [8] é [beautiful]? *)

(* PREENCHER *)
(** [] *)

(* ####################################################### *)
(** ** Construindo Evidência *)

(** [Francisco] In Coq, we can express the definition of [beautiful] as
    follows: *)

Inductive beautiful : nat -> Prop :=
  b_0   : beautiful 0
| b_3   : beautiful 3
| b_5   : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).

(** *** *)
(** 
    [Renan] The rules introduced this way have the same status as proven 
    theorems; that is, they are true axiomatically. 
    So we can use Coq's [apply] tactic with the rule names to prove 
    that particular numbers are [beautiful].  *)

Theorem three_is_beautiful: beautiful 3.
Proof.
   (* Segue diretamente da regra [b_3]. *)
   apply b_3.
Qed.

Theorem eight_is_beautiful: beautiful 8.
Proof.
   (* Primeiramente usamos a regra [b_sum], instruindo Coq como
      instanciar [n] e [m]. *)
   apply b_sum with (n:=3) (m:=5).
   (* Para solucionar as submetas geradas por [b_sum], devemos prover
      evidência para [beautiful 3] e [beautiful 5]. Felizmente, temos
      regras para ambas. *)
   apply b_3.
   apply b_5.
Qed.

(** *** *)
(** [Vitor] As you would expect, we can also prove theorems that have
hypotheses about [beautiful]. *)

Theorem beautiful_plus_eight: forall n, beautiful n -> beautiful (8+n).
Proof.
  intros n B.
  apply b_sum with (n:=8) (m:=n).
  apply eight_is_beautiful.
  apply B.
Qed.

(** **** Exercício: nível 2 (b_times2)  *)
Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
Proof.
    (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 3 (b_timesm)  *)
Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof.
   (* PREENCHER *) Admitted.
(** [] *)


(* ####################################################### *)
(** * Uso de Evidência em Provas *)
(** ** Indução sobre Evidência *)

(** [Claudia]Besides _constructing_ evidence that numbers are beautiful, we can
    also _reason about_ such evidence. *)

(** [Dalay]The fact that we introduced [beautiful] with an [Inductive]
    declaration tells Coq not only that the constructors [b_0], [b_3],
    [b_5] and [b_sum] are ways to build evidence, but also that these
    four constructors are the _only_ ways to build evidence that
    numbers are beautiful. *)

(** Em outras palavras, se alguém nos dá a evidência [E] para a asserção
    [beautiful n], então sabemos que [E] deve ter um desses quatro formatos:

      - [E] é [b_0] (e [n] é [O]),
      - [E] é [b_3] (e [n] é [3]), 
      - [E] é [b_5] (e [n] é [5]), ou
      - [E] é [b_sum n1 n2 E1 E2] (e [n] é [n1+n2], em que [E1] é
        evidência que [n1] é beautiful e [E2] é evidência que [n2]
        é beautiful). *)

(** *** *)    
(** [Francisco]This permits us to _analyze_ any hypothesis of the form [beautiful
    n] to see how it was constructed, using the tactics we already
    know.  In particular, we can use the [induction] tactic that we
    have already seen for reasoning about inductively defined _data_
    to reason about inductively defined _evidence_.

    [Renan]To illustrate this, let's define another property of numbers: *)

Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n).

(** **** Exercício: nível 1 (gorgeous_tree)  *)
(** [Vitor]Write out the definition of [gorgeous] numbers using inference rule
    notation.
 
(* PREENCHER *)
[]
*)


(** **** Exercício: nível 1 (gorgeous_plus13)  *)
Theorem gorgeous_plus13: forall n, 
  gorgeous n -> gorgeous (13+n).
Proof.
   (* PREENCHER *) Admitted.
(** [] *)

(** *** *)
(** [Claudia]It seems intuitively obvious that, although [gorgeous] and
    [beautiful] are presented using slightly different rules, they are
    actually the same property in the sense that they are true of the
    same numbers.  Indeed, we can prove this. *)


Theorem gorgeous__beautiful_FAILED : forall n, 
  gorgeous n -> beautiful n.
Proof.
   intros. induction n as [| n'].
   Case "n = 0". apply b_0.
   Case "n = S n'". (* Estamos travados! *)
Abort.

(** [Dalay]The problem here is that doing induction on [n] doesn't yield a
    useful induction hypothesis. Knowing how the property we are
    interested in behaves on the predecessor of [n] doesn't help us
    prove that it holds for [n]. Instead, we would like to be able to
    have induction hypotheses that mention other numbers, such as [n -
    3] and [n - 5]. This is given precisely by the shape of the
    constructors for [gorgeous]. *)


(** *** *)

(** Vamos ver o que acontece se nós tentarmos provar isso por indução sobre a
    evidência [H] em vez de sobre [n]. *)

Theorem gorgeous__beautiful : forall n, 
  gorgeous n -> beautiful n.
Proof.
   intros n H.
   induction H as [|n'|n'].
   Case "g_0".
       apply b_0.
   Case "g_plus3". 
       apply b_sum. apply b_3.
       apply IHgorgeous.
   Case "g_plus5".
       apply b_sum. apply b_5. apply IHgorgeous. 
Qed.


(* [Francisco]These exercises also require the use of induction on the evidence. *)

(** **** Exercício: nível 2 (gorgeous_sum)  *)
Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
 (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 3, avançado (beautiful__gorgeous)  *)
Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
 (* PREENCHER *) Admitted.
(** [] *)




(** **** Exercício: nível 3 stars, opcional (g_times2)  *)
(** [Renan] Prove the [g_times2] theorem below without using [gorgeous__beautiful].
    You might find the following helper lemma useful. *)

Lemma helper_g_times2 : forall x y z, x + (z + y) = z + x + y.
Proof.
   (* FILL IN HERE *) Admitted.

Theorem g_times2: forall n, gorgeous n -> gorgeous (2*n).
Proof.
   intros n H. simpl. 
   induction H.
   (* PREENCHER *) Admitted.
(** [] *)



(** [Vitor]Here is a proof that the inductive definition of evenness implies
the computational one. *)

Theorem ev__even : forall n,
  ev n -> even n.
Proof.
  intros n E. induction E as [| n' E'].
  Case "E = ev_0". 
    unfold even. reflexivity.
  Case "E = ev_SS n' E'".  
    unfold even. apply IHE'.  
Qed.

(** **** Exercício: nível 1 (ev__even)  *) 
(** [Claudia]Could this proof also be carried out by induction on [n] instead
    of [E]?  If not, why not? *)

(* PREENCHER *)
(** [] *)

(** [Dalay]Intuitively, the induction principle [ev n] evidence [ev n] is
    similar to induction on [n], but restricts our attention to only
    those numbers for which evidence [ev n] could be generated. *)

(** **** Exercício: nível 1 (l_fails)  *)
(** A tentativa de prova a seguir não irá funcionar.
     Theorem l : forall n,
       ev n.
     Proof.
       intros n. induction n.
         Case "O". simpl. apply ev_0.
         Case "S".
           ...
   [Francisco]Intuitively, we expect the proof to fail because not every
   number is even. However, what exactly causes the proof to fail?

(* PREENCHER *)
*)
(** [] *)

(** [Renan]Here's another exercise requiring induction on evidence. *)
(** **** Exercício: nível 2 (ev_sum)  *)

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof. 
  (* PREENCHER *) Admitted.
(** [] *)



(* ####################################################### *)
(** ** Inversão em Evidência *)


(** [Vitor]Having evidence for a proposition is useful while proving, because we 
   can _look_ at that evidence for more information. For example, consider 
    proving that, if [n] is even, then [pred (pred n)] is
    too.  In this case, we don't need to do an inductive proof.  Instead 
    the [inversion] tactic provides all of the information that we need.

 *)

Theorem ev_minus2: forall n,  ev n -> ev (pred (pred n)). 
Proof.
  intros n E.
  inversion E as [| n' E'].
  Case "E = ev_0". simpl. apply ev_0. 
  Case "E = ev_SS n' E'". simpl. apply E'.  Qed.

(** **** Exercício: nível 1, opcional (ev_minus2_n)  *)
(** [Claudia]What happens if we try to use [destruct] on [n] instead of [inversion] on [E]? *)

(* PREENCHER *)
(** [] *)

(** *** *)
(** [Dalay]Here is another example, in which [inversion] helps narrow down to
the relevant cases. *)

Theorem SSev__even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. 
  inversion E as [| n' E']. 
  apply E'. Qed.

(** ** Revisitando a Tática Inversion *)

(** O uso do [inversion] pode parecer um pouco misterioso no início.
    Até agora, temos utilizado o [inversion] somente em proposições de 
    igualdade, para utilizar injectividade de contrutores ou para discriminar
    entre diferentes contrutores.  Mas nós podemos ver que
    [inversion] também pode ser aplicada para análisar evidências
    de proposições indutivamente definidas.

    [Francisco](You might also expect that [destruct] would be a more suitable
    tactic to use here. Indeed, it is possible to use [destruct], but 
    it often throws away useful information, and the [eqn:] qualifier
    doesn't help much in this case.)    

    [Renan]Here's how [inversion] works in general.  Suppose the name
    [I] refers to an assumption [P] in the current context, where
    [P] has been defined by an [Inductive] declaration.  Then,
    for each of the constructors of [P], [inversion I] generates
    a subgoal in which [I] has been replaced by the exact,
    specific conditions under which this constructor could have
    been used to prove [P].  Some of these subgoals will be
    self-contradictory; [inversion] throws these away.  The ones
    that are left represent the cases that must be proved to
    establish the original goal.

    [Vitor]In this particular case, the [inversion] analyzed the construction
    [ev (S (S n))], determined that this could only have been
    constructed using [ev_SS], and generated a new subgoal with the
    arguments of that constructor as new hypotheses.  (It also
    produced an auxiliary equality, which happens to be useless here.)
    We'll begin exploring this more general behavior of inversion in
    what follows. *)


(** **** Exercício: nível 1 (inversion_practice)  *)
Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  (* PREENCHER *) Admitted.

(** [Claudia]The [inversion] tactic can also be used to derive goals by showing
    the absurdity of a hypothesis. *)

Theorem even5_nonsense : 
  ev 5 -> 2 + 2 = 9.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 3, avançado (ev_ev__ev)  *)
(** [Dalay]Finding the appropriate thing to do induction on is a
    bit tricky here: *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 3, opcional (ev_plus_plus)  *)
(** Aqui está um exercício que somente requer aplicação de lemas já existentes.
    Nem indução ou até mesmo análise por caso é necessária, mas algumas das 
    reescritas podem ser tediosas. *)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  (* PREENCHER *) Admitted.
(** [] *)


(* ####################################################### *)
(** * Discussões e Variantes *)
(** ** Definição Computacional ou Definição Indutiva *)

(** [Francisco]We have seen that the proposition "[n] is even" can be
    phrased in two different ways -- indirectly, via a boolean testing
    function [evenb], or directly, by inductively describing what
    constitutes evidence for evenness.  These two ways of defining
    evenness are about equally easy to state and work with.  Which we
    choose is basically a question of taste.

    [Renan]However, for many other properties of interest, the direct
    inductive definition is preferable, since writing a testing
    function may be awkward or even impossible.  

    [Vitor]One such property is [beautiful].  This is a perfectly sensible
    definition of a set of numbers, but we cannot translate its
    definition directly into a Coq Fixpoint (or into a recursive
    function in any other common programming language).  We might be
    able to find a clever way of testing this property using a
    [Fixpoint] (indeed, it is not too hard to find one in this case),
    but in general this could require arbitrarily deep thinking.  In
    fact, if the property we are interested in is uncomputable, then
    we cannot define it as a [Fixpoint] no matter how hard we try,
    because Coq requires that all [Fixpoint]s correspond to
    terminating computations.

    [Claudia]On the other hand, writing an inductive definition of what it
    means to give evidence for the property [beautiful] is
    straightforward. *)




(* ####################################################### *)
(** ** Estruturas de Dados com Parâmetros *)

(** [Dalay]So far, we have only looked at propositions about natural numbers. However, 
   we can define inductive predicates about any type of data. For example, 
   suppose we would like to characterize lists of _even_ length. We can 
   do that with the following definition.  *)

Inductive ev_list {X:Type} : list X -> Prop :=
  | el_nil : ev_list []
  | el_cc  : forall x y l, ev_list l -> ev_list (x :: y :: l).

(** É claro, essa proposição é equivalente a dizer que o tamanho
da lista é par. *)

Lemma ev_list__ev_length: forall X (l : list X), ev_list l -> ev (length l).
Proof. 
    intros X l H. induction H.
    Case "el_nil". simpl. apply ev_0.
    Case "el_cc".  simpl.  apply ev_SS. apply IHev_list.
Qed.

(** [Francisco]However, because evidence for [ev] contains less information than
evidence for [ev_list], the converse direction must be stated very
carefully. *)

Lemma ev_length__ev_list: forall X n, ev n -> forall (l : list X), n = length l -> ev_list l.
Proof.
  intros X n H. 
  induction H.
  Case "ev_0". intros l H. destruct l.
    SCase "[]". apply el_nil. 
    SCase "x::l". inversion H.
  Case "ev_SS". intros l H2. destruct l. 
    SCase "[]". inversion H2. destruct l.
    SCase "[x]". inversion H2.
    SCase "x :: x0 :: l". apply el_cc. apply IHev. inversion H2. reflexivity.
Qed.
    

(** **** Exercício: nível 4 (palindromes)  *)
(** [Renan]A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor
        c : forall l, l = rev l -> pal l
      may seem obvious, but will not work very well.)
 
    - Prove [pal_app_rev] that 
       forall l, pal (l ++ rev l).
    - Prove [pal_rev] that 
       forall l, pal l -> l = rev l.
*)

(* PREENCHER *)
(** [] *)

(* [Vitor]Again, the converse direction is much more difficult, due to the
lack of evidence. *)

(** **** Exercício: nível 5, opcional (palindrome_converse)  *)
(** [Claudia]Using your definition of [pal] from the previous exercise, prove
    that
     forall l, l = rev l -> pal l.
*)

(* PREENCHER *)
(** [] *)



(* ####################################################### *)
(** ** Relações *)

(** [Dalay]A proposition parameterized by a number (such as [ev] or
    [beautiful]) can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

Module LeModule.  


(** Um exemplo útil é relação "menor que ou igual à"
    em números. *)

(** [Francisco]The following definition should be fairly intuitive.  It
    says that there are two ways to give evidence that one number is
    less than or equal to another: either observe that they are the
    same number, or give evidence that the first is less than or equal
    to the predecessor of the second. *)

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).


(** [Renan]Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [ev] in chapter [Prop].  We can [apply] the constructors to prove [<=]
    goals (e.g., to show that [3<=3] or [3<=6]), and we can use
    tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [(2 <= 1) -> 2+2=5].) *)

(** *** *)
(** [Vitor]Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations.) *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* REALIZADO EM SALA *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* REALIZDO EM SALA *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof. 
  (* REALIZDO EM SALA *)
  intros H. inversion H. inversion H2.  Qed.

(** *** *)
(** [Claudia]The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

End LeModule.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** [Dalay]Here are a few more simple relations on numbers: *)

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn : forall n:nat, next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 : forall n, ev (S n) -> next_even n (S n)
  | ne_2 : forall n, ev (S (S n)) -> next_even n (S (S n)).

(** **** Exercício: nível 2 (total_relation)  *)
(** Definir uma relação binária indutiva [total_relation] que exista
    entre qualquer par de números naturais. *)

(* PREENCHER *)
(** [] *)

(** **** Exercício: nível 2 (empty_relation)  *)
(** [Francisco]Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)

(* PREENCHER *)
(** [] *)

(** **** Exercício: nível 2, opcional (le_exercises)  *)
(** [Renan]Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  (* PREENCHER *) Admitted.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  (* PREENCHER *) Admitted.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof. 
  (* PREENCHER *) Admitted.


Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof. 
  (* PREENCHER *) Admitted.


Theorem le_plus_l : forall a b,
  a <= a + b.
Proof. 
  (* PREENCHER *) Admitted.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof. 
 unfold lt. 
 (* PREENCHER *) Admitted.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  (* PREENCHER *) Admitted.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof. 
  (* PREENCHER *) Admitted.

Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
  (* Dica: Pode ser mais fácil provar por indução sobre [m]. *)
  (* PREENCHER *) Admitted.

Theorem ble_nat_true_trans : forall n m o,
  ble_nat n m = true -> ble_nat m o = true -> ble_nat n o = true.                               
Proof.
  (* Dica: Este teorema é facilmente provado sem [induction]. *)
  (* PREENCHER *) Admitted.

(** **** Exercício: nível 2, opcional (ble_nat_false)  *)
Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  (* PREENCHER *) Admitted.
(** [] *)


(** **** Exercício: nível 3 (R_provability2)  *)
Module R.
(** [Vitor]We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0 
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

(** [Claudia]- Which of the following propositions are provable?
      - [R 1 1 2]
      - [R 2 2 6]

    [Dalay]- If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.
  
    - Se nós utilizarmos o construtor [c4] a partir da definição de [R],
      poderá o conjunto de proposições prováveis mudar?  Brevemente (1
      sentença) explique sua resposta.

(* PREENCHER *)
[]
*)

(** **** Exercício: nível 3, opcional (R_fact)  *)  
(** [Francisco]Relation [R] actually encodes a familiar function.  State and prove two
    theorems that formally connects the relation and the function. 
    That is, if [R m n o] is true, what can we say about [m],
    [n], and [o], and vice versa?
*)

(* PREENCHER *)
(** [] *)

End R.

(** **** Exercício: nível 4, avançado (subsequence)  *)
(** [Renan]A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,
    [1,2,3]
    is a subsequence of each of the lists
    [1,2,3]
    [1,1,1,2,2,3]
    [1,2,7,3]
    [5,6,1,9,9,2,7,3,8]
    but it is _not_ a subsequence of any of the lists
    [1,2]
    [1,3]
    [5,6,2,1,7,3,8]

    [Claudia]- Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    [Dalay]- Prove [subseq_refl] that subsequence is reflexive, that is, 
      any list is a subsequence of itself.  

    - Provar [subseq_app] que para qualquer lista [l1], [l2], e [l3], 
      se [l1] é uma subsequência de [l2], então [l1] também é uma subsequência
      de [l2 ++ l3].

    [Francisco]- (Optional, harder) Prove [subseq_trans] that subsequence is 
      transitive -- that is, if [l1] is a subsequence of [l2] and [l2] 
      is a subsequence of [l3], then [l1] is a subsequence of [l3].  
      Hint: choose your induction carefully!
*)

(* PREENCHER *)
(** [] *)

(** **** Exercício: nível 2, opcional (R_provability)  *)
(** [Renan]Suppose we give Coq the following definition:
    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.
    Which of the following propositions are provable?

    - [R 2 [1,0]]
    - [R 1 [1,2,1,0]]
    - [R 6 [3,2,1,0]]
*)

(** [] *)


(* ##################################################### *)
(** * Programação através de Proposições *)

(** [Vitor]As we have seen, a _proposition_ is a statement expressing a factual claim,
    like "two plus two equals four."  In Coq, propositions are written
    as expressions of type [Prop]. . *)

Check (2 + 2 = 4).
(* ===> 2 + 2 = 4 : Prop *)

Check (ble_nat 3 2 = false).
(* ===> ble_nat 3 2 = false : Prop *)

Check (beautiful 8).
(* ===> beautiful 8 : Prop *)

(** *** *)
(** [Claudia]Both provable and unprovable claims are perfectly good
    propositions.  Simply _being_ a proposition is one thing; being
    _provable_ is something else! *)

Check (2 + 2 = 5).
(* ===> 2 + 2 = 5 : Prop *)

Check (beautiful 4).
(* ===> beautiful 4 : Prop *)

(** [Dalay]Both [2 + 2 = 4] and [2 + 2 = 5] are legal expressions
    of type [Prop]. *)

(** *** *)
(** Nós temos principalmente visto um lugar que proposições podem aparecer em
    Coq: em declarações de [Theorem] (e [Lemma] e [Example]). *)

Theorem plus_2_2_is_4 : 
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(** [Francisco]But they can be used in many other ways.  For example, we have also seen that
    we can give a name to a proposition using a [Definition], just as we have
    given names to expressions of other sorts. *)

Definition plus_fact : Prop  :=  2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)

(** [Renan]We can later use this name in any situation where a proposition is
    expected -- for example, as the claim in a [Theorem] declaration. *)

Theorem plus_fact_is_true : 
  plus_fact.
Proof. reflexivity.  Qed.

(** *** *)
(** [Vitor]We've seen several ways of constructing propositions.  

       - We can define a new proposition primitively using [Inductive].

       - Given two expressions [e1] and [e2] of the same type, we can
         form the proposition [e1 = e2], which states that their
         values are equal.

       - We can combine propositions using implication and
         quantification. *)
(** *** *)
(** [Claudia]We have also seen _parameterized propositions_, such as [even] and
    [beautiful]. *)

Check (even 4).
(* ===> even 4 : Prop *)
Check (even 3).
(* ===> even 3 : Prop *)
Check even. 
(* ===> even : nat -> Prop *)

(** *** *)
(** [Dalay]The type of [even], i.e., [nat->Prop], can be pronounced in
    three equivalent ways: (1) "[even] is a _function_ from numbers to
    propositions," (2) "[even] is a _family_ of propositions, indexed
    by a number [n]," or (3) "[even] is a _property_ of numbers."  *)

(** Proposições -- incluindo proposições parametrizadas -- são
    cidadãos de primeira classe em Coq.  Por exemplo, nós podemos definir
    funções a partir de números para proposições... *)

Definition between (n m o: nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.

(** ... e então aplica-las parcialmente: *)

Definition teen : nat->Prop := between 13 19.

(** [Francisco]We can even pass propositions -- including parameterized
    propositions -- as arguments to functions: *)

Definition true_for_zero (P:nat->Prop) : Prop :=
  P 0.

(** *** *)
(** [Renan]Here are two more examples of passing parameterized propositions
    as arguments to a function.  

    [Vitor]The first function, [true_for_all_numbers], takes a proposition
    [P] as argument and builds the proposition that [P] is true for
    all natural numbers. *)

Definition true_for_all_numbers (P:nat->Prop) : Prop :=
  forall n, P n.

(** [Claudia]The second, [preserved_by_S], takes [P] and builds the proposition
    that, if [P] is true for some natural number [n'], then it is also
    true by the successor of [n'] -- i.e. that [P] is _preserved by
    successor_: *)

Definition preserved_by_S (P:nat->Prop) : Prop :=
  forall n', P n' -> P (S n').

(** *** *)
(** [Dalay]Finally, we can put these ingredients together to define
a proposition stating that induction is valid for natural numbers: *)

Definition natural_number_induction_valid : Prop :=
  forall (P:nat->Prop),
    true_for_zero P ->
    preserved_by_S P -> 
    true_for_all_numbers P. 





(** **** Exercício: nível 3 (combine_odd_even)  *)
(** Completar a definição da função [combine_odd_even] abaixo. 
    Ela toma como argumento duas propriedades dos números, [Podd] e
    [Peven]. Como resultado, ela deve retornar uma nova propriedade [P] tal
    que [P n] é equivalente a [Podd n] quando [n] é impar, e caso contrário é
    equivalente a [Peven n]. *)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  (* PREENCHER *) admit.

(** [Francisco]To test your definition, see whether you can prove the following
    facts: *)

Theorem combine_odd_even_intro : 
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  (* PREENCHER *) Admitted.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  (* PREENCHER *) Admitted.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  (* PREENCHER *) Admitted.

(** [] *)

(* ##################################################### *)
(** [Renan]One more quick digression, for adventurous souls: if we can define
    parameterized propositions using [Definition], then can we also
    define them using [Fixpoint]?  Of course we can!  However, this
    kind of "recursive parameterization" doesn't correspond to
    anything very familiar from everyday mathematics.  The following
    exercise gives a slightly contrived example. *)

(** **** Exercício: nível 4, opcional (true_upto_n__true_everywhere)  *)
(** [Vitor]Define a recursive function
    [true_upto_n__true_everywhere] that makes
    [true_upto_n_example] work. *)

(* 
Fixpoint true_upto_n__true_everywhere
(* PREENCHER *)

Example true_upto_n_example :
    (true_upto_n__true_everywhere 3 (fun n => even n))
  = (even 3 -> even 2 -> even 1 -> forall m : nat, even m).
Proof. reflexivity.  Qed.
*)
(** [] *)




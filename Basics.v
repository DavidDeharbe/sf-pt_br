(** * Basics: Functional Programming in Coq *)
 
(*
   [Admitted] is Coq's "escape hatch" that says accept this definition
   without proof.  We use it to mark the 'holes' in the development
   that should be completed as part of your homework exercises.  In
   practice, [Admitted] is useful when you're incrementally developing
   large proofs. *)
Definition admit {T: Type} : T.  Admitted.

(* ###################################################################### *)
(** * Introduction *)

(** The functional programming style brings programming closer to
    simple, everyday mathematics: If a procedure or method has no side
    effects, then pretty much all you need to understand about it is
    how it maps inputs to outputs -- that is, you can think of it as
    just a concrete method for computing a mathematical function.
    This is one sense of the word "functional" in "functional
    programming."  The direct connection between programs and simple
    mathematical objects supports both formal proofs of correctness
    and sound informal reasoning about program behavior.

    The other sense in which functional programming is "functional" is
    that it emphasizes the use of functions (or methods) as
    _first-class_ values -- i.e., values that can be passed as
    arguments to other functions, returned as results, stored in data
    structures, etc.  The recognition that functions can be treated as
    data in this way enables a host of useful and powerful idioms.

    Outra característica comum das linguagens funcionais incluem _tipos de dados
    algébricos_ e _casamento de padrão_, tornando fácil de construir e
    manipular estruturas de dados rica, e sofistacados
    _sistemas de tipo polimórfico_ que suportam abstração e reuso
    de código.  Coq compartilha de todas essas características.

    The first half of this chapter introduces the most essential
    elements of Coq's functional programming language.  The second
    half introduces some basic _tactics_ that can be used to prove
    simple properties of Coq programs.
*)

(* ###################################################################### *)
(** * Enumerated Types *)

(** One unusual aspect of Coq is that its set of built-in
    features is _extremely_ small.  For example, instead of providing
    the usual palette of atomic data types (booleans, integers,
    strings, etc.), Coq offers an extremely powerful mechanism for
    defining new data types from scratch -- so powerful that all these
    familiar types arise as instances.  

    Naturally, the Coq distribution comes with an extensive standard
    library providing definitions of booleans, numbers, and many
    common data structures like lists and hash tables.  But there is
    nothing magic or primitive about these library definitions: they
    are ordinary user code.  To illustrate this, we will explicitly
    recapitulate all the definitions we need in this course, rather
    than just getting them implicitly from the library.

    To see how this mechanism works, let's start with a very simple
    example. *)

(* ###################################################################### *)
(** ** Days of the Week *)

(** The following declaration tells Coq that we are defining
    a new set of data values -- a _type_. *)

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

(** The type is called [day], and its members are [monday],
    [tuesday], etc.  The second and following lines of the definition
    can be read "[monday] is a [day], [tuesday] is a [day], etc."

    Uma vez definido [day], é possível escrever funções que operam em
    dias. *)

Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

(** Algo notável é que o argumento e os tipos de retorno dessa
    função estão declaradas explicitamente.  Como a maioria das linguagens
    de programação funcional, Coq pode frequentemente descobrir esses tipos
    sózinho, quando eles não são dados explictamente -- isto é, ele executa
    uma _inferência de tipo_ -- mas sempre devemos inclui-los para facilitar
    a leitura. *)

(** Having defined a function, we should check that it works on
    some examples.  There are actually three different ways to do this
    in Coq.  

    First, we can use the command [Eval compute] to evaluate a
    compound expression involving [next_weekday].  *)

Eval compute in (next_weekday friday).
   (* ==> monday : day *)
Eval compute in (next_weekday (next_weekday saturday)).
   (* ==> tuesday : day *)

(** If you have a computer handy, this would be an excellent
    moment to fire up the Coq interpreter under your favorite IDE --
    either CoqIde or Proof General -- and try this for yourself.  Load
    this file ([Basics.v]) from the book's accompanying Coq sources,
    find the above example, submit it to Coq, and observe the
    result. *)

(** The keyword [compute] tells Coq precisely how to
    evaluate the expression we give it.  For the moment, [compute] is
    the only one we'll need; later on we'll see some alternatives that
    are sometimes useful. *)

(** Second, we can record what we _expect_ the result to be in
    the form of a Coq example: *)

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

(** This declaration does two things: it makes an
    assertion (that the second weekday after [saturday] is [tuesday]),
    and it gives the assertion a name that can be used to refer to it
    later. *)
(** Having made the assertion, we can also ask Coq to verify it,
    like this: *)

Proof. simpl. reflexivity.  Qed.

(** The details are not important for now (we'll come back to
    them in a bit), but essentially this can be read as "The assertion
    we've just made can be proved by observing that both sides of the
    equality evaluate to the same thing, after some simplification." *)

(** Third, we can ask Coq to _extract_, from our [Definition], a
    program in some other, more conventional, programming
    language (OCaml, Scheme, or Haskell) with a high-performance
    compiler.  This facility is very interesting, since it gives us a
    way to construct _fully certified_ programs in mainstream
    languages.  Indeed, this is one of the main uses for which Coq was
    developed.  We'll come back to this topic in later chapters.  More
    information can also be found in the Coq'Art book by Bertot and
    Casteran, as well as the Coq reference manual. *)


(* ###################################################################### *)
(** ** Booleans *)

(** De maneira similar, é possível definir um tipo padrão [bool] de
    booleanos, com membros [true] e [false]. *)

Inductive bool : Type :=
  | true : bool
  | false : bool.

(** Apesar de estarmos rodando nossas próprias booleanas com o objetivo
    de construir tudo do zero, o Coq, é claro,
    provém uma implementação padrão de booleanas em sua biblioteca
    padrão, junto com uma grande quantidade de funções úteis e
    normas.  (Dê uma olhada em [Coq.Init.Datatypes] na biblioteca documental
    do Coq se estiver interessado.)  Sempre que possível, nomearemos
    nossa própria definição e teoremas, então elas iream coincidir exatamente
    com as definições na biblioteca padrão. *)

(** Functions over booleans can be defined in the same way as
    above: *)

Definition negb (b:bool) : bool := 
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool := 
  match b1 with 
  | true => b2 
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool := 
  match b1 with 
  | true => true
  | false => b2
  end.

(** The last two illustrate the syntax for multi-argument
    function definitions. *)

(** The following four "unit tests" constitute a complete
    specification -- a truth table -- for the [orb] function: *)

Example test_orb1:  (orb true  false) = true. 
Proof. reflexivity.  Qed.
Example test_orb2:  (orb false false) = false.
Proof. reflexivity.  Qed.
Example test_orb3:  (orb false true)  = true.
Proof. reflexivity.  Qed.
Example test_orb4:  (orb true  true)  = true.
Proof. reflexivity.  Qed.

(** (Note that we've dropped the [simpl] in the proofs.  It's not
    actually needed because [reflexivity] automatically performs
    simplification.) *)

(** _A note on notation_: In .v files, we use square brackets to
    delimit fragments of Coq code within comments; this convention,
    also used by the [coqdoc] documentation tool, keeps them visually
    separate from the surrounding text.  In the html version of the
    files, these pieces of text appear in a [different font]. *)

(** The values [Admitted] and [admit] can be used to fill
    a hole in an incomplete definition or proof.  We'll use them in the
    following exercises.  In general, your job in the exercises is 
    to replace [admit] or [Admitted] with real definitions or proofs. *)

(** **** Exercise: 1 star (nandb)  *)
(** Complete the definition of the following function, then make
    sure that the [Example] assertions below can each be verified by
    Coq.  *)

(** Essa função deve retornar [true] se um ou todas as
    entradas sâo [false]. *)

Definition nandb (b1:bool) (b2:bool) : bool :=
  (* PREENCHA AQUI *) admit.

(** Remova "[Admitted.]" e preencha cada prova com 
    "[Proof. reflexivity. Qed.]" *)

Example test_nandb1:               (nandb true false) = true.
(* PREENCHA AQUI *) Admitted.
Example test_nandb2:               (nandb false false) = true.
(* PREENCHA AQUI *) Admitted.
Example test_nandb3:               (nandb false true) = true.
(* PREENCHA AQUI *) Admitted.
Example test_nandb4:               (nandb true true) = false.
(* PREENCHA AQUI *) Admitted.
(** [] *)

(** **** Exercise: 1 star (andb3)  *)
(** Do the same for the [andb3] function below. This function should
    return [true] when all of its inputs are [true], and [false]
    otherwise. *)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  (* FILL IN HERE *) admit.

Example test_andb31:                 (andb3 true true true) = true.
(* FILL IN HERE *) Admitted.
Example test_andb32:                 (andb3 false true true) = false.
(* FILL IN HERE *) Admitted.
Example test_andb33:                 (andb3 true false true) = false.
(* FILL IN HERE *) Admitted.
Example test_andb34:                 (andb3 true true false) = false.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################################### *)
(** ** Function Types *)

(** The [Check] command causes Coq to print the type of an
    expression.  For example, the type of [negb true] is [bool]. *)

Check true.
(* ===> true : bool *)
Check (negb true).
(* ===> negb true : bool *)

(** Functions like [negb] itself are also data values, just like
    [true] and [false].  Their types are called _function types_, and
    they are written with arrows. *)

Check negb.
(* ===> negb : bool -> bool *)

(** The type of [negb], written [bool -> bool] and pronounced
    "[bool] arrow [bool]," can be read, "Given an input of type
    [bool], this function produces an output of type [bool]."
    Similarly, the type of [andb], written [bool -> bool -> bool], can
    be read, "Given two inputs, both of type [bool], this function
    produces an output of type [bool]." *)

(* ###################################################################### *)
(** ** Numbers *)

(** _Technical digression_: Coq provides a fairly sophisticated
    _module system_, to aid in organizing large developments.  In this
    course we won't need most of its features, but one is useful: If
    we enclose a collection of declarations between [Module X] and
    [End X] markers, then, in the remainder of the file after the
    [End], these definitions will be referred to by names like [X.foo]
    instead of just [foo].  Here, we use this feature to introduce the
    definition of the type [nat] in an inner module so that it does
    not shadow the one from the standard library. *)

Module Playground1.

(** The types we have defined so far are examples of "enumerated
    types": their definitions explicitly enumerate a finite set of
    elements.  A more interesting way of defining a type is to give a
    collection of "inductive rules" describing its elements.  For
    example, we can define the natural numbers as follows: *)

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

(** The clauses of this definition can be read: 
      - [O] is a natural number (note that this is the letter "[O]," not
        the numeral "[0]").
      - [S] is a "constructor" that takes a natural number and yields
        another one -- that is, if [n] is a natural number, then [S n]
        is too.

    Let's look at this in a little more detail.  

    Todo conjunto definido indutivamente ([day], [nat], [bool], etc.) é
    na realidade um conjunto de _expressões_.  A definição de [nat] diz como
    expressões do conjunto [nat] podem ser construidas:

    - the expression [O] belongs to the set [nat]; 
    - if [n] is an expression belonging to the set [nat], then [S n]
      is also an expression belonging to the set [nat]; and
    - expressions formed in these two ways are the only ones belonging
      to the set [nat].

    The same rules apply for our definitions of [day] and [bool]. The
    annotations we used for their constructors are analogous to the
    one for the [O] constructor, and indicate that each of those
    constructors doesn't take any arguments. *)

(** These three conditions are the precise force of the
    [Inductive] declaration.  They imply that the expression [O], the
    expression [S O], the expression [S (S O)], the expression
    [S (S (S O))], and so on all belong to the set [nat], while other
    expressions like [true], [andb true false], and [S (S false)] do
    not.

    We can write simple functions that pattern match on natural
    numbers just as we did above -- for example, the predecessor
    function: *)

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

(** The second branch can be read: "if [n] has the form [S n']
    for some [n'], then return [n']."  *)

End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

(** Because natural numbers are such a pervasive form of data,
    Coq provides a tiny bit of built-in magic for parsing and printing
    them: ordinary arabic numerals can be used as an alternative to
    the "unary" notation defined by the constructors [S] and [O].  Coq
    prints numbers in arabic form by default: *)

Check (S (S (S (S O)))).
Eval compute in (minustwo 4).

(** The constructor [S] has the type [nat -> nat], just like the
    functions [minustwo] and [pred]: *)

Check S.
Check pred.
Check minustwo.

(** These are all things that can be applied to a number to yield a
    number.  However, there is a fundamental difference: functions
    like [pred] and [minustwo] come with _computation rules_ -- e.g.,
    the definition of [pred] says that [pred 2] can be simplified to
    [1] -- while the definition of [S] has no such behavior attached.
    Although it is like a function in the sense that it can be applied
    to an argument, it does not _do_ anything at all! *)

(** For most function definitions over numbers, pure pattern
    matching is not enough: we also need recursion.  For example, to
    check that a number [n] is even, we may need to recursively check
    whether [n-2] is even.  To write such functions, we use the
    keyword [Fixpoint]. *)

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

(** We can define [oddb] by a similar [Fixpoint] declaration, but here
    is a simpler definition that will be a bit easier to work with: *)

Definition oddb (n:nat) : bool   :=   negb (evenb n).

Example test_oddb1:    (oddb (S O)) = true.
Proof. reflexivity.  Qed.
Example test_oddb2:    (oddb (S (S (S (S O))))) = false.
Proof. reflexivity.  Qed.

(** Naturally, we can also define multi-argument functions by
    recursion.  (Once again, we use a module to avoid polluting the
    namespace.) *)

Module Playground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

(** Adding three to two now gives us five, as we'd expect. *)

Eval compute in (plus (S (S (S O))) (S (S O))).

(** The simplification that Coq performs to reach this conclusion can
    be visualized as follows: *)

(*  [plus (S (S (S O))) (S (S O))]    
==> [S (plus (S (S O)) (S (S O)))] by the second clause of the [match]
==> [S (S (plus (S O) (S (S O))))] by the second clause of the [match]
==> [S (S (S (plus O (S (S O)))))] by the second clause of the [match]
==> [S (S (S (S (S O))))]          by the first clause of the [match]
*)

(** As a notational convenience, if two or more arguments have
    the same type, they can be written together.  In the following
    definition, [(n m : nat)] means just the same as if we had written
    [(n : nat) (m : nat)]. *)

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. reflexivity.  Qed.

(** You can match two expressions at once by putting a comma
    between them: *)

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O   , _    => O
  | S _ , O    => n
  | S n', S m' => minus n' m'
  end.

(** The _ in the first line is a _wildcard pattern_.  Writing _ in a
    pattern is the same as writing some variable that doesn't get used
    on the right-hand side.  This avoids the need to invent a bogus
    variable name. *)

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

(** **** Exercise: 1 star (factorial)  *)
(** Recall the standard factorial function:
<<
    factorial(0)  =  1 
    factorial(n)  =  n * factorial(n-1)     (if n>0)
>>
    Translate this into Coq. *)

Fixpoint factorial (n:nat) : nat := 
(* FILL IN HERE *) admit.

Example test_factorial1:          (factorial 3) = 6.
(* FILL IN HERE *) Admitted.
Example test_factorial2:          (factorial 5) = (mult 10 12).
(* FILL IN HERE *) Admitted.

(** [] *)

(** We can make numerical expressions a little easier to read and
    write by introducing "notations" for addition, multiplication, and
    subtraction. *)

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

(** (The [level], [associativity], and [nat_scope] annotations
   control how these notations are treated by Coq's parser.  The
   details are not important, but interested readers can refer to the
   "More on Notation" subsection in the "Advanced Material" section at
   the end of this chapter.) *)

(** Note que estas não mudam as definições que já foram realizadas:
    elas são simplesmente instruções para que o analisador do Coq aceite [x
    + y] no lugar de [plus x y] e, reciprocamente, para que o Coq
    imprima [plus x y] como [x + y]. *)

(** When we say that Coq comes with nothing built-in, we really
    mean it: even equality testing for numbers is a user-defined
    operation! *)
(** The [beq_nat] function tests [nat]ural numbers for [eq]uality,
    yielding a [b]oolean.  Note the use of nested [match]es (we could
    also have used a simultaneous match, as we did in [minus].)  *)

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

(** Similarly, the [ble_nat] function tests [nat]ural numbers for
    [l]ess-or-[e]qual, yielding a [b]oolean. *)

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Example test_ble_nat1:             (ble_nat 2 2) = true.
Proof. reflexivity.  Qed.
Example test_ble_nat2:             (ble_nat 2 4) = true.
Proof. reflexivity.  Qed.
Example test_ble_nat3:             (ble_nat 4 2) = false.
Proof. reflexivity.  Qed.

(** **** Exercise: 2 stars (blt_nat)  *)
(** The [blt_nat] function tests [nat]ural numbers for [l]ess-[t]han,
    yielding a [b]oolean.  Instead of making up a new [Fixpoint] for
    this one, define it in terms of a previously defined function. *)

Definition blt_nat (n m : nat) : bool :=
  (* FILL IN HERE *) admit.

Example test_blt_nat1:             (blt_nat 2 2) = false.
(* FILL IN HERE *) Admitted.
Example test_blt_nat2:             (blt_nat 2 4) = true.
(* FILL IN HERE *) Admitted.
Example test_blt_nat3:             (blt_nat 4 2) = false.
(* FILL IN HERE *) Admitted.

(** [] *)

(* ###################################################################### *)
(** * Proof by Simplification *)

(** Now that we've defined a few datatypes and functions, let's
    turn to the question of how to state and prove properties of their
    behavior.  Actually, in a sense, we've already started doing this:
    each [Example] in the previous sections makes a precise claim
    about the behavior of some function on some particular inputs.
    The proofs of these claims were always the same: use [reflexivity] 
    to check that both sides of the [=] simplify to identical values. 

    (By the way, it will be useful later to know that
    [reflexivity] actually does somewhat more simplification than [simpl] 
    does -- for example, it tries "unfolding" defined terms, replacing them with
    their right-hand sides.  The reason for this difference is that,
    when reflexivity succeeds, the whole goal is finished and we don't
    need to look at whatever expanded expressions [reflexivity] has
    found; by contrast, [simpl] is used in situations where we may
    have to read and understand the new goal, so we would not want it
    blindly expanding definitions.) 

    The same sort of "proof by simplification" can be used to prove
    more interesting properties as well.  For example, the fact that
    [0] is a "neutral element" for [+] on the left can be proved
    just by observing that [0 + n] reduces to [n] no matter what
    [n] is, a fact that can be read directly off the definition of [plus].*)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity.  Qed.


(** (_Note_: You may notice that the above statement looks
    different in the original source file and the final html output. In Coq
    files, we write the [forall] universal quantifier using the
    "_forall_" reserved identifier. This gets printed as an
    upside-down "A", the familiar symbol used in logic.)  *)

(** The form of this theorem and proof are almost exactly the
    same as the examples above; there are just a few differences.

    Primeiramente, foi utilizado a palavra-chave [Theorem] no lugar de
    [Example].  De fato, a diferença é puramente um questão de
    estilo; as palavras-chave [Example] e [Theorem] (e algumas outras,
    incluindo [Lemma], [Fact], e [Remark]) significam exatamente a mesma
    coisa para o Coq.

    Secondly, we've added the quantifier [forall n:nat], so that our
    theorem talks about _all_ natural numbers [n].  In order to prove
    theorems of this form, we need to to be able to reason by
    _assuming_ the existence of an arbitrary natural number [n].  This
    is achieved in the proof by [intros n], which moves the quantifier
    from the goal to a "context" of current assumptions. In effect, we
    start the proof by saying "OK, suppose [n] is some arbitrary number."

    The keywords [intros], [simpl], and [reflexivity] are examples of
    _tactics_.  A tactic is a command that is used between [Proof] and
    [Qed] to tell Coq how it should check the correctness of some
    claim we are making.  We will see several more tactics in the rest
    of this lecture, and yet more in future lectures. *)

(** We could try to prove a similar theorem about [plus] *)

Theorem plus_n_O : forall n, n + 0 = n.

(** However, unlike the previous proof, [simpl] doesn't do anything in
    this case *)

Proof.
  simpl. (* Doesn't do anything! *)
Abort.

(** (Can you explain why this happens?  Step through both proofs with
    Coq and notice how the goal and context change.) *)

Theorem plus_1_l : forall n:nat, 1 + n = S n. 
Proof.
  intros n. reflexivity.  Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity.  Qed.

(** The [_l] suffix in the names of these theorems is
    pronounced "on the left." *)


(* ###################################################################### *)
(** * Proof by Rewriting *)

(** Here is a slightly more interesting theorem: *)

Theorem plus_id_example : forall n m:nat,
  n = m -> 
  n + n = m + m.

(** Instead of making a completely universal claim about all numbers
    [n] and [m], this theorem talks about a more specialized property
    that only holds when [n = m].  The arrow symbol is pronounced
    "implies."

    As before, we need to be able to reason by assuming the existence
    of some numbers [n] and [m].  We also need to assume the hypothesis
    [n = m]. The [intros] tactic will serve to move all three of these
    from the goal into assumptions in the current context. 

    Desde que [n] e [m] sejam números arbitrários, pode ser utilizado
    simplificação para provar este teorema.  Entretanto, provamos isso
    observando que, se estamos assumindo que [n = m], então podemos substituir
    [n] com [m] na declaração dos objetivos e obtemos uma igualdade com a
    mesma expressão dos dois lados.  A tática que diz ao Coq para
    realizar essa substituição é chamada de [rewrite]. *)

Proof.
  intros n m.   (* move ambos os quantificadores para o contexto *)
  intros H.     (* move a hipótese para o contexto *)
  rewrite -> H. (* Reescreve o objetivo usando a hipótese *)
  reflexivity.  Qed.

(** A primeira linha da prova move as variáveis [n] e [m] universalmente
    quantificadas para o contexto.  A segunda move a hipótese
    [n = m] para o contexto e assume para ela o nome (arbitrário)
    [H].  A terceira diz para o Coq reescrever o objetivo atual ([n + n
    = m + m]) substituindo o lado esquerdo da hipótese de igualdade
    [H] pelo lado direito.

    (The arrow symbol in the [rewrite] has nothing to do with
    implication: it tells Coq to apply the rewrite from left to right.
    To rewrite from right to left, you can use [rewrite <-].  Try
    making this change in the above proof and see what difference it
    makes in Coq's behavior.) *)

(** **** Exercise: 1 star (plus_id_exercise)  *)
(** Remove "[Admitted.]" and fill in the proof. *)

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** As we've seen in earlier examples, the [Admitted] command
    tells Coq that we want to skip trying to prove this theorem and
    just accept it as a given.  This can be useful for developing
    longer proofs, since we can state subsidiary facts that we believe
    will be useful for making some larger argument, use [Admitted] to
    accept them on faith for the moment, and continue thinking about
    the larger argument until we are sure it makes sense; then we can
    go back and fill in the proofs we skipped.  Be careful, though:
    every time you say [Admitted] (or [admit]) you are leaving a door
    open for total nonsense to enter Coq's nice, rigorous, formally
    checked world! *)

(** We can also use the [rewrite] tactic with a previously proved
    theorem instead of a hypothesis from the context. *)

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.  Qed.

(** **** Exercise: 2 stars (mult_S_1)  *)
Theorem mult_S_1 : forall n m : nat,
  m = S n -> 
  m * (1 + n) = m * m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(* ###################################################################### *)
(** * Proof by Case Analysis *) 

(** Of course, not everything can be proved by simple
    calculation: In general, unknown, hypothetical values (arbitrary
    numbers, booleans, lists, etc.) can block the calculation.  
    For example, if we try to prove the following fact using the 
    [simpl] tactic as above, we get stuck. *)

Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. 
  simpl.  (* does nothing! *)
Abort.

(** The reason for this is that the definitions of both
    [beq_nat] and [+] begin by performing a [match] on their first
    argument.  But here, the first argument to [+] is the unknown
    number [n] and the argument to [beq_nat] is the compound
    expression [n + 1]; neither can be simplified.

    É preciso considerar as possíveis formas de [n]
    separadamente.  Se [n] é [O], então é possível calcular o resultado final
    de [beq_nat (n + 1) 0] e verificar se é, de fato, [false].
    E se [n = S n'] para algum [n'], então, embora nós não saberemos
    exatamente qual é o número [n + 1], podemos calcular que, pelo
    menos, irá começar com um [S], e isso é suficiente para calcular que, 
    novamente, [beq_nat (n + 1) 0] será [false].

    The tactic that tells Coq to consider, separately, the cases where
    [n = O] and where [n = S n'] is called [destruct]. *)

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
    reflexivity.
    reflexivity.  Qed.

(** The [destruct] generates _two_ subgoals, which we must then
    prove, separately, in order to get Coq to accept the theorem as
    proved.  (No special command is needed for moving from one subgoal
    to the other.  When the first subgoal has been proved, it just
    disappears and we are left with the other "in focus.")  In this
    proof, each of the subgoals is easily proved by a single use of
    [reflexivity].

    The annotation "[as [| n']]" is called an _intro pattern_.  It
    tells Coq what variable names to introduce in each subgoal.  In
    general, what goes between the square brackets is a _list_ of
    lists of names, separated by [|].  Here, the first component is
    empty, since the [O] constructor is nullary (it doesn't carry any
    data).  The second component gives a single name, [n'], since [S]
    is a unary constructor.

    The [destruct] tactic can be used with any inductively defined
    datatype.  For example, we use it here to prove that boolean
    negation is involutive -- i.e., that negation is its own
    inverse. *)

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
    reflexivity.
    reflexivity.  Qed.

(** Note that the [destruct] here has no [as] clause because
    none of the subcases of the [destruct] need to bind any variables,
    so there is no need to specify any names.  (We could also have
    written [as [|]], or [as []].)  In fact, we can omit the [as]
    clause from _any_ [destruct] and Coq will fill in variable names
    automatically.  Although this is convenient, it is arguably bad
    style, since Coq often makes confusing choices of names when left
    to its own devices. *)

(** **** Exercise: 1 star (zero_nbeq_plus_1)  *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* ###################################################################### *)
(** * More Exercises *)

(** **** Exercise: 2 stars (boolean_functions)  *)
(** Use the tactics you have learned so far to prove the following 
    theorem about boolean functions. *)

Theorem identity_fn_applied_twice : 
  forall (f : bool -> bool), 
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  (* FILL IN HERE *) Admitted.

(** Now state and prove a theorem [negation_fn_applied_twice] similar
    to the previous one but where the second hypothesis says that the
    function [f] has the property that [f x = negb x].*)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 2 stars (andb_eq_orb)  *)
(** Prove o seguinte teorema.  (Você pode querer provar uma 
    norma subsidirária ou duas. De maneira alternativa, lembre que você
    não tem que intruduzir todas as hipótese ao mesmo tempo.) *)

Theorem andb_eq_orb : 
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (binary)  *)
(** Consider a different, more efficient representation of natural
    numbers using a binary rather than unary system.  That is, instead
    of saying that each natural number is either zero or the successor
    of a natural number, we can say that each binary number is either

      - zero,
      - twice a binary number, or
      - one more than twice a binary number.

    (a) First, write an inductive definition of the type [bin]
        corresponding to this description of binary numbers. 

    (Hint: Recall that the definition of [nat] from class,
    Inductive nat : Type :=
      | O : nat
      | S : nat -> nat.
    says nothing about what [O] and [S] "mean."  It just says "[O] is
    in the set called [nat], and if [n] is in the set then so is [S
    n]."  The interpretation of [O] as zero and [S] as successor/plus
    one comes from the way that we _use_ [nat] values, by writing
    functions to do things with them, proving things about them, and
    so on.  Your definition of [bin] should be correspondingly simple;
    it is the functions you will write next that will give it
    mathematical meaning.)

    (b) Next, write an increment function [incr] for binary numbers, 
        and a function [bin_to_nat] to convert binary numbers to unary numbers.

    (c) Write five unit tests [test_bin_incr1], [test_bin_incr2], etc.
        for your increment and binary-to-unary functions. Notice that 
        incrementing a binary number and then converting it to unary 
        should yield the same result as first converting it to unary and 
        then incrementing. 
*)

(* FILL IN HERE *)
(** [] *)

(* ###################################################################### *)
(** * More on Notation (Advanced) *)

(** In general, sections marked Advanced are not needed to follow the
    rest of the book, except possibly other Advanced sections.  On a
    first reading, you might want to skim these sections so that you
    know what's there for future reference. *)

Notation "x + y" := (plus x y)  
                       (at level 50, left associativity) 
                       : nat_scope.
Notation "x * y" := (mult x y)  
                       (at level 40, left associativity) 
                       : nat_scope.

(** For each notation-symbol in Coq we can specify its _precedence level_
    and its _associativity_. The precedence level n can be specified by the
    keywords [at level n] and it is helpful to disambiguate
    expressions containing different symbols. The associativity is helpful
    to disambiguate expressions containing more occurrences of the same 
    symbol. For example, the parameters specified above for [+] and [*]
    say that the expression [1+2*3*4] is a shorthand for the expression
    [(1+((2*3)*4))]. Coq uses precedence levels from 0 to 100, and 
    _left_, _right_, or _no_ associativity.

    Each notation-symbol in Coq is also active in a _notation scope_.  
    Coq tries to guess what scope you mean, so when you write [S(O*O)] 
    it guesses [nat_scope], but when you write the cartesian
    product (tuple) type [bool*bool] it guesses [type_scope].
    Occasionally you have to help it out with percent-notation by
    writing [(x*y)%nat], and sometimes in Coq's feedback to you it
    will use [%nat] to indicate what scope a notation is in.

    Notation scopes also apply to numeral notation (3,4,5, etc.), so you
    may sometimes see [0%nat] which means [O], or [0%Z] which means the
    Integer zero.
*)

(** * [Fixpoint] and Structural Recursion (Advanced) *)

Fixpoint plus' (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus' n' m)
  end.

(** When Coq checks this definition, it notes that [plus'] is
    "decreasing on 1st argument."  What this means is that we are
    performing a _structural recursion_ over the argument [n] -- i.e.,
    that we make recursive calls only on strictly smaller values of
    [n].  This implies that all calls to [plus'] will eventually
    terminate.  Coq demands that some argument of _every_ [Fixpoint]
    definition is "decreasing".
    
    Esse requisito é uma característica fundamental do projeto do Coq: em
    particular, isso garante que toda função que pode ser definida
    no Coq irá funcionar com todas as entradas.  Entretanto, como o
    "analisador de decaimento" do Coq não é muito sofisticado, algumas vezes
    é necessário escrever funções de uma maneira não natural. *)

(** **** Exercise: 2 stars, optional (decreasing)  *)
(** To get a concrete sense of this, find a way to write a sensible
    [Fixpoint] definition (of a simple function on numbers, say) that
    _does_ terminate on all inputs, but that Coq will reject because
    of this restriction. *)

(* FILL IN HERE *)
(** [] *)

(** $Date: 2014-12-31 15:31:47 -0500 (Wed, 31 Dec 2014) $ *)


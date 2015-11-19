(** * Imp: Programas Imperativos Simples *)

(** [Claudia] In this chapter, we begin a new direction that will continue for
    the rest of the course.  Up to now most of our attention has been
    focused on various aspects of Coq itself, while from now on we'll
    mostly be using Coq to formalize other things.  (We'll continue to
    pause from time to time to introduce a few additional aspects of
    Coq.)

    [Dalay] Our first case study is a _simple imperative programming language_
    called Imp, embodying a tiny core fragment of conventional
    mainstream languages such as C and Java.  Here is a familiar
    mathematical function written in Imp.

     Z ::= X;;
     Y ::= 1;;
     WHILE not (Z = 0) DO
       Y ::= Y * Z;;
       Z ::= Z - 1
     END
*)

(** [Diego] This chapter looks at how to define the _syntax_ and _semantics_
    of Imp; the chapters that follow develop a theory of _program
    equivalence_ and introduce _Hoare Logic_, a widely used logic for
    reasoning about imperative programs. *)

(* ####################################################### *)
(** *** Sflib *)

(** [Francisco]A minor technical point: Instead of asking Coq to import our
    earlier definitions from chapter [Logic], we import a small library
    called [Sflib.v], containing just a few definitions and theorems
    from earlier chapters that we'll actually use in the rest of the
    course.  This change should be nearly invisible, since most of what's
    missing from Sflib has identical definitions in the Coq standard
    library.  The main reason for doing it is to tidy the global Coq
    environment so that, for example, it is easier to search for
    relevant theorems. *)

Require Export SfLib.

(* ####################################################### *)
(** * Expressões Aritméticas e Booleanas *)

(** Vamos apresentar Imp em três partes: primeiro, um núcleo de 
    linguagem de _expressões aritméticas e booleanas_, em seguida, 
    uma extensão dessas expressões com _variáveis_ e, finalmente, 
    uma linguagem de _comandos_ que inclui atribuição, condições, 
    sequenciamento e loops. *)

(* ####################################################### *)
(** ** Sintaxe *)

Module AExp.

(** Estas duas definições especificam a _sintaxe abstrata_ para expressões aritméticas e 
booleanas. *)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

(** [Claudia]In this chapter, we'll elide the translation from the
    concrete syntax that a programmer would actually write to these
    abstract syntax trees -- the process that, for example, would
    translate the string ["1+2*3"] to the AST [APlus (ANum
    1) (AMult (ANum 2) (ANum 3))].  The optional chapter [ImpParser]
    develops a simple implementation of a lexical analyzer and parser
    that can perform this translation.  You do _not_ need to
    understand that file to understand this one, but if you haven't
    taken a course where these techniques are covered (e.g., a
    compilers course) you may want to skim it. *)

(** *** *)
(** [Dalay]For comparison, here's a conventional BNF (Backus-Naur Form)
    grammar defining the same abstract syntax:
    a ::= nat
        | a + a
        | a - a
        | a * a

    b ::= true
        | false
        | a = a
        | a <= a
        | not b
        | b and b
*)

(** Comparado com a versão Coq acima...

       - [Diego]The BNF is more informal -- for example, it gives some
         suggestions about the surface syntax of expressions (like the
         fact that the addition operation is written [+] and is an
         infix symbol) while leaving other aspects of lexical analysis
         and parsing (like the relative precedence of [+], [-], and
         [*]) unspecified.  Some additional information -- and human
         intelligence -- would be required to turn this description
         into a formal definition (when implementing a compiler, for
         example).

         The Coq version consistently omits all this information and
         concentrates on the abstract syntax only.

       - [Francisco]On the other hand, the BNF version is lighter and
         easier to read.  Its informality makes it flexible, which is
         a huge advantage in situations like discussions at the
         blackboard, where conveying general ideas is more important
         than getting every detail nailed down precisely.

         De fato, existem dezenas de notações do tipo BNF, e as pessoas 
         alternam livremente entre elas, geralmente sem se importar em 
         dizer qual forma de BNF elas estão usando, simplesmente porque 
         não há necessidade: um entendimento informal improvisado é 
         tudo que é necessário. *)

(** É bom estar confortável com ambos os tipos de notações: os informais para a 
comunicação 
entre os seres humanos e os formais para a realização de implementações e provas. *)

(* ####################################################### *)
(** ** Avaliação *)

(** [Claudia]_Evaluating_ an arithmetic expression produces a number. *)

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2  => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

(** *** *)
(** [Dalay]Similarly, evaluating a boolean expression yields a boolean. *)

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval a1) (aeval a2)
  | BLe a1 a2   => ble_nat (aeval a1) (aeval a2)
  | BNot b1     => negb (beval b1)
  | BAnd b1 b2  => andb (beval b1) (beval b2)
  end.

(* ####################################################### *)
(** ** Otimização *)

(** [Diego]We haven't defined very much yet, but we can already get
    some mileage out of the definitions.  Suppose we define a function
    that takes an arithmetic expression and slightly simplifies it,
    changing every occurrence of [0+e] (i.e., [(APlus (ANum 0) e])
    into just [e]. *)

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | APlus (ANum 0) e2 =>
      optimize_0plus e2
  | APlus e1 e2 =>
      APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 =>
      AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 =>
      AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

(** [Francisco]To make sure our optimization is doing the right thing we
    can test it on some examples and see if the output looks OK. *)

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

(** Mas se nós quisermos ter certeza de que a otimização é 
    correta -- ou seja, que avaliar uma expressão otimizada 
    retorna o mesmo resultado que a original -- nós devemos provar 
    isso. *)

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  Case "ANum". reflexivity.
  Case "APlus". destruct a1.
    SCase "a1 = ANum n". destruct n.
      SSCase "n = 0".  simpl. apply IHa2.
      SSCase "n <> 0". simpl. rewrite IHa2. reflexivity.
    SCase "a1 = APlus a1_1 a1_2".
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    SCase "a1 = AMinus a1_1 a1_2".
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    SCase "a1 = AMult a1_1 a1_2".
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  Case "AMinus".
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  Case "AMult".
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.  Qed.

(* ####################################################### *)
(** * Automação em Coq *)

(** A repetição nesta última prova está começando a ser um pouco chata. Se a linguagem de 
expressões aritméticas ou a otimização sendo provada fossem significativamente mais 
complexas poderíamos começar a ter realmente um problema.

    [Claudia]So far, we've been doing all our proofs using just a small handful
    of Coq's tactics and completely ignoring its powerful facilities
    for constructing parts of proofs automatically.  This section
    introduces some of these facilities, and we will see more over the
    next several chapters.  Getting used to them will take some
    energy -- Coq's automation is a power tool -- but it will allow us
    to scale up our efforts to more complex definitions and more
    interesting properties without becoming overwhelmed by boring,
    repetitive, low-level details. *)

(* ####################################################### *)
(** ** Taticais *)

(** [Dalay]_Tacticals_ is Coq's term for tactics that take other tactics as
    arguments -- "higher-order tactics," if you will.  *)

(* ####################################################### *)
(** *** O Tatical [repeat] *)

(** [Diego]The [repeat] tactical takes another tactic and keeps applying
    this tactic until the tactic fails. Here is an example showing
    that [100] is even using repeat. *)

Theorem ev100 : ev 100.
Proof.
  repeat (apply ev_SS). (* aplique ev_SS 50 vezes,
                           até que [apply ev_SS] falhe *)
  apply ev_0.
Qed.
(* Print ev100. *)

(** [Francisco]The [repeat T] tactic never fails; if the tactic [T] doesn't apply
    to the original goal, then repeat still succeeds without changing
    the original goal (it repeats zero times). *)

Theorem ev100' : ev 100.
Proof.
  repeat (apply ev_0). (* não falha, aplica ev_0 zero vezes *)
  repeat (apply ev_SS). apply ev_0. (* podemos continuar a demonstração *)
Qed.

(** A tática [repeat T] não tem qualquer limite com relação ao número 
    de vezes que ela aplica [T]. Se [T] é uma tática que sempre é bem 
    sucedida, então repeat [T] será um loop infinito (por exemplo, 
    [repeat simpl] é um loop infinito já que [simpl] sempre funciona). 
    Enquanto a linguagem de expressão de Coq garante término, a 
    linguagem de tática de Coq não! *)

(* ####################################################### *)
(** *** O Tatical [try] *)

(** Se [T] é uma tática então [try T] é uma tática exatamente igual a [T] exceto que, se 
[T] falha então [try T] não realiza nenhuma ação na prova, sendo isto considerado um 
_sucesso_ na ação (no lugar de ser uma falha) *).

Theorem silly1 : forall ae, aeval ae = aeval ae.
Proof. try reflexivity. (* this just does [reflexivity] *) Qed.

Theorem silly2 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity. (* se fosse apenas [reflexivity] o comando teria falhado *)
  apply HP. (* ainda podemos finalizar a prova de outra forma *)
Qed.

(** [Claudia]Using [try] in a completely manual proof is a bit silly, but
    we'll see below that [try] is very useful for doing automated
    proofs in conjunction with the [;] tactical. *)

(* ####################################################### *)
(** *** O Tatical [;] (Forma Simples) *)

(** [Dalay]In its most commonly used form, the [;] tactical takes two tactics
    as argument: [T;T'] first performs the tactic [T] and then
    performs the tactic [T'] on _each subgoal_ generated by [T]. *)

(** [Diego]For example, consider the following trivial lemma: *)

Lemma foo : forall n, ble_nat 0 n = true.
Proof.
  intros.
  destruct n.
    (* Cria duas sub-metas, que são verificadas de forma idêntica...  *)
    Case "n=0". simpl. reflexivity.
    Case "n=Sn'". simpl. reflexivity.
Qed.

(** [Francisco]We can simplify this proof using the [;] tactical: *)

Lemma foo' : forall n, ble_nat 0 n = true.
Proof.
  intros.
  destruct n; (* [destruct] a meta atual *)
  simpl; (* depois [simpl] cada sub-meta resultante *)
  reflexivity. (* e aplique [reflexivity] a cada sub-meta resultante *)
Qed.

(** Usando [try] e [;] juntos, podemos nos livrar da repetição na prova, 
    o que estava nos incomodando até pouco tempo atrás. *)

Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* A maior parte dos casos seguem diretamente da hipótese de indução *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
  (* Os demais casos -- ANum e APlus -- são diferentes *)
  Case "ANum". reflexivity.
  Case "APlus".
    destruct a1;
      (* Novamente, a maioria dos casos segue direto da hipótese de indução *)
      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).
    (* O caso interessante, no qual [try...] é inefetivo,
       é quando [e1 = ANum n]. Neste cas, devemos desconstruir
       [n] (para ver se a otimização se aplica) e reescrever
       com a hipótese de indução. *)
    SCase "a1 = ANum n". destruct n;
      simpl; rewrite IHa2; reflexivity.   Qed.

(** Os especialistas em Coq muitas vezes usam o idioma "[...; try... ]" após uma tática 
como [induction] para cuidar de muitos casos semelhantes de uma vez. Naturalmente esta 
prática possui um análogo em provas informais. 

    [Claudia]Here is an informal proof of this theorem that matches the
    structure of the formal one:

    _Theorem_: For all arithmetic expressions [a],
       aeval (optimize_0plus a) = aeval a.
    _Proof_: By induction on [a].  The [AMinus] and [AMult] cases
    follow directly from the IH.  The remaining cases are as follows:

      [Dalay]- Suppose [a = ANum n] for some [n].  We must show
          aeval (optimize_0plus (ANum n)) = aeval (ANum n).
        This is immediate from the definition of [optimize_0plus].

      [Diego]- Suppose [a = APlus a1 a2] for some [a1] and [a2].  We
        must show
          aeval (optimize_0plus (APlus a1 a2))
        = aeval (APlus a1 a2).
        Consider the possible forms of [a1].  For most of them,
        [optimize_0plus] simply calls itself recursively for the
        subexpressions and rebuilds a new expression of the same form
        as [a1]; in these cases, the result follows directly from the
        IH.

        [Francisco]The interesting case is when [a1 = ANum n] for some [n].
        If [n = ANum 0], then
          optimize_0plus (APlus a1 a2) = optimize_0plus a2
        and the IH for [a2] is exactly what we need.  On the other
        hand, if [n = S n'] for some [n'], then again [optimize_0plus]
        simply calls itself recursively, and the result follows from
        the IH.  [] *)

(** Essa prova ainda pode ser melhorada: o primeiro caso (para 
    [a = ANum n]) é muito trivial -- ainda mais trivial do que os casos 
    que nós dissemos serem simplesmente seguidos da HI - ainda que 
    tenhamos escolhido escrevê-lo na íntegra. Seria melhor e mais 
    claro para eliminá-lo dizer, na parte superior, "A maioria dos 
    casos são ou imediatos ou diretos da HI. O único caso interessante 
    é o do [APlus]...". Nós podemos fazer a mesma melhoria em nossa 
    prova formal também. Aqui está como ficaria: *)

Theorem optimize_0plus_sound'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* A maioria dos casos seguem diretamente da HI *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    (* ... ou são imediatos pela definição *)
    try reflexivity.
  (* O caso interessante é quando a = APlus a1 a2. *)
  Case "APlus".
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    SCase "a1 = ANum n". destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.

(* ####################################################### *)
(** *** O Tatical [;] (Forma Geral) *)

(** A tática [;] possui uma forma mais geral que o simples [T;T'] visto acima, sendo útil 
em alguns casos. Se [T], [T1], ..., [Tn] são táticas então 
	T; [T1 | T2 | ... | Tn] 
	é uma tática que executa primeiramente [T] e então executa [T1] na primeira submeta 
	gerada por [T], executa [T2] na segunda submeta, etc.

   [Claudia]So [T;T'] is just special notation for the case when all of the
   [Ti]'s are the same tactic; i.e. [T;T'] is just a shorthand for:
      T; [T' | T' | ... | T']
*)

(* ####################################################### *)
(** ** Definindo Novas Notações de Tática *)

(** [Dalay]Coq also provides several ways of "programming" tactic scripts.

      [Diego]- The [Tactic Notation] idiom illustrated below gives a handy
        way to define "shorthand tactics" that bundle several tactics
        into a single command.

      [Francisco]- For more sophisticated programming, Coq offers a small
        built-in programming language called [Ltac] with primitives
        that can examine and modify the proof state.  The details are
        a bit too complicated to get into here (and it is generally
        agreed that [Ltac] is not the most beautiful part of Coq's
        design!), but they can be found in the reference manual, and
        there are many examples of [Ltac] definitions in the Coq
        standard library that you can use as examples.

      [Renan]- There is also an OCaml API, which can be used to build tactics
        that access Coq's internal structures at a lower level, but
        this is seldom worth the trouble for ordinary Coq users.

O [Tactic Notation] é o mecanismo mais fácil de lidar e oferece bastante poder para 
vários propósitos. Aqui está um exemplo.
*)

Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.

(** [Claudia]This defines a new tactical called [simpl_and_try] which
    takes one tactic [c] as an argument, and is defined to be
    equivalent to the tactic [simpl; try c].  For example, writing
    "[simpl_and_try reflexivity.]" in a proof would be the same as
    writing "[simpl; try reflexivity.]" *)

(** [Dalay]The next subsection gives a more sophisticated use of this
    feature... *)

(* ####################################################### *)
(** *** Tornando Mais Robustas as Análises por Casos *)

(** [Diego]Being able to deal with most of the cases of an [induction]
    or [destruct] all at the same time is very convenient, but it can
    also be a little confusing.  One problem that often comes up is
    that _maintaining_ proofs written in this style can be difficult.
    For example, suppose that, later, we extended the definition of
    [aexp] with another constructor that also required a special
    argument.  The above proof might break because Coq generated the
    subgoals for this constructor before the one for [APlus], so that,
    at the point when we start working on the [APlus] case, Coq is
    actually expecting the argument for a completely different
    constructor.  What we'd like is to get a sensible error message
    saying "I was expecting the [AFoo] case at this point, but the
    proof script is talking about [APlus]."  Here's a nice trick (due
    to Aaron Bohannon) that smoothly achieves this. *)

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult" ].

(** [Francisco]([Case_aux] implements the common functionality of [Case],
    [SCase], [SSCase], etc.  For example, [Case "foo"] is defined as
    [Case_aux Case "foo".) *)

(** [Renan]For example, if [a] is a variable of type [aexp], then doing
      aexp_cases (induction a) Case
    will perform an induction on [a] (the same as if we had just typed
    [induction a]) and _also_ add a [Case] tag to each subgoal
    generated by the [induction], labeling which constructor it comes
    from.  For example, here is yet another proof of
    [optimize_0plus_sound], using [aexp_cases]: *)

Theorem optimize_0plus_sound''': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  aexp_cases (induction a) Case;
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    try reflexivity.
    
    (* Neste momento já existe um nome de caso ["APlus"] no contexto. O [Case "APlus"] 
    aqui no texto da prova possui o efeito de verificação de sanidade: se a cadeia de 
    caracteres "Case" no contexto for qualquer coisa _diferente de_ ["APlus"] (por 
    exemplo, porque nós adicionamos uma cláusula na definição de [aexp] e esquecemos de 
    mudar a prova) receberemos um erro útil nos informando que esse agora é o caso 
    errado. *)
    
  Case "APlus".
    aexp_cases (destruct a1) SCase;
      try (simpl; simpl in IHa1;
           rewrite IHa1; rewrite IHa2; reflexivity).
    SCase "ANum". destruct n;
      simpl; rewrite IHa2; reflexivity.  Qed.

(** **** Exercício: nível 3 (optimize_0plus_b)  *)
(** [Claudia]Since the [optimize_0plus] tranformation doesn't change the value
    of [aexp]s, we should be able to apply it to all the [aexp]s that
    appear in a [bexp] without changing the [bexp]'s value.  Write a
    function which performs that transformation on [bexp]s, and prove
    it is sound.  Use the tacticals we've just seen to make the proof
    as elegant as possible. *)

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  (* PREENCHER *) admit.


Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 4, opcional (optimizer)  *)
(** [Dalay]_Design exercise_: The optimization implemented by our
    [optimize_0plus] function is only one of many imaginable
    optimizations on arithmetic and boolean expressions.  Write a more
    sophisticated optimizer and prove it correct.

(* PREENCHER *)
*)
(** [] *)

(* ####################################################### *)
(** ** A Tática [omega] *)

(** [Diego]The [omega] tactic implements a decision procedure for a subset of
    first-order logic called _Presburger arithmetic_.  It is based on
    the Omega algorithm invented in 1992 by William Pugh.

    [Francisco]If the goal is a universally quantified formula made out of

      [Renan]- numeric constants, addition ([+] and [S]), subtraction ([-]
        and [pred]), and multiplication by constants (this is what
        makes it Presburger arithmetic),

		- igualdade ([=] e [<>]) e desigualdade ([<=]), e

      [Claudia]- the logical connectives [/\], [\/], [~], and [->],

    [Dalay]then invoking [omega] will either solve the goal or tell you that
    it is actually false. *)

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. omega.
Qed.

(** [Diego]Leibniz wrote, "It is unworthy of excellent men to lose
    hours like slaves in the labor of calculation which could be
    relegated to anyone else if machines were used."  We recommend
    using the omega tactic whenever possible. *)

(* ####################################################### *)
(** ** Mais Algumas Táticas Convenientes *)

(** [Francisco]Finally, here are some miscellaneous tactics that you may find
    convenient.

     - [clear H]: Apaga a hipótese [H] do contexto.

     [Dalay]- [subst x]: Find an assumption [x = e] or [e = x] in the
       context, replace [x] with [e] throughout the context and
       current goal, and clear the assumption.

     [Diego]- [subst]: Substitute away _all_ assumptions of the form [x = e]
       or [e = x].

     [Francisco]- [rename... into...]: Change the name of a hypothesis in the
       proof context.  For example, if the context includes a variable
       named [x], then [rename x into y] will change all occurrences
       of [x] to [y].

     [Renan]- [assumption]: Try to find a hypothesis [H] in the context that
       exactly matches the goal; if one is found, behave just like
       [apply H].

	- [contradição]: Tente encontrar uma hipótese [H] no contexto atual que é logicamente 
	equivalente a [False]. Se uma for encontrada, solucione a meta.

     [Claudia]- [constructor]: Try to find a constructor [c] (from some
       [Inductive] definition in the current environment) that can be
       applied to solve the current goal.  If one is found, behave
       like [apply c]. *)

(** Veremos vários exemplos de aplicação destas táticas nas provas abaixo. *)

(* ####################################################### *)
(** * Avaliação enquanto Relação *)

(** [Dalay]We have presented [aeval] and [beval] as functions defined by
    [Fixpoints].  Another way to think about evaluation -- one that we
    will see is often more flexible -- is as a _relation_ between
    expressions and their values.  This leads naturally to [Inductive]
    definitions like the following one for arithmetic
    expressions... *)

Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum  : forall (n: nat),
      aevalR (ANum n) n
  | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus: forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult : forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

(** [Diego]As is often the case with relations, we'll find it
    convenient to define infix notation for [aevalR].  We'll write [e
    || n] to mean that arithmetic expression [e] evaluates to value
    [n].  (This notation is one place where the limitation to ASCII
    symbols becomes a little bothersome.  The standard notation for
    the evaluation relation is a double down-arrow.  We'll typeset it
    like this in the HTML version of the notes and use a double
    vertical bar as the closest approximation in [.v] files.)  *)

Notation "e '||' n" := (aevalR e n) : type_scope.

End aevalR_first_try.

(** [Francisco]In fact, Coq provides a way to use this notation in the definition
    of [aevalR] itself.  This avoids situations where we're working on
    a proof involving statements in the form [e || n] but we have to
    refer back to a definition written using the form [aevalR e n].

    [Renan]We do this by first "reserving" the notation, then giving the
    definition together with a declaration of what the notation
    means. *)

Reserved Notation "e '||' n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) || n
  | E_APlus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 || n1) -> (e2 || n2) -> (APlus e1 e2) || (n1 + n2)
  | E_AMinus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 || n1) -> (e2 || n2) -> (AMinus e1 e2) || (n1 - n2)
  | E_AMult :  forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 || n1) -> (e2 || n2) -> (AMult e1 e2) || (n1 * n2)

  where "e '||' n" := (aevalR e n) : type_scope.

Tactic Notation "aevalR_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_ANum" | Case_aux c "E_APlus"
  | Case_aux c "E_AMinus" | Case_aux c "E_AMult" ].

(* ####################################################### *)
(** ** Notação de Regra de Inferência *)

(** Nas discussões informais é conveniente escrever as regras para [aevalR] e relações 
semelhantes na forma de _regras de inferência_, uma forma gráfica mais legível, onde as 
premissas acima da linha justificam a conclusão abaixo da mesma (já vimos isso antes no 
capítulo Prop). *)

(** [Claudia]For example, the constructor [E_APlus]...
      | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
          aevalR e1 n1 ->
          aevalR e2 n2 ->
          aevalR (APlus e1 e2) (n1 + n2)
    ...would be written like this as an inference rule:
                               e1 || n1
                               e2 || n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 || n1+n2
*)

(** [Dalay]Formally, there is nothing very deep about inference rules:
    they are just implications.  You can read the rule name on the
    right as the name of the constructor and read each of the
    linebreaks between the premises above the line and the line itself
    as [->].  All the variables mentioned in the rule ([e1], [n1],
    etc.) are implicitly bound by universal quantifiers at the
    beginning. (Such variables are often called _metavariables_ to
    distinguish them from the variables of the language we are
    defining.  At the moment, our arithmetic expressions don't include
    variables, but we'll soon be adding them.)  The whole collection
    of rules is understood as being wrapped in an [Inductive]
    declaration (informally, this is either elided or else indicated
    by saying something like "Let [aevalR] be the smallest relation
    closed under the following rules..."). *)

(** [Diego]For example, [||] is the smallest relation closed under these
    rules:
                             -----------                               (E_ANum)
                             ANum n || n

                               e1 || n1
                               e2 || n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 || n1+n2

                               e1 || n1
                               e2 || n2
                        ---------------------                        (E_AMinus)
                        AMinus e1 e2 || n1-n2

                               e1 || n1
                               e2 || n2
                         --------------------                         (E_AMult)
                         AMult e1 e2 || n1*n2
*)



(* ####################################################### *)
(** ** Equivalência das Definições *)

(** [Francisco]It is straightforward to prove that the relational and functional
    definitions of evaluation agree on all possible arithmetic
    expressions... *)

Theorem aeval_iff_aevalR : forall a n,
  (a || n) <-> aeval a = n.
Proof.
 split.
 Case "->".
   intros H.
   aevalR_cases (induction H) SCase; simpl.
   SCase "E_ANum".
     reflexivity.
   SCase "E_APlus".
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   SCase "E_AMinus".
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   SCase "E_AMult".
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
 Case "<-".
   generalize dependent n.
   aexp_cases (induction a) SCase;
      simpl; intros; subst.
   SCase "ANum".
     apply E_ANum.
   SCase "APlus".
     apply E_APlus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   SCase "AMinus".
     apply E_AMinus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   SCase "AMult".
     apply E_AMult.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
Qed.

(** [Renan]Note: if you're reading the HTML file, you'll see an empty square box instead
of a proof for this theorem.  
You can click on this box to "unfold" the text to see the proof.
Click on the unfolded to text to "fold" it back up to a box. We'll be using
this style frequently from now on to help keep the HTML easier to read.
The full proofs always appear in the .v files. *)

(** Nós podemos fazer a prova de uma forma um pouco mais curta através do uso de mais 
táticas "de segunda ordem"... *)

Theorem aeval_iff_aevalR' : forall a n,
  (a || n) <-> aeval a = n.
Proof.
  (* REALIZADO EM SALA *)
  split.
  Case "->".
    intros H; induction H; subst; reflexivity.
  Case "<-".
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.

(** **** Exercício: nível 3(bevalR)  *)
(** [Claudia]Write a relation [bevalR] in the same style as
    [aevalR], and prove that it is equivalent to [beval].*)

(* 
Inductive bevalR:
(* PREENCHER *)
*)
(** [] *)
End AExp.

(* ####################################################### *)
(** ** Comparando Definições Computacionais e Relacionais *)

(** [Dalay]For the definitions of evaluation for arithmetic and boolean
    expressions, the choice of whether to use functional or relational
    definitions is mainly a matter of taste.  In general, Coq has
    somewhat better support for working with relations.  On the other
    hand, in some sense function definitions carry more information,
    because functions are necessarily deterministic and defined on all
    arguments; for a relation we have to show these properties
    explicitly if we need them. Functions also take advantage of Coq's
    computations mechanism.

    [Diego]However, there are circumstances where relational definitions of
    evaluation are preferable to functional ones.  *)

Module aevalR_division.

(** [Francisco]For example, suppose that we wanted to extend the arithmetic
    operations by considering also a division operation:*)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp
  | ADiv : aexp -> aexp -> aexp.   (* <--- new *)

(** [Renan]Extending the definition of [aeval] to handle this new operation
    would not be straightforward (what should we return as the result
    of [ADiv (ANum 5) (ANum 0)]?).  But extending [aevalR] is
    straightforward. *)

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) || n
  | E_APlus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (APlus a1 a2) || (n1 + n2)
  | E_AMinus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (AMinus a1 a2) || (n1 - n2)
  | E_AMult :  forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (AMult a1 a2) || (n1 * n2)
  | E_ADiv :  forall (a1 a2: aexp) (n1 n2 n3: nat),
      (a1 || n1) -> (a2 || n2) -> (mult n2 n3 = n1) -> (ADiv a1 a2) || n3

where "a '||' n" := (aevalR a n) : type_scope.

End aevalR_division.
Module aevalR_extended.

(** Suponha no lugar disso que queiramos extender as operações aritméticas através de um 
gerador de números não determinístico [any]:*)

Inductive aexp : Type :=
  | AAny  : aexp                   (* <--- NOVO *)
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

(** [Claudia]Again, extending [aeval] would be tricky (because evaluation is
    _not_ a deterministic function from expressions to numbers), but
    extending [aevalR] is no problem: *)

Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any : forall (n:nat),
      AAny || n                 (* <--- new *)
  | E_ANum : forall (n:nat),
      (ANum n) || n
  | E_APlus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (APlus a1 a2) || (n1 + n2)
  | E_AMinus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (AMinus a1 a2) || (n1 - n2)
  | E_AMult :  forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (AMult a1 a2) || (n1 * n2)

where "a '||' n" := (aevalR a n) : type_scope.

End aevalR_extended.

(** * Expressões com Variáveis *)

(** [Dalay]Let's turn our attention back to defining Imp.  The next thing we
    need to do is to enrich our arithmetic and boolean expressions
    with variables.  To keep things simple, we'll assume that all
    variables are global and that they only hold numbers. *)

(* ##################################################### *)
(** ** Identificadores *)

(** [Diego] To begin, we'll need to formalize _identifiers_ such as
    program variables.  We could use strings for this -- or, in a real compiler,
    fancier structures like pointers into a symbol table.  But for simplicity
    let's just use natural numbers as identifiers. *)

(** [Francisco](We hide this section in a module because these definitions are
    actually in [SfLib], but we want to repeat them here so that we
    can explain them.) *)

Module Id. 

(** [Renan]We define a new inductive datatype [Id] so that we won't confuse
    identifiers and numbers.  We use [sumbool] to define a computable
    equality operator on [Id]. *)

Inductive id : Type :=
  Id : nat -> id.

Theorem eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof.
   intros id1 id2.
   destruct id1 as [n1]. destruct id2 as [n2].
   destruct (eq_nat_dec n1 n2) as [Heq | Hneq].
   Case "n1 = n2".
     left. rewrite Heq. reflexivity.
   Case "n1 <> n2".
     right. intros contra. inversion contra. apply Hneq. apply H0.
Defined. 


(** Os seguintes lemas serão úteis para reescrever termos envolvendo [eq_id_dec]. *)

Lemma eq_id : forall (T:Type) x (p q:T), 
              (if eq_id_dec x x then p else q) = p. 
Proof.
  intros. 
  destruct (eq_id_dec x x). 
  Case "x = x". 
    reflexivity.
  Case "x <> x (impossible)". 
    apply ex_falso_quodlibet; apply n; reflexivity. Qed.

(** **** Exercício: nível 1, opcional (neq_id)  *)
Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> 
               (if eq_id_dec x y then p else q) = q. 
Proof.
  (* PREENCHER *) Admitted.
(** [] *)


End Id. 

(* ####################################################### *)
(** ** Estados *)

(** [Claudia]A _state_ represents the current values of _all_ the variables at
    some point in the execution of a program. *)

(** [Dalay]For simplicity (to avoid dealing with partial functions), we
    let the state be defined for _all_ variables, even though any
    given program is only going to mention a finite number of them. 
    The state captures all of the information stored in memory.  For Imp
    programs, because each variable stores only a natural number, we
    can represent the state as a mapping from identifiers to [nat].  
    For more complex programming languages, the state might have more 
    structure.  
*)

Definition state := id -> nat.

Definition empty_state : state :=
  fun _ => 0.

Definition update (st : state) (x : id) (n : nat) : state :=
  fun x' => if eq_id_dec x x' then n else st x'.

(** [Diego]For proofs involving states, we'll need several simple properties
    of [update]. *)

(** **** Exercício: nível 1 (update_eq)  *)
Theorem update_eq : forall n x st,
  (update st x n) x = n.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 1 (update_neq)  *)
Theorem update_neq : forall x2 x1 n st,
  x2 <> x1 ->                        
  (update st x2 n) x1 = (st x1).
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 1 (update_example)  *)
(** [Francisco]Before starting to play with tactics, make sure you understand
    exactly what the theorem is saying! *)

Theorem update_example : forall (n:nat),
  (update empty_state (Id 2) n) (Id 3) = 0.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 1 (update_shadow)  *)
Theorem update_shadow : forall n1 n2 x1 x2 (st : state),
   (update  (update st x2 n1) x2 n2) x1 = (update st x2 n2) x1.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 2 (update_same)  *)
Theorem update_same : forall n1 x1 x2 (st : state),
  st x1 = n1 ->
  (update st x1 n1) x2 = st x2.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 3 (update_permute)  *)
Theorem update_permute : forall n1 n2 x1 x2 x3 st,
  x2 <> x1 -> 
  (update (update st x2 n1) x1 n2) x3 = (update (update st x1 n2) x2 n1) x3.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(* ################################################### *)
(** ** Sintaxe  *)

(** [Renan]We can add variables to the arithmetic expressions we had before by
    simply adding one more constructor: *)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp                (* <----- NOVO *)
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "AId" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult" ].

(** Definir alguns nomes de variáveis como atalhos notacionais tornarão os exemplos mais 
fáceis de serem lidas: *)

Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

(** [Claudia](This convention for naming program variables ([X], [Y],
    [Z]) clashes a bit with our earlier use of uppercase letters for
    types.  Since we're not using polymorphism heavily in this part of
    the course, this overloading should not cause confusion.) *)

(** [Dalay]The definition of [bexp]s is the same as before (using the new
    [aexp]s): *)

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Tactic Notation "bexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BTrue" | Case_aux c "BFalse" | Case_aux c "BEq"
  | Case_aux c "BLe" | Case_aux c "BNot" | Case_aux c "BAnd" ].

(* ################################################### *)
(** ** Avaliação *)

(** [Diego]The arith and boolean evaluators can be extended to handle
    variables in the obvious way: *)

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                        (* <----- NOVO *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2   => ble_nat (aeval st a1) (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

Example aexp1 :
  aeval (update empty_state X 5)
        (APlus (ANum 3) (AMult (AId X) (ANum 2)))
  = 13.
Proof. reflexivity. Qed.

Example bexp1 :
  beval (update empty_state X 5)
        (BAnd BTrue (BNot (BLe (AId X) (ANum 4))))
  = true.
Proof. reflexivity. Qed.

(* ####################################################### *)
(** * Comandos *)

(** [Francisco]Now we are ready define the syntax and behavior of Imp
    _commands_ (often called _statements_). *)

(* ################################################### *)
(** ** Sintaxe *)

(** [Renan]Informally, commands [c] are described by the following BNF
    grammar:
     c ::= SKIP
         | x ::= a
         | c ;; c
         | WHILE b DO c END
         | IFB b THEN c ELSE c FI
]] 
*)

(** Por exemplo, aqui está a função fatorial em Imp.
     Z ::= X;;
     Y ::= 1;;
     WHILE not (Z = 0) DO
       Y ::= Y * Z;;
       Z ::= Z - 1
     END
     Quando este comando terminar, a variável [Y] irá conter o fatorial do valor inicial 
     de [X].
*)

(** [Claudia]Here is the formal definition of the syntax of commands: *)

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";;"
  | Case_aux c "IFB" | Case_aux c "WHILE" ].

(** [Dalay]As usual, we can use a few [Notation] declarations to make things
    more readable.  We need to be a bit careful to avoid conflicts
    with Coq's built-in notations, so we'll keep this light -- in
    particular, we won't introduce any notations for [aexps] and
    [bexps] to avoid confusion with the numerical and boolean
    operators we've already defined.  We use the keyword [IFB] for
    conditionals instead of [IF], for similar reasons. *)

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

(** [Diego]For example, here is the factorial function again, written as a
    formal definition to Coq: *)

Definition fact_in_coq : com :=
  Z ::= AId X;;
  Y ::= ANum 1;;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    Y ::= AMult (AId Y) (AId Z);;
    Z ::= AMinus (AId Z) (ANum 1)
  END.

(* ####################################################### *)
(** ** Exemplos *)

(** Atribuição: *)

Definition plus2 : com :=
  X ::= (APlus (AId X) (ANum 2)).

Definition XtimesYinZ : com :=
  Z ::= (AMult (AId X) (AId Y)).

Definition subtract_slowly_body : com :=
  Z ::= AMinus (AId Z) (ANum 1) ;;
  X ::= AMinus (AId X) (ANum 1).


(** *** Laços *)

Definition subtract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    subtract_slowly_body
  END.

Definition subtract_3_from_5_slowly : com :=
  X ::= ANum 3 ;;
  Z ::= ANum 5 ;;
  subtract_slowly.


(** *** Um laço infinito: *)

Definition loop : com :=
  WHILE BTrue DO
    SKIP
  END.

(* ################################################################ *)
(** * Avaliação *)

(** [Francisco]Next we need to define what it means to evaluate an Imp command.
    The fact that [WHILE] loops don't necessarily terminate makes defining
    an evaluation function tricky... *)

(* #################################### *)
(** ** Avaliação como uma Função (Tentativa Falha) *)

(** [Renan]Here's an attempt at defining an evaluation function for commands,
    omitting the [WHILE] case. *)

Fixpoint ceval_fun_no_while (st : state) (c : com) : state :=
  match c with
    | SKIP =>
        st
    | x ::= a1 =>
        update st x (aeval st a1)
    | c1 ;; c2 =>
        let st' := ceval_fun_no_while st c1 in
        ceval_fun_no_while st' c2
    | IFB b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_fun_no_while st c1
          else ceval_fun_no_while st c2
    | WHILE b DO c END =>
        st  (* bogus *)
  end.
  
(** Em uma linguagem de programação funcional como ML ou Haskell poderíamos escrever o 
caso [WHILE} da seguinte forma:
  <<
  Fixpoint ceval_fun (st : state) (c : com) : state :=
    match c with
      ...
      | WHILE b DO c END =>
          if (beval st b1)
            then ceval_fun st (c1; WHILE b DO c END)
            else st
    end.
>>
    [Claudia]Coq doesn't accept such a definition ("Error: Cannot guess
    decreasing argument of fix") because the function we want to
    define is not guaranteed to terminate. Indeed, it doesn't always
    terminate: for example, the full version of the [ceval_fun]
    function applied to the [loop] program above would never
    terminate. Since Coq is not just a functional programming
    language, but also a consistent logic, any potentially
    non-terminating function needs to be rejected. Here is
    an (invalid!) Coq program showing what would go wrong if Coq
    allowed non-terminating recursive functions:
<<
     Fixpoint loop_false (n : nat) : False := loop_false n.
>>
    [Dalay]That is, propositions like [False] would become provable
    (e.g. [loop_false 0] would be a proof of [False]), which
    would be a disaster for Coq's logical consistency.

    [Diego]Thus, because it doesn't terminate on all inputs, the full version
    of [ceval_fun] cannot be written in Coq -- at least not without
    additional tricks (see chapter [ImpCEvalFun] if curious). *)

(* #################################### *)
(** ** Avaliação como uma Relação *)

(** [Francisco]Here's a better way: we define [ceval] as a _relation_ rather
    than a _function_ -- i.e., we define it in [Prop] instead of [Type], as we
    did for [aevalR] above. *)

(** [Renan]This is an important change.  Besides freeing us from the awkward
    workarounds that would be needed to define evaluation as a
    function, it gives us a lot more flexibility in the definition.
    For example, if we added concurrency features to the language,
    we'd want the definition of evaluation to be non-deterministic --
    i.e., not only would it not be total, it would not even be a
    partial function! *)
    
(** Usaremos a notação [c / st || st'] para a nossa relação [ceval]: [c / st || st'] 
significa que o programa em execução [c] em um estado inicial [st] resulta em um estado 
final [st']. Isso pode ser pronunciado como "[c] leva o estado [st] para [st']".
*)

(** *** Semântica Operacional
                           ----------------                            (E_Skip)
                           SKIP / st || st

                           aeval st a1 = n
                   --------------------------------                     (E_Ass)
                   x := a1 / st || (update st x n)

                           c1 / st || st'
                          c2 / st' || st''
                         -------------------                            (E_Seq)
                         c1;;c2 / st || st''

                          beval st b1 = true
                           c1 / st || st'
                -------------------------------------                (E_IfTrue)
                IF b1 THEN c1 ELSE c2 FI / st || st'

                         beval st b1 = false
                           c2 / st || st'
                -------------------------------------               (E_IfFalse)
                IF b1 THEN c1 ELSE c2 FI / st || st'

                         beval st b1 = false
                    ------------------------------                 (E_WhileEnd)
                    WHILE b DO c END / st || st

                          beval st b1 = true
                           c / st || st'
                  WHILE b DO c END / st' || st''
                  ---------------------------------               (E_WhileLoop)
                    WHILE b DO c END / st || st''
*)

(** [Claudia]Here is the formal definition.  (Make sure you understand
    how it corresponds to the inference rules.) *)

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st || st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      (x ::= a1) / st || (update st x n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  || st' ->
      c2 / st' || st'' ->
      (c1 ;; c2) / st || st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      c1 / st || st' ->
      (IFB b THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      c2 / st || st' ->
      (IFB b THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall b st c,
      beval st b = false ->
      (WHILE b DO c END) / st || st
  | E_WhileLoop : forall st st' st'' b c,
      beval st b = true ->
      c / st || st' ->
      (WHILE b DO c END) / st' || st'' ->
      (WHILE b DO c END) / st || st''

  where "c1 '/' st '||' st'" := (ceval c1 st st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop" ].

(** *** *)
(** [Dalay]The cost of defining evaluation as a relation instead of a
    function is that we now need to construct _proofs_ that some
    program evaluates to some result state, rather than just letting
    Coq's computation mechanism do it for us. *)

Example ceval_example1:
    (X ::= ANum 2;;
     IFB BLe (AId X) (ANum 1)
       THEN Y ::= ANum 3
       ELSE Z ::= ANum 4
     FI)
   / empty_state
   || (update (update empty_state X 2) Z 4).
Proof.
  (* Devemos fornecer o estado intermediário *)
  apply E_Seq with (update empty_state X 2).
  Case "assignment command".
    apply E_Ass. reflexivity.
  Case "if command".
    apply E_IfFalse.
      reflexivity.
      apply E_Ass. reflexivity.  Qed.

(** **** Exercício: nível 2 (ceval_example2)  *)
Example ceval_example2:
    (X ::= ANum 0;; Y ::= ANum 1;; Z ::= ANum 2) / empty_state ||
    (update (update (update empty_state X 0) Y 1) Z 2).
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 3, avançado (pup_to_n)  *)
(** [Diego]Write an Imp program that sums the numbers from [1] to
   [X] (inclusive: [1 + 2 + ... + X]) in the variable [Y].
   Prove that this program executes as intended for X = 2
   (this latter part is trickier than you might expect). *)

Definition pup_to_n : com :=
  (* PREENCHER *) admit.

Theorem pup_to_2_ceval :
  pup_to_n / (update empty_state X 2) ||
    update (update (update (update (update (update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) X 0.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)


(* ####################################################### *)
(** ** Determinismo em Avaliação *)

(** [Francisco]Changing from a computational to a relational definition of
    evaluation is a good move because it allows us to escape from the
    artificial requirement (imposed by Coq's restrictions on
    [Fixpoint] definitions) that evaluation should be a total
    function.  But it also raises a question: Is the second definition
    of evaluation actually a partial function?  That is, is it
    possible that, beginning from the same state [st], we could
    evaluate some command [c] in different ways to reach two different
    output states [st'] and [st'']?

    [Renan]In fact, this cannot happen: [ceval] is a partial function.
    Here's the proof: *)

Theorem ceval_deterministic: forall c st st1 st2,
     c / st || st1  ->
     c / st || st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  ceval_cases (induction E1) Case;
           intros st2 E2; inversion E2; subst.
  Case "E_Skip". reflexivity.
  Case "E_Ass". reflexivity.
  Case "E_Seq".
    assert (st' = st'0) as EQ1.
      SCase "Proof of assertion". apply IHE1_1; assumption.
    subst st'0.
    apply IHE1_2. assumption.
  Case "E_IfTrue".
    SCase "b1 evaluates to true".
      apply IHE1. assumption.
    SCase "b1 evaluates to false (contradiction)".
      rewrite H in H5. inversion H5.
  Case "E_IfFalse".
    SCase "b1 evaluates to true (contradiction)".
      rewrite H in H5. inversion H5.
    SCase "b1 evaluates to false".
      apply IHE1. assumption.
  Case "E_WhileEnd".
    SCase "b1 evaluates to false".
      reflexivity.
    SCase "b1 evaluates to true (contradiction)".
      rewrite H in H2. inversion H2.
  Case "E_WhileLoop".
    SCase "b1 evaluates to false (contradiction)".
      rewrite H in H4. inversion H4.
    SCase "b1 evaluates to true".
      assert (st' = st'0) as EQ1.
        SSCase "Proof of assertion". apply IHE1_1; assumption.
      subst st'0.
      apply IHE1_2. assumption.  Qed.


(* ####################################################### *)
(** * Raciocinar Sobre Programas Imp *)

(** Nós iremos nos aprofundar bastante em técnicas sistemáticas para raciocínio sobre os 
programas Imp nos capítulos seguintes, mas já podemos trabalhar um pouco com as 
definições básicas. *)

(* Essa seção explora alguns exemplos. *)

Theorem plus2_spec : forall st n st',
  st X = n ->
  plus2 / st || st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.
  (* Inverter Heval essencialmente obriga Coq a expandir um
     passo na computação do ceval - neste caso revelando que
     st' deve ser st estendido com o novo valor de X, pois
     plus2 é uma atribuição *)
  inversion Heval. subst. clear Heval. simpl.
  apply update_eq.  Qed.

(** **** Exercício: nível 3 (XtimesYinZ_spec)  *)
(** [Claudia]State and prove a specification of [XtimesYinZ]. *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercício: nível 3 (loop_never_stops)  *)
Theorem loop_never_stops : forall st st',
  ~(loop / st || st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef eqn:Heqloopdef.
    (* Proceder por indução na derivação assumida, mostrando que
     [loopdef] termina.  A maior parte dos casos entram imediatamente
     em contradição (e podem então ser resolvidos em um passo com
     [inversion]). *)
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 3 (no_whilesR)  *)
(** [Dalay]Consider the definition of the [no_whiles] property below: *)

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP       => true
  | _ ::= _    => true
  | c1 ;; c2  => andb (no_whiles c1) (no_whiles c2)
  | IFB _ THEN ct ELSE cf FI => andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END  => false
  end.

(** [Diego]This property yields [true] just on programs that
    have no while loops.  Using [Inductive], write a property
    [no_whilesR] such that [no_whilesR c] is provable exactly when [c]
    is a program with no while loops.  Then prove its equivalence
    with [no_whiles]. *)

Inductive no_whilesR: com -> Prop :=
 (* PREENCHER *)
  .

Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 4 (no_whiles_terminating)  *)
(** [Francisco]Imp programs that don't involve while loops always terminate.
    State and prove a theorem [no_whiles_terminating] that says this. *)
(** (Use either [no_whiles] or [no_whilesR], as you prefer.) *)

(* PREENCHER *)
(** [] *)

(* ####################################################### *)
(** * Exercícios Extras *)

(** **** Exercício: nível 3 (stack_compiler)  *)
(** [Renan]HP Calculators, programming languages like Forth and Postscript,
    and abstract machines like the Java Virtual Machine all evaluate
    arithmetic expressions using a stack. For instance, the expression
<<
   (2*3)+(3*(4-2))
>>
   would be entered as
<<
   2 3 * 3 4 2 - * +
>>
   and evaluated like this:
<<
  []            |    2 3 * 3 4 2 - * +
  [2]           |    3 * 3 4 2 - * +
  [3, 2]        |    * 3 4 2 - * +
  [6]           |    3 4 2 - * +
  [3, 6]        |    4 2 - * +
  [4, 3, 6]     |    2 - * +
  [2, 4, 3, 6]  |    - * +
  [2, 3, 6]     |    * +
  [6, 6]        |    +
  [12]          |
>>

A tarefa deste exercício é escrever um compilador que traduza [aexp]s em instruções de 
uma máquina de pilha.

O conjunto de instruções para a nossa linguagem de pilha consistirá das seguintes 
instruções:
	 - [SPush n]: Insere o número [n] na pilha.
	 - [SLoad x]: Carrega o identificador [x] a partir da loja e o insere na pilha
	 - [SPlus]: Retira dois números do topo da pilha, realiza uma soma com eles, e 
	 adiciona o resultado na pilha
	 - [SMinus]: Semelhante ao anterior, mas realização uma subtração.
	 - [SMult]: Semelhante ao anterior, mas realiza uma multiplicação. *)
	 
Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SLoad : id -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr.

(** [Claudia]Write a function to evaluate programs in the stack language. It
    takes as input a state, a stack represented as a list of
    numbers (top stack item is the head of the list), and a program
    represented as a list of instructions, and returns the stack after
    executing the program. Test your function on the examples below.

    [Dalay]Note that the specification leaves unspecified what to do when
    encountering an [SPlus], [SMinus], or [SMult] instruction if the
    stack contains less than two elements.  In a sense, it is
    immaterial what we do, since our compiler will never emit such a
    malformed program. *)

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat :=
(* PREENCHER *) admit.


Example s_execute1 :
     s_execute empty_state []
       [SPush 5; SPush 3; SPush 1; SMinus]
   = [2; 5].
(* PREENCHER *) Admitted.

Example s_execute2 :
     s_execute (update empty_state X 3) [3;4]
       [SPush 4; SLoad X; SMult; SPlus]
   = [15; 4].
(* PREENCHER *) Admitted.

(** [Diego]Next, write a function which compiles an [aexp] into a stack
    machine program. The effect of running the program should be the
    same as pushing the value of the expression on the stack. *)

Fixpoint s_compile (e : aexp) : list sinstr :=
(* PREENCHER *) admit.

(** [Francisco]After you've defined [s_compile], prove the following to test
    that it works. *)

Example s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercício: nível 3, avançado (stack_compiler_correct)  *)
(** [Renan]The task of this exercise is to prove the correctness of the
    compiler implemented in the previous exercise.  Remember that
    the specification left unspecified what to do when encountering an
    [SPlus], [SMinus], or [SMult] instruction if the stack contains
    less than two elements.  (In order to make your correctness proof
    easier you may find it useful to go back and change your
    implementation!)

	Prove o seguinte teorema, cuja afirmação é de que a função [compile] se comporta 
	corretamente. Você terá que começar definindo um lema mais geral para obter uma 
	hipótese indutiva utilizável; o teorema principal então será um simples corolário 
	desse lema. *)  

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  (* PREENCHA AQUI *) Admitted.
(** [] *)

(** **** Exercício: nível 5, avançado (break_imp)  *)
Module BreakImp.

(** [Claudia]Imperative languages such as C or Java often have a [break] or
    similar statement for interrupting the execution of loops. In this
    exercise we will consider how to add [break] to Imp.

    [Dalay]First, we need to enrich the language of commands with an
    additional case. *)

Inductive com : Type :=
  | CSkip : com
  | CBreak : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "BREAK" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" ].

Notation "'SKIP'" :=
  CSkip.
Notation "'BREAK'" :=
  CBreak.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

(** [Diego]Next, we need to define the behavior of [BREAK].  Informally,
    whenever [BREAK] is executed in a sequence of commands, it stops
    the execution of that sequence and signals that the innermost
    enclosing loop (if any) should terminate. If there aren't any
    enclosing loops, then the whole program simply terminates. The
    final state should be the same as the one in which the [BREAK]
    statement was executed.

    [Francisco]One important point is what to do when there are multiple loops
    enclosing a given [BREAK]. In those cases, [BREAK] should only
    terminate the _innermost_ loop where it occurs. Thus, after
    executing the following piece of code...
   X ::= 0;;
   Y ::= 1;;
   WHILE 0 <> Y DO
     WHILE TRUE DO
       BREAK
     END;;
     X ::= 1;;
     Y ::= Y - 1
   END
    ... the value of [X] should be [1], and not [0].

    [Renan]One way of expressing this behavior is to add another parameter to
    the evaluation relation that specifies whether evaluation of a
    command executes a [BREAK] statement: *)

Inductive status : Type :=
  | SContinue : status
  | SBreak : status.

Reserved Notation "c1 '/' st '||' s '/' st'"
                  (at level 40, st, s at level 39).

(** Intuitivamente, [c / st || s / st'] significa que, se [c] é um estado inicial [st], 
então ele termina no estado [st'] e dá a ordem para que ou os laços circundantes (ou todo 
o programa) finalizem imediatamente ([s = SBreak]) ou a execução continue normalmente ([s 
= SContinue]).

    [Claudia]The definition of the "[c / st || s / st']" relation is very
    similar to the one we gave above for the regular evaluation
    relation ([c / st || s / st']) -- we just need to handle the
    termination signals appropriately:

    [Dalay]- If the command is [SKIP], then the state doesn't change, and
      execution of any enclosing loop can continue normally.

    [Diego]- If the command is [BREAK], the state stays unchanged, but we
      signal a [SBreak].

    [Francisco]- If the command is an assignment, then we update the binding for
      that variable in the state accordingly and signal that execution
      can continue normally.

    [Renan]- If the command is of the form [IF b THEN c1 ELSE c2 FI], then
      the state is updated as in the original semantics of Imp, except
      that we also propagate the signal from the execution of
      whichever branch was taken.

	- Se o comando é uma sequência [c1 ; c2], executamos primeiramente [c1]. Se isso gera 
	um [SBreak] nós pulamos a execução de [c2] e propagamos o sinal [SBreak] para o 
	contexto envolvente. O estado resultante deve ser o mesmo que o obtido pela execução 
	de [c1] sozinho. Caso contrário nós executamos [c2] no estado obtido após a execução 
	de [c1], propagando o sinal gerado a partir disso.

    [Claudia]- Finally, for a loop of the form [WHILE b DO c END], the
      semantics is almost the same as before. The only difference is
      that, when [b] evaluates to true, we execute [c] and check the
      signal that it raises. If that signal is [SContinue], then the
      execution proceeds as in the original semantics. Otherwise, we
      stop the execution of the loop, and the resulting state is the
      same as the one resulting from the execution of the current
      iteration. In either case, since [BREAK] only terminates the
      innermost loop, [WHILE] signals [SContinue]. *)

(** [Dalay]Based on the above description, complete the definition of the
    [ceval] relation. *)

Inductive ceval : com -> state -> status -> state -> Prop :=
  | E_Skip : forall st,
      CSkip / st || SContinue / st
  (* PREENCHER *)

  where "c1 '/' st '||' s '/' st'" := (ceval c1 st s st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip"
  (* PREENCHER *)
  ].

(** [Diego]Now the following properties of your definition of [ceval]: *)

Theorem break_ignore : forall c st st' s,
     (BREAK;; c) / st || s / st' ->
     st = st'.
Proof.
  (* PREENCHER *) Admitted.

Theorem while_continue : forall b c st st' s,
  (WHILE b DO c END) / st || s / st' ->
  s = SContinue.
Proof.
  (* PREENCHER *) Admitted.

Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  c / st || SBreak / st' ->
  (WHILE b DO c END) / st || SContinue / st'.
Proof.
  (* PREENCHER *) Admitted.

(** **** Exercício: nível 3, avançado, opcional (while_break_true)  *)
Theorem while_break_true : forall b c st st',
  (WHILE b DO c END) / st || SContinue / st' ->
  beval st' b = true ->
  exists st'', c / st'' || SBreak / st'.
Proof.
(* PREENCHER *) Admitted.

(** **** Exercício: nívle 4, avançado, opcional (ceval_deterministic)  *)
Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
     c / st || s1 / st1  ->
     c / st || s2 / st2 ->
     st1 = st2 /\ s1 = s2.
Proof.
  (* PREENCHER *) Admitted.

End BreakImp.
(** [] *)

(** **** Exercício: nível 3, opcional (short_circuit)  *)

(** [Diego]Most modern programming languages use a "short-circuit" evaluation
    rule for boolean [and]: to evaluate [BAnd b1 b2], first evaluate
    [b1].  If it evaluates to [false], then the entire [BAnd]
    expression evaluates to [false] immediately, without evaluating
    [b2].  Otherwise, [b2] is evaluated to determine the result of the
    [BAnd] expression.

    [Francisco]Write an alternate version of [beval] that performs short-circuit
    evaluation of [BAnd] in this manner, and prove that it is
    equivalent to [beval]. *)

(* PREENCHER *)
(** [] *)

(** **** Exercício: nível 4, opcional (add_for_loop)  *)

(** [Renan]Add C-style [for] loops to the language of commands, update the
    [ceval] definition to define the semantics of [for] loops, and add
    cases for [for] loops as needed so that all the proofs in this file
    are accepted by Coq.
    
	Um laço [for] deve ser parametrizado por (a) uma sentença executada inicialmente, (b) 
	um teste que é executado em cada iteração do laço a fim de determinar se o mesmo deve 
	continuar, (c) uma sentença executada no fim de cada iteração de laço e (d) uma 
	declaração que constitui o corpo desse laço. (Você não precisa se preocupar em criar 
	uma Notação concreta para os laços [for], mas sinta-se livre para fazê-lo também 
	se preferir.) *)

(* PREENCHER *)
(** [] *)



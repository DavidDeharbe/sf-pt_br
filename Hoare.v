(** * Hoare: Lógica de Hoare, Parte I *)

Require Export Imp.

(** [Dalay]In the past couple of chapters, we've begun applying the
    mathematical tools developed in the first part of the course to
    studying the theory of a small programming language, Imp.

    - Nós definimos um tipo de _árvores de sintaxe abstrata_ para o Imp,
      juntamente com uma _relação de avaliação_ (uma função parcial sobre os
      estados) que especifíca a _semântica operacional_ de programas.

      A linguagem que definimos, embora pequena, capitura algumas das
      características chaves desenvolvidas em linguagens como C, C++ e Java, incluindo
      a noção fundamental de estado mutável e alguns controles de estruturas comuns.

    - Nós provamos uma série de _propriedades metateóricas_ -- "meta" 
      no sentido de que eles são propriedades da linguagem como um todo, 
      ao invés de propriedades de programas específicos da linguagem. 
      Isso incluiu:

        - [Vitor]determinism of evaluation

        - [Vitor]equivalence of some different ways of writing down the
          definitions (e.g. functional and relational definitions of
          arithmetic expression evaluation)

        - [Vitor]guaranteed termination of certain classes of programs

        - [Vitor]correctness (in the sense of preserving meaning) of a number
          of useful program transformations

        - [Vitor]behavioral equivalence of programs (in the [Equiv] chapter). 

    [Dalay]If we stopped here, we would already have something useful: a set
    of tools for defining and discussing programming languages and
    language features that are mathematically precise, flexible, and
    easy to work with, applied to a set of key properties.  All of
    these properties are things that language designers, compiler
    writers, and users might care about knowing.  Indeed, many of them
    are so fundamental to our understanding of the programming
    languages we deal with that we might not consciously recognize
    them as "theorems."  But properties that seem intuitively obvious
    can sometimes be quite subtle (in some cases, even subtly wrong!).

    Nós vamos retornar para o tema de propriedades metateóricas de linguagens
    inteiras mais tarde no curso, quando discutimos _tipos_ e _solidez
    de escrita_.  Nesse capítulo, entretanto, nós vamos tornar para um 
    diferente conjunto de problemas.

    Nosso objetivo é para ver como executar alguns exemplos simples de
    _verificação de programa_ -- ex., usando a definição precisa de Imp para provar
    formalmente que programas particulares satisfazem especificações particulares do
    comportamento deles. Nós iremos desenvolver um sistema de raciocínio chamado
    _Lógica Floyd-Hoare_ -- frequentemente encurtado para apenas _Lógica de Hoare_
    -- em que cada construção sintática de Imp é equipado com um único, "regra de prova"
    genérica que pode ser usado para razão composicionalmente sobre a corretude de programas
    envolvendo esta construção.

    A Lógica de Hoare se origina na década de 1960, e continua a ser 
    objeto de intensa pesquisa até os dias atuais. Situa-se no centro 
    de uma infinidade de ferramentas que estão sendo usadas no meio 
    acadêmico e na indústria para especificar e verificar sistemas 
    de software reais. *)


  
(* ####################################################### *)
(** * Lógica de Hoare *)

(** [Vitor]Hoare Logic combines two beautiful ideas: a natural way of
    writing down _specifications_ of programs, and a _compositional
    proof technique_ for proving that programs are correct with
    respect to such specifications -- where by "compositional" we mean
    that the structure of proofs directly mirrors the structure of the
    programs that they are about. *)

(* ####################################################### *)
(** ** Asserções *)

(** [Dalay]To talk about specifications of programs, the first thing we
    need is a way of making _assertions_ about properties that hold at
    particular points during a program's execution -- i.e., claims
    about the current state of the memory when program execution
    reaches that point.  Formally, an assertion is just a family of
    propositions indexed by a [state]. *)

Definition Assertion := state -> Prop.

(** **** Exercício: nível 1, opcional (assertions)  *)
Module ExAssertions.

(** Paraphrase the following assertions in English. *)

Definition as1 : Assertion := fun st => st X = 3.
Definition as2 : Assertion := fun st => st X <= st Y.
Definition as3 : Assertion :=
  fun st => st X = 3 \/ st X <= st Y.
Definition as4 : Assertion :=
  fun st => st Z * st Z <= st X /\
            ~ (((S (st Z)) * (S (st Z))) <= st X).
Definition as5 : Assertion := fun st => True.
Definition as6 : Assertion := fun st => False.

(* PREENCHER *)

End ExAssertions.
(** [] *)

(* ####################################################### *)
(** ** Notação para Asserções *)

(** Esse meio de escrever asserções pode ser um pouco pesado,
    por duas razões: (1) cada asserção que nós alguma vez escrevermos vai
    ser com [fun st => ]; e (2) o estado [st] é o único que nunca usamos para 
    procurar variáveis (nunca precisaremos falar sobre dois estados de memória
    diferentes ao mesmo tempo).  Para discurssão informal de exemplos, vamos 
    adotar algumas convenções simplificadoras: deixaremos de lado o [fun st =>]
    inicial, e iremos escrever somente [X] para significar [st X].  Então, ao 
    em vez de escrever *)
(** 
      fun st => (st Z) * (st Z) <= m /\
                ~ ((S (st Z)) * (S (st Z)) <= m)
    we'll write just
         Z * Z <= m /\ ~((S Z) * (S Z) <= m).
*)

(** Dado duas asserções [P] e [Q], nós dizemos que [P] _implica_ [Q],
    escrito [P ->> Q] (em ASCII, [P -][>][> Q]), se, sempre que [P] satisfaz algum
    estado [st], [Q] também satisfaz. *)

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" :=
  (assert_implies P Q) (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

(** Também teremos a oportunidade de usar a variante de implicação "sse" 
    entre as afirmações: *)

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

(* ####################################################### *)
(** ** Triplas de Hoare *)

(** [Vitor]Next, we need a way of making formal claims about the
    behavior of commands. *)

(** [Dalay]Since the behavior of a command is to transform one state to
    another, it is natural to express claims about commands in terms
    of assertions that are true before and after the command executes:

      - "Se o comando [c] é iniciado em um estado satisfazendo a asserção
        [P], e se [c] eventualmente termina em algum estado final,
        então esse estado final satisfará a asserção [Q]."

    Tal afirmação é chamado um _Tripla de Hoare_. A propriedade [P] é
    chamado de _pré-condição_ de [c], enquanto [Q] é _pós-condição_. Formalmente: *)

Definition hoare_triple
           (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st',
       c / st || st'  ->
       P st  ->
       Q st'.

(** Já que estaremos trabalhando muito com triplas de Hoare, é útil ter 
    uma notação compacta:
       {{P}} c {{Q}}.
*)
(** [Vitor](The traditional notation is [{P} c {Q}], but single braces
    are already used for other things in Coq.)  *)

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

(** [Dalay](The [hoare_spec_scope] annotation here tells Coq that this
    notation is not global but is intended to be used in particular
    contexts.  The [Open Scope] tells Coq that this file is one such
    context.) *)

(** **** Exercício: nível 1, opcional (triples)  *)
(** Paraphrase the following Hoare triples in English.
   1) {{True}} c {{X = 5}}

   2) {{X = m}} c {{X = m + 5)}}

   3) {{X <= Y}} c {{Y <= X}}

   4) {{True}} c {{False}}

   5) {{X = m}} 
      c
      {{Y = real_fact m}}.

   6) {{True}} 
      c 
      {{(Z * Z) <= m /\ ~ (((S Z) * (S Z)) <= m)}}

 *)


(** [] *)

(** **** Exercise: 1 star, optional (valid_triples)  *)
(** Qual das triplas de Hoare a seguir são _válidas_ -- isto é, a
    relação alegada entre [P], [c], e [Q] é verdadeira?

   1) {{True}} X ::= 5 {{X = 5}}

   2) {{X = 2}} X ::= X + 1 {{X = 3}}

   3) {{True}} X ::= 5; Y ::= 0 {{X = 5}}

   4) {{X = 2 /\ X = 3}} X ::= 5 {{X = 0}}

   5) {{True}} SKIP {{False}}

   6) {{False}} SKIP {{True}}

   7) {{True}} WHILE True DO SKIP END {{False}}

   8) {{X = 0}}
      WHILE X == 0 DO X ::= X + 1 END
      {{X = 1}}

   9) {{X = 1}}
      WHILE X <> 0 DO X ::= X + 1 END
      {{X = 100}}

*)
(* PREENCHER *)
(** [] *)

(** (Note que nós estamos usando notações matemáticas informal para 
    expressões dentro de comandos, para legibilidade, em vez de códigos formal deles
    [aexp] e [bexp]. Nós iremos continuar fazendo ao longo do capítulo.) *)

(** Para nos aquecer para o que está vindo, aqui estão dois fatos 
    simples sobre triplas de Hoare. *)

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  apply H.  Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~(P st)) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  unfold not in H. apply H in HP.
  inversion HP.  Qed.

(* ####################################################### *) 
(** ** Regras de Demonstração *)

(** [Vitor]The goal of Hoare logic is to provide a _compositional_
    method for proving the validity of Hoare triples.  That is, the
    structure of a program's correctness proof should mirror the
    structure of the program itself.  To this end, in the sections
    below, we'll introduce one rule for reasoning about each of the
    different syntactic forms of commands in Imp -- one for
    assignment, one for sequencing, one for conditionals, etc. -- plus
    a couple of "structural" rules that are useful for gluing things
    together. We will prove programs correct using these proof rules,
    without ever unfolding the definition of [hoare_triple]. *)

(* ####################################################### *) 
(** *** Atribuição *)

(** [Dalay]The rule for assignment is the most fundamental of the Hoare logic
    proof rules.  Here's how it works.

    Consider this (valid) Hoare triple:
       {{ Y = 1 }}  X ::= Y  {{ X = 1 }}
    In English: if we start out in a state where the value of [Y]
    is [1] and we assign [Y] to [X], then we'll finish in a
    state where [X] is [1].  That is, the property of being equal
    to [1] gets transferred from [Y] to [X].

    Similarmente, em
       {{ Y + Z = 1 }}  X ::= Y + Z  {{ X = 1 }}
    a mesma propriedade (sendo igual a um) é transferida para
    [X] a partir da expressão [Y + Z] no lado direito da
    atribuição.

    Mais geralmente, se [a] é _qualquer_ expressão aritmética, então
       {{ a = 1 }}  X ::= a {{ X = 1 }}
    é uma tripla de Hoare válida.

    Isso pode ser tornado ainda mais geral. Para concluir que uma 
    propriedade _arbitrária_ [Q] é satisfeita depois de [X :: = a], 
    temos que assumir que [Q] é satisfeita antes de [X :: = a], porém 
    _com todas as ocorrências de_ [X] substituídas por [a] em [Q].
    Isso leva à regra de Hoare para atribuição
      {{ Q [X |-> a] }} X ::= a {{ Q }}
    onde "[Q [X |-> a]]" é pronunciado "[Q] onde [a] é substituído
    por [X]".

    [Vitor]For example, these are valid applications of the assignment
    rule:
      {{ (X <= 5) [X |-> X + 1]
         i.e., X + 1 <= 5 }}  
      X ::= X + 1  
      {{ X <= 5 }}

      {{ (X = 3) [X |-> 3]
         i.e., 3 = 3}}  
      X ::= 3  
      {{ X = 3 }}

      {{ (0 <= X /\ X <= 5) [X |-> 3]
         i.e., (0 <= 3 /\ 3 <= 5)}}  
      X ::= 3  
      {{ 0 <= X /\ X <= 5 }}
*)

(** [Dalay]To formalize the rule, we must first formalize the idea of
    "substituting an expression for an Imp variable in an assertion."
    That is, given a proposition [P], a variable [X], and an
    arithmetic expression [a], we want to derive another proposition
    [P'] that is just the same as [P] except that, wherever [P]
    mentions [X], [P'] should instead mention [a].  
   
    Desde que [P] é uma proposição arbitrária do Coq, nós não podemos 
    diretamente "editar" seu texto.  Em vez disso, nós podemos alcançar o 
    efeito que queremos calculando [P] em um estado atualizado: *)

Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (update st X (aeval st a)).

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).

(** Isto é, [P [X |-> a]] é uma asserção [P'] que é apenas como [P]
    exceto que, sempre que [P] procura a variável [X] no estado atual, [P']
    ao invés disso usa o valor da expressão [a].

    Para ver como isso funciona, vamos calcular o que acontece com um par 
    de exemplos. Primeiro, suponha que [P'] é [(X <= 5) [X |-> 3]] -- ou 
    seja, mais formalmente, [P'] é a expressão Coq
    fun st => 
      (fun st' => st' X <= 5) 
      (update st X (aeval st (ANum 3))),
    que é simplificada para 
    fun st => 
      (fun st' => st' X <= 5) 
      (update st X 3)
    e é simplificada mais ainda para
    fun st => 
      ((update st X 3) X) <= 5)
    e por uma simplificação maior para 
    fun st => 
      (3 <= 5).
    Isto é, [P'] é a asserção de que [3] é inferior ou igual a [5] 
    (como esperado).

    [Vitor]For a more interesting example, suppose [P'] is [(X <= 5) [X |->
    X+1]].  Formally, [P'] is the Coq expression
    fun st => 
      (fun st' => st' X <= 5) 
      (update st X (aeval st (APlus (AId X) (ANum 1)))),
    which simplifies to 
    fun st => 
      (((update st X (aeval st (APlus (AId X) (ANum 1))))) X) <= 5
    and further simplifies to
    fun st => 
      (aeval st (APlus (AId X) (ANum 1))) <= 5.
    That is, [P'] is the assertion that [X+1] is at most [5].

*)

(** [Dalay]Now we can give the precise proof rule for assignment: 
      ------------------------------ (hoare_asgn)
      {{Q [X |-> a]}} X ::= a {{Q}}
*)

(** Nós podemos provar formalmente que essa regra é de fato válida. *)

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X ::= a) {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption.  Qed.

(** Aqui está uma primeira prova formal usando esta regra. *)

Example assn_sub_example :
  {{(fun st => st X = 3) [X |-> ANum 3]}}
  (X ::= (ANum 3))
  {{fun st => st X = 3}}.
Proof.
  apply hoare_asgn.  Qed.

(** **** Exercício: nível 2 (hoare_asgn_examples)  *)
(** Translate these informal Hoare triples...
    1) {{ (X <= 5) [X |-> X + 1] }}
       X ::= X + 1
       {{ X <= 5 }}

    2) {{ (0 <= X /\ X <= 5) [X |-> 3] }}
       X ::= 3
       {{ 0 <= X /\ X <= 5 }}
   ...into formal statements [assn_sub_ex1, assn_sub_ex2] 
   and use [hoare_asgn] to prove them. *)

(* PREENCHER *)
(** [] *)

(** **** Exercício: nível 2 (hoare_asgn_wrong)  *)
(** A regra de atribuição parece ser de trás para frente para quase todos 
    que a veem pela primeira vez. Se ela ainda parece ser de trás para 
    frente para você, pode ser útil pensar um pouco sobre regras 
    alternativas "de frente para trás". Aqui está uma aparentemente 
    natural:
      ------------------------------ (hoare_asgn_wrong)
      {{ True }} X ::= a {{ X = a }}
    Dê um contraexemplo mostrando que esta regra é incorreta 
    (informalmente). Dica: a regra quantifica universalmente 
    sobre a expressão aritmética [a], e seu contraexemplo 
    precisa apresentar um [a] para o qual a regra não funciona. *)

(* PREENCHER *)
(** [] *)

(** **** Exercício: nível 3, avançado (hoare_asgn_fwd)  *)
(** [Vitor]However, using an auxiliary variable [m] to remember the original
    value of [X] we can define a Hoare rule for assignment that does,
    intuitively, "work forwards" rather than backwards.
  ------------------------------------------ (hoare_asgn_fwd)
  {{fun st => P st /\ st X = m}}
    X ::= a
  {{fun st => P st' /\ st X = aeval st' a }}
  (where st' = update st X m)
    [Dalay]Note that we use the original value of [X] to reconstruct the
    state [st'] before the assignment took place. Prove that this rule
    is correct (the first hypothesis is the functional extensionality
    axiom, which you will need at some point). Also note that this
    rule is more complicated than [hoare_asgn].
*)

Theorem hoare_asgn_fwd :
  (forall {X Y: Type} {f g : X -> Y},
     (forall (x: X), f x = g x) ->  f = g) ->
  forall m a P,
  {{fun st => P st /\ st X = m}}
    X ::= a
  {{fun st => P (update st X m) /\ st X = aeval (update st X m) a }}.
Proof.
  intros functional_extensionality m a P.
  (* PREENCHER *) Admitted.
(** [] *)


(** **** Exercise: 2 stars, advanced (hoare_asgn_fwd_exists)  *)
(** Outra maneira de definir uma regra avançada para atribuições é
    quantificar existencialmente sobre o valor anterior da variável
    atribuida.

  ------------------------------------------ (hoare_asgn_fwd_exists)
  {{fun st => P st}}
    X ::= a
  {{fun st => exists m, P (update st X m) /\
                 st X = aeval (update st X m) a }}
*)
(* Esta regra foi proposta por Nick Giannarakis e Zoe Paraskevopoulou. *)

Theorem hoare_asgn_fwd_exists :
  (forall {X Y: Type} {f g : X -> Y},
     (forall (x: X), f x = g x) ->  f = g) ->
  forall a P,
  {{fun st => P st}}
    X ::= a
  {{fun st => exists m, P (update st X m) /\
                st X = aeval (update st X m) a }}.
Proof.
  intros functional_extensionality a P.
  (* PREENCHER *) Admitted.
(** [] *)

(* ####################################################### *) 
(** *** Consequência *)

(** Às vezes, as pré-condições e pós-condições que recebemos das regras 
    de Hoare não serão exatamente aquelas que nós queremos na situação 
    particular que temos em mãos -- elas podem ser logicamente 
    equivalentes, mas ter uma forma sintática diferente que seja 
    incapaz de unificar com a meta que estamos tentando provar, ou 
    elas realmente podem ser logicamente mais fracas 
    (para pré-condições) ou mais fortes (para pós-condições) do que 
    a que nós precisamos.

    [Vitor]For instance, while
      {{(X = 3) [X |-> 3]}} X ::= 3 {{X = 3}},
    follows directly from the assignment rule, 
      {{True}} X ::= 3 {{X = 3}}.
    does not.  This triple is valid, but it is not an instance of
    [hoare_asgn] because [True] and [(X = 3) [X |-> 3]] are not
    syntactically equal assertions.  However, they are logically
    equivalent, so if one triple is valid, then the other must
    certainly be as well.  We might capture this observation with the
    following rule:
                {{P'}} c {{Q}}
                  P <<->> P'
         -----------------------------   (hoare_consequence_pre_equiv)
                {{P}} c {{Q}}
    [Dalay]Taking this line of thought a bit further, we can see that
    strengthening the precondition or weakening the postcondition of a
    valid triple always produces another valid triple. This
    observation is captured by two _Rules of Consequence_.
                {{P'}} c {{Q}}
                   P ->> P'
         -----------------------------   (hoare_consequence_pre)
                {{P}} c {{Q}}

                {{P}} c {{Q'}}
                  Q' ->> Q 
         -----------------------------    (hoare_consequence_post)
                {{P}} c {{Q}}
*)

(** Seguem as versões formais: *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st'). 
  assumption. apply Himp. assumption. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st st' Hc HP. 
  apply Himp.
  apply (Hhoare st st'). 
  assumption. assumption. Qed.

(** [Diego]For example, we might use the first consequence rule like this:
                {{ True }} ->>
                {{ 1 = 1 }} 
    X ::= 1
                {{ X = 1 }}
    Or, formally... 
*)

Example hoare_asgn_example1 :
  {{fun st => True}} (X ::= (ANum 1)) {{fun st => st X = 1}}.
Proof.
  apply hoare_consequence_pre
    with (P' := (fun st => st X = 1) [X |-> ANum 1]).
  apply hoare_asgn.
  intros st H. unfold assn_sub, update. simpl. reflexivity.
Qed.

(** Finalmente, por conveniente em algumas provas, nós podemos declarar uma 
    regra "combinada" de consequência que nos permite varias ambas as pré-condições e
    as pós-condições.
                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
*)

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  apply hoare_consequence_pre with (P' := P').
  apply hoare_consequence_post with (Q' := Q').
  assumption. assumption. assumption.  Qed.

(* ####################################################### *)
(** *** Digressão: a tática [eapply] *)

(** Este é um bom momento para introduzir um outro recurso conveniente 
    de Coq. Tivemos que escrever "[with (P' := ...)]" explicitamente 
    nas provas de [hoare_asgn_example1] e [hoare_consequence] acima, 
    para nos certificarmos de que todas as metavariáveis nas 
    premissas da regra [hoare_consequence_pre] receberiam valores 
    específicos. (Uma vez que [P'] não aparece na conclusão de 
    [hoare_consequence_pre], o processo de unificar a conclusão 
    com a meta atual não restringe [P'] a uma asserção específica.

    [Vitor]This is a little annoying, both because the assertion is a bit
    long and also because for [hoare_asgn_example1] the very next
    thing we are going to do -- applying the [hoare_asgn] rule -- will
    tell us exactly what it should be!  We can use [eapply] instead of
    [apply] to tell Coq, essentially, "Be patient: The missing part is
    going to be filled in soon." *)

Example hoare_asgn_example1' :
  {{fun st => True}} 
  (X ::= (ANum 1)) 
  {{fun st => st X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  intros st H.  reflexivity.  Qed.

(** [Dalay]In general, [eapply H] tactic works just like [apply H] except
    that, instead of failing if unifying the goal with the conclusion
    of [H] does not determine how to instantiate all of the variables
    appearing in the premises of [H], [eapply H] will replace these
    variables with so-called _existential variables_ (written [?nnn])
    as placeholders for expressions that will be determined (by
    further unification) later in the proof. *)

(** [Diego]In order for [Qed] to succeed, all existential variables need to
    be determined by the end of the proof. Otherwise Coq
    will (rightly) refuse to accept the proof. Remember that the Coq
    tactics build proof objects, and proof objects containing
    existential variables are not complete. *)

Lemma silly1 : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (forall x y : nat, P x y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. eapply HQ. apply HP.

(**  Coq dar um alerta depois de [apply HP]:
     Sem mais submetas mas variáveis existencial não-instanciados.
     Existential 1 =
     ?171 : [P : nat -> nat -> Prop
             Q : nat -> Prop
             HP : forall x y : nat, P x y
             HQ : forall x y : nat, P x y -> Q x |- nat] 
  
     (dependent evars: ?171 open,)

     Você pode usar Grab Existential Variables.
   Tentar terminar a prova com [Qed] da um erro:
<<
    Erro: Tentativa de salvar uma prova com variáveis existenciais ainda não instanciado.
>> *)

Abort.

(** Uma restrição adicional é que as variáveis existenciais não podem ser 
    instanciadas com termos contendo variáveis (ordinárias) que não 
    existiam no momento em que a variável existencial foi criada. *)

Lemma silly2 :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. eapply HQ. destruct HP as [y HP'].
(** [Vitor]Doing [apply HP'] above fails with the following error:
     Error: Impossible to unify "?175" with "y".
    In this case there is an easy fix:
    doing [destruct HP] _before_ doing [eapply HQ].
*)

Abort.

Lemma silly2_fixed :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP'].
  eapply HQ. apply HP'.
Qed.

(** [Dalay]In the last step we did [apply HP'] which unifies the existential
    variable in the goal with the variable [y]. The [assumption]
    tactic doesn't work in this case, since it cannot handle
    existential variables. However, Coq also provides an [eassumption]
    tactic that solves the goal if one of the premises matches the
    goal up to instantiations of existential variables. We can use
    it instead of [apply HP']. *)

Lemma silly2_eassumption : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP']. eapply HQ. eassumption.
Qed.

    

(** **** Exercício: nível 2 (hoare_asgn_examples_2)  *)
(** [Diego]Translate these informal Hoare triples...
       {{ X + 1 <= 5 }}  X ::= X + 1  {{ X <= 5 }}
       {{ 0 <= 3 /\ 3 <= 5 }}  X ::= 3  {{ 0 <= X /\ X <= 5 }}
   ...into formal statements [assn_sub_ex1', assn_sub_ex2'] and 
   use [hoare_asgn] and [hoare_consequence_pre] to prove them. *)

(* PREENCHER *)
(** [] *)

(* ####################################################### *)
(** *** Skip *)

(** Uma vez que [SKIP] não muda o estado, ele preserva qualquer
    propriedade P:
      --------------------  (hoare_skip)
      {{ P }} SKIP {{ P }}
*)

Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  assumption.  Qed.

(* ####################################################### *) 
(** *** Sequenciamento *)

(** De maneira mais interessante, se o comando [c1] leva qualquer 
    estado onde [P] é satisfeita a um estado onde [Q] é satisfeita, 
    e se [c2] leva qualquer estado onde [Q] é satisfeita a um onde 
    [R] é satisfeita, então fazendo [c1] seguido de [c2] levará 
    qualquer estado onde [P] é satisfeita a um onde [R] é 
    satisfeita:
        {{ P }} c1 {{ Q }} 
        {{ Q }} c2 {{ R }}
       ---------------------  (hoare_seq)
       {{ P }} c1;;c2 {{ R }}
*)

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); assumption. Qed.

(** [Vitor]Note that, in the formal rule [hoare_seq], the premises are
    given in "backwards" order ([c2] before [c1]).  This matches the
    natural flow of information in many of the situations where we'll
    use the rule: the natural way to construct a Hoare-logic proof is
    to begin at the end of the program (with the final postcondition)
    and push postconditions backwards through commands until we reach
    the beginning. *)

(** [Dalay]Informally, a nice way of recording a proof using the sequencing
    rule is as a "decorated program" where the intermediate assertion
    [Q] is written between [c1] and [c2]:
      {{ a = n }}
    X ::= a;;
      {{ X = n }}      <---- decoration for Q
    SKIP
      {{ X = n }}
*)

Example hoare_asgn_example3 : forall a n,
  {{fun st => aeval st a = n}} 
  (X ::= a;; SKIP) 
  {{fun st => st X = n}}.
Proof.
  intros a n. eapply hoare_seq.
  Case "right part of seq".
    apply hoare_skip.
  Case "left part of seq".
    eapply hoare_consequence_pre. apply hoare_asgn. 
    intros st H. subst. reflexivity. Qed.

(** [Diego]You will most often use [hoare_seq] and
    [hoare_consequence_pre] in conjunction with the [eapply] tactic,
    as done above. *)

(** **** Exercício: nível 2 (hoare_asgn_example4)  *)
(** Traduza este "programa decorado" para uma prova formal:
                   {{ True }} ->>
                   {{ 1 = 1 }}
    X ::= 1;;
                   {{ X = 1 }} ->>
                   {{ X = 1 /\ 2 = 2 }}
    Y ::= 2
                   {{ X = 1 /\ Y = 2 }}
*)

Example hoare_asgn_example4 :
  {{fun st => True}} (X ::= (ANum 1);; Y ::= (ANum 2)) 
  {{fun st => st X = 1 /\ st Y = 2}}.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 3 (swap_exercise)  *)
(** Escrever um programa Imp [c] que troca os valores de [X] e [Y] 
    e mostrar (em Coq) que ele satisfaz a seguinte 
    especificação:
      {{X <= Y}} c {{Y <= X}}
*)

Definition swap_program : com :=
  (* PREENCHER *) admit.

Theorem swap_exercise :
  {{fun st => st X <= st Y}} 
  swap_program
  {{fun st => st Y <= st X}}.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 3 (hoarestate1)  *)
(** [Vitor]Explain why the following proposition can't be proven:
      forall (a : aexp) (n : nat),
         {{fun st => aeval st a = n}}
         (X ::= (ANum 3);; Y ::= a)
         {{fun st => st Y = n}}.
*)

(* PREENCHER *)
(** [] *)

(* ####################################################### *) 
(** *** Condicionais *)

(** [Dalay]What sort of rule do we want for reasoning about conditional
    commands?  Certainly, if the same assertion [Q] holds after
    executing either branch, then it holds after the whole
    conditional.  So we might be tempted to write:
              {{P}} c1 {{Q}}
              {{P}} c2 {{Q}}
      --------------------------------
      {{P}} IFB b THEN c1 ELSE c2 {{Q}}
   [Diego]However, this is rather weak. For example, using this rule,
   we cannot show that:
     {{ True }} 
     IFB X == 0
     THEN Y ::= 2
     ELSE Y ::= X + 1 
     FI
     {{ X <= Y }}
   since the rule tells us nothing about the state in which the
   assignments take place in the "then" and "else" branches. *)
   
(** Mas nós podemos realmente dizer algo mais preciso. No ramo
    "then", nós sabemos que a expressão booleana [b] avalia para [verdadeiro],
    e no ramo "else", nós sabemos que ele avalia para o [falso].
    Fazendo esta informação disponívelna premissa da regra nos da mais informações
    para trabalhar com ele quando racioncinamos sobre o comportamento de [c1] e [c2]
    (ex., as razões do por que que eles estabelecem a pós-condição [Q]).*)
(**
              {{P /\  b}} c1 {{Q}}
              {{P /\ ~b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} IFB b THEN c1 ELSE c2 FI {{Q}} 
*)

(** Para interpretar essa regra formalmente, precisamos trabalhar um 
    pouco. A rigor, a asserção que nós escrevemos, [P /\ b], é a 
    conjunção de uma asserção com uma expressão booleana -- ou seja, 
    ela não faz checagem de tipo.  Para corrigir isso, precisamos de 
    uma maneira de formalmente "erguer" qualquer bexp [b] para 
    uma asserção. Vamos escrever [bassn b] para a asserção "a 
    expressão booleana [b] é avaliada para [true] (no estado dado)." *)

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

(** Alguns fatos úteis acerca de [bassn] são: *)

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption.  Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.  Qed.

(** [Vitor]Now we can formalize the Hoare proof rule for conditionals
    and prove it correct. *)

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
  {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst. 
  Case "b is true".
    apply (HTrue st st'). 
      assumption. 
      split. assumption. 
             apply bexp_eval_true. assumption.
  Case "b is false".
    apply (HFalse st st'). 
      assumption. 
      split. assumption.
             apply bexp_eval_false. assumption. Qed.


(* ####################################################### *) 

(** * Lógica de Hoare: até agora *)

(** 
[Dalay]Idea: create a _domain specific logic_ for reasoning about properties of Imp programs.

- This hides the low-level details of the semantics of the program
- Leads to a compositional reasoning process


[Diego]The basic structure is given by _Hoare triples_ of the form:
  {{P}} c {{Q}}
]] 

- [P] and [Q] are predicates about the state of the Imp program
- "If command [c] is started in a state satisfying assertion
        [P], and if [c] eventually terminates in some final state,
        then this final state will satisfy the assertion [Q]."

*)


(** ** Regras da lógica de Hoare (parcial) *)

(**
             ------------------------------ (hoare_asgn)
             {{Q [X |-> a]}} X::=a {{Q}}

             --------------------  (hoare_skip)
             {{ P }} SKIP {{ P }}

               {{ P }} c1 {{ Q }} 
               {{ Q }} c2 {{ R }}
              ---------------------  (hoare_seq)
              {{ P }} c1;;c2 {{ R }}

              {{P /\  b}} c1 {{Q}}
              {{P /\ ~b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} IFB b THEN c1 ELSE c2 FI {{Q}} 


                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
*)


(** *** Exemplo *)
(** Aqui esta uma prova formal que o programa que nós
    usamos para motivar as regras satisfaz a especificação que nós demos. *)

Example if_example : 
    {{fun st => True}} 
  IFB (BEq (AId X) (ANum 0)) 
    THEN (Y ::= (ANum 2)) 
    ELSE (Y ::= APlus (AId X) (ANum 1)) 
  FI
    {{fun st => st X <= st Y}}.
Proof.
  (* WORKED IN CLASS *)
  apply hoare_if.
  Case "Then".
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold bassn, assn_sub, update, assert_implies.
    simpl. intros st [_ H].
    apply beq_nat_true in H.
    rewrite H. omega.
  Case "Else".
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold assn_sub, update, assert_implies.
    simpl; intros st _. omega.
Qed.

(** **** Exercício: nível 2 (if_minus_plus)  *)
(** Provar a seguinte tripla de Hoare usando [hoare_if]: *)

Theorem if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}. 
Proof.
  (* PREENCHER *) Admitted.

(* ####################################################### *)
(** *** Exercício: Condicionais de ramificação única *)

(** **** Exercício: nível 4 (if1_hoare)  *)

(** [Vitor]In this exercise we consider extending Imp with "one-sided
    conditionals" of the form [IF1 b THEN c FI]. Here [b] is a
    boolean expression, and [c] is a command. If [b] evaluates to
    [true], then command [c] is evaluated. If [b] evaluates to
    [false], then [IF1 b THEN c FI] does nothing.

    [Dalay]We recommend that you do this exercise before the ones that
    follow, as it should help solidify your understanding of the
    material. *)


(** [Diego]The first step is to extend the syntax of commands and introduce
    the usual notations.  (We've done this for you.  We use a separate
    module to prevent polluting the global name space.) *)

Module If1.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CIf1 : bexp -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" | Case_aux c "CIF1" ].

Notation "'SKIP'" := 
  CSkip.
Notation "c1 ;; c2" := 
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" := 
  (CAss X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" := 
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" := 
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'IF1' b 'THEN' c 'FI'" := 
  (CIf1 b c) (at level 80, right associativity).

(** Em seguida, precisamos estender a relação de avaliação para acomodar 
    os ramos de [IF1].  Isso é para você fazer... Que regra(s) precisam 
    ser adicionadas a [Ceval] para avaliar condicionais unilaterais? *)

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st : state, SKIP / st || st
  | E_Ass : forall (st : state) (a1 : aexp) (n : nat) (X : id),
            aeval st a1 = n -> (X ::= a1) / st || update st X n
  | E_Seq : forall (c1 c2 : com) (st st' st'' : state),
            c1 / st || st' -> c2 / st' || st'' -> (c1 ;; c2) / st || st''
  | E_IfTrue : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
               beval st b1 = true ->
               c1 / st || st' -> (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
                beval st b1 = false ->
                c2 / st || st' -> (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall (b1 : bexp) (st : state) (c1 : com),
                 beval st b1 = false -> (WHILE b1 DO c1 END) / st || st
  | E_WhileLoop : forall (st st' st'' : state) (b1 : bexp) (c1 : com),
                  beval st b1 = true ->
                  c1 / st || st' ->
                  (WHILE b1 DO c1 END) / st' || st'' ->
                  (WHILE b1 DO c1 END) / st || st''
(* PREENCHER *)

  where "c1 '/' st '||' st'" := (ceval c1 st st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop"
  (* PREENCHER *)
  ].

(** [Vitor]Now we repeat (verbatim) the definition and notation of Hoare triples. *)

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', 
       c / st || st'  ->
       P st  ->
       Q st'.

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q) 
                                  (at level 90, c at next level) 
                                  : hoare_spec_scope.

(** [Dalay]Finally, we (i.e., you) need to state and prove a theorem,
    [hoare_if1], that expresses an appropriate Hoare logic proof rule
    for one-sided conditionals. Try to come up with a rule that is
    both sound and as precise as possible. *)

(* PREENCHER *)

(** [Diego]For full credit, prove formally [hoare_if1_good] that your rule is 
    precise enough to show the following valid Hoare triple:
  {{ X + Y = Z }}
  IF1 Y <> 0 THEN
    X ::= X + Y
  FI
  {{ X = Z }}
*)

(** Dica: Sua prova desta tripla pode precisar usar outra 
    regra de prova também. Por nós estarmos trabalhando em um módulo separado,
    você irá precisar compiar aqui as regras que você achar necessário. *)


Lemma hoare_if1_good :
  {{ fun st => st X + st Y = st Z }}
  IF1 BNot (BEq (AId Y) (ANum 0)) THEN
    X ::= APlus (AId X) (AId Y)
  FI
  {{ fun st => st X = st Z }}.
Proof. (* PREENCHER *) Admitted.

End If1.
(** [] *)

(* ####################################################### *)
(** *** Laços *)

(** Finalmente, precisamos de uma regra para o raciocínio sobre laços while. *)

(** Suponha que nós temos um laço 
      WHILE b DO c END
    e nós queremos encontrar uma pré-condição [P] e uma pós-condição
    [Q] tal que
      {{P}} WHILE b DO c END {{Q}} 
    é uma tripla válida. *)

(** *** *)

(** [Dalay]First of all, let's think about the case where [b] is false at the
    beginning -- i.e., let's assume that the loop body never executes
    at all.  In this case, the loop behaves like [SKIP], so we might
    be tempted to write: *)

(**
      {{P}} WHILE b DO c END {{P}}.
*)

(** 
    [Diego]But, as we remarked above for the conditional, we know a
    little more at the end -- not just [P], but also the fact
    that [b] is false in the current state.  So we can enrich the
    postcondition a little:
*)
(** 
      {{P}} WHILE b DO c END {{P /\ ~b}}
*)

(** 
    E sobre o caso onde o corpo do laço _does_ é executado?
    Para garantir que [P] satisfaz quando o laço finalmente sai, nós certamente
    precisamos ter certeza que o comando [c] garante que [P] satisfaz a qualquer
    momento que [c] termina.
    Além disse, desde que [P] satisfaça no começo da primeira execução de [c],
    e uma vez que cada execução de [c] reestabelece [P] quando ele termina, nós
    sempre assumimos que [P] satisfaz o inicio de [c]. Isso nos leva para a seguinte
    regra:
*)
(** 
                   {{P}} c {{P}}
        -----------------------------------  
        {{P}} WHILE b DO c END {{P /\ ~b}}
*)
(** 
    Isso é quase a regra que queremos, mas novamente ela pode ser 
    melhorada um pouco: no começo do corpo do laço, sabemos não 
    apenas que [P] é satisfeita, mas também que a guarda [b] é 
    verdadeira no estado atual.  Isso nos dá um pouco mais de 
    informações para usar no raciocínio sobre [c] (mostrando 
    que estabelece o invariante no momento em que termina).  
    Isso nos dá a versão final da regra:
*)
(**
               {{P /\ b}} c {{P}}
        -----------------------------------  (hoare_while)
        {{P}} WHILE b DO c END {{P /\ ~b}}
    A proposição [P] é chamada o _invariante_ do laço.
*)

Lemma hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  (* Como nós vimos anteriormente, nós precisamos raciocinar por
     indução com [He] pois, no caso de repetir o laço, as hipóteses 
     associadas tratam do laço completo ao invés de somente [c]. *)
  remember (WHILE b DO c END) as wcom eqn:Heqwcom.
  ceval_cases (induction He) Case;
    try (inversion Heqwcom); subst; clear Heqwcom.
  Case "E_WhileEnd".
    split. assumption. apply bexp_eval_false. assumption.
  Case "E_WhileLoop".
    apply IHHe2. reflexivity.
    apply (Hhoare st st'). assumption.
      split. assumption. apply bexp_eval_true. assumption.
Qed.

(**
    [Vitor]One subtlety in the terminology is that calling some assertion [P]
    a "loop invariant" doesn't just mean that it is preserved by the
    body of the loop in question (i.e., [{{P}} c {{P}}], where [c] is
    the loop body), but rather that [P] _together with the fact that
    the loop's guard is true_ is a sufficient precondition for [c] to
    ensure [P] as a postcondition.

    [Dalay]This is a slightly (but significantly) weaker requirement.  For
    example, if [P] is the assertion [X = 0], then [P] _is_ an
    invariant of the loop
    WHILE X = 2 DO X := 1 END
    although it is clearly _not_ preserved by the body of the
    loop.
*)





Example while_example :
    {{fun st => st X <= 3}}
  WHILE (BLe (AId X) (ANum 2))
  DO X ::= APlus (AId X) (ANum 1) END
    {{fun st => st X = 3}}.
Proof.
  eapply hoare_consequence_post. 
  apply hoare_while. 
  eapply hoare_consequence_pre. 
  apply hoare_asgn. 
  unfold bassn, assn_sub, assert_implies, update. simpl.
    intros st [H1 H2]. apply ble_nat_true in H2. omega.
  unfold bassn, assert_implies. intros st [Hle Hb]. 
    simpl in Hb. destruct (ble_nat (st X) 2) eqn : Heqle. 
    apply ex_falso_quodlibet. apply Hb; reflexivity.  
    apply ble_nat_false in Heqle. omega. 
Qed.






(** *** *)
(** [Diego]We can use the while rule to prove the following Hoare triple,
    which may seem surprising at first... *)

Theorem always_loop_hoare : forall P Q,
  {{P}} WHILE BTrue DO SKIP END {{Q}}.
Proof.
  (* WORKED IN CLASS *)
  intros P Q.
  apply hoare_consequence_pre with (P' := fun st : state => True).
  eapply hoare_consequence_post.
  apply hoare_while.
  Case "Loop body preserves invariant".
    apply hoare_post_true. intros st. apply I. 
  Case "Loop invariant and negated guard imply postcondition".
    simpl. intros st [Hinv Hguard].
    apply ex_falso_quodlibet. apply Hguard. reflexivity.
  Case "Precondition implies invariant".
    intros st H. constructor.  Qed.

(** Claro, esse resultado não é surpresa se nós lembrarmos que
    a definição de [hoare_triple] asserta que a pós-condição deve satisfazer
    _apenas_ quando o comando terminar. Se o comando não terminar, nós podemos
    provar qualquer coisa que nós quisermos sobre a pós-condição. *)

(** Regras de Hoare que só falam sobre comandos que são encerrados 
    são muitas vezes ditos descreverem a lógica de correção 
    "parcial". É possível também fornecer regras de Hoare para correção 
    "total", que se aproveita do fato de que os comandos terminam. 
    No entanto, neste curso vamos falar apenas sobre correção parcial. *)

(* ####################################################### *)
(** *** Exercício: [REPEAT] *)

Module RepeatExercise.

(** **** Exercício: nível 4, avançado (hoare_repeat)  *)
(** [Vitor]In this exercise, we'll add a new command to our language of
    commands: [REPEAT] c [UNTIL] a [END]. You will write the
    evaluation rule for [repeat] and add a new Hoare rule to
    the language for programs involving it. *)

Inductive com : Type :=
  | CSkip : com
  | CAsgn : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

(** [Dalay][REPEAT] behaves like [WHILE], except that the loop guard is
    checked _after_ each execution of the body, with the loop
    repeating as long as the guard stays _false_.  Because of this,
    the body will always execute at least once. *)

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE"
  | Case_aux c "CRepeat" ].

Notation "'SKIP'" := 
  CSkip.
Notation "c1 ;; c2" := 
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" := 
  (CAsgn X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" := 
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" := 
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'REPEAT' e1 'UNTIL' b2 'END'" := 
  (CRepeat e1 b2) (at level 80, right associativity).

(** [Diego]Add new rules for [REPEAT] to [ceval] below.  You can use the rules
    for [WHILE] as a guide, but remember that the body of a [REPEAT]
    should always execute at least once, and that the loop ends when
    the guard becomes true.  Then update the [ceval_cases] tactic to
    handle these added cases.  *)

Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      ceval st SKIP st
  | E_Ass  : forall st a1 n X,
      aeval st a1 = n ->
      ceval st (X ::= a1) (update st X n)
  | E_Seq : forall c1 c2 st st' st'',
      ceval st c1 st' ->
      ceval st' c2 st'' ->
      ceval st (c1 ;; c2) st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      ceval st c2 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_WhileEnd : forall b1 st c1,
      beval st b1 = false ->
      ceval st (WHILE b1 DO c1 END) st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st' (WHILE b1 DO c1 END) st'' ->
      ceval st (WHILE b1 DO c1 END) st''
(* PREENCHER *)
.

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass"
  | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop" 
(* PREENCHER *)
].

(** As duas definições acima, copiadas aqui usam o novo [ceval]. *)

Notation "c1 '/' st '||' st'" := (ceval st c1 st') 
                                 (at level 40, st at level 39).

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) 
                        : Prop :=
  forall st st', (c / st || st') -> P st -> Q st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level).

(** Para se certificar de que você tem as regras de avaliação corretas para 
    [REPEAT], provar que [ex1_repeat] avalia corretamente. *)

Definition ex1_repeat :=
  REPEAT
    X ::= ANum 1;;
    Y ::= APlus (AId Y) (ANum 1)
  UNTIL (BEq (AId X) (ANum 1)) END.

Theorem ex1_repeat_works :
  ex1_repeat / empty_state ||
               update (update empty_state X 1) Y 1.
Proof.
  (* PREENCHER *) Admitted.

(** [Vitor]Now state and prove a theorem, [hoare_repeat], that expresses an
    appropriate proof rule for [repeat] commands.  Use [hoare_while]
    as a model, and try to make your rule as precise as possible. *)

(* PREENCHER *)

(** [Dalay]For full credit, make sure (informally) that your rule can be used
    to prove the following valid Hoare triple:
  {{ X > 0 }}
  REPEAT
    Y ::= X;;
    X ::= X - 1
  UNTIL X = 0 END
  {{ X = 0 /\ Y > 0 }}
*)


End RepeatExercise.
(** [] *)

(* ####################################################### *)
(** ** Exercício: [HAVOC] *)

(** **** Exercício: nível 3 (himp_hoare)  *)

(** [Diego]In this exercise, we will derive proof rules for the [HAVOC] command
    which we studied in the last chapter. First, we enclose this work
    in a separate module, and recall the syntax and big-step semantics
    of Himp commands. *)

Module Himp.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : id -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" | Case_aux c "HAVOC" ].

Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAsgn X a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'HAVOC' X" := (CHavoc X) (at level 60).

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st : state, SKIP / st || st
  | E_Ass : forall (st : state) (a1 : aexp) (n : nat) (X : id),
            aeval st a1 = n -> (X ::= a1) / st || update st X n
  | E_Seq : forall (c1 c2 : com) (st st' st'' : state),
            c1 / st || st' -> c2 / st' || st'' -> (c1 ;; c2) / st || st''
  | E_IfTrue : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
               beval st b1 = true ->
               c1 / st || st' -> (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
                beval st b1 = false ->
                c2 / st || st' -> (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall (b1 : bexp) (st : state) (c1 : com),
                 beval st b1 = false -> (WHILE b1 DO c1 END) / st || st
  | E_WhileLoop : forall (st st' st'' : state) (b1 : bexp) (c1 : com),
                  beval st b1 = true ->
                  c1 / st || st' ->
                  (WHILE b1 DO c1 END) / st' || st'' ->
                  (WHILE b1 DO c1 END) / st || st''
  | E_Havoc : forall (st : state) (X : id) (n : nat),
              (HAVOC X) / st || update st X n

  where "c1 '/' st '||' st'" := (ceval c1 st st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop"
  | Case_aux c "E_Havoc" ].

(** A definição da tripla de Hoare é exatamente como antes. Não como nossa
    noção de programas equivalente, ao qual teve consequências sutis com os comandos 
    ocasionalmente não-terminados (exercício [havoc_diverge]), esta definição ainda é
    completamente satisfatória. Convença de você mesmo antes de prosseguir.*)

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', c / st || st' -> P st -> Q st'.

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q) 
                                  (at level 90, c at next level) 
                                  : hoare_spec_scope.

(** Complete the Hoare rule for [HAVOC] commands below by defining
    [havoc_pre] and prove that the resulting rule is correct. *)

Definition havoc_pre (X : id) (Q : Assertion) : Assertion :=
(* PREENCHER *) admit.

Theorem hoare_havoc : forall (Q : Assertion) (X : id),
  {{ havoc_pre X Q }} HAVOC X {{ Q }}.
Proof.
  (* PREENCHER *) Admitted.

End Himp.
(** [] *)


(* ####################################################### *)
(** ** Lista completa de regras para a lógica de Hoare *)

(** Acima, nós introduzimos a Lógica de Hoare como uma ferramenta 
    para o raciocínio sobre programas Imp. No restante deste 
    capítulo, vamos explorar uma forma sistemática de usar 
    a Lógica de Hoare para provar propriedades sobre programas. 
    As regras da Lógica de Hoare são as seguintes: *)

(**
             ------------------------------ (hoare_asgn)
             {{Q [X |-> a]}} X::=a {{Q}}

             --------------------  (hoare_skip)
             {{ P }} SKIP {{ P }}

               {{ P }} c1 {{ Q }} 
               {{ Q }} c2 {{ R }}
              ---------------------  (hoare_seq)
              {{ P }} c1;;c2 {{ R }}

              {{P /\  b}} c1 {{Q}}
              {{P /\ ~b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} IFB b THEN c1 ELSE c2 FI {{Q}} 

               {{P /\ b}} c {{P}}
        -----------------------------------  (hoare_while)
        {{P}} WHILE b DO c END {{P /\ ~b}}

                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
    [Vitor]In the next chapter, we'll see how these rules are used to prove
    that programs satisfy specifications of their behavior.
*)


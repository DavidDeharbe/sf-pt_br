(** * Imp: Programas Imperativos Simples *)

(** [Claudia] In this chapter, we begin a new direction that will continue for
    the rest of the course.  Up to now most of our attention has been
    focused on various aspects of Coq itself, while from now on we'll
    mostly be using Coq to formalize other things.  (We'll continue to
    pause from time to time to introduce a few additional aspects of
    Coq.)

    Nosso primeiro caso de estudo é uma _simples linguagem de programação
    imperativa_ chamada Imp, contendo um pequeno fragmento central das 
    linguagens convencionais tradicionais como C e Java. Aqui está uma 
    função matemática familiar escrita em Imp.

     Z ::= X;;
     Y ::= 1;;
     WHILE not (Z = 0) DO
       Y ::= Y * Z;;
       Z ::= Z - 1
     END
*)

(** Este capítulo visa como definir a _sintaxe_ e a _semântica_ 
    de um Imp; os capítulos que o seguem desenvolvem a teória da _equivalência
    de programas_ e introduz a _Lógica de Hoare_, uma lógica largamente
    utlizada para raciocínio sobre programas imperativos. *)

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
(** Por comparação, aqui está uma gramática BNF (Forma Backus-Naur) 
    convencional definindo a mesma sintaxe abstrata:
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

       - O BNF é mais informal -- por exemplo, ele fornece algumas
         sugestões sobre a sintaxe superficial das expressões (como o
         fato que o operador da adição é escrito como [+] e é um
         símbolo infixo) enquanto leva outros aspectos da análise lexical
         e análise (como a relativa a precedência do [+], [-], e
         [*]) não especificada.  Algumas informações adicionais -- e 
         inteligência humana -- podem ser requiridas para tornar esta descrição
         em uma definição formal (quando implementamos um compilador, por
         exemplo).

         A versão Coq omite sistematicamente todas estas informações e
         concentra apenas na sintaxe abstrata.

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
(** Similarmente, avaliar uma expressão boleana produz um boleano. *)

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

(** Nós ainda não definimos muito, mas já podemos obter alguma
    milhagem fora das definições. Supondo que definimos uma função 
    que toma uma expressão aritmética e a simplifica, 
    modificando cada ocorrência de [0+e] (isto é, [(APlus (ANum 0) e])
    em somente [e]. *)

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

(** _Tacticals_ é o temo em Coq para táticas que usam outras táticas como
    argumento -- "táticas de alta ordem", se assim você desejar. *)

(* ####################################################### *)
(** *** O Tatical [repeat] *)

(** A tática [repeat] toma outra tática e continua aplicando
    essa tática até ela falhar. Aqui está um exemplo mostrando que
    [100] é par utilizando o repeat. *)

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

(** Em sua forma mais comumente utilizada, o Tatical [;] usa outras duas 
    táticas como argumento: [T;T'] primeiro executa a tática [T] e então
    executa a tática [T'] em _cada submeta_gerada por [T]. *)

(** Por exemplo, considere o lema trivial a seguir: *)

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

       - Suponha [a = ANum n] para algum [n]. Nós devemos mosttrar
         aeval (optimize_0plus (ANum n)) = aeval (ANum n).
         Isso é instantâneo a partir da definição de [optimize_0plus].

      - Supondo [a = APlus a1 a2] para algum [a1] e [a2].  Nós
        devemos mostrar
          aeval (optimize_0plus (APlus a1 a2))
        = aeval (APlus a1 a2).
        Considerar a possíveis formas de [a1].  Para a maioria delas,
        [optimize_0plus] simplesmente chama ela mesma recursivamente para as
        subexpressões e reconstrói uma nova expressão da mesma forma que
        [a1]; nesses casos, o resultado segue diretamente para
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

(** Coq também fornece muitos meios de "programar" scripts de tática.

      - A linguagem [Tactic Notation] ilustrada abaixo dá um caminho
        acessível para definir as "táticas de taquigrafia" que agrupam várias
        táticas em um único comando.

      [Francisco]- For more sophisticated programming, Coq offers a small
        built-in programming language called [Ltac] with primitives
        that can examine and modify the proof state.  The details are
        a bit too complicated to get into here (and it is generally
        agreed that [Ltac] is not the most beautiful part of Coq's
        design!), but they can be found in the reference manual, and
        there are many examples of [Ltac] definitions in the Coq
        standard library that you can use as examples.

      - Há também uma API OCaml, que pode ser usada para construir táticas 
      que acessam estruturas internas de Coq a um nível mais baixo, mas isso 
      raramente vale a pena para usuários Coq comuns.

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

(** A próxima subseção nos dá um uso mais sofisticado dessa funcionalidade... *)

(* ####################################################### *)
(** *** Tornando Mais Robustas as Análises por Casos *)

(** Ser capaz de lidar com a maioria dos casos de um [induction]
    ou [destruct] ao mesmo tempo é muito conveniente, mas também pode
    ser um pouco confuso.  Um problema que frequentemente acontece é
    que a _manutenção_ da prova, escrita nessa estilo, pode ser difícil.
    Por exemplo, suponha que, mais tarde, extendemos a definição de
    [aexp] com outro construtor que também requer um argumento especial.
    A prova acima pode quebrar por que o Coq gerará as submetas para
    esse construtor antes de um para o [APlus], de modo que,
    nesse ponto quando começarmos a trabalhar no caso [APlus], o Coq está
    esperando o argumento para um construtor completamente diferente.
    O que gostariamos de obter é uma sensata mensagem de erro
    dizendo "Eu estava esperando o caso [AFoo] nesse ponto, mas o
    script da prova está falando sobre [APlus]."  Aqui está um bom truque
    (devido à Aaron Bohannon) que consegue isso sem problemas. *)

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult" ].

(** [Francisco]([Case_aux] implements the common functionality of [Case],
    [SCase], [SSCase], etc.  For example, [Case "foo"] is defined as
    [Case_aux Case "foo".) *)

(** Por exemplo, se [a] é uma variável do tipo [aexp], então, ao 
    utilizar aexp_cases (induction a) Case, será realizada uma 
    indução sobre [a] (a mesma que se tivéssemos apenas digitado 
    [induction a]) e _também_ será adicionada uma tag [Case] para 
    cada submeta gerada pela [induction], nomeando a qual construtor 
    ela pertence.  Por exemplo, aqui está mais uma prova de 
    [optimize_0plus_sound], utilizando [aexp_cases]: *)

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
(** _Exercício de Design_: A otimização implementada por nossa função 
    [optimize_0plus] é somente uma das muitas otimizações imagináveis em
    expressões aritméticas e boleanas. Escreva um otimizador mais
    sofisticado e prove a sua corretude.

(* PREENCHER *)
*)
(** [] *)

(* ####################################################### *)
(** ** A Tática [omega] *)

(** A tática [omega] implementa um procedimento de decisão para um subconjunto
    de lógica de primeira ordem chamada de _aritmética de Presburger_.  Essa 
    aritmética é baseada no algoritmo Omega, inventado em 1992 por William Pugh.

    [Francisco]If the goal is a universally quantified formula made out of

      - constantes numéricas, adição ([+] e [S]), subtração ([-] 
        e [pred]), e multiplicação por constantes (isto é o que 
        faz com que seja Aritmética de Presburger),

	  - igualdade ([=] e [<>]) e desigualdade ([<=]), e

      [Claudia]- the logical connectives [/\], [\/], [~], and [->],

    Então invocar [omega] vai ou resolver a meta ou lhe dizer que isso é
    falso. *)

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. omega.
Qed.

(** Leibniz escreveu, "É indigno de homens excelentes perder
    horas como escravos no trabalho de cálculos que poderiam ser
    relegados para qualquer outra pessoa, se máquinas forem usadas."  Nós
    recomendamos utilizar a tática omega sempre que possível. *)

(* ####################################################### *)
(** ** Mais Algumas Táticas Convenientes *)

(** [Francisco]Finally, here are some miscellaneous tactics that you may find
    convenient.

     - [clear H]: Apaga a hipótese [H] do contexto.

     - [subst x]: Encontra uma suposição [x = e] ou [e = x] no 
       contexto, substitui [x] por [e] através do contexto e da 
       meta atual, e limpa a suposição.

     - [subst]: Substitui _todas_ as premissas do formato [x = e]
       ou [e = x].

     [Francisco]- [rename... into...]: Change the name of a hypothesis in the
       proof context.  For example, if the context includes a variable
       named [x], then [rename x into y] will change all occurrences
       of [x] to [y].

     - [assumption]: Tenta encontrar uma hipótese [H] no contexto que 
     corresponda exatamente à meta; se uma for encontrada, comporta-se 
     exatamente como [apply H].

	- [contradição]: Tente encontrar uma hipótese [H] no contexto atual que é logicamente 
	equivalente a [False]. Se uma for encontrada, solucione a meta.

     [Claudia]- [constructor]: Try to find a constructor [c] (from some
       [Inductive] definition in the current environment) that can be
       applied to solve the current goal.  If one is found, behave
       like [apply c]. *)

(** Veremos vários exemplos de aplicação destas táticas nas provas abaixo. *)

(* ####################################################### *)
(** * Avaliação enquanto Relação *)

(** Nós temos apresentado [aeval] e [beval] como funções definidas por
    [Fixpoints]. Outro modo de pensar a respeito de avaliação -- um que 
    nós veremos que é também mais flexível -- é como uma _relação_ entre
    expressões e seus valores. Isso leva naturalmente a definições indutivas 
    [Inductive] como o exemplo seguinte para expressões aritméticas... *)

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

(** Como é frequentemente o caso com relações, nós vamos achar
    conveniente definir notações fixas para [aevalR].  Nós escreveremos [e
    || n] para significar que a expressão aritmética [e] calcula para o valor
    [n].  (Esta notação é uma que a limitação para o símbolos ASCII se
    torna um pouco enfadonha.  A notação padrão para a
    relação de avaliação é uma seta dupla para baixo.  Nós vamos tipar
    como na versão HTML das notas e utilizar uma dupla barra vertical
    para como a melhor aproximação em arquivos [.v].)  *)

Notation "e '||' n" := (aevalR e n) : type_scope.

End aevalR_first_try.

(** [Francisco]In fact, Coq provides a way to use this notation in the definition
    of [aevalR] itself.  This avoids situations where we're working on
    a proof involving statements in the form [e || n] but we have to
    refer back to a definition written using the form [aevalR e n].

    Fazemos isso primeiro "reservando" a notação, em seguida, dando 
    a definição em conjunto com uma declaração do que a notação 
    significa. *)

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

(** Formalmente, não há nada tão fundo a respeito de regras de inferência:
    elas são somente implicações. Você pode ler o nome da regra na direita
    como o nome do construtor e ler cada quebra de linha entre as premissas 
    acima da linha e a própria linha como [->]. Todas as variáveis mencionadas
    an regra ([e1], [n1], etc.) são implicitamente limitadas pelos 
    quantificadores universais no começo. (Tais variáveis são também chamadas
    _metavariáveis_ para as distiguir das variáveis da linguagem que estamos 
    definindo. No momento, nossas expressões aritméticas não incluem variáveis,
    mas nós vamos em breve adicioná-las.) A coleção completa de regras é 
    entendida como sendo envolvida em uma declaração indutiva ([Inductive])
    (imformalmente, essa é ou emitida ou indicada por dizer algo como "sendo
    [aevalR] a menor relação fechada sobre as seguintes regras..."). *)

(** Por exemplo, [||] é a menor relação fechada sob essas
    regras:
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

(** Nota: se você estiver lendo o arquivo HTML, você verá uma caixa 
quadrada vazia em vez de uma prova para este teorema.
Você pode clicar nessa caixa para "revelar" o texto para ver a prova. 
Clique no texto revelado para "embrulhá-lo" de volta em uma caixa. 
Nós usaremos este estilo com freqüência a partir de agora para 
ajudar a manter o HTML mais fácil de ler. As provas completas 
sempre aparecem nos arquivos .v. *)

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

(** Para as definições de avaliação para expressões aritméticas e 
    boleanas, a escolha de usar definições funcionais ou relacionais
    são principalmente uma questão de gosto. No geral, Coq tem um 
    suporte melhor para trabalhar com relações. Na outra mão, em algum 
    sentido definições de funções carregam mais informação, porque 
    funções são necessariamente deterministicas e definidas em todos
    os argumentos; por uma relação nós temos que mostrar essas 
    propriedades explicitamente se nós precisamos delas. Funções também
    tiram vantagem do mecanismo de computação do Coq.

    Entretanto, há circunstâncias em que definições relacionais de
    avaliação são preferíveis às funcionais. *)

Module aevalR_division.

(** [Francisco]For example, suppose that we wanted to extend the arithmetic
    operations by considering also a division operation:*)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp
  | ADiv : aexp -> aexp -> aexp.   (* <--- new *)

(** Estender a definição de [aeval] para lidar com esta nova operação
    não seria simples (o que devemos retornar como resultado
    de [ADiv (ANum 5) (ANum 0)]?). Mas estender [aevalR] é
    direto. *)

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

(** vamos voltar a nossa atenção de volta para definir Imp. A proxima coisa 
    que nós precisamos fazer é enriquecer nossas expressões aritméticas e 
    boleanas com variáveis. Para manter as coisas simples, nós assumimos
    que todas as variáveis são globais e que elas somente mantém números. *)

(* ##################################################### *)
(** ** Identificadores *)

(** Para começar, nós precisamos formalizar os _identificadores_ como variáveis
    de programas.  Nós podemos utilizar uma cadeia de caracteres para isso -- 
    ou, em um compilador real, estruturas elaboradas, como ponteiros, em uma 
    tabela de símbolos.  Mas, por simplicidade, somente vamos utilizar números 
    naturais como identificadores. *)

(** [Francisco](We hide this section in a module because these definitions are
    actually in [SfLib], but we want to repeat them here so that we
    can explain them.) *)

Module Id. 

(** Nós definimos um novo tipo de dados indutivo [Id] de modo que nós não 
    confundiremos identificadores e números.  Nós usamos [sumbool] para 
    definir um operador computável de igualdade em [Id]. *)

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

(** Por simplicidade (para evitar lidar com funções parciais), nós deixamos
    o estado ser definido por _todas_ as variáveis, mesmo que alguns
    programas dados somente mencionem um número finito delas. O estado
    captura todas as informações guardadas na memória. Para programas Imp, 
    porque cada variável guarda somente um número natural, nós podemos 
    representar o estado como um mapeamento de indentificadores para [nat].
    Para linguagens de programação mais comlexas, o estado pode ter mais 
    estrutura. 
*)

Definition state := id -> nat.

Definition empty_state : state :=
  fun _ => 0.

Definition update (st : state) (x : id) (n : nat) : state :=
  fun x' => if eq_id_dec x x' then n else st x'.

(** Para provas envolvendo estados, nós vamos precisar de várias propriedades
    simples de [update]. *)

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

(** Podemos adicionar variáveis para as expressões aritméticas que tínhamos antes, 
    simplesmente adicionando mais um construtor: *)

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

(** A definição de [bexp]s é a mesma de antes (usando o novo [aexp]s: *)

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

(** Os avaliadores aritméticos e booleanos podem ser extendidos para manejar
    variáveis de forma óbvia: *)

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

(** Informalmente, comandos [c] são descritos pela seguinte gramática BNF:
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

(** Como de costume, nós podemos usar algumas declarações [Notation] para
    fazer as coisas mais legíveis. Nós precisamos ser um pouco mais 
    cuidadosos  para evitar comflitos com as notações construídas em Coq, 
    assim nós manteremos essa luz -- em paticular, nós não introduzimos 
    qualquer notação para [aexps] e [bexps] para evitar confusão com os 
    operadores numéricos e boleanos que nós ja temos definido. Nós usamos 
    a palavra chave [IFB] para condicionais ao invés de [IF], por razões 
    similares. *)

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

(** Por exemplo, aqui é a função fatorial novamente, escrita como
    uma definição formal para o Coq: *)

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

(** Aqui está uma tentativa de definir uma função de avaliação para os 
    comandos, omitindo o caso [WHILE]. *)

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
    Isso é, proposições como [False] se tornairam prováveis 
    (por exemplo [loop_false 0] seria uma prova de [false]), 
    o que seria um disastre para a consistência lógica de Coq.

    Então, já que isso não termina em todos as entradas, a versão completa
    de [ceval_fun] não pode ser escrita em Coq -- ao menos, não sem truques
    adicionais (ver capítulo [ImpCEvalFun] se estiver curioso). *)

(* #################################### *)
(** ** Avaliação como uma Relação *)

(** [Francisco]Here's a better way: we define [ceval] as a _relation_ rather
    than a _function_ -- i.e., we define it in [Prop] instead of [Type], as we
    did for [aevalR] above. *)

(** Esta é uma mudança importante.  Além de nos libertar das soluções 
    alternativas embaraçosas que seriam necessárias para definir a 
    avaliação como uma função, isso nos dá muito mais flexibilidade na 
    definição. Por exemplo, se nós adicionássemos recursos de 
    concorrência para a linguagem, nós iríamos querer que a definição 
    de avaliação fosse não determinística - isto é, não só não seria 
    total, não seria nem mesmo uma função parcial! *)
    
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
(** O custo de definir avaliação como uma relação ao invés de uma
    função é que nós agora temos que construir _provas_ que alguns
    programas avaliam para algum estado resultado, ao invés de 
    apenas deixar o mecanismo de computação do Coq fazer isso por nós. *)

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
(** Escrever um programa Imp que soma os números de [1] até
    [X] (inclusive: [1 + 2 + ... + X]) na variável [Y].
    Prove que este programa executa como intencionado para X = 2
    (essa última parte é mais complicada do que você poderia esperar). *)

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

    De fato, isso não pode acontecer: [ceval] é uma função parcial. 
    Aqui está a prova: *)

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
(** Considere a definição da propriedade [no_whiles] abaixo: *)

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP       => true
  | _ ::= _    => true
  | c1 ;; c2  => andb (no_whiles c1) (no_whiles c2)
  | IFB _ THEN ct ELSE cf FI => andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END  => false
  end.

(** Esta propriedade fornece [true] sómente em programas que
    não tem laços while. Utilizando [Inductive], escreva uma propriedade
    [no_whilesR] que como [no_whilesR c] é provável exatamente quando [c]
    é um programa sem laços while.  Então prove sua equivalência com
    [no_whiles]. *)

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
(** Calculadoras HP, linguagens de programação como Forth e Postscript, 
    e máquinas virtuais como o Java Virtual Machine, todas avaliam 
    expressões aritméticas usando uma pilha. Por exemplo, a expressão
<<
   (2*3)+(3*(4-2))
>>
   seria inserida como 
<<
   2 3 * 3 4 2 - * +
>>
   e avaliada assim:
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

    Note que a especificação deixa não especificado o que fazer quando 
    encontrar uma instrução [SPlus], [SMinus] ou [SMult] se a pilha contém
    menos que dois elementos. De certo modo, isso é imaterial o que fazemos, 
    uma vez que nosso compilador não vai nunca emitir um programa mal-formado
    como esse. *)

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

(** Em seguinda, escreva uma função que compila um [aexp] em um programa
    de máquina de pilha. O efeito de execução do programa deve ser o mesmo
    que colocar o valor da expressão na pilha. *)

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
(** A tarefa deste exercício é demonstrar a correção do compilador 
    implementado no exercício anterior.  Lembre-se de que a especificação 
    deixou indeterminado o que fazer quando encontrar uma instrução [SPLUS], 
    [SMinus] ou [SMult] se a pilha contiver menos de dois elementos. 
    (A fim de fazer a sua demonstração de correção mais fácil, você pode achar 
    útil voltar e mudar a sua implementação!)

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

    Primeiramente, nós precisamos enriquecer a linguagem de comandos
    com um caso adicional. *)

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

(** Em seguida, defina o comportamento de [BREAK].  Informalmente,
    sempre que [BREAK] é executado em uma sequência de comandos, ele para
    a execução dessa sequência e sinaliza que o laço mais
    interno (se houver) deve terminar. Se não houver nenhum
    laço delimitador, então todo o programa simplesmente termina. O
    estado final deve ser o mesmo que o estado em que o [BREAK]
    foi executado.

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

    Uma maneira de expressar esse comportamento é adicionar outro parâmetro 
    para a relação de avaliação que especifica se a avaliação de um comando 
    executa uma declaração [BREAK]:
    
    Uma maneira de expressar esse comportamento é adicionar outro parâmetro 
    para a relação de avaliação que especifica se a avaliação de um comando executa um [BREAK] declaração: *)

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

    - Se o comando é [SKIP], então o estado não muda, e a execução de
      algum loop delimitador pode continuar normalmente.

    - Se o comando é [BREAK], o estado se mantêm inalterado, mas
      sinalizamos um [SBreak].

    [Francisco]- If the command is an assignment, then we update the binding for
      that variable in the state accordingly and signal that execution
      can continue normally.

    - Se o comando é da forma [IF b THEN c1 ELSE c2 FI], então o estado 
    é atualizado como na semântica original de Imp, exceto que nós 
    também propagamos o sinal da execução de qualquer ramo que 
    foi tomado.

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

(** Baseado na descrição acima, complete a definição da relação [ceval]. *)

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

(** Agora, as seguintes propriedades da definição de [ceval]: *)

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

(** A maioria das linguagem de programação modernas usam uma regra de avaliação
    "curto-circuito" para booleanos [and]: para avaliar [BAnd b1 b2],
    primeiramente avalia [b1].  Se isso é avaliado para [false], então toda a 
    expressão [BAnd] é imediatamente avaliada para [false], sem avaliar [b2].
    Entretanto, [b2] é avaliado para determinar o resultado da
    expressão [BAnd].

    [Francisco]Write an alternate version of [beval] that performs short-circuit
    evaluation of [BAnd] in this manner, and prove that it is
    equivalent to [beval]. *)

(* PREENCHER *)
(** [] *)

(** **** Exercício: nível 4, opcional (add_for_loop)  *)

(** Adicionar loops [for], no estilo de C, para a linguagem de comandos, 
    atualizar a definição de [ceval] para definir a semântica de loops 
    [for], e adicionar casos para loops [for], conforme necessário, 
    para que todas as provas neste arquivo sejam aceitas por Coq.
    
	Um laço [for] deve ser parametrizado por (a) uma sentença executada inicialmente, (b) 
	um teste que é executado em cada iteração do laço a fim de determinar se o mesmo deve 
	continuar, (c) uma sentença executada no fim de cada iteração de laço e (d) uma 
	declaração que constitui o corpo desse laço. (Você não precisa se preocupar em criar 
	uma Notação concreta para os laços [for], mas sinta-se livre para fazê-lo também 
	se preferir.) *)

(* PREENCHER *)
(** [] *)



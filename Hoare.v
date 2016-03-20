(** * Hoare: Lógica de Hoare, Parte I *)

Require Export Imp.

(** nos dois ultimos capítulos, nós começamos a aplicar as ferramentas
    matemáticas desenvolvidas na primeira parte do curso para estudar
    a teoria de uma pequena linguagem de programação, Imp.

    - Nós definimos um tipo de _árvores de sintaxe abstrata_ para o Imp,
      juntamente com uma _relação de avaliação_ (uma função parcial sobre os
      estados) que especifica a _semântica operacional_ de programas.

      A linguagem que definimos, embora pequena, capitura algumas das
      características chaves desenvolvidas em linguagens como C, C++ e Java, incluindo
      a noção fundamental de estado mutável e alguns controles de estruturas comuns.

    - Nós provamos uma série de _propriedades metateóricas_ -- "meta" 
      no sentido de que eles são propriedades da linguagem como um todo, 
      ao invés de propriedades de programas específicos da linguagem. 
      Isso incluiu:

        - determinismo da avaliação 

		- equivalência de algumas maneiras diferentes de escrever as definições (por 
		exemplo, definições funcionais e relacionais da avaliação de expressão aritmética)

		- terminação garantida de certas classes de programas
		
		- correção (no sentido de preservação) de uma série de transformações úteis de 
		programas
		
		- equivalência de comportamento de programas (no capítulo [Equiv]).

    Se nós parássemos aqui, nós já poderiamos ter algo útil: um conjunto
    de ferramentas para definir e discutir linguagens de programação e
    funcionalidades de linguagem que são matematicamente precisas, 
    fexíveis e fáceis de se trabalhar, aplicadas a um conjunto de 
    propriedades chave. Todas essas propriedades são coisas que designers 
    de liguagem, escritores de compiladores e usuários podem querer 
    conhecer. De fato, muitas delas são tão fundamentais para o nosso 
    entendimento das linguagens de programação que lidamos que nós
    podemos não reconhecê-las conscientemente como "teoremas". Mas 
    propriedades que parecem intuitivamente óbvias podem às vezes ser
    bastante sutis (em alguns casos, até sutilmente erradas!).

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

(** A Lógica de Hoare combina duas belas ideias: uma forma natural de escrever 
_especificações_ de programas e uma _técnica de prova composicional_ para provar que os 
programas são corretos com relação a tais especificações -- no qual queremos dizer como  
"composicional" que a estrutura das provas refletem diretamente a estrutura dos programas 
sobre os quais são gerados. *)

(* ####################################################### *)
(** ** Asserções *)

(** Para falar a respeito de especificações de programas, a primeira
    coisa que nós precisamos é de uma maneira de fazer _asserções_ a 
    respeito de propriedades que mantém um ponto particular durante a 
    execução do programa -- isto é, afirmações a respeito do estado
    atual da memória quando a execução do programa alcança determinado 
    ponto. Formalmente, uma asserção é somente uma família de 
    proposições idexadas por um [state] (estado). *)

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

(** Em seguida, precisamos de uma maneira de fazer declarações formais a respeito do 
comportamento dos comandos. *)

(** Devido ao fato de que o comportamento de um comando é transformar
    um estado em outro, é natural expressar afirmações a respeito de
    comandos em termos de asserções que são verdade antes e depois do
    comando executar:

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

(** (A notação tradicional é [{P} c {Q}], mas chaves individuais já são usadas para 
outras coisas no Coq.) *)

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

(** (A anotação [hoare_spec_scope] aqui diz ao Coq que essa notação 
    não é global mas tem a intenção de ser usada em contextos 
    particulares. A [Open Scope] diz ao Coq que esse arquivo é um
    desses contextos.) *)

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

(** O objetivo da lógica de Hoare é proporcionar um método _composicional_ para provar a 
validade das triplas de Hoare. Ou seja, a estrutura de uma prova para a correção de um 
programa deve espelhar a estrutura do próprio programa. Para este fim, nas seções abaixo, 
iremos introduzir uma regra para o raciocínio sobre cada uma das diferentes formas 
sintáticas de comandos no Imp - um para atribuição, um para o sequenciamento, um para 
condicionais, etc. - além de um par de regras "estruturais" para unir tudo. Nós 
provaremos que os programas estão corretos usando estas regras de prova, sem nunca 
desdobrar a definição de [hoare_triple]. *) 

(* ####################################################### *) 
(** *** Atribuição *)

(**  A regra para atribuição é a mais fundamentas das regras de prova da
     lógica de Hoare. Aqui está como ela funciona.

    Considere essa tripla de Hoare (válida):
       {{ Y = 1 }}  X ::= Y  {{ X = 1 }}
    Em português: se nós começarmos em um estado onde o valor de [Y]
    é [1] e nós assinalarmos [Y] a [X], então nós iremos terminar em um
    estado onde [X] é [1]. Isso é, a propriedade de ser igual a [1] é
    transferida de [Y] para [X].

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

	Por exemplo, a seguir se encontram aplicações válidas para a regra de atribuição:
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

(** Para formalizar a regra, nos devemos primeiramente formalizar 
    a ideia de "substituir uma expressão por uma variável Imp em uma 
    asserção." Isso é, dada uma proposição [P], uma variável [X] e uma
    expressão aritmética [a], nós queremos derivar outra proposição [P']
    que é o mesmo que [P] exceto que, sempre que [P] menciona [X], [P']
    deve mencionar [a].
   
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

	Para um exemplo mais interessante, suponha que [P'] é [(X <= 5) [X |-> X+1]]. 
	Formalmente, [P'] é a expressão Coq fun st => 
	      (fun st' => st' X <= 5) 
	      (update st X (aeval st (APlus (AId X) (ANum 1)))),
	sendo simplificado para
    fun st => 
      (((update st X (aeval st (APlus (AId X) (ANum 1))))) X) <= 5
	e simplificado mais ainda para
    fun st => 
      (aeval st (APlus (AId X) (ANum 1))) <= 5.
	Ou seja, [P'] é a afirmação de que [X+1] é, no máximo, [5]. *)

(** Agora nós podemos dar a regra de prova precisa para atribuição:
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
(** No entanto, usando uma variável auxiliar [m] para lembrar o valor original de [X], 
podemos definir uma regra de Hoare para atribuição que faz, intuitivamente, ser de 
"avançar" no lugar de ir de trás pra frente.

  ------------------------------------------ (hoare_asgn_fwd)
  {{fun st => P st /\ st X = m}}
    X ::= a
  {{fun st => P st' /\ st X = aeval st' a }}
  (onde st' = update st X m)
    Note que nós usamos o valor original de [X] para reconstruir o
    estado [st'] antes da atribuição. Prove que essa regra é correta
    (a primeira hipótese é o axioma extensionalmente funcional, que
    você vai precisar em determinado momento). Também note que essa
    regra é mais complicada que [hoare_asgn].
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

	Por exemplo, enquanto {{(X = 3) [X |-> 3]}} X ::= 3 {{X = 3}} decorre diretamente da 
	regra de atribuição, {{True}} X ::= 3 {{X = 3}} não. Esta tripla é válida, porém não 
	é uma instância de [hoare_asgn] pois [True] e [(X = 3) [X |-> 3]] não são afirmações 
	sintaticamente iguais. No entanto, eles são logicamente equivalente, por isso, se uma 
	tripla é válida, então o outro deve certamente ser também. Poderíamos capturar essa 
	observação com a seguinte regra:
	                {{P'}} c {{Q}}
	                  P <<->> P'
	         -----------------------------   (hoare_consequence_pre_equiv)
	                {{P}} c {{Q}}
    Indo um pouco mais além nessa linha de pensamento, nós podemos
    ver que fortificar uma pré-condição ou enfraquecer a pós-condição
    de uma tripla válida sempre produz outra tripla válida. essa 
    observação é capturada por duas _Regras de Consequência_.
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

(** Por exemplo, nós podemos usar a primeira regra da consequência assim:
                {{ True }} ->>
                {{ 1 = 1 }} 
    X ::= 1
                {{ X = 1 }}
    Ou, formalmente... 
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

	Isto é um pouco chato pois tanto a asserção é longa demais como o próximo passo a 
	ser feito com [hoare_asgn_example1] -- a aplicação da regra [hoare_asgn] -- irá nos 
	dizer exatamente o que deveria ser! Nós podemos usar [eapply] no lugar de 
	[apply] para dizer ao Coq, essencialmente, "Tenha calma: a parte que está faltando 
	será preenchida em breve." *)
	
Example hoare_asgn_example1' :
  {{fun st => True}} 
  (X ::= (ANum 1)) 
  {{fun st => st X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  intros st H.  reflexivity.  Qed.

(** Geralmente, a tática [eapply H] funciona como [apply H] exceto que, 
    ao invés de falhar se unificar a meta com a conclusão de [H] não 
    determina como instanciar todas as variáveis que aparecem nas 
    premissas de [H], [eapply H] vai substituir essas variáveis com
    as chamadas _variáveis existenciais_ (escritas [?nnn]) como espaços
    reservados para expressões que serão determinados (por uma posterior 
    unificação) mais tarde na prova. *)

(** A fim de que [Qed] suceda, toda variáveis existênciais precisam
    ser determinadas até o fim da prova. Caso contrário Coq
    irá (com razão) recusar aceitar a prova. Se lembre que as táticas do Coq
    constroem objetos de prova, e objetos de prova contendo variáveis
    existênciais não são completos. *)

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
(** A execução de [apply HP'] acima falha com o seguinte erro: 
     Error: Impossible to unify "?175" with "y".
	Existe um concerto fácil para este caso:
	executar [destruct HP] _antes_ de [eapply HQ].
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

(** No último passo nós fizemos [apply HP'] o qual unifica a variável
    existencial na meta com a variável [y]. A tática [assumption] não 
    funciona nesse caso, devido ao fato de ela não poder lidar com 
    variáveis existenciais. Contudo, Coq também fornece uma tática
    [eassumption] que resolve a meta se uma das premissas corresponde
    à meta até instâncias de variáveis existenciais. Nós podemos usar
    isso ao invés de [apply HP']. *)

Lemma silly2_eassumption : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP']. eapply HQ. eassumption.
Qed.

    

(** **** Exercício: nível 2 (hoare_asgn_examples_2)  *)
(** Traduzir as triplas de Hoare informais...
       {{ X + 1 <= 5 }}  X ::= X + 1  {{ X <= 5 }}
       {{ 0 <= 3 /\ 3 <= 5 }}  X ::= 3  {{ 0 <= X /\ X <= 5 }}
   ...em afirmações formais [assn_sub_ex1', assn_sub_ex2'] e 
   usar [hoare_asgn] e [hoare_consequence_pre] para prova-las. *)

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

(** Perceba que, na regra formal [hoare_seq], as premisas são dadas numa ordem contrária 
([c2] before [c1]). Isto combina com o fluxo natural de informações em muitas situações 
na qual usamos a regra: o caminho natural para construir uma prova na lógica de Hoare é 
começar no fim do programa (com uma pós-condição final) e empurrar as pós-condições de 
volta até chegar em seu início. *)

(** Informalmente, um modo legal de gravar uma prova usando a regra de 
    sequência é como um "programa decorado" onde a asserção intermediária
    [Q] é escrita entre [c1] e [c2;]

      {{ a = n }}
    X ::= a;;
      {{ X = n }}      <---- decoração para Q
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

(** Vamos frequentemente utilizar [hoare_seq] e
    [hoare_consequence_pre] em combinação com a tática [eapply],
    como feito acima. *)

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
(** Explique por que a seguinte proposição não pode ser provada:
      forall (a : aexp) (n : nat),
         {{fun st => aeval st a = n}}
         (X ::= (ANum 3);; Y ::= a)
         {{fun st => st Y = n}}.
*)

(* PREENCHER *)
(** [] *)

(* ####################################################### *) 
(** *** Condicionais *)

(** Que ordenação de regra nós queremos para raciocinar a respeito
    de comandos condicionais? Certamente, se a mesma asserção [Q]
    se mantém depois de executar cada branch, então ela se mantém
    depois de toda a condicional. Então nós devemos ser tentados a 
    escrever:
              {{P}} c1 {{Q}}
              {{P}} c2 {{Q}}
      --------------------------------
      {{P}} IFB b THEN c1 ELSE c2 {{Q}}
   Contudo, isso é muito fraco. Por exemplo, usando essa regra,
   nós não podemos mostrar que:
     {{ True }} 
     IFB X == 0
     THEN Y ::= 2
     ELSE Y ::= X + 1 
     FI
     {{ X <= Y }}
   uma vez que a regra não diz nada sobre o estado em que as atribuições
   tomam lugar nos ramos "then" e "else". *)
   
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

(** Agora podemos formalizar a regra de prova Hoare para condicionais e prová-lo que está 
correto. *)

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
Ideia: crie uma _lógica de domínio específico_ para raciocinar 
a respeito de propriedades de programas Imp.

- Isso esconde os detalhes de baixo nível da semântica do programa
- Leva a um processo de raciocínio composicional


A estrutura básica é dada pela _Tripla de Hoare_ na forma:
  {{P}} c {{Q}}
]] 

- [P] e [Q] são predicados sobre o estado do programa Imp
- "Se o comando [c] é iniciado em um estado satisfazendo a afirmação
        [P], e se [c] eventualmente termina em algum estado final,
        então esse estado final satisfará a afirmação [Q]."

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

(** Neste exercício iremos estender Imp com "condicionais unilaterais" com a forma     
[IF1 b THEN c FI]. Aqui, [b] é uma expressão booleana e [c] um comando. Se [b] for 
avaliada como [true], então o comando [c] é avaliado. Se [b] for avaliada como [false], 
então [IF1 b THEN c FI] não faz nada.  

    Nós recomendamos que você faça esse exercício antes dos que seguem,
    pois ele deve ajudar a solidificar seu entendimento do material. *)


(** O primeiro passo é extender a sintaxe de comandos e introduzir
    as notações usuais.  (Já fizemos isso para você.  Nós usamos um módulo
    separado para previnir poluir o contexto para identificadores global.) *)

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

(** Agora iremos repetir (literalmente) a definição e notação das triplas de Hoare. *)

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', 
       c / st || st'  ->
       P st  ->
       Q st'.

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q) 
                                  (at level 90, c at next level) 
                                  : hoare_spec_scope.

(** Finalmente, nós (isto é, você) precisa declarar e provar um teorema
    [hoare_if1], que expressa uma regra de prova de lógica de Hoare 
    apropriada para condicionais unilaterais. Tente criar uma regra que
    é sólida e tão precisa como for possível. *)

(* PREENCHER *)

(** Para um crédito total, provar formalmente que sua regra é 
    precisa o suficiente para mostra a seguinte tripla de Hoare [hoare_if1_good]:
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

(** Primeiro de tudo, vamos pensar a respeito do caso onde [b] é falso no
    começo -- isto é, vamos assumir que o corpo do loop nunca executa 
    ompletamente. Nesse caso, o loop se comporta como [SKIP], então nós 
    devemos ser tentados a escrever: *)

(**
      {{P}} WHILE b DO c END {{P}}.
*)

(** 
    Mas, como observamos acima para a condicional, sabemos um
    pouco mais ao final -- não somente [P], mas também o fato que
    [b] é falso em um estado atual.  Então podemos enriquecer um
    pouco a pós-condição:
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
	Uma sutileza na terminologia é que chamar uma asserção [P] de "invariante de laço" 
	(loop invariant) não significa apenas que ele é preservado pelo corpo do laço em 
	questão (ou seja, [{{P}} c {{P}}], no qual [c] é o corpo do laço), mas sim que [P] 
	_junto com o fato de que a guarda do laço é verdadeira_ é uma pré-condição suficiente 
	de [c] para assegurar [P] como uma pós-condição.

    Isso é uma exigência levemente (mas significantemente) mais fraca.
    Por exemplo, se [P] é a asserção [X = 0], então [P] _é_ uma invariante 
    do loop
    WHILE X = 2 DO X := 1 END
    embora isso seja claramente _não_ preservado pelo corpo do loop.
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
(** Nós podemos utilizar a regra _while_ para provar a seguinte tripla
    de Hoare, que pode ser surpreendente ao início... *)

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
(** Neste exercício iremos adicionar um novo comando para a nossa linguagem de comandos: 
[REPEAT] c [UNTIL] a [END]. Você irá escrever a regra de avaliação para [repeat] e 
adicionar uma nova regra de Hoare para este comando. *)

Inductive com : Type :=
  | CSkip : com
  | CAsgn : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

(** [REPEAT] se comporta como [WHILE], exceto que a guarda do loop é
    checada _depois_ de cada execução do corpo, com o loop repetindo 
    tão longo quanto a guarda permaneça _falsa_. Por causa disso, o
    corpo vai sempre executar pelo menos uma vez. *)

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

(** [Diego]Adicionar novas regras para [REPEAT] no [ceval] abaixo.  Você pode 
    usar as regras para [WHILE] como guia, mas lembrar que o corpo de um 
    [REPEAT] sempre deve ser executado ao menos uma vez, e que o loop termina
    quando a guarda se torna verdadeira.  Então atualizar a tática [ceval_cases]
    para lidar com os casos adicionados.  *)

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

(** Agora declare e prove um teorema, [hoare_repeat], que expresse uma regra de prova 
apropriada para comandos [repeat]. Use [hoare_while] como um modelo, criando sua 
regra de modo mais preciso possível. *)

(* PREENCHER *)

(** Para o crédito total, tenha certeza (informalmente) que sua regra pode 
    ser usada para provar a seguinte tripla de Hoare válida:
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

(** Nesse exercício, vamos derivar regras de prova para o comando 
    [HAVOC] que foi estudado no capítulo anterior. Primeiramente, vamos 
    enclausurar esse trabalho em um módulo separado, e relembrar a sintaxe e
    a semântica big-step dos comandos Himp. *)

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
    No próximo capítulo, iremos ver como essas regras são usadas para provar que os 
    programas satisfazem as especificações de seus comportamentos.
*)


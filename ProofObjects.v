(** * ProofObjects: Trabalhando Explicitamente com Evidência em Coq *)

Require Export MoreLogic.

(* ##################################################### *)

(** Nos vimos que Coq possui mecanismos tanto para _programar_,
    utilizando tipos de dados indutivos (como [nat] e [list]) e
    funções sobre esses tipos, e para _provar  propriedades destes
    programas utilizando proposições indutivas (como [ev] e [eq]),
    implicação, e quantificação universal. Até agora, tratamos estes
    mecanismos como se fossem separados; para muitos propósitos esta
    é uma boa abordagem. Mas também encontramos indícios de que as
    facilidades de programação e de prova em Coq são estreitamente
    relacionados. Por exemplo, a palavra-chave [Inductive] é usada
    tanto para declarar tipos de dados e proposições, e [->] é utilizado
    ao mesmo tempo para enunciar o tipo das funções e para a implicação
    lógica. Isto não é um mero acaso! De fato, programas e provas em Coq
    são quase a mesma coisa. Neste capítulo, estudaremos os mecanismos
    desta similaridade.

    Já fomos confrontados com a ideia fundamental que demonstrabilidade é
    representada em Coq por _evidência  concreta. Quando nós construímos
    a demonstração de uma proposição básic, nós elaboramos de fato uma
    árvore de evidência, a qual pode ser enxergada como uma estrutura de
    dados. Se a proposição for uma implicação, como [A -> B], então a
    evidência será um _transformador_ de evidência: uma receita para 
    elaborar uma evidência para [B] a partir de uma evidência para [A].
    Essencialmente, provas são simplesmente programas que manipulam
    evidência.

*)
(**
    Q. Se evidência for um dado, o que são as proposições?

    A. Elas são tipos!

    Veja novamente a definição formal da propriedade [beautiful].  *)

Print beautiful. 
(* ==>
  Inductive beautiful : nat -> Prop :=
      b_0 : beautiful 0
    | b_3 : beautiful 3
    | b_5 : beautiful 5
    | b_sum : forall n m : nat, beautiful n -> beautiful m -> beautiful (n + m)
*)

(** *** *)

(** O truque é pronunciar "[:]" de forma diferente. Ao invés de "tem tipo",
    podemos dizer "é uma demonstração de". Por exemplo, a segunda linha da
    definição de [beautiful] afirma que [b_0: beautiful_0]. Assim, ao invés de
    "[b_0] tem tipo [beautiful 0]", podemos ler "[b_0] é uma demonstração de
    [beautiful 0]", e similarmente para [b_3] e [b_5]. *)

(** *** *)

(** Esse jogo de palavras entre tipos e proposições (entre [:] como "tem tipo"
    e [:] como "é uma demonstração de" ou "constitui evidência para") é 
    chamado a _correspondência de Curry-Howard". Ele evidencia uma conexão
    fundamental entre o mundo da lógica e o mundo da computação.
<<
                 proposições   ~  tipos
                 demonstrações ~  valores
>>
    Desta conexão decorrem vários discernimentos úteis. Para começar, 
    ela proporciona uma interpretação natual do tipo do construtor [b_sum]: *)

Check b_sum.
(* ===> b_sum : forall n m, 
                  beautiful n -> 
                  beautiful m -> 
                  beautiful (n+m) *)
(** Pode ser ido como "[b_sum] é um construtor com quatro arguments -- 
    dois números [n] e [m], e duas demonstrações, para as proposições
    [beautiful n] e [beautiful m], respectivamente -- e produz uma
    demonstraçào para a proposição [beautiful (n+m)." *)

(** Agora, vamos revisitar uma demonstração anterior envolvendo [beautiful]. *)

Theorem eight_is_beautiful: beautiful 8.
Proof.
    apply b_sum with (n := 3) (m := 5). 
    apply b_3.
    apply b_5. Qed.

(** Da mesma forma que para valores e funções ordinários, podemos executar
    o comando [Print] para ver o  objeto demonstrador  que resulta da 
    transcrição desta demonstração. *)

Print eight_is_beautiful.
(* ===> eight_is_beautiful = b_sum 3 5 b_3 b_5  
     : beautiful 8  *)

(** Tendo isto em vista, poderiamos indagar se nós mesmos podemos escrever tal
    expressão. De fato, isto é possível: *)

Check (b_sum 3 5 b_3 b_5).  
(* ===> beautiful (3 + 5) *)

(** A expressão [b_sum 3 5 b_3 b_5] pode ser interpretada como a a aplicação
    [b_sum] com seus parâmetros sendo instanciados com os argumentos específicos
    [3], [5] e os objetos de demonstração para as suas premissas, a saber
    [beautiful 3] e [beautiful 5] (Coq é programado para determinar que
    3+5=8). De forma alternativa, podemos interpretar [b_sum] como um
    "construtor de evidência" primitivo que, quando a aplicado a dois
    números específicos, precisa ainda ser aplicado à evidência que estes
    números são [beautiful]. Seu tipo, a saber
    [forall n m, beautiful n -> beautiful m -> beautiful (n+m)],
    expressar esta funcionalidade, da mesma forma que o tipo polimórfico
    [forall X, list X] visto anteriormente, expressa o fato que o
    construtor [nil] pode ser interpretado como uma função que vai dos
    tipos para as listas vazias com elementos daqueles tipos. *)

(** Logo, temos uma forma alternativa de escrever uma demonstração do que
    [8] é [beautiful]: *)

Theorem eight_is_beautiful': beautiful 8.
Proof.
   apply (b_sum 3 5 b_3 b_5).
Qed.

(** Repare que estamos aqui usando [apply] de uma nova maneira: ao invés de
    somente fornecer o _nome  de uma hipótese ou de um teorema demonstrador
    anteriormente, cujo tipo corresponde à meta atual, estamos fornecendo uma
    _expressão  que constroi diretamente evidência do tipo necessário. *)


(* ##################################################### *)
(** * Transcrição de Demonstrações e Objetos de Demonstrações *)

(** Esses objetos de demonstrações fazem parte do cerne do funcionamento do Coq.

    Quando Coq segue uma transcrição de demonstração, o que acontece
    internamente é que um objeto demonstrador vem sendo construído aos poucos
    -- um termo cujo tipo é a proposição sendo demonstrada.  As táticas entre o
    comando [Proof] e o término [Qed] indicam ao Coq como construir um termo do
    tipo requerido. Para ver este processo em ação, vamos utilizar o comando
    [Show Proof] para exibir o estado atual da árvore de demonstração em vários
    pontos da demonstração por táticas que segue. *)

Theorem eight_is_beautiful'': beautiful 8.
Proof.
   Show Proof.
   apply b_sum with (n:=3) (m:=5).
   Show Proof.
   apply b_3.
   Show Proof.
   apply b_5.
   Show Proof.
Qed.

(** A cada etapa, Coq construiu um termo com "buracos" (indicados por [?1],
    [?2], e assim sucessivamente), e também sabe qual tipo de elemento de
    evidência é necessário para preencher cada buraco. *)

(** Cada buraco corresponde a uma submeta, e a demonstração é concluída quando
    não há mais submetas. Neste ponto, o comando [Theorem] associa um nome com a
    evidência que construimos e armazena esta associação no contexto global. *)

(** Demonstrações por táticas são úteis e convenientes, porém não essenciais: em
    princípio, podemos sempre construir manualmente a evidência necessária como
    mostrado anteriormente. Podemos então utilizar [Definition] (ao invés de
    [Theorem]) para dar um nome global diretamente ao uma evidência. *)

Definition eight_is_beautiful''' : beautiful 8 :=
  b_sum 3 5 b_3 b_5.

(** Todas essas maneiras diferentes de construir uma demonstração levam 
    a salvar exatametne a mesma evidência no contexto global. *)

Print eight_is_beautiful.
(* ===> eight_is_beautiful    = b_sum 3 5 b_3 b_5 : beautiful 8 *)
Print eight_is_beautiful'.
(* ===> eight_is_beautiful'   = b_sum 3 5 b_3 b_5 : beautiful 8 *)
Print eight_is_beautiful''.
(* ===> eight_is_beautiful''  = b_sum 3 5 b_3 b_5 : beautiful 8 *)
Print eight_is_beautiful'''.
(* ===> eight_is_beautiful''' = b_sum 3 5 b_3 b_5 : beautiful 8 *)

(** **** Exercício: nível 1 (six_is_beautiful)  *)
(** Dar uma demonstração por tática e um objeto demonstrador
    comprovando que [6] é [beautiful]. *)

Theorem six_is_beautiful :
  beautiful 6.
Proof.
  (* PREENCHER *) Admitted.

Definition six_is_beautiful' : beautiful 6 :=
  (* PREENCHER *) admit.
(** [] *)

(** **** Exercício: nível 1 (nine_is_beautiful)  *)
(** Dar uma demonstração por tática e um objeto demonstrador
    comprovando que [9] é [beautiful]. *)

Theorem nine_is_beautiful :
  beautiful 9.
Proof.
  (* FILL IN HERE *) Admitted.

Definition nine_is_beautiful' : beautiful 9 :=
  (* FILL IN HERE *) admit.
(** [] *)

(* ##################################################### *)
(** * Quantificação, Implicações e Funções *)

(** No universo computacional do Coq (onde ficamos principalmente até este
    capítulo), há duas famílias de valores com setas em seus tipos:
    _constructors  introduzido em tipos definidos indutivamente (através de
    [Inductive]), e funções.

    Similarmente, no universo lógico de Coq, há duas maneiras de prover
    evidência para uma implicação: construtores introduzidos por proposições
    definidas indutivamente (através de [Inductive]), e... funções!

    Por exemplo, considere esta afirmação: *)

Theorem b_plus3: forall n, beautiful n -> beautiful (3+n).
Proof.
   intros n H.
   apply b_sum.
   apply b_3.
   apply H.
Qed.

(** Qual é o objeto demonstrador correspondente a [b_plus3]? 

    Estamos procurando uma expressão cujo _tipo  é [forall n, beautiful n ->
    beautiful (3+n)] -- isto é, uma _função_ que tem dois argumentos (um número
    e um elemento de evidência e retorna um elemento de evidência!  Eis ela: *)

Definition b_plus3' : forall n, beautiful n -> beautiful (3+n) := 
  fun (n : nat) => fun (H : beautiful n) =>
    b_sum 3 n b_3 H.

Check b_plus3'.
(* ===> b_plus3' : forall n : nat, beautiful n -> beautiful (3+n) *)

(** Lembre que [fun n => blah] significa "a função que, dado [n], retorna
    [blah]."  Uma outra forma, equivalente, de escrever esta definição é: *)

Definition b_plus3'' (n : nat) (H : beautiful n) : beautiful (3+n) := 
  b_sum 3 n b_3 H.

Check b_plus3''.
(* ===> b_plus3'' : forall n, beautiful n -> beautiful (3+n) *)

(** Quando enxergamos a proposição sendo provada por [b_plus3] como um tipo
    função, um dos seus aspectos pode parecer um pouco inusitado.  O tipo do
    segundo argumento é [beautiful n], e inclui o _valor_ do primeiro argumento
    [n]. Embora tais _tipos dependentes  não se encontram normalmente em
    linguagens de programação, mesmo linguagens funcionais como ML e Haskell,
    eles poderiam ser úteis nelas também.

    Observe que tanto a implicação ([->]) quanto a quantificação ([forall])
    correspondem a funções sobre evidência. De fato, são essencialmente a
    mesma coisa: [->] é apenas um atalho para um uso degenerado de
    [forall] onde não há dependência, ou seja, não é necessário dar um nome
    ao tipo no lado esquerdo da seta. *)

(** Por exemplo, considere a proposição seguinte: *)

Definition beautiful_plus3 : Prop := 
  forall n, forall (E : beautiful n), beautiful (n+3).

(** Um termo de demonstração habitando esta proposição seria uma função com dois
    argumentos: [n], um número, e [E], uma evidência que [n] é [beautiful].
    Mas o nome [E] para esta evidência não é usado no resto da afirmação, portanto
    é um bobo se dar o trabalho de lhe dar um nome. Nós poderiamos ter escrito
    assim, utilizando o identificador coringa [_] ao invés de um verdadeiro nome: *)

Definition beautiful_plus3' : Prop := 
  forall n, forall (_ : beautiful n), beautiful (n+3).

(** Ou, de forma equivalente, podemos escrever em uma notação mais comun: *)

Definition beatiful_plus3'' : Prop :=
  forall n, beautiful n -> beautiful (n+3). 

(** Em geral, "[P -> Q]" é apenas açúcar sintático para "[forall (_:P), Q]". *)


(** **** Exercício: nível 2 b_times2  *)

(** Fornecer um objeto demonstrador correspondente ao teorema [b_times2] oriundo de Prop.v *)

Definition b_times2': forall n, beautiful n -> beautiful (2*n) :=
  (* PREENCHER *) admit.
(** [] *)


(** **** Exercise: nível 2, opcional (gorgeous_plus13_po)  *) 
(** Elaborar um objeto demonstrativo correspondente ao teorema [gorgeous_plus13] oriundo de Prop.v *)

Definition gorgeous_plus13_po: forall n, gorgeous n -> gorgeous (13+n):=
   (* PREENCHER *) admit.
(** [] *)

(** É bastante revelador acompanhar os objetos demonstrativos 
    envolvendo os conectores lógics que definimos com proposições
    indutivas em Logic.v. *)

Theorem and_example : 
  (beautiful 0) /\ (beautiful 3).
Proof.
  apply conj.
   (* Case "left". *)  apply b_0.
   (* Case "right". *)  apply b_3.  Qed.

(** Vamos dar uma olhada ao objeto demonstrativo deste teorema. *)

Print and_example. 
(* ===>  conj (beautiful 0) (beautiful 3) b_0 b_3
            : beautiful 0 /\ beautiful 3 *)

(** Note que a demonstração tem a forma
    conj (beautiful 0) (beautiful 3) 
         (...dem de beautiful 3...) (...dem de beautiful 3...)
    como esperado, dado o tipo de [conj]. *)

(** **** Exercício: nível 1, opcional (case_proof_objects)  *)
(** As táticas [Case] foram comentadas na demonstração de [and_example]
    para evitar de bagunçar o objeto demonstrativo. Como que você acha
    que o objeto demonstrativo parecerá se tiramos essas táticas dos
    comentários? Tente e veja por você mesmo. *)
(** [] *)

Theorem and_commut : forall P Q : Prop, 
  P /\ Q -> Q /\ P.
Proof.
  intros P Q H.
  inversion H as [HP HQ]. 
  split.  
    (* Case "left". *) apply HQ. 
    (* Case "right". *) apply HP.  Qed.

(** Novamente, comentamos as táticas [Case] para facilitar a leitura do objeto
    demonstrador desse teorema. Ainda é um pouco complicado, mas após
    efetuar alguns passos de redução, podemos ver que tudo que está acontecendo
    é desmontar um registro contendo evidência para [P] e para [Q] e remontar
    ele na ordem oposta: *)

Print and_commut.
(* ===>
    and_commut = 
      fun (P Q : Prop) (H : P /\ Q) =>
        (fun H0 : Q /\ P => H0)
            match H with
            | conj HP HQ => (fun (HP0 : P) (HQ0 : Q) => conj Q P HQ0 HP0) HP HQ
            end
      : forall P Q : Prop, P /\ Q -> Q /\ P *)

(** Após reduzir as aplicações diretas de expressões [fun] aos seus
    argumentos, obtemos: *)

(* ===> 
   and_commut = 
     fun (P Q : Prop) (H : P /\ Q) =>
     match H with
     | conj HP HQ => conj Q P HQ HP
     end 
     : forall P Q : Prop, P /\ Q -> Q /\ P *)



(** **** Exercício: nível 2, opcional (conj_fact)  *)
(** Construir um objeto demonstrador para a proposição seguinte. *)

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  (* PREENCHER *) admit.
(** [] *)


(** **** Exercício: nível 2, avançado, opcional (beautiful_iff_gorgeous)  *)

(** Nós mostramos que as famílias de proposições [beautiful] e [gorgeous]
    caracterizam o mesmo conjunto de números.  Demonstrar que [beautiful n <->
    gorgeous n] para todo [n].  Como desafio, escrever a demonstração como um
    objeto demonstrativo, ao invés de usar táticas. (_Dica : caso você use
    teoremas já definidos, você só deve necessitar de uma única linha!) *)

Definition beautiful_iff_gorgeous :
  forall n, beautiful n <-> gorgeous n :=
  (* PREENCHER *) admit.
(** [] *)


(** **** Exercício: nível 2, opcional (or_commut'')  *)
(** Escrever um objeto demonstrador para [or_commut] (sem utilizar [Print]
    para espiar aqueles que já definimos!) *)

(* PREENCHER *)
(** [] *)

(** Lembre que modelamos uma propriedade existencial como um par composto por
    um valor testemunho e por uma demonstração que o testemunho satisfaz a
    propriedade. Podemos escolher de construir a prova explicitamente.

    Por exemplo, considere esta proposição existencialmente quantificada: *)
Check ex.

Definition some_nat_is_even : Prop := 
  ex _ ev.

(** Para demonstrar esta proposição, precisamos escolher um número em particular
    como testemunho -- digamos, 4 -- e prover a evidência que este número é
    [even] (par). *)

Definition snie : some_nat_is_even := 
  ex_intro _ ev 4 (ev_SS 2 (ev_SS 0 ev_0)).


(** **** Exercício: nível 2, opcional (ex_beautiful_Sn)  *)
(** Termine a definição do objeto demonstrador seguinte: *)

Definition p : ex _ (fun n => beautiful (S n)) :=
(* PREENCHER *) admit.
(** [] *)



(* ##################################################### *)
(** * Argumentos Explícitos para Lemas e Hipóteses *)

(** Mesmo quando nós usamos demonstrações utilizando táticas, pode ser
    útil entender a natureza funcional subjacente das implicações e das
    quantificações.

    Por exemplo, é frequentemente conveniente aplicar [apply] ou [rewrite] com
    um lema o hipótese tendo um ou mais quantificadores já instanciados de forma
    a poder direcionar o resultado. Por exemplo: *)

Check plus_comm.
(* ==> 
    plus_comm
     : forall n m : nat, n + m = m + n *)

Lemma plus_comm_r : forall a b c, c + (b + a) = c + (a + b).
Proof.
   intros a b c.
   (* rewrite plus_comm. *) 
      (* aplica-se na primeira posição disponível; não é o que queremos *)
   rewrite (plus_comm b a).  (* direciona a reescrita na posição certa *)
   reflexivity.  Qed.


(** Neste caso, fornecer apenas um argumento teria sido suficiente. *)

Lemma plus_comm_r' : forall a b c, c + (b + a) = c + (a + b).
Proof.
   intros a b c.
   rewrite (plus_comm b). 
   reflexivity.  Qed.

(** Os argumentos devem ser listados na ordem, mas coringas (_)
    podem ser utilizados para pular argumentos que Coq pode deduzir.  *)

Lemma plus_comm_r'' : forall a b c, c + (b + a) = c + (a + b).
Proof.
  intros a b c.
  rewrite (plus_comm _ a).
  reflexivity. Qed.

(** O autor de um lema pode escolher de declarar como implícitos os argumentos
    passíveis de serem deduzidos, da mesma forma que com funções e construtores.

    As cláusulas [with] que já encontramos são apenas uma forma de especificar
    os argumentos selecionados por nome, e não por posição:  *)

Lemma plus_comm_r''' : forall a b c, c + (b + a) = c + (a + b).
Proof.
  intros a b c.
  rewrite plus_comm with (n := b). 
  reflexivity. Qed.


(** **** Exercício: nível 2 (trans_eq_example_redux)  *)
(** Refazer a demonstração do teorema seguinte (oriundo de MoreCoq.v) com um
    [apply] de [trans_eq] mas _sem  utilizar uma cláusula [with]. *)

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  (* PREENCHER *) Admitted.
(** [] *)



(* ##################################################### *)
(** * Programação com Táticas (Avançado) *)

(** Se podemos construir demonstrações com termos explícitos ao invés
    de táticas, talvez você está se questionando se podemos construir
    programas que utilizam táticas ao invés de termos explícitos.
    Certamente! *)

Definition add1 : nat -> nat. 
intro n. 
Show Proof.
apply S. 
Show Proof.
apply n. Defined.

Print add1. 
(* ==>
    add1 = fun n : nat => S n
         : nat -> nat
*)

Eval compute in add1 2. 
(* ==> 3 : nat *)

(** Note que terminamos com [Definition] com um [.] ao invés de [:=] seguido de
    um termo. Isso instrui Coq para entrar em modo de transcrição de
    demonstração de forma a construir um objeto do tipo [nat -> nat]. Também
    terminamos a demonstração com [Defined] ao invés de [Qed]; isto torna a
    definição _transparente  de tal forma que pode ser utilizado em computações
    como uma função definida de maneira usual.

    Esta possibilidade é principalmente útil para escrever funções com tipos
    dependentes, mas não adiantaremos muito mais este aspecto neste
    livro. Contudo é uma boa forma de ilustrar a uniformidade e ortogonalidade
    das ideias fundamentais em Coq. *)


(** * Logic: Lógica em Coq *)

Require Export MoreCoq. 



(** A lógica embutida no Coq é muito simples: as únicas primitivas são
    as definições indutivas ([Inductive]), a quantificação universal ([forall])
    e a implicação ([->]). Todos os demais conectores lógicos -- conjunção,
    disjunção, negação, quantificação existencial, e até a igualdade -- podem
    ser codificados a partir desta base.

    Esse capítulo explica essas codificações e mostra como as táticas 
    que temos aprendido podem ser usadas para implementar formas padronizadas
    de raciocínio lógico envolvendo esses conectivos.

*)

(* ########################################################### *)
(** * Proposições *)

(** Nos capítulos anteriores, nós vimos vários exemplos de alegações
    fatuais (_proposições_) e meios de apresentar evidências das suas
    verdades (_demonstrações_).  Em particular, nós temos trabalhados
    extensivamente com _proposições de igualdades_ da forma [e1 = e2],
    com implicações ([P -> Q]), e com proposições quantificadas
    ([forall x, P]).  *)


(** Em Coq, o tipo das coisas que são (potencialmente) passíveis de
   serem demonstradas é [Prop]. *)

(** Eis um exemplo de uma proposição demonstrável: *)

Check (3 = 3).
(* ===> Prop *)

(** Abaixo se encontra um exemplo de proposição impossível de ser demonstrada: *)

Check (forall (n:nat), n = 2).
(* ===> Prop *)

(** Lembre que o comando [Check] solicita ao Coq informar o tipo da
    expressão fornecida. *)

(* ########################################################### *)
(** * Demonstrações e Evidência *)

(** Em Coq, proposições tem o mesmo status que outros tipos, como
    [nat].  Assim como os números naturais [0], [1], [2], etc. habitam
    o tipo [nat], uma proposição Coq [P] é habitada por suas demonstrações
    (_proofs_). Nós vamos referenciar esses habitantes como expressão
    demonstradora (_proof term_) ou objeto demonstrador (_proof
    object_) ou evidência (_evidence_) para a verdade de [P].

    Em Coq, quando nós afirmamos e então demonstramos um lema como:

Lemma silly : 0 * 3 = 0.  
Proof. reflexivity. Qed.

    As táticas que nós usamos dentro das palavras chaves
    [Proof]...[Qed] diz para Coq como construir um termo demonstrador
    que habita a proposição. Neste caso, a proposição [0 * 3 = 0] é
    justificado por uma combinação da _definição_ de [mult], a qual
    diz que [0 * 3] é _simplificado_ apenas para [0], e o princípio da
    igualdade, _reflexividade_, que diz que [0 = 0].

*)

(** *** *)

Lemma silly : 0 * 3 = 0.
Proof. reflexivity. Qed.

(** Podemos ver que expressão demonstradora Coq constrói para um dado
    lema usando a diretiva [Print]: *)

Print silly.
(* ===> silly = eq_refl : 0 * 3 = 0 *)

(** Aqui, a expressão demonstradora [eq_refl] testemunha a
    igualdade. (Depois haverá mais sobre igualdades!)*)

(** ** Implicações _são_ Funções *)

(** Da mesma forma que a multiplicação entre números naturais pode ser
    implementada como uma função:

[
mult : nat -> nat -> nat 
]

    a expressão demonstradora para uma implicação [P -> Q] é uma
    função que tem uma evidência para [P] como entrada e produz umn
    evidência para [Q] como saída.
*)

Lemma silly_implication : (1 + 1) = 2  ->  0 * 3 = 0.
Proof. intros H. reflexivity. Qed.

(** Nós podemos ver que a expressão demonstradora do lema abaixo é de fato
    uma função: *)

Print silly_implication.
(* ===> silly_implication = fun _ : 1 + 1 = 2 => eq_refl
     : 1 + 1 = 2 -> 0 * 3 = 0 *)

(** ** Definição de Proposições *)

(** Assim como podemos criar tipo indutivos definidos 
    pelo usuário (como as listas, representação binária de números naturais, 
    etcs., que nós vimos antes), nós também podemos criar proposições _definidos
    pelo usuário_.

    Pergunta: Como você define o significado de uma proposição?  
*)

(** *** *)

(** O significado de uma proposição é dada pelas _regras_ e
    _definições_ que afirmam como construir uma _evidência_ para a
    verdade da proposição a partir de outra evidência.

    - Tipicamente, regras são definidas _indutivamente_, como qualquer outro
    tipo de dados.

    - Algumas vezes uma proposição é declarada verdade sem evidências
    substanciais. Essas proposições são chamadas de axiomas (_axioms_).

    Neste, e nos capítulos subsequentes, nós veremos de maneira mais detalhada
    mais sobre como essas expressões demonstradoras funcionam.
*)

(* ########################################################### *)
(** * Conjunção ("e" Lógico) *)

(** A conjunção lógica de proposições [P] e [Q] pode ser representada
    usando uma definição [Inductive] com um construtor. *)

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q). 

(** A intuição por trás dessa definição é simples: para construir 
    evidência para [and P Q], devemos fornecer evidência para [P] 
    e evidência para [Q]. Mais precisamente:
    
    - [conj p q] pode ser tomada como uma evidência para [and P Q] se [p] for 
    evidência para [P] e [q] for evidência para [Q]; e

    - essa é a _única  maneira de constituir evidência para [and P Q] --
    isto é, se for fornecida alguma evidência para [and P Q], sabemos que
    deve ter a forma [conj p q], onde [p] é evidência para [P] e [q] é
    evidência para  [Q]. 

    Como nós usaremos bastante conjunção, vamos introduzir uma notação
    mais familiar para isso. *)

Notation "P /\ Q" := (and P Q) : type_scope.

(** (A anotação [type_scope] diz ao Coq que essa notação
    irá aparecer em proposições, não em valores.) *)

(** Considere o "tipo" do construtor [conj]: *)

Check conj.
(* ===>  forall P Q : Prop, P -> Q -> P /\ Q *)

(** Observe que tem quatro entradas -- a saber, as proposições [P] 
    e [Q] e evidências para [P] e [Q] -- e retorna como saída a 
    evidência de [P /\ Q]. *)

(** ** "Introdução" de conjunções *)

(** Além da elegância de construir tudo a partir de uma fundação
    minúscula, definir conjunção desta maneira permite demonstrar
    sentenças envolvendo conjunções usando as táticas que já
    conhecemos. Por exemplo, se a sentença da meta for uma conjunção,
    podemos demonstrá-la aplicando o construtor simples [conj] (como
    pode ser visto a partir do tipo de [conj]), solucionando a meta
    atual e deixando as duas partes da conjunção como submetas a serem
    demonstradas separadamente. *)

Theorem and_example : 
  (0 = 0) /\ (4 = mult 2 2).
Proof.
  apply conj.
  Case "left". reflexivity.
  Case "right". reflexivity.  Qed.

(** Como mera facilidade, podemos utilizar a tática [split] como atalho para
    [apply conj]. *)

Theorem and_example' : 
  (0 = 0) /\ (4 = mult 2 2).
Proof.
  split.
    Case "left". reflexivity.
    Case "right". reflexivity.  Qed.

(** ** "Eliminação" de conjunções *)

(** Reciprocamente, a tática [destruct] pode ser usada para utilizar uma
    hipótese conjunção no contexto, calcular que evidência deve ter sido
    utilizada para construir ela, e adicionar variáveis representando essa
    evidência ao contexto. *)

Theorem proj1 : forall P Q : Prop, 
  P /\ Q -> P.
Proof.
  intros P Q H.
  destruct H as [HP HQ]. 
  apply HP.  Qed.

(** **** Exercício: nível 1, opcional (proj2)  *)
Theorem proj2 : forall P Q : Prop, 
  P /\ Q -> Q.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

Theorem and_commut : forall P Q : Prop, 
  P /\ Q -> Q /\ P.
Proof.
  (* REALIZADO EM SALA *)
  intros P Q H.
  destruct H as [HP HQ]. 
  split.  
    Case "left". apply HQ. 
    Case "right". apply HP.  Qed.

(** **** Exercício: nível 2 (and_assoc)  *)
(** Na demonstração a seguir, notar como o _aninhamento padrão_ no
    [destruct] quebra a hipótese [H : P /\ (Q /\ R)] em
    [HP: P], [HQ : Q], and [HR : R]. Concluir a demonstração a partir
    desse ponto: *)

Theorem and_assoc : forall P Q R : Prop, 
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  destruct H as [HP [HQ HR]].
(* PREENCHER *) Admitted.
(** [] *)



(* ###################################################### *)
(** * Se e Somente Se *)

(** O conectivo "se e somento se" é apenas a conjunção de duas implicações. *)

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q) 
                      (at level 95, no associativity) 
                      : type_scope.

Theorem iff_implies : forall P Q : Prop, 
  (P <-> Q) -> P -> Q.
Proof.  
  intros P Q H. 
  destruct H as [HAB HBA]. apply HAB.  Qed.

Theorem iff_sym : forall P Q : Prop, 
  (P <-> Q) -> (Q <-> P).
Proof.
  (* REALIZADO EM SALA *)
  intros P Q H. 
  destruct H as [HAB HBA].
  split.
    Case "->". apply HBA.
    Case "<-". apply HAB.  Qed.

(** **** Exercício: nível 1, opcional (iff_properties)  *)
(** Usando a demonstração acima de que [<->] é simétrico ([iff_sym]) 
    como um guia, demonstrar que também é reflexivo e transitivo. *)

Theorem iff_refl : forall P : Prop, 
  P <-> P.
Proof. 
  (* PREENCHER *) Admitted.

Theorem iff_trans : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  (* PREENCHER *) Admitted.

(** Dica: se você possui uma hipótese com uma bi-implicação no
    contexto, você pode usar [inversion] para quebrá-la em duas
    implicações separadas. (Aproveite para refletir por que isto
    funciona desta forma.) *)
(** [] *)


(** Algumas das táticas Coq tratam afirmações [iff] de maneira especial,
    eliminando a necessidade de raciocinar sobre elas para algumas 
    manipulações de baixo nível. Em particular, [rewrite] pode ser utilizada
    com afirmações [iff], e não somente igualdades. *)

(* ############################################################ *)
(** * Disjunção ("ou" Lógico) *)

(** ** Implementação da Disjunção *)

(** Disjunção ("ou lógico") pode ser também definido como proposição
    indutiva. *)

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q. 

Notation "P \/ Q" := (or P Q) : type_scope.

(** Considere o "tipo" do construtor [or_introl]: *)

Check or_introl.
(* ===>  forall P Q : Prop, P -> P \/ Q *)

(** Tem três entradas, a saber as proposições [P], [Q] e evidência de
    [P], e retorna, como saída, a evidência de [P \/ Q]. Em seguida,
    analize o tipo de [or_intror]: *)

Check or_intror.
(* ===>  forall P Q : Prop, Q -> P \/ Q *)

(** É similar a [or_introl] mas requer evidência para [Q] em vez de
    evidência para [P]. *)

(** Intuitivamente, aqui estão duas formas de fornecer uma evidência
    para [P \/ Q]:

    - Dê evidência para [P] (e informa que está fornecendo evidência
      para [P] -- isto é o papel do construtir [or_introl]), ou

    - Dê evidência para [Q], marcada com o constutor [or_intror]. *)

(** *** *)
(** Como [P \/ Q] possui dois construtores, realizar um [destruct] em
    uma hipótese do tipo [P \/ Q] gera duas submetas. *)

Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  destruct H as [HP | HQ].
    Case "left". apply or_intror. apply HP.
    Case "right". apply or_introl. apply HQ.  Qed.

(** Daqui em diante, nós usaremos as táticas [left] e [right]
    nós lugar de [apply or_introl] e [apply or_intror]. *)

Theorem or_commut' : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  destruct H as [HP | HQ].
    Case "left". right. apply HP.
    Case "right". left. apply HQ.  Qed.

Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof. 
  intros P Q R. intros H. destruct H as [HP | [HQ HR]]. 
    Case "left". split.
      SCase "left". left. apply HP.
      SCase "right". left. apply HP.
    Case "right". split.
      SCase "left". right. apply HQ.
      SCase "right". right. apply HR.  Qed.

(** **** Exercício: nível 2 (or_distributes_over_and_2)  *)
Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 1, opcional (or_distributes_over_and)  *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(* ################################################### *)
(** ** Relacionando [/\] e [\/] com [andb] e [orb] *)

(** Nós já vimos em várias oportunidades que estruturas análogas podem
    ser encontradas nos mundos computacional ([Type]) e lógico
    ([Prop]) de Coq. Mais um caso semelhante é que os operadores
    booleanos [andb] e [orb] são claramente análogos dos conectivos
    lógicos [/\] e [\/]. Essa analogia pode ser tornada mais precisa
    através dos seguintes teoremas, que mostram como traduzir
    conhecimento sobre os comportamentos de [andb] e [orb] para certas
    entradas, em fatos proposicionais sobre essas entradas. *)

Theorem andb_prop : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  (* REALIZADO EM SALA *)
  intros b c H.
  destruct b.
    Case "b = true". destruct c.
      SCase "c = true". apply conj. reflexivity. reflexivity.
      SCase "c = false". inversion H.
    Case "b = false". inversion H.  Qed.

Theorem andb_true_intro : forall b c,
  b = true /\ c = true -> andb b c = true.
Proof.
  (* REALIZADO EM SALA *)
  intros b c H.
  destruct H.
  rewrite H. rewrite H0. reflexivity. Qed.

(** **** Exercício: nível 2, opcional (andb_false)  *)
Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof. 
  (* PREENCHER *) Admitted.

(** **** Exercício: nível 2, opcional (orb_false)  *)
Theorem orb_prop : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  (* PREENCHER *) Admitted.

(** **** Exercício: nível 2, opcional (orb_false_elim)  *)
Theorem orb_false_elim : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof. 
  (* PREENCHER *) Admitted.
(** [] *)



(* ################################################### *)
(** * Falsidade *)

(** Falsidade lógica pode ser representada no Coq como uma proposição
    definida indutivamente sem nenhum construtor.*)

Inductive False : Prop := . 

(** Explicação intuitiva: [False] é uma proposição para qual não existe
    nenhuma maneira de construir alguma evidência. *)

(** Como [False] não tem construtores, inverter uma suposição do tipo [False]
    sempre resulta em zero sumbetas, permitindo-nos demonstrar imediatamente toda 
    meta. *)

Theorem False_implies_nonsense :
  False -> 2 + 2 = 5.
Proof. 
  intros contra.
  inversion contra.  Qed. 

(** Como isso funciona? A tática [inversion] quebra [contra] em cada um dos
    seus possíveis casos, e gera uma submeta para cada caso. Como [contra] é
    evidência para [False], ela _não_ tem casos possíveis, conseqüentemente,
    não tem casos possíveis na submeta e a demonstração está feita. *)

(** *** *)
(** Reciprocamente, o único jeito de demonstrar [False] é se já existe 
    algo sem sentido ou contraditório no contexto: *)

Theorem nonsense_implies_False :
  2 + 2 = 5 -> False.
Proof.
  intros contra.
  inversion contra.  Qed.

(** Na verdade, uma vez que a demonstração de [False_implies_nonsense] na 
    verdade não tem nada a ver com a afirmação específica sem sentido 
    que está sendo demonstrada, ela pode ser facilmente generalizada 
    para funcionar para um [P] arbitrário: *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* REALIZADO EM SALA *)
  intros P contra.
  inversion contra.  Qed.

(** A expressão latina _ex falso quodlibet_ significa, literalmente,
    "a partir de uma contradição, qualquer coisa segue." Esse teorema
    também conhecido como o _princípio da explosão_. *)

(* #################################################### *)
(** ** Veracidade *)

(** Uma vez que definimos falsidade em Coq, podemos indagar se é possível
    definir veracidade de uma forma semelhante. A respostsa é sim. *)

(** **** Exercício: nível 2, avançado (True)  *)
(** Definir [True] como outra proposição definida indutivamente. (A intuição
    é que [True] deve ser uma proposição para a qual é trivial dar evidência). *)

(* PREENCHER *)
(** [] *)

(** Entretanto, diferentemente de [False], o qual vamos utilizar 
    extensivamente, [True] é utilizado muito raramente. Por si própria, ela é
    trivial (e portanto desinteressante) para demonstrar como uma meta, e carrega
    informação inútil como uma hipótese. Mas ela pode ser útil ao definir
    [Prop]s complexos utilizando condicionais, ou como um parâmetro para 
    [Prop]s de ordem superior. *)

(* #################################################### *)
(** * Negação *)

(** O complemento lógico da proposição [P] é escrito [not
    P] ou, pelo atalho, [~P]: *)

Definition not (P:Prop) := P -> False.

(** A intuição é que, se [P] não é verdade, então qualquer coisa 
    (até mesmo [False]) segue da suposição de [P]. *)

Notation "~ x" := (not x) : type_scope.

Check not.
(* ===> Prop -> Prop *)

(** É preciso um pouco de prática para se acostumar a trabalhar com
    negação no Coq. Mesmo que você consiga ver perfeitamente por que
    um certo fato é verdadeiro pode ser, a princípio, um pouco difícil
    organizar as coisas para que o Coq possa enxergar uma solução!
    Abaixo se encontram demonstrações de algumas propriedadess
    familiares a respeito de negação para lhe aquecer. *)

Theorem not_False : 
  ~ False.
Proof.
  unfold not. intros H. inversion H.  Qed.

(** *** *)
Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof. 
  (* REALIZADO EM SALA *)
  intros P Q H. destruct H as [HP HNA]. unfold not in HNA. 
  apply HNA in HP. inversion HP.  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* REALIZADO EM SALA *)
  intros P H. unfold not. intros G. apply G. apply H.  Qed.

(** **** Exercício: nível 2, avançado (double_neg_inf)  *)
(** Escreva uma demonstração informal de  [double_neg]:

   _Teorema_: [P] implica [~~P], para qualquer proposição [P].

   _Demonstração_:
(* PREENCHER *)
   []
*)

(** **** Exercício: nível 2 (contrapositive)  *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 1 (not_both_true_and_false)  *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof. 
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 1, avançado (informal_not_PNP)  *)
(** Escreva uma demonstração informal (em inglês) da proposição [forall P
    : Prop, ~(P /\ ~P)]. *)

(* PREENCHER *)
(** [] *)

(** *** Lógica Construtiva *)
(** Note que alguns teoremas que são verdadeiros em lógica clássica
    _não_ são demonstráveis na lógica (construtiva) do Coq.  Por
    exemplo, vamos observar como a demonstração seguinte fica travada... *)

Theorem classic_double_neg : forall P : Prop,
  ~~P -> P.
Proof.
  (* REALIZADO EM SALA *)
  intros P H. unfold not in H. 
  (* E agora? Não tem como inventar evidência para [~P] 
     a partir de evidência para [P]. *) 
  Abort.

(** **** Exercício: 5 stars, avançado, opcional (classical_axioms)  *)
(** Para aqueles que gostam de um desafio, aqui está um exercício
    tirado do livro Coq'Art (p. 123). As cincos sentenças seguintes
    são frequentemente consideradas como caracterização de lógica
    clássica (em contraste com a lógica construtiva, a qual é o que é
    "construído" em Coq). Nós podemos adicionar qualquer uma delas
    como um axioma não-demonstrado se nós desejamos trabalhar com
    lógica classica. Demonstre que essas cincos proposições são
    equivalentes. *)

Definition peirce := forall P Q: Prop, 
  ((P->Q)->P)->P.
Definition classic := forall P:Prop, 
  ~~P -> P.
Definition excluded_middle := forall P:Prop, 
  P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop, 
  ~(~P /\ ~Q) -> P\/Q.
Definition implies_to_or := forall P Q:Prop, 
  (P->Q) -> (~P\/Q). 

(* PREENCHER *)
(** [] *)

(** **** Exercício: nível 3 (excluded_middle_irrefutable)  *)
(** Este teorema implica que é sempre seguro adicionar um axioma de
    decidibilidade (ou seja, uma instância do terceiro excluído) para
    qualquer Prop [P] _particular_. Por quê? Porque nós não podemos
    demonstrar a negação de tal axioma; se pudéssemos, teríamos tanto [~
    (P \/ ~P)] e [~ ~ (P \/ ~P)], uma contradição.

 *)

Theorem excluded_middle_irrefutable:  forall (P:Prop), ~ ~ (P \/ ~ P).  
Proof.
  (* PREENCHER *) Admitted.


(* ########################################################## *)
(** ** Desigualdade *)

(** Afirmar [x <> y] é apenas o mesmo que afirmar [~(x = y)].

Notation "x <> y" := (~ (x = y)) : type_scope.

(** Como a desigualdade envolve a negação, também necessita de um
    pouco de prática para ser apto a trabalhar com ela de forma
    fluente. Tem um truque muito útil. Caso esteja tentando demonstrar
    uma meta sem sentido (por exemplo, se a meta é  [false = true]),
    aplique o lema [ex_falso_quodlibet] para alterar esta meta para
    [False]. Isto torna mais fácil utilizar as hipóteses da forma [~P]
    que são disponíveis no contexto -- em particular, hipóteses da
    forma [x<>y]. *)

Theorem not_false_then_true : forall b : bool,
  b <> false -> b = true.
Proof.
  intros b H. destruct b.
  Case "b = true". reflexivity.
  Case "b = false".
    unfold not in H.  
    apply ex_falso_quodlibet.
    apply H. reflexivity.   Qed.


(** *** *)

(** *** *)

(** *** *)

(** *** *)

(** *** *)

(** **** Exercício: nível 2 (false_beq_nat)  *)
Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof. 
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 2, opcional (beq_nat_false)  *)
Theorem beq_nat_false : forall n m,
  beq_nat n m = false -> n <> m.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)



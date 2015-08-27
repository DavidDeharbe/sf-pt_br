(** * Indução: Prova por Indução *)
 

(** A próxima linha importa todas as nossas definições do capítulo anterior. *)

Require Export Basics.

(** For it to work, you need to use [coqc] to compile [Basics.v]
    into [Basics.vo].  (This is like making a .class file from a .java
    file, or a .o file from a .c file.)
  
    Here are two ways to compile your code:
  
     - CoqIDE:
   
         Open [Basics.v].
         In the "Compile" menu, click on "Compile Buffer".
   
     - Command line:
   
         Run [coqc Basics.v]

    *)

(** * Nomeando Casos *)

(** [Dalay] The fact that there is no explicit command for moving from
    one branch of a case analysis to the next can make proof scripts
    rather hard to read.  In larger proofs, with nested case analyses,
    it can even become hard to stay oriented when you're sitting with
    Coq and stepping through the proof.  (Imagine trying to remember
    that the first five subgoals belong to the inner case analysis and
    the remaining seven cases are what remains of the outer one...)
    Disciplined use of indentation and comments can help, but a better
    way is to use the [Case] tactic. *)

(** [Case] (_Caso_) não é predefinido no Coq: é preciso definí-lo.
    Não existe necessidade de entender os detalhes desta definição -- você 
    pode somente 
    pular a definição e ir direto para o exemplo que a segue.  _Case_ utiliza algumas
    ferramentas do Coq que ainda não foram discutidas -- a biblioteca de
    cadeias de caracteres (somente para a sintaxe concreta das cadeias de caracteres citadas) e o comando
    [Ltac], que permite a declaração de táticas costumizadas.  Muitos elogios
    para Aaron Bohannon por esse ótimo truque! *)

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.
(** Aqui está um exemplo de como [Case] é usado.  Veja a prova a seguir e
    observe como o contexto muda. *)

Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".  (* <----- aqui *)
    reflexivity.
  Case "b = false".  (* <---- e aqui *)
    rewrite <- H. 
    reflexivity.  
Qed.

(** [Francisco] [Case] does something very straightforward: It simply adds a
    string that we choose (tagged with the identifier "Case") to the
    context for the current goal.  When subgoals are generated, this
    string is carried over into their contexts.  When the last of
    these subgoals is finally proved and the next top-level goal
    becomes active, this string will no longer appear in the context
    and we will be able to see that the case where we introduced it is
    complete.  Also, as a sanity check, if we try to execute a new
    [Case] tactic while the string left by the previous one is still
    in the context, we get a nice clear error message.
	
    Para as análises aninhadas de casos (por exemplo, quando nós queremos 
    usar um [destruct] para resolver uma meta que também foi gerada 
    por um [destruct]), há uma tática de "subcaso" [SCase]. *)

(** **** Exercício 2: ** (andb_true_elim2)  *)
(** Provar [andb_true_elim2], marcando casos (e subcasos) quando
    você usar [destruct]. *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  (* PREENCHER AQUI *) Admitted.
(** [] *)

(** Não existem regras rígidas e rápidas para como as provas devem ser
 formatadas no Coq -- em particular, sobre onde as linhas devem ser
 quebradas e como seções da prova deveriam ser indentadas para indicar
 suas estruturas aninhadas. Porém, se os lugares onde múltiplas metas
 são geradas estão marcadas com táticas [Case] explícitas no início
 das linhas, então a prova será legível independentemente de quais escolhas
 foram feitas sobre outros aspectos do layout.

      Este é um bom lugar para mencionar um outro (possivelmente óbvio) conselho
      sobre comprimentos de linha. Usuários iniciantes em Coq às vezes tendem
      aos extremos, seja escrevendo cada tática em uma nova linha ou provas
      inteiras em uma linha. Um bom estilo encontra-se entre os dois extremos.
      Em particular, uma convenção razoável é limitar -se a linhas de 80
      caracteres. Linhas com mais do que isso são difíceis de ler e podem ser
      inconvenientes para exibir e imprimir. Muitos editores têm recursos que
      ajudam a reforçar isso.

(** * Prova por Indução *)

(** [Dalay]We proved in the last chapter that [0] is a neutral element
    for [+] on the left using a simple argument.  The fact that it is
    also a neutral element on the _right_... *)

Theorem plus_0_r_firsttry : forall n:nat,
  n + 0 = n.

(** ... cannot be proved in the same simple way.  Just applying
  [reflexivity] doesn't work: the [n] in [n + 0] is an arbitrary
  unknown number, so the [match] in the definition of [+] can't be
  simplified.  *)

Proof.
  intros n.
  simpl. (* Does nothing! *)
Abort.

(** *** *)

(** E o raciocíonio utilizando [destruct n] não nos leva
    muito mais longe: conseguimos fechar o ramo da análise de caso em 
    que é assumido [n = 0], mas o ramo em que [n = S n'] para qualquer [n'] 
    ficamos bloqueados da mesma maneira.  Nós podemos usar [destruct n'] para
    ir um passo adiante, mas como [n] pode ser arbitrariamente grande, se nós
    tentarmos continuar dessa maneira nós nunca chegaremos ao fim. *)


Theorem plus_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [| n'].
  Case "n = 0".
    reflexivity. (* até aqui tudo bem... *)
  Case "n = S n'".
    simpl.       (* ...mas aqui ficamos presos novamente *)
Abort.

(** *** *)

(** [Francisco] To prove such facts -- indeed, to prove most interesting
    facts about numbers, lists, and other inductively defined sets --
    we need a more powerful reasoning principle: _induction_.

    Recall (from high school) the principle of induction over natural
    numbers: If [P(n)] is some proposition involving a natural number
    [n] and we want to show that P holds for _all_ numbers [n], we can
    reason like this:
         - show that [P(O)] holds;
         - show that, for any [n'], if [P(n')] holds, then so does
           [P(S n')];
         - conclude that [P(n)] holds for all [n].

    Em Coq, os passos são os mesmos, mas a ordem é inversa: começamos 
    com a meta de provar [P(n)] para todo [n] e dividimo-na (através 
    da aplicação da tática [induction]) em duas submetas separadas: 
    primeiro demonstrando [P(O)] e, em seguida, demonstrando 
    [P(n') -> P (S n')]. A seguir está ilustrado como isso funciona 
    para o teorema que estamos tentando provar no momento: *)

(** *** *)

Theorem plus_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".     reflexivity.
  Case "n = S n'".  simpl. rewrite -> IHn'. reflexivity.  Qed.

(** Assim como [destruct], a tática [induction] usa a cláusula
 [as...] para especificar os nomes das variáveis que serão
 introduzidas nas submetas. No primeiro ramo, [n] é substituída por
 [0] e a meta se torna  [0 + 0 = 0], que, em seguida, é
 simplificada. No segundo ramo, [n] é substituído por [S n'] e a
 hipótese [n' + 0 = n'] é adicionada no contexto (com o nome [IHn']:
 Inductive Hypothesis for [n']). O objetivo se torna, neste
 caso, [(S n') + 0 = S n'], que é simplificado para [S (n' + 0) = S
 n'] devido à hipótese indutiva. *)

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  (* TRABALHADO EM SALA *)
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.  Qed.

(** **** Exercício: ** (basic_induction)  *)

(** Prove os seguintes lemas usando indução. Você pode precisar de resultados
    provados anteriormente. *)

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  (* PREENCHER AQUI *) Admitted.

Theorem plus_n_Sm : forall n m : nat, 
  S (n + m) = n + (S m).
Proof. 
  (* PREENCHER AQUI *) Admitted.


Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  (* PREENCHER AQUI *) Admitted.


Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  (* PREENCHER AQUI *) Admitted.
(** [] *)

(** **** Exercício: ** (double_plus)  *)

(** [Dalay] Consider the following function, which doubles its argument: *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** Use induction to prove this simple fact about [double]: *)

Lemma double_plus : forall n, double n = n + n .
Proof.  
  (* PREENCHER AQUI *) Admitted.
(** [] *)


(** **** Exercício: 1 star (destruct_induction)  *)
(** Explicar brevemente a diferença entre as táticas
    [destruct] e [induction].

(* PREENCHER AQUI *)

*)
(** [] *)


(** * Provas dentro de Provas *)


(** [Francisco]In Coq, as in informal mathematics, large proofs are very
    often broken into a sequence of theorems, with later proofs
    referring to earlier theorems.  Occasionally, however, a proof
    will need some miscellaneous fact that is too trivial (and of too
    little general interest) to bother giving it its own top-level
    name.  In such cases, it is convenient to be able to simply state
    and prove the needed "sub-theorem" right at the point where it is
    used.  The [assert] tactic allows us to do this.  For example, our
    earlier proof of the [mult_0_plus] theorem referred to a previous
    theorem named [plus_O_n].  We can also use [assert] to state and
    prove [plus_O_n] in-line: *)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). 
    Case "Proof of assertion". reflexivity.
  rewrite -> H.
  reflexivity.  Qed.

(** A tática [assert] introduz duas submetas. A primeira é a afirmação 
    em si; prefixando-a com [H:], nós passamos a chamar a afirmação 
    de [H]. (Observe que poderíamos também nomear a afirmação com 
    [as], assim como fizemos anteriormente com [destruct] e 
    [induction], ou seja, [assert (0 + n = n) as H]. Observe 
    também que nós marcamos a prova desta afirmação com um [Case], 
    tanto para facilitar a leitura quanto para que, ao usar Coq 
    interativamente, nós possamos ver quando terminarmos de provar 
    a afirmação, observando quando a cadeira de caracteres 
    ["Proof of assertion"] desaparece do contexto.) A segunda meta 
    é a mesma que aquela no ponto em que invocamos [assert], exceto 
    que, no contexto, temos a suposição [H] de que [0 + n = n]. 
    Ou seja, [assert] gera uma submeta onde temos que provar o 
    fato afirmado e uma segunda submeta onde podemos usar o fato 
    afirmado para fazer progressos sobre o que nós estávamos 
    tentando provar desde o início. *)

(** Na verdade, [assert] será proveitoso em várias situações
 diferentes. Por exemplo, suponha que queiramos provar [(n + m) + (p +
 q) = (m + n) + (p + q)]. A única diferença entre os dois lados de [=]
 é que os argumentos [m] e [n] no primeiro parênteses estão
 trocados. Desta forma, podemos usar, aparentemente, a 
 comutatividade da adição ([plus_comm]) para reescrever um dos termos,
 torando ambos iguais. Porém, a tática [rewrite] é um pouco estúpida
 com relação a _onde_ ele deve aplicar a reescrita. Há três usos
 de [+] aqui, e a execução de [rewrite -> plus_comm] irá
 afetar apenas a soma mais _externa_. *)

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* Precisamos apenas trocar (n + m) por (m + n)...
    parece que com plus_comm podemos fazer isso! *)
  rewrite -> plus_comm.
  (* Não funciona... Coq reescreveu a soma errada! *)
Abort.

(** Para conseguir aplicar [plus_comm] no ponto onde queremos, podemos
    introduzir um lema local afirmando que [n + m = m + n] (para os específicos [m]
    e [n] dos quais falamos aqui), provar este lema usando [plus_comm] e, então,
    usar este lema para fazer a reescrita desejada. *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
    Case "Proof of assertion".
    rewrite -> plus_comm. reflexivity.
  rewrite -> H. reflexivity.  Qed.

(** **** Exercício: **** (mult_comm)  *)
(** [Dalay]Use [assert] to help prove this theorem.  You shouldn't need to
    use induction. *)

Theorem plus_swap : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  (* PREENCHER AQUI *) Admitted.


(** Now prove commutativity of multiplication.  (You will probably
    need to define and prove a separate subsidiary theorem to be used
    in the proof of this one.)  You may find that [plus_swap] comes in
    handy. *)

Theorem mult_comm : forall m n : nat,
 m * n = n * m.
Proof.
  (* PREENCHER AQUI *) Admitted.
(** [] *)

(** **** Exercício: **, opcional (evenb_n__oddb_Sn)  *)

(** Provar o simples fato a seguir: *)

Theorem evenb_n__oddb_Sn : forall n : nat,
  evenb n = negb (evenb (S n)).
Proof.
  (* PREENCHER AQUI *) Admitted.
(** [] *)

(** * Mais Exercícios *)

(** **** Exercício: ***, opcional (more_exercises)  *)
(** Pegar uma folha branca.  Para cada teorema a seguir, primeiro
    _pensar_ se (a) pode ser provado utilizando somente
    simplificações e reescritas, ou (b) é também necessário uma análise
    de caso ([destruct]), ou (c) é também necessário indução.  Escrever
    sua previsão.  Então preencher a prova.  (Não há necessidade
    de entregar a sua folha; isto é somente para encorajar você a 
    refletir antes de resolver a base de tentativa e erro!) *)

Theorem ble_nat_refl : forall n:nat,
  true = ble_nat n n.
Proof.
  (* PREENCHER AQUI *) Admitted.

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  (* PREENCHER AQUI *) Admitted.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  (* PREENCHER AQUI *) Admitted.

Theorem plus_ble_compat_l : forall n m p : nat, 
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  (* PREENCHER AQUI *) Admitted.

Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
  (* PREENCHER AQUI *) Admitted.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  (* PREENCHER AQUI *) Admitted.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  (* PREENCHER AQUI *) Admitted.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  (* PREENCHER AQUI *) Admitted.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  (* PREENCHER AQUI *) Admitted.
(** [] *)

(** **** Exercício: **, opcional (beq_nat_refl)  *)
(** [Francisco] Prove the following theorem.  Putting [true] on the left-hand side
of the equality may seem odd, but this is how the theorem is stated in
the standard library, so we follow suit.  Since rewriting 
works equally well in either direction, we will have no 
problem using the theorem no matter which way we state it. *)

Theorem beq_nat_refl : forall n : nat, 
  true = beq_nat n n.
Proof.
  (* PREENCHER AQUI *) Admitted.
(** [] *)

(** **** Exercício: **, opcional (plus_swap')  *)
(** A tática [replace] permite que você especifique um subtermo em
    particular para reescrever e para o que você quer que ele seja reescrito. 
    Mais precisamente, [substituir (t) com (u)] substitui (todas as cópias de) 
    expressões [t], nas metas, pela expressão [u], e gera [t = u] como uma
    submeta adicional. Isso é frequentemente útil quando um simples [rewrite] 
    atua sobre a parte errada da meta.
    
    Use a tática [replace] para fazer uma prova de [plus_swap'], tal como 
    [plus_swap], mas sem a necessidade de fazer um [assert (n + m = m + n)].
*)

Theorem plus_swap' : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  (* PREENCHER AQUI *) Admitted.
(** [] *)


(** **** Exercício: *** (binary_commute)  *)

 (** Relembre as funções [increment] e [binary-to-unary] que você
 escreveu para o exercício [binary] no capítulo [Basics]. Prove que
 estas funções comutam -- isto é, incrementar um número binário e
 convertê-lo para unário possui o mesmo resultado que convertê-lo
 primeiro para binário e depois incrementá-lo. Nomeie seu teorema como
 [bin_to_nat_press_incr]. 

  (Antes de começar a trabalhar neste exercício, por favor, copie as
  definições de sua solução para o exercício [binary] daqui para que
  este arquivo esteja completo por si só. Se você deseja mudar alguma
  definição original para tornar a propriedade mais fácil de ser
  provada, sinta-se livre para realizá-la.) *)

(* PREENCHER AQUI *)
(** [] *)


(** **** Exercício: *****, avançado (binary_inverse)  *)
(** [Cláudia] This exercise is a continuation of the previous exercise about
    binary numbers.  You will need your definitions and theorems from
    the previous exercise to complete this one.

    (a)[Dalay]First, write a function to convert natural numbers to binary
        numbers.  Then prove that starting with any natural number,
        converting to binary, then converting back yields the same
        natural number you started with.

    (b) Você naturalmente deve pensar que nós deveriamos também provar a
        direção oposta: a de que começando com um número binário,
        convertendo para um número natural, e então voltando para um número binário
        teriamos o mesmo número que começamos.  Entretanto, isso não é verdade!
        Explique qual é o problema.

    (c)[Francisco]Define a "direct" normalization function -- i.e., a function
        [normalize] from binary numbers to binary numbers such that,
        for any binary number b, converting to a natural and then back
        to binary yields [(normalize b)].  Prove it.  (Warning: This
        part is tricky!)

    Again, feel free to change your earlier definitions if this helps
    here. 
*)

(* PREENCHER AQUI *)
(** [] *)

(* ###################################################################### *)
(** * Prova Formal e Prova Informal (Avançado) *)

(** "Provas informais são algoritmos; provas formais são código." *)

(** A questão sobre o que, exatamente, constitui uma "prova" de uma 
    alegação matemática tem desafiado os filósofos há milênios. Uma 
    definição curta e grossa, no entanto, poderia ser esta: uma prova 
    de uma proposição matemática [P] é um texto escrito (ou falado) 
    que inspira no leitor ou ouvinte a certeza de que [P] é verdade. 
    Ou seja, uma prova é um ato de comunicação.

    Agora, os atos de comunicação podem envolver diferentes tipos de
    leitores. De um lado, o "leitor" pode ser um programa como o Coq, em
    que, no caso, a "crença" transmitida é uma simples verificação
    mecânica de que [P] pode ser derivada a partir de um conjunto de
    regras lógicas formais, e a prova é uma receita que guia o programa
    em sua verificação. Estas receitas são as provas _formais_.

    Além disso, o leitor pode ser um ser humano e, nesse caso, a prova será
    escrita em português ou em alguma outra linguagem natural, portanto,
    necessariamente _informal_. Aqui, os critérios para o sucesso são
    especificados com menos clareza. Uma "boa" prova é aquela que faz o leitor
    acreditar em [P]. Mas, a mesma prova pode ser lida por muitos leitores
    diferentes, alguns deles podem ser convencidos por uma determinada forma
    de frasear o argumento, enquanto outros podem não ser. Um leitor pode ser
    particularmente minucioso, inexperiente ou, simplesmente, teimoso; a única
    maneira de convencê-los será fazer o argumento nos mínimos detalhes. Mas,
    outros leitores, mais familiarizados com a área, podem achar todos esses
    detalhes tão sufocantes que perdem o traço principal. Tudo que eles querem
    é conhecer as ideais principais, porque é mais fácil preenchê-las
    sozinhos. Enfim, não existe um padrão universal, porque não há uma maneira
    única de escrever uma prova informal que garanta o convencimento de todos
    os prováveis leitores. Na prática, no entanto, matemáticos desenvolveram
    um rico conjunto de convenções e expressões idiomáticas para escrever
    sobre objetos matemáticos complexos que, dentro de uma determinada
    comunidade, tornam a comunicação bastante confiável. As convenções dessa
    forma estilizada de comunicação fornecem um padrão bastante claro para
    julgar provas boas ou ruins.

    Como estamos utilizando Coq nesse curso, nós iremos trabalhar
    exaustivamente com provas formais. Mas isto não significa que podemos ignorar
    as provas informais! Provas formais são úteis em vários aspectos, mas
    elas _não_ são um meio muito eficiente para comunicar ideias entre
    seres humanos. *)

(** Por exemplo, aqui está uma prova de que a adição é associativa: *)


Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n']. reflexivity. 
  simpl. rewrite -> IHn'. reflexivity.  Qed.

(** [Francisco]Coq is perfectly happy with this as a proof.  For a human,
    however, it is difficult to make much sense of it.  If you're used
    to Coq you can probably step through the tactics one after the
    other in your mind and imagine the state of the context and goal
    stack at each point, but if the proof were even a little bit more
    complicated this would be next to impossible.  Instead, a
    mathematician might write it something like this: *)
(** - _Theorem_: For any [n], [m] and [p],
      n + (m + p) = (n + m) + p.
    _Proof_: By induction on [n].

    - First, suppose [n = 0].  We must show 
        0 + (m + p) = (0 + m) + p.  
      This follows directly from the definition of [+].

    - Next, suppose [n = S n'], where
        n' + (m + p) = (n' + m) + p.
      We must show
        (S n') + (m + p) = ((S n') + m) + p.
      By the definition of [+], this follows from
        S (n' + (m + p)) = S ((n' + m) + p),
      which is immediate from the induction hypothesis. *)
(** _Qed_ *)

(** A forma geral da prova é basicamente similar. Isso não é por acaso: 
    Coq foi concebido de modo que a sua tática de [induction] gera as 
    mesmas submetas, na mesma ordem, como os pontos de linha que um 
    matemático iria escrever. Mas existem diferenças significativas de 
    detalhes: a prova formal é muito mais explícita em alguns aspectos 
    (por exemplo, o uso de [reflexivity]), mas muito menos explícita 
    em outros (em particular, o "estado da prova" em qualquer ponto na
    prova do Coq é completamente implícita, enquanto a prova informal 
    lembra ao leitor várias vezes onde as coisas estão). *)

(** Aqui está uma prova formal que mostra a estrutura de forma mais
 clara: *)
		
Theorem plus_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n']. 
  Case "n = 0".
    reflexivity. 
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.   Qed.

(** **** Exercício: **, avançado (plus_comm_informal)  *)
(** Traduza sua a sua solução de [plus_comm] para uma prova informal. *) 

(** Teorema: Adição é comutativa.
 
    Proof: (* PREENCHER AQUI *)
*)
(** [] *)

(** **** Exercício: **, opcional (beq_nat_refl_informal)  *)
(** Escreva uma prova informal para o seguinte teorema, usando a prova
 informal para [plus_assoc] como modelo. Não reescreva simplesmente as
 táticas do Coq em inglês!

    Theorem: [true = beq_nat n n] for any [n].
    
    Proof: (* PREENCHER AQUI *) 
[] *)

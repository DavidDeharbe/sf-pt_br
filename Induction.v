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

(** O falto de que não existe um comando explícito  para mover de 
    uma ramificação de uma análise de caso para a próxima pode fazer
    escriptes scripts de provas mais difíceis de serem lidos. Em 
    provas maiores, com análises de casos aninhadas, isso pode fazer
    com que seja difícil de se manter orientado quando você está 
    caminhando em direção à prova no Coq. (Imagine tentar lembrar que
    as cinco primeiras provas pertencem à análise de caso mais interna
    e as outras sete provas restantes são as que se referem às mais 
    externas...) O uso disciplinado da identação e comentários pode
    ajudar, mas um melhor modo é fazer uso da tática [Case] (_Caso_). *)

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

(** [Case] realiza algo muito simples: Ele simplesmente adiciona uma
    cadeia de caracteres que nós escolhemos (marcado com o identificador "Case") para o
    contexto para a meta atual.  Quando submetas são gerados, esta
    cadeia de caracteres é levada para o seus contextos.  Quando a última dessas
    submetas é finalmente provada e a próxima meta de nível superior
    se torna ativa, esta cadeia de caracteres não irá mais aparecer no contexto
    e nós poderemos ver que o caso onde nós introduzimos ela está completo. 
    Também, como uma verificação de sanidade, se a gente tentar executar uma nova
    tática de [Case] enquanto a cadeia de caracteres deixada pela anterior
    ainda está no contexto, nós receberemos uma mensagem de erro.
	
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
      Em particular, uma convenção razoável é limitar-se a linhas de 80
      caracteres. Linhas com mais do que isso são difíceis de ler e podem ser
      inconvenientes para exibir e imprimir. Muitos editores têm recursos que
      ajudam a cumprir isso.*)

(** * Prova por Indução *)

(** Nós provamos no último capítulo que [0] é um elemento neutro
    para [+] ma esquerda, usando um simples argumnto. O fato que 
    ele é também um elemento neutro na _direita_... *)

Theorem plus_0_r_firsttry : forall n:nat,
  n + 0 = n.

(** ... não pode ser provado da mesma maneira. Somente aplicando 
    [reflexivity] não funciona: o [n] em [n + 0] é um número desconhecido
    arbitrário, então o [match] na definição de [+] não pode ser 
    simplificado.  *)

Proof.
  intros n.
  simpl. (* Faz nada! *)
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

(** Para provar tais fatos -- de fato, para provar a maioria dos fatos
    interessantes sobre números, listas, e outros conjuntos definidos indutivamente --
    nós precisamos de um princípio de raciocínio mais poderoso: _induction_.

    Relembrando (a partir do ensino médio) o princípio de indução sobre os números
    naturais: Se [P(n)] é alguma proposição que envolve um número natural
    [n] e nós queremos mostrar que P é válido para _todos_ os números [n], nós podemos
    raciocinar como:
         - mostrar que [P(O)] é válido;
         - mostrar que, para qualquer [n'], se [P(n')] é válido, [P(S n')] também é;
         - conclui que [P(n)] é válido para todo [n].

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

(** Considere a seguinte função, a qual dobra seus argumentos: *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** Use indução para provar esse fato simples a respeito de [double]: *)

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


(** Em Coq, como em matemática informal, grandes provas são muito
    frequente quebrados em uma sequencia de teoremas, com provas posteriores
    referindo-se à provas anteriores. Ocasionalmente, contudo, uma prova
    vai precisar de algum fato diverso que é muito trivial(e também
    de pouco interesse geral) de se preocupar dando-lhe o seu próprio 
    nome de nível superior. Em tais casos, isto é conveniente para ser capaz 
    de um estado simples e provar direito "sub-teoremos" necessários 
    no momento em que ele é usado. A tática [assert] permite a gente fazer isso.  
    Por exemplo, nossa prova anterior do teorema [mult_0_plus] refere-se ao 
    teorema anterior nomeado de [plus_O_n]. Nós podemos também usar [assert] para declarar
    e provar [plus_O_n]: *)

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
(** Use [assert] para ajudar a provar esse teorema. Você não deve precisar
    usar indução. *)

Theorem plus_swap : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  (* PREENCHER AQUI *) Admitted.


(** Agora prove a comutatividade da multiplicação. (você provavelmente
    precisará definir e provar um teorema auxiliar separado para ser 
    usado nessa prova.) Você deve achar que [plus_swap] seja útil. *)

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
(** Prove o seguinte teorema.  Colocar [verdadeiro] no lado esquerdo
da igualdade pode parecer estranho, mas isso é como o teorema é declarado
na biblioteca padrão, então a gente segue o exemplo.  Desde reescrever
funciona igualmente em qualquer direção, nós não iremos ter problemas em usar
o teorema não importa como nós o declaramos. *)

Theorem beq_nat_refl : forall n : nat, 
  true = beq_nat n n.
Proof.
  (* PREENCHER AQUI *) Admitted.
(** [] *)

(** **** Exercício: **, opcional (plus_swap')  *)
(** A tática [replace] permite que você especifique um subtermo em
    particular para reescrever e para o que você quer que ele seja reescrito. 
    Mais precisamente, [substituir (t) com (u)] substitui (todas as cópias de) 
    expressões [t], na meta, pela expressão [u], e gera [t = u] como uma
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

    (a) Primeiramente, escreva uma função para converter números naturais para 
        números binários. Então prove que começando com qualquer número natural,
        convertendo para binário, e então convertendo de volta resulta no mesmo
        número natural que você começou.

    (b) Você naturalmente deve pensar que nós deveriamos também provar a
        direção oposta: a de que começando com um número binário,
        convertendo para um número natural, e então voltando para um número binário
        teriamos o mesmo número que começamos.  Entretanto, isso não é verdade!
        Explique qual é o problema.

    (c) Defina uma função de normalização "Direta" -- por exemplo, uma função
        [normalize] de número binários para números binários tal que,
        para qualquer número binário b, converta para um natural e então
        volte para binário [(normalize b)].  Prove.  (Atenção: está
        parte é complicado!)

    Novamente, sinta-se livre para mudar as definições anteriores se isso ajudar
    aqui. 
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

(** Coq está perfeitamente feliz com isso como uma prova. Para um humano,
    contudo, isto é difícil fazer muito sentido. Se você esta acostumado com Coq,
    você pode provavelmente passar os passos um após o outro em sua mente
    e imaginar o estado do contexto e a meta presa em cada ponto,
    mas se a prova foi mesmo um pouco mais complicado, isso seria quase
    impossível.  Em vez, um matematico pode escreve isto algo como: *)
(** - _Theorem_: For any [n], [m] and [p],
      n + (m + p) = (n + m) + p.
    _Prova_: Por indução em [n].

    - Primeiro, suponha [n = 0].  Nós devemos mostrar 
        0 + (m + p) = (0 + m) + p.  
      Isso segue diretamente da definição de [+].

    - próximo, suponha [n = S n'], onde
        n' + (m + p) = (n' + m) + p.
      Nós devemos mostrar
        (S n') + (m + p) = ((S n') + m) + p.
      Pela definição de [+], isso segue de
        S (n' + (m + p)) = S ((n' + m) + p),
      ao qual é imediato pela hipótese de indução. *)
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

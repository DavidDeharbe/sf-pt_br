(** * Embasamento: Programação Funcional em Coq *)
 
(*
   [Admitted] is Coq's "escape hatch" that says accept this definition
   without proof.  We use it to mark the 'holes' in the development
   that should be completed as part of your homework exercises.  In
   practice, [Admitted] is useful when you're incrementally developing
   large proofs. *)
Definition admit {T: Type} : T.  Admitted.

(** * Introdução *)

(** O estilo de programação funcional aproxima a programação à matemática
    simples do dia-a-dia: se um procedimento ou método não possui efeitos
    colaterais, então, basicamente, tudo que você precisa entender é como
    entradas são mapeadas para saídas -- isto é, você pode pensar nisto
    simplesmente como um método concreto para computar uma função
    matemática. Esse é um dos significados da palavra "funcional" em
    "programação funcional". A conexão direta entre programas e objetos
    matemáticos simples autoriza tanto provas formais de corretude quanto
    raciocínio informal de correção sobre o comportamento do programa.

    O outro sentido no qual a programação funcional é "funcional" é a 
    ênfase que ela dá ao uso de funções (ou métodos) como valores de 
    primeira classe, como por exemplo, valores que podem ser passados 
    como argumentos para outras funções, retornados como resultados, 
    guardados em estruturas de dados, etc. O entendimento de que funções 
    podem ser tratadas como dados dessa maneira permite uma série de
    idiomas úteis e poderosos.

    Other common features of functional languages include _algebraic
    data types_ and _pattern matching_, which make it easy to construct
    and manipulate rich data structures, and sophisticated
    _polymorphic type systems_ that support abstraction and code
    reuse.  Coq shares all of these features.

    The first half of this chapter introduces the most essential
    elements of Coq's functional programming language.  The second
    half introduces some basic _tactics_ that can be used to prove
    simple properties of Coq programs.
*)

(** * Tipos Enumerados *)

(** Um aspecto incomum de Coq é que o seu conjunto de recursos internos 
    é extremamente pequeno. Por exemplo, em vez de fornecer a paleta habitual 
    de tipos atômicos de dados (booleans, integers, strings, etc.), Coq oferece 
    um mecanismo extremamente poderoso para a definição de novos tipos de 
    dados a partir do zero - tão poderoso que todos estes tipos familiares 
    surgem como instâncias.  

    Naturalmente, a distribuição Coq vem com uma extensiva biblioteca padrão,
    fornecendo definições de booleanos, números e muitas outras estruturas de
    dados como listas e tabelas de dispersão. Mas não há nada de mágico ou
    primitivo sobre estas definições da biblioteca: elas foram implementadas com
    código simples de usuário. Para ilustrar isto, recapitularemos
    explicitamente todas as definições que precisarmos neste curso, ao invés de
    usar as definições da biblioteca.

    Para ver como este mecanismo funciona, começaremos com um exemplo muito
    simples.*)

(** ** Dias da Semana *)

(** A declaração abaixo diz ao Coq que estamos definindo um novo conjunto
    de valores -- um tipo *)

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

(** O tipo é chamado [day] (_dia_) e seus membros são [monday]
    (_segunda-feira_), [tuesday] (_terça-feira_), etc. A partir da segunda linha
    a definição pode ser lida como "[monday] é um [day], [tuesday] é um [day]",
    etc.

    Having defined [day], we can write functions that operate on
    days. *)

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

(** One thing to note is that the argument and return types of
    this function are explicitly declared.  Like most functional
    programming languages, Coq can often figure out these types for
    itself when they are not given explicitly -- i.e., it performs
    some _type inference_ -- but we'll always include them to make
    reading easier. *)

(** Having defined a function, we should check that it works on
    some examples.  There are actually three different ways to do this
    in Coq.  

    Primeiro, nós podemos usar o comando [Eval compute] (_avalia cálculo_) para
    avaliar uma expressão composta envolvendo [next_weekday].  *)

Eval compute in (next_weekday friday).
   (* ==> monday : day *)
Eval compute in (next_weekday (next_weekday saturday)).
   (* ==> tuesday : day *)

(** Se você tiver um computador acessível, este seria um excelente 
    momento de disparar o interpretador Coq sob seu IDE favorito - 
    CoqIDE ou Proof General - e tentar isso por si próprio. Carregue 
    este arquivo ([Basics.v]) a partir dos arquivos fontes do Coq anexos 
    ao livro, encontre o exemplo acima, submeta-o ao Coq, e observe 
    o resultado. *)

(** A palavra-chave [compute] (_calcular_) informa ao Coq exatamente como
    avaliar as expressões que lhe damos. No momento, precisamos saber apenas
    sobre [compute]; posteriormente veremos algumas alternativas que podem ser
    úteis em alguns casos.  *)

(** A segunda maneira consiste em registrar o resultado _esperado_ sob a a forma
    de um exemplo Coq: *)

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

(** Esta declaração faz duas coisas: define uma asserção de que o segundo dia da
    semana depois de [saturday] (_sábado_) é [tuesday] (_terça_), e dá a esta
    asserção um nome que pode ser usado para referenciá-la posteriormente. *)

(** Tendo feito essa asserção, também podemos pedir ao Coq para verificá-la da
    seguinte forma: *)

Proof. simpl. reflexivity.  Qed.

(** Os detalhes não são importantes por enquanto (voltaremos a considerá-los em
    breve), mas, essencialmente, isto pode ser lido como "A asserção que
    acabamos de fazer pode ser provada pela observação de que, após
    simplificação, o valor calculado em ambos os lados da igualdade é o mesmo."
    *)

(** Por último, podemos pedir ao Coq para extrair da nossa [Definition]
    (definição), um programa em alguma outra linguagem de programação mais
    convencional (OCaml, Scheme, ou Haskell) com um compilador de alta
    performance. Essa facilidade é muito interessante, já que nos dá um modo de
    construir programas totalmente provados em liguagens mais comuns. De fato,
    esse é um dos principais usos para o qual Coq foi criado. Voltaremos a esse
    assunto em capítulos posteriores. Mais informações podem ser encontradas no
    livro "Coq'Art" de Bertot e Casteran, assim como no manual de referência de
    Coq. *)


(** ** Booleanos *)

(** In a similar way, we can define the standard type [bool] of
    booleans, with members [true] and [false]. *)

Inductive bool : Type :=
  | true : bool
  | false : bool.

(** Although we are rolling our own booleans here for the sake
    of building up everything from scratch, Coq does, of course,
    provide a default implementation of the booleans in its standard
    library, together with a multitude of useful functions and
    lemmas.  (Take a look at [Coq.Init.Datatypes] in the Coq library
    documentation if you're interested.)  Whenever possible, we'll
    name our own definitions and theorems so that they exactly
    coincide with the ones in the standard library. *)

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

(** Os quatro seguintes "testes unitários" constituem uma especificação completa
    -- uma tabela verdade -- para a função [orb] *)

Example test_orb1:  (orb true  false) = true. 
Proof. reflexivity.  Qed.
Example test_orb2:  (orb false false) = false.
Proof. reflexivity.  Qed.
Example test_orb3:  (orb false true)  = true.
Proof. reflexivity.  Qed.
Example test_orb4:  (orb true  true)  = true.
Proof. reflexivity.  Qed.

(** (Observe que nós removemos o [simpl] nas provas. Ele não é
    realmente necessário porque [reflexivity] executa simplificação
    automaticamente.) *)

(** _Uma observação sobre anotações_: Em arquivos .v, utilizamos colchetes para
    delimitar fragmentos de código Coq nos comentários. O objetivo desta
    convenção, também usada pela ferramenta de documentação [coqdoc], é manter
    estes fragmentos visualmente diferentes do texto ao redor: na versão html
    dos arquivos, estas partes do texto aparecem com uma [fonte diferente]. *)

(** Os valores [Admitted] (_admitido_) e [admit] (_admitir_) podem ser usados
    para preencher um espaço em uma definição ou prova imcompletas. Usaremos
    tais valores nos próximos exercícios. Em geral, nossa tarefa nos exercícios
    é substituir [admit] ou [Admitted] por definições ou provas reais. *)

(** **** Exercício: 1 estrela (nandb)  *)

(** Complete a definição das seguintes funções, depois, certifique que as
    asserções [Example] (_exemplo_) abaixo podem ser verificadas pelo Coq.  *)

(** This function should return [true] (_verdadeiro_) if either or both of its
    inputs are [false] (_falso_). *)

Definition nandb (b1:bool) (b2:bool) : bool :=
  (* PREENCHER *) admit.

(** Remove "[Admitted.]" and fill in each proof with 
    "[Proof. reflexivity. Qed.]" *)

Example test_nandb1:               (nandb true false) = true.
(* PREENCHER *) Admitted.
Example test_nandb2:               (nandb false false) = true.
(* PREENCHER *) Admitted.
Example test_nandb3:               (nandb false true) = true.
(* PREENCHER *) Admitted.
Example test_nandb4:               (nandb true true) = false.
(* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: 1 star (andb3)  *)
(** Do the same for the [andb3] function below. This function should
    return [true] when all of its inputs are [true], and [false]
    otherwise. *)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  (* PREENCHER *) admit.

Example test_andb31:                 (andb3 true true true) = true.
(* PREENCHER *) Admitted.
Example test_andb32:                 (andb3 false true true) = false.
(* PREENCHER *) Admitted.
Example test_andb33:                 (andb3 true false true) = false.
(* PREENCHER *) Admitted.
Example test_andb34:                 (andb3 true true false) = false.
(* PREENCHER *) Admitted.
(** [] *)

(** ** Tipos funcionais *)

(** O comando [Check] (_verifique_) faz com que Coq imprima o tipo de uma
    expressão. Por exemplo, o tipo de [negb true] é [bool]. *)

Check true.
(* ===> true : bool *)
Check (negb true).
(* ===> negb true : bool *)

(** Funções como [negb] em si também são valores de dados, assim como [true] e
    [false]. Seus tipos são chamados _function types_ (_tipos funcionais_), e
    eles são escritos com setas. *)

Check negb.
(* ===> negb : bool -> bool *)

(** O tipo de [negb], escrito [bool -> bool] e pronunciado 
    "[bool] seta [bool]," pode ser lido: "Dada uma entrada do tipo 
     [bool], esta função produz uma saída do tipo [bool]." Da mesma 
    forma, o tipo de [andb], escrito [bool -> bool -> bool], pode ser 
    lido, "Dadas duas entradas, ambas do tipo [bool], esta função produz 
    uma saída do tipo [bool]." *)

(** ** Números *)

(** _Digressão técnica_: O Coq fornece um _sistema modular_ bastante sofisticado
    para auxiliar na organização de desenvolvimentos robustos. Neste curso não
    precisaremos da maioria de suas funcionalidades, mas uma é bastante útil: se
    inserimos uma coleção de declarações entre os marcadores [Module X] (_módulo
    X_) e [End X] (_término X_), então, no restante do arquivo após o [End],
    estas definições serão referenciadas através de nomes como [X.foo] no lugar
    de [foo]. Aqui, usaremos esta funcionalidade para introduzir a definição do
    tipo [nat] em um módulo interno, para que a definição presente na biblioteca
    padrão não seja omitida. *)

Module Playground1.

(** Os tipos que definimos até o momento são exemplos de “tipos enumerados”:
    suas definições enumeram explicitamente um conjunto finito de elementos. Uma
    forma mais interessante de definir um tipo é através de uma coleção de
    "regras indutivas" descrevendo seus elementos. Por exemplo, podemos definir
    os números naturais desta forma: *)

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

(** As cláusulas desta definição podem ser lidas como: *)

(** 
      - [O] é um número natural (perceba que isto é a letra "[O]", e não
      o numeral "[0]"). 
      - [S] é um "construtor" que recebe um número natural e retorna um outro
      número natural---isto é, se [n] é um número natural, então [S n] também
      o é.

    Vamos olhar isso com um pouco mais de detalhamento.

    Every inductively defined set ([day], [nat], [bool], etc.) is
    actually a set of _expressions_.  The definition of [nat] says how
    expressions in the set [nat] can be constructed:

    - the expression [O] belongs to the set [nat]; 
    - if [n] is an expression belonging to the set [nat], then [S n]
      is also an expression belonging to the set [nat]; and
    - expressions formed in these two ways are the only ones belonging
      to the set [nat].

    The same rules apply for our definitions of [day] and [bool]. The
    annotations we used for their constructors are analogous to the
    one for the [O] constructor, and indicate that each of those
    constructors doesn't take any arguments. *)

(** Estas três condições são a força precisa da declaração [Inductive]. 
    Elas implicam que a expressão [O], a expressão [S O], a expressão 
    [S (S O)], a expressão [S (S (S O))], e assim por diante, todas 
    pertencem ao conjunto [nat], enquanto outras expressões como [true], 
    [andb true false] e [S (S false)] não.

    Nós podemos escrever funções simples que realizam casamento de padrões em
    números naturais assim como fizemos acima -- por exemplo, a função
    predecessor: *)

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

(** O segundo ramo pode ser lido assim:"se [n] possui a forma [S n'] para algum
    [n'], então retorne [n']." *)

End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

(** Como os números naturais são uma forma de informação tão difundida, Coq
    provê um pouquinho de mágica construída internamente para interpretá-los e
    imprimí-los: algarismos árabes comuns podem ser usados como alternativa para
    a notação "unária" definida pelos construtores [S] e [O]. Por padrão, Coq
    imprime números na forma árabe: *) 

Check (S (S (S (S O)))).
Eval compute in (minustwo 4).

(** O construtor [S] possui o tipo [nat -> nat], assim como as funções
    [minustwo] e [pred]: *)

Check S.
Check pred.
Check minustwo.


(** Estas são todas as coisas que podem ser aplicadas a um número para obter
    outro número. Porém, existe uma diferença fundamental: funções como [pred] e
    [minustwo] vêm com _regras computacionais_ -- por exemplo, a definição de
    [pred] afirma que [pred 2] pode ser simplificado para [1] -- enquanto que a
    definição de [S] não possui nenhum comportamento incorporado. Embora o
    último seja uma função no sentido de que pode ser aplicado a um argumento,
    ele realmente não _faz_ nada!  *)

(** Para muitas definições de funções sobre números, casamento de padrões puro
    não é suficiente: também precisamos de recursão. Por exemplo, para verificar
    que um número [n] é par, precisamos verificar recursivamente se [n-2] é
    par. Para escrever essas funções, usamos a palavra-chave [Fixpoint] (_ponto
    fixo_). *)

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

(** Podemos definir [oddb] através de uma declaração [Fixpoint] similar, mas
    aqui está uma definição mais simples com a qual será um pouco mais fácil de
    trabalhar: *)

Definition oddb (n:nat) : bool   :=   negb (evenb n).

Example test_oddb1:    (oddb (S O)) = true.
Proof. reflexivity.  Qed.
Example test_oddb2:    (oddb (S (S (S (S O))))) = false.
Proof. reflexivity.  Qed.

(** Naturalmente, também podemos definir funções com múltiplos argumentos
    através de recursão. (Mais uma vez, usamos um módulo para evitar a poluição
    do contexto para identificadores.) *)

Module Playground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

(** Somar três com dois nos dá agora cinco, conforme esperado. *)

Eval compute in (plus (S (S (S O))) (S (S O))).

(** A simplificação que o Coq realiza para chegar à essa conclusão pode ser
visualizada a seguir: *)

(*  [plus (S (S (S O))) (S (S O))]    
==> [S (plus (S (S O)) (S (S O)))] pela segunda cláusula do [match]
==> [S (S (plus (S O) (S (S O))))] pela segunda cláusula do [match]
==> [S (S (S (plus O (S (S O)))))] pela segunda cláusula do [match]
==> [S (S (S (S (S O))))]          pela primeira cláusula do [match]
*)

(** Por convenção notacional, se dois ou mais argumentos têm o mesmo tipo, eles
    podem ser escritos juntos. Na definição à seguir, [(n m : nat)] significa
    apenas o mesmo que se tivéssemos escrito [(n : nat) (m : nat)]. *)

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. reflexivity.  Qed.

(** Você pode casar duas expressões ao mesmo tempo colocando uma vírgula entre
    elas: *)

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O   , _    => O
  | S _ , O    => n
  | S n', S m' => minus n' m'
  end.

(** O _ na primeira linha é uma _padrão coringa_. Escrever _ em um padrão é o
    mesmo que escrever alguma variável que não será usada no lado direito. Isso
    evita a necessidade de inventar um nome falso de variável. *)

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

(** **** Exercício: 1 estrela (factorial)  *)
(** Relembrando a função fatorial tradicional:
<<
    factorial(0)  =  1 
    factorial(n)  =  n * factorial(n-1)     (if n>0)
>>
    Traduza isto em Coq. *)

Fixpoint factorial (n:nat) : nat := 
(* PREENCHER *) admit.

Example test_factorial1:          (factorial 3) = 6.
(* PREENCHER *) Admitted.
Example test_factorial2:          (factorial 5) = (mult 10 12).
(* PREENCHER *) Admitted.

(** [] *)

(** Nós podemos tornar a leitura e a escrita de expressões numéricas
    mais fáceis ao introduzir "notações" para adição, multiplicação 
    e subtração. *)

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

(** (As anotações [level] (_nível_), [associativity] ( associatividade_), e
    [nat_scope] controlam como essas notações são tratadas pelo analisador do
    Coq. Os detalhes não são importantes, mas leitores interessados podem se
    dirigir à subseção "Mais em Notações", na seção de "Material Avançado", no
    final desse capítulo.) *)

(** Note that these do not change the definitions we've already
    made: they are simply instructions to the Coq parser to accept [x
    + y] in place of [plus x y] and, conversely, to the Coq
    pretty-printer to display [plus x y] as [x + y]. *)

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

(** **** Exercício: ** (blt_nat)  *)

(** The [blt_nat] function tests [nat]ural numbers for [l]ess-[t]han,
    yielding a [b]oolean.  Instead of making up a new [Fixpoint] for
    this one, define it in terms of a previously defined function. *)

Definition blt_nat (n m : nat) : bool :=
  (* PREENCHER *) admit.

Example test_blt_nat1:             (blt_nat 2 2) = false.
(* PREENCHER *) Admitted.
Example test_blt_nat2:             (blt_nat 2 4) = true.
(* PREENCHER *) Admitted.
Example test_blt_nat3:             (blt_nat 4 2) = false.
(* PREENCHER *) Admitted.

(** [] *)

(** * Prova por Simplificação *)

(** Now that we've defined a few datatypes and functions, let's
    turn to the question of how to state and prove properties of their
    behavior.  Actually, in a sense, we've already started doing this:
    each [Example] in the previous sections makes a precise claim
    about the behavior of some function on some particular inputs.
    The proofs of these claims were always the same: use [reflexivity] 
    to check that both sides of the [=] simplify to identical values. 

    (A propósito, posteriormente será útil saber que [reflexivity] na verdade 
    perfaz mais simplificação do que [simpl] -- por exemplo, ele tenta 
    "desdobrar" termos definidos, substituindo-os pelos seus lados direitos. A 
    razão para esta diferença é que, quando a aplicação da reflexividade é bem 
    sucedida, todo o objetivo é finalizado e não precisaremos visualizar as 
    expressões que foram expandidas por [reflexivity]. Em contrapartida, 
    [simpl] é usado em situações onde devemos ler e entender o objetivo, então 
    não queremos que definições sejam expandidas sem nosso conhecimento.) 

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

(** As formas desse teorema e da prova são quase exatamente as mesmas
    que no exemplo acima; Existem somente algumas diferenças.

    First, we've used the keyword [Theorem] instead of
    [Example].  Indeed, the difference is purely a matter of
    style; the keywords [Example] and [Theorem] (and a few others,
    including [Lemma], [Fact], and [Remark]) mean exactly the same
    thing to Coq.

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


(** Poderíamos provar um teorema similar sobre [plus] *)

Theorem plus_n_O : forall n, n + 0 = n.

(** Porém, diferentemente da prova anterior, [simpl] não faz nada neste caso *)

Proof.
  simpl. (* Doesn't do anything! *)
Abort.

(** (Você consegue explicar por que isto acontece? Percorra ambas as provas com Coq e perceba como o objetivo e o contexto mudam.) *)

Theorem plus_1_l : forall n:nat, 1 + n = S n. 
Proof.
  intros n. reflexivity.  Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity.  Qed.

(**O sufixo [_l] nos nomes destes teoremas é pronunciado "à esquerda." *)

(** * Prova por Reescrita *)

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

    Since [n] and [m] are arbitrary numbers, we can't just use
    simplification to prove this theorem.  Instead, we prove it by
    observing that, if we are assuming [n = m], then we can replace
    [n] with [m] in the goal statement and obtain an equality with the
    same expression on both sides.  The tactic that tells Coq to
    perform this replacement is called [rewrite]. *)

Proof.
  intros n m.   (* move both quantifiers into the context *)
  intros H.     (* move the hypothesis into the context *)
  rewrite -> H. (* Rewrite the goal using the hypothesis *)
  reflexivity.  Qed.

(** The first line of the proof moves the universally quantified
    variables [n] and [m] into the context.  The second moves the
    hypothesis [n = m] into the context and gives it the (arbitrary)
    name [H].  The third tells Coq to rewrite the current goal ([n + n
    = m + m]) by replacing the left side of the equality hypothesis
    [H] with the right side.

    (The arrow symbol in the [rewrite] has nothing to do with
    implication: it tells Coq to apply the rewrite from left to right.
    To rewrite from right to left, you can use [rewrite <-].  Try
    making this change in the above proof and see what difference it
    makes in Coq's behavior.) *)

(** **** Exercício: 1 star (plus_id_exercise)  *)
(** Remove "[Admitted.]" and fill in the proof. *)

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** Como vimos nos exemplos anteriores, o comando [Admitted] informa a Coq que
    queremos pular a tentativa de prova do teorema e simplesmente aceitar a
    declaração dada. Isto pode ser útil no desenvolvimento de provas mais
    longas, uma vez que podemos determinar fatos subsidiários que acreditamos
    serem importantes na criação de argumentos maiores. Use [Admitted] para
    aceitar estes teoremas na fé do momento, e continuar pensando no argumento
    maior até termos certeza de que faz sentido; e então, poderemos voltar e
    concluir as provas incompletas. Porém tenha cuidado: Toda vez que você usa [
    Admitted] (ou [admit]) você está deixando uma porta aberta para que um
    disparate total entre no mundo formal, rigoroso, verificado e agradável do
    Coq. *)

(** We can also use the [rewrite] tactic with a previously proved
    theorem instead of a hypothesis from the context. *)

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.  Qed.

(** **** Exercício: ** (mult_S_1)  *)
Theorem mult_S_1 : forall n m : nat,
  m = S n -> 
  m * (1 + n) = m * m.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)


(** * Prova por Análise de Casos *) 

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

    What we need is to be able to consider the possible forms of [n]
    separately.  If [n] is [O], then we can calculate the final result
    of [beq_nat (n + 1) 0] and check that it is, indeed, [false].
    And if [n = S n'] for some [n'], then, although we don't know
    exactly what number [n + 1] yields, we can calculate that, at
    least, it will begin with one [S], and this is enough to calculate
    that, again, [beq_nat (n + 1) 0] will yield [false].

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

    A tática [destruct] pode ser usada com qualquer tipo de dado definido
    indutivamente. Por exemplo, nós podemos usá-lo aqui para provar que a
    negação booleana é involutiva – isto é, que a negação é a sua própria
    inversa. *)

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
    reflexivity.
    reflexivity.  Qed.

(** Note que [destruct] aqui não possui nenhuma cláusula [as] pois nenhum dos
    subcasos de [destruct] precisa ser vinculado a nenhuma das variáveis. Por
    isso, não há necessidade de especificar nenhum nome (Poderíamos ter escrito
    também [as [|]], ou [as []]). De fato, podemos omitir a cláusula [as] de
    qualquer [destruct] e Coq irá preencher automaticamente os nomes de
    variáveis. Embora seja conveniente, isto é indiscutivelmente um estilo ruim,
    uma vez que o Coq pode fazer escolhas confusas de nomes quando lhe é deixada
    esta decisão. *)

(** **** Exercício: 1 star (zero_nbeq_plus_1)  *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  (* PREENCHER *) Admitted.

(** [] *)

(** * Mais Exercícios *)

(** **** Exercício: ** (boolean_functions)  *)

(** Use the tactics you have learned so far to prove the following 
    theorem about boolean functions. *)

Theorem identity_fn_applied_twice : 
  forall (f : bool -> bool), 
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  (* PREENCHER *) Admitted.

(** Now state and prove a theorem [negation_fn_applied_twice] similar
    to the previous one but where the second hypothesis says that the
    function [f] has the property that [f x = negb x].*)

(* PREENCHER *)
(** [] *)

(** **** Exercício: ** (andb_eq_orb)  *)

(** Prove the following theorem.  (You may want to first prove a
    subsidiary lemma or two. Alternatively, remember that you do
    not have to introduce all hypotheses at the same time.) *)

Theorem andb_eq_orb : 
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: *** (binary)  *)

(** Consider a different, more efficient representation of natural
    numbers using a binary rather than unary system.  That is, instead
    of saying that each natural number is either zero or the successor
    of a natural number, we can say that each binary number is either

      - zero,
      - twice a binary number, or
      - one more than twice a binary number.

    (a) Primeiro, escreva uma definição indutiva para o tipo [bin] que
    corresponda a esta descrição de números binários.

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

(* PREENCHER *)
(** [] *)

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

    Cada símbolo de notação no Coq está também ativo num escopo de notação.  O
    Coq tenta descobrir a qual escopo é feito referência, de modo que, quando
    você escreve [S(O*O)], ele infere [nat_scope], mas quando você escreve o
    tipo produto cartesiano (produto cartesiano) [bool*bool], ele infere
    [type_scope].  Ocasionalmente, você tem que ajudá-lo com uma notação de
    percentagem escrevendo [(x*y)%nat], e, algumas vezes, em suas respostas para
    você, o Coq usará [%nat] para indicar em qual escopo se encontra a notação.

    Notation scopes also apply to numeral notation (3,4,5, etc.), so you
    may sometimes see [0%nat] which means [O], or [0%Z] which means the
    Integer zero.
*)

(** * [Fixpoint] e Recursão Estrutural (Avançado) *)

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

    This requirement is a fundamental feature of Coq's design: In
    particular, it guarantees that every function that can be defined
    in Coq will terminate on all inputs.  However, because Coq's
    "decreasing analysis" is not very sophisticated, it is sometimes
    necessary to write functions in slightly unnatural ways. *)

(** **** Exercício: **, optional (decreasing)  *)

(** To get a concrete sense of this, find a way to write a sensible
    [Fixpoint] definition (of a simple function on numbers, say) that
    _does_ terminate on all inputs, but that Coq will reject because
    of this restriction. *)



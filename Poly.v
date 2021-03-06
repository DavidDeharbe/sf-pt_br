(** * Poly: Polimorfismo e Funções de Ordem Superior *)

(** Neste capítulo, continuaremos nosso desenvolvimento de conceitos básicos de
    programação funcional. as novas ideias cruciais são _polimorfismo_ (abstraindo
    funções sobre os tipos de dados elas manipulam) e funções de ordem superior_
    (considerando funções como dados).
*)

Require Export Lists.   

(* ###################################################### *)
(** * Polimorfismo *)
(* ###################################################### *)
(** ** Listas Polimôrficas *)

(** Nos últimos capítulos nós temos trabalhado somente com listas de 
    números. Obviamente, programas interessantes também precisam 
    poder manipular listas com elementos de outros tipos -- listas 
    de strings, listas de booleanos, listas de listas, etc. Nós
    _poderíamos_ apenas definir novos tipos indutivos para cada uma
    dessas, por exemplo...*)

Inductive boollist : Type :=
  | bool_nil : boollist
  | bool_cons : bool -> boollist -> boollist.

(** ...mas isto rapidamente se torna tedioso, em parte porque nós temos 
    que inventar diferentes nomes para os construtores de cada tipo de dado, 
    mas principalmente porque também precisamos definir novas versões de toda
    nossa lista de funções de manipulação ([length], [rev], etc.)  para cada
    novo tipo de dado definido. *)

(** *** *)

(** Para evitar todas essas repetições, Coq suporta definições
    de tipos indutivos _polymorphic_. Por exemplo, aqui é um tipo de dado
    _polymorphic list_. *)

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.


(** Esta é exatamente como a definição de [natlist] do capítulo anterior, 
    exceto que o argumento [nat] do construtor [cons] foi substituído 
    por um tipo X arbitrário, uma ligação para [X] foi adicionada ao 
    cabeçalho, e as ocorrências de [natlist] nos tipos dos construtores 
    foram substituídas por [list X]. (Podemos reutilizar os nomes dos 
    construtores [nil] e [cons] porque a definição anterior de [natlist] 
    estava dentro de uma definição de [Module] que agora está fora de
    escopo.) *)

(** Que tipo de coisa é a própria [list]? Uma boa forma de pensar a respeito é 
determinar que [list] é uma _função_ de [Type]s para definições [Inductive]; 
ou, pondo de outra forma, [list] é uma função de [Type]s para [Type]s. Para 
qualquer tipo específico [X], o tipo [list X] é um conjunto de listas definido 
indutivamente (com [Inductive]) cujo elementos são coisas do tipo [X]. *) 

(** Com esta definição, quando usamos os construtores [nil] e [cons] para
    construir listas, precisamos dizer ao Coq qual é o tipo dos elementos nas listas
    que estamos construindo -- isto é, [nil] e [cons] agora são _construtores
    polimórficos_. Observe os tipos destes construtores: *)

Check nil.
(* ===> nil : forall X : Type, list X *)
Check cons.
(* ===> cons : forall X : Type, X -> list X -> list X *)

(** O "[forall X]" nesses tipos pode ser lido como um argumento adicional
    aos contrutores que tetermina os tipos esperados dos argumentos 
    seguintes. quando [nil] e [cons] são usados, esses argumentos são
    fornecidos da mesma maneira que os outros. Por exemplo, a lista 
    contendo [2] e [1] é escrita assim:*)

Check (cons nat 2 (cons nat 1 (nil nat))).

(** (Nós voltamos a escrever [nil] e [cons] explicitamente
    porque não definimos as notações [ [] ] e [::]
    para a nova versão das listas. Faremos isso em breve.) *)

(** Nós agora podemos boltar e fazer versões polimorficas
    (ou "genérica") de todas as funções de processamento de listas que
    nós escrevemos antes. Aqui está [length], por exemplo: *)

(** *** *)

Fixpoint length (X:Type) (l:list X) : nat :=
  match l with
  | nil      => 0
  | cons h t => S (length X t)
  end.

(** Note que os usos de [nil] e [cons] em padrões [match] não requerem 
    quaisquer anotações de tipo: Coq já sabe que a lista [l] contém 
    elementos do tipo [X], então não há nenhuma razão para incluir [X] 
    no padrão. (Mais precisamente, o tipo [X] é um parâmetro de toda a 
    definição de [list], não dos construtores individuais. Voltaremos 
    a este ponto mais tarde.)

	Assim como com [nil] e [cons], nós podemos usar [length] aplicando-o 
	primeiramente em um tipo e depois no argumento lista: *)

Example test_length1 :
    length nat (cons nat 1 (cons nat 2 (nil nat))) = 2.
Proof. reflexivity.  Qed.

(** Para usar nossa função [length] com outros tipos de listas, basta
    instanciá-la com um parâmetro de tipo apropriado: *)

Example test_length2 :
    length bool (cons bool true (nil bool)) = 1.
Proof. reflexivity.  Qed.


(** *** *)
(** Vaos fechar essa subseção reimplementando algumas outras funções 
    padrões sobre listas em nossa nova lista polimórfica.*)

Fixpoint app (X : Type) (l1 l2 : list X)
                : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons X h (app X t l2)
  end.

Fixpoint snoc (X:Type) (l:list X) (v:X) : (list X) :=
  match l with
  | nil      => cons X v (nil X)
  | cons h t => cons X h (snoc X t v)
  end.

Fixpoint rev (X:Type) (l:list X) : list X :=
  match l with
  | nil      => nil X
  | cons h t => snoc X (rev X t) h
  end.

Example test_rev1 :
    rev nat (cons nat 1 (cons nat 2 (nil nat)))
  = (cons nat 2 (cons nat 1 (nil nat))).
Proof. reflexivity.  Qed.

Example test_rev2:
  rev bool (nil bool) = nil bool.
Proof. reflexivity.  Qed.

Module MumbleBaz.
(** **** Exercise: 2 stars (mumble_grumble)  *)
(** Considerar os dois tipos indutivamente definidos a seguir. *)

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.
Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

(** Qual das alternativas são elementos bem-tipados de [grumble X] 
    para algum tipo [X]?
      - [d (b a 5)]
      - [d mumble (b a 5)]
      - [d bool (b a 5)]
      - [e bool true]
      - [e mumble (b c 0)]
      - [e bool (b c 0)]
      - [c] 
(* PREENCHA AQUI *)
*)
(** [] *)


(** **** Exercise: 2 stars (baz_num_elts)  *)
(** Considere a seguinte definição indutiva: *)

Inductive baz : Type :=
   | x : baz -> baz
   | y : baz -> bool -> baz.

(** _Quantos_ elementos possui o tipo [baz]?
(* PREENCHA AQUI *)
*)
(** [] *)

End MumbleBaz.

(* ###################################################### *)
(** *** Inferência de Anotação de Tipagem *)

(** Vamos escrever a definição de [app] novamente, mas, desta vez, não
    especificaremos os tipos de nenhum dos argumentos. Será que Coq ainda vai
    aceitar isto? *)

Fixpoint app' X l1 l2 : list X :=
  match l1 with
  | nil      => l2
  | cons h t => cons X h (app' X t l2)
  end.

(** De fato ele vai. Vamos ver que tipo o Coq tem atribuído a [app']: *)

Check app'.
(* ===> forall X : Type, list X -> list X -> list X *)
Check app.
(* ===> forall X : Type, list X -> list X -> list X *)

(** Ele tem o mesmo tipo de [app]. Coq foi capaz de utilizar um processo 
    chamado _inferência de tipo_ para deduzir quais devesm ser os tipos
    de [X], [l1], e [l2], baseado em como eles são utilizados.  Por exemplo,
    uma vez que [X] é usado como um argumento para [cons], ele deve ser um
    [Type], já que [cons] espera um [Type] como seu primeiro argumento;
    correspondendo [l1] com [nil] e [cons] significa que ele deve ser uma
    [list]; e assim por diante.

    Essa grande facilidade significa que nós nem sempre temos
    que escrever explicitamente em todo lugar anotações, embora digitar
    explicitamente são ainda bastante util como documentação e checagem de
    sanidade.  Vocẽ deve tentar achar um equilibrio em seu próprio código
    entre digitar muitas anotações (bastantes que causam desordem e distração)
    e muito pouco (que força os leitores a realizar inferência de tipo nas
    suas cabeças de modo a entender seu código). *)

(* ###################################################### *)
(** *** Síntese de Tipo de Argumento *)

(** Sempre que usarmos uma função polimórfica, precisamos fornecer a ela 
    um ou mais tipos, além de seus outros argumentos. Por exemplo, a 
    chamada recursiva no corpo da função [length] acima tem de passar 
    juntamente o Tipo [X]. Mas, assim como o fornecimento de anotações 
    de tipo explícitas em todos os lugares, isso é pesado e prolixo. 
    Já que o segundo argumento de [length] é uma lista de [X]s, parece 
    inteiramente óbvio que o primeiro argumento só pode ser [X] -- por 
    que temos que escrever isso explicitamente?

	Felizmente o Coq nos permite evitar esse tipo de redundância. No lugar de 
	qualquer argumento de tipo, nós podemos escrever o "argumento implícito" 
	[_], que pode ser lido como "Por favor descubra por si mesmo qual é o 
	tipo aqui." Mais precisamente, quando o Coq encontra um [_], ele tentará 
	_unificar_ todas as informações disponíveis localmente -- o tipo da função 
	que está sendo aplicada, os tipos dos demais argumentos e o tipo esperado 
	no contexto em que a aplicação aparece -- para determinar qual tipo 
	concreto deve ser inserido no lugar de [_].

    Isto pode parecer semelhante à inferência de anotação de tipo -- e os
    métodos baseiam-se, de fato, nos mesmos mecanismos subjacentes. Ao invés de
    simplesmente omitir os tipos de alguns argumentos para um função, como em
      app' X l1 l2 : list X :=
    podemos também substituir os tipos por [_], como em
      app' (X : _) (l1 l2 : _) : list X :=
    que pede ao Coq para tentar inferir a informação em falta apenas analisando os argumentos.

    Usando argumentos implícitos, a função [length] pode ser escrita assim:*)

Fixpoint length' (X:Type) (l:list X) : nat :=
  match l with
  | nil      => 0
  | cons h t => S (length' _ t)
  end.

(** Neste caso, nós não poupamos muito ao escrever [_] em vez de
    [X].  Mas, em muitos casos, a diferença pode ser significante.  Por
    exemplo, suponha que queremos escrever uma lista contendo os
    números [1], [2], e [3].  Em vez de escrevermos isto... *)

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

(** ...Nós podemos usar a síntese de argumento para escrever isto: *)

Definition list123' := cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(* ###################################################### *)
(** *** Argumentos Implícitos *)

(** Na verdade, podemos ir mais longe. Para evitar ter que espalhar [_]'s 
    ao longo de nossos programas, podemos dizer ao Coq para _sempre_ 
    inferir o tipo de argumento(s) de uma dada função. A diretiva 
    [Arguments] especifica o nome da função ou do construtor, e, em seguida, 
    lista os nomes de seus argumentos, com chaves em torno de quaisquer 
    argumentos a serem tratados como implícitos. 
    *)

Arguments nil {X}.
Arguments cons {X} _ _.  (* use underscore for argument position that has no name *)
Arguments length {X} l.
Arguments app {X} l1 l2.
Arguments rev {X} l. 
Arguments snoc {X} l v.

(* note: no _ arguments required... *)
Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
Check (length list123'').

(** *** *)

(** Alternativamente nó podemos declarar um argumento para que seja implícito 
enquanto a função é definida, cercando o argumento com chaves. Por exemplo: *) 

Fixpoint length'' {X:Type} (l:list X) : nat :=
  match l with
  | nil      => 0
  | cons h t => S (length'' t)
  end.

(** Note que nem sequer temos que fornecer um argumento de tipo para a chamada
    recursiva de [length'']; na verdade, é até inválido fornecer um.) Vamos usar
    este estilo sempre que possível, mas vamos continuar a usar declarações
    [Argument] explícitas para construtores [Inductive] *)

(** *** *)

(** Um pequeno problema com declarar argumentos [Impricit] é que, 
    ocasionalmente, o Coq não tem informações locais suficientes para 
    determinar um argumento tipo; nesses casos, nós precisamos dizer ao 
    Coq que nós queremos dar o argumento explicitamente dessa vez, mesmo
    que nós tenhamos declarado globalmente que ele é [Implicit]. Por 
    exemplo, suponha que nós escrevemos isso: *)

(* Definition mynil := nil.  *)

(** Se não comentarmos essa definição, Coq dará um erro, porque ele não
    reconhece o tipo de argumento para compor [nil]. Nós podemos ajuda-lo ao
    prover uma declaração explícita de tipo (então o Coq
    terá mais informações disponíveis quando ocorrer a "aplicação"
    de [nil]): *)

Definition mynil : list nat := nil.

(** Alternativamente, nós podemos força o argumento implícito para ser
   explicito, prefixando o nome da função com [@]. *)

Check @nil.

Definition mynil' := @nil nat.

(** *** *)
(** Usando síntese de argumentos e argumentos implícitos, podemos 
    definir uma notação conveniente para as listas, como antes. 
    Uma vez que tornamos os tipos de argumentos do construtor 
    implícitos, Coq saberá inferi-los automaticamente quando 
    usarmos as notações. *)

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(** Agora listas podem ser escritas exatamente como esperávamos: *)

Definition list123''' := [1; 2; 3].

(* ###################################################### *)
(** *** Exercícios: Listas Polimórficas *)

(** **** Exercise: 2 stars, optional (poly_exercises)  *)
(** Temos aqui alguns exercícios simples, como aqueles do capítulo [Listas],
    para praticar o uso de polimorfismo. Preencha as definições e complete as
    provas abaixo.*)

Fixpoint repeat {X : Type} (n : X) (count : nat) : list X :=
  (* PREENCHA AQUI *) admit.

Example test_repeat1:
  repeat true 2 = cons true (cons true nil).
 (* PREENCHA AQUI *) Admitted.

Theorem nil_app : forall X:Type, forall l:list X,
  app [] l = l.
Proof.
  (* PREENCHA AQUI *) Admitted.

Theorem rev_snoc : forall X : Type,
                     forall v : X,
                     forall s : list X,
  rev (snoc s v) = v :: (rev s).
Proof.
  (* PREENCHA AQUI *) Admitted.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
(* PREENCHA AQUI *) Admitted.

Theorem snoc_with_append : forall X : Type,
                         forall l1 l2 : list X,
                         forall v : X,
  snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  (* PREENCHA AQUI *) Admitted.
(** [] *)

(* ###################################################### *)
(** ** Pares Polimórficos *)

(** Seguindo o mesmo padrão, a definição de tipo que demos no último
    capítulo para pares de números pode ser generalizada para _pares 
    polimórficos_ (ou _produtos_):  *)

Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

(** Tal como para listas, fizemos argumentos de tipo implícito e definimos
    a notação concreta familiar. *)

Notation "( x , y )" := (pair x y).

(** Nós podemos também usasr o mecanismo de [Notation] para definir o padrão
    de notação para _tipos_ pares: *)

Notation "X * Y" := (prod X Y) : type_scope.

(** (A anotação [: type_scope] diz ao Coq que esta abreviação deve ser 
    usada ao analisar tipos. Isso evita um conflito com o símbolo de 
    multiplicação.) *)

(** *** *)

(** Uma nota de cautela: no início é fácil se confundir entre [(x,y)] e [X*Y]. 
Lembre-se que [(x,y)] é um _valor_ construído a partir de outros dois valores e 
[X*Y] é um _tipo_ construído a partir de dois outros tipos. Se [x] possui o 
tipo [X] e [y] possui o tipo [Y], então [(x,y)] possui o tipo [X*Y]. *)

(** Agora a primeira e a segunda função de projeção se parecem muito com o que
    seriam em qualquer linguagem de programação funcional. *)

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with (x,y) => x end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with (x,y) => y end.

(** A função seguinte usa duas listas e as combina em uma lista de pares.
    Em muitas linguagens de programação funcional, isso é chamado [zip].
    Nós chamamos isso de [combine] ("combinar") para ter consistência com
    a biblioteca padrão do Coq. *)
(** Perceba que a notação em par pode ser utilizada tanto para expressões e
    padrões... *)

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match (lx,ly) with
  | ([],_) => []
  | (_,[]) => []
  | (x::tx, y::ty) => (x,y) :: (combine tx ty)
  end.

(** **** Exercício: nível 1, opcional (combine_checks)  *)
(** Tente responder as questões adiante no papel e
    cheque suas respostas no Coq:
    - Qual é o tipo de [combine] (ex., O que imprime [Check @combine]?)
    - O que imprime
        Eval compute in (combine [1;2] [false;false;true;true]).?   []
*)

(** **** Exercício: nível 2 (split)  *)
(** A função [split] é justamente o inverso de combine: recebe uma 
    lista de pares e retorna um par de listas. Em muitas linguagens de 
    programação funcionais, essa função é chamada de [unzip].

 Retire os comentários do material abaixo e insira a definição de [split]. 
 Certifique-se de que ele passa nos testes de unidade dados. *)

Fixpoint split
           {X Y : Type} (l : list (X*Y))
           : (list X) * (list Y) :=
(* PREENCHA AQUI *) admit.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
(* PREENCHA AQUI *) Admitted.
(** [] *)

(* ###################################################### *)
(** ** Opções Polimórficas *)

(** Um último tipo polimórfico por enquanto: _opções polimórficas_. A declaração
    de tipo generaliza aquela de [natoption] do capítulo anterior: *)

Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.

Arguments Some {X} _. 
Arguments None {X}. 

(** *** *)
(** Nós podemos agora reescrever a função [index] para que ela funcione
    com qualquer tipo de listas. *)

Fixpoint index {X : Type} (n : nat)
               (l : list X) : option X :=
  match l with
  | [] => None
  | a :: l' => if beq_nat n O then Some a else index (pred n) l'
  end.

Example test_index1 :    index 0 [4;5;6;7]  = Some 4.
Proof. reflexivity.  Qed.
Example test_index2 :    index  1 [[1];[2]]  = Some [2].
Proof. reflexivity.  Qed.
Example test_index3 :    index  2 [true]  = None.
Proof. reflexivity.  Qed.

(** **** Exercise: 1 star, optional (hd_opt_poly)  *)
(** Completar a definção de uma versão polimórfica da função
    [hd_opt] apresentada no último capítulo. Certifique-se que ela
    passa nos testes de unidade abaixo. *)

Definition hd_opt {X : Type} (l : list X)  : option X :=
  (* PREENCHA AQUI *) admit.

(** Outra vez, para forçar o argumento implícito seja explicito,
    nós podemos usar [@] antes do nome da função *)

Check @hd_opt.

Example test_hd_opt1 :  hd_opt [1;2] = Some 1.
 (* PREENCHA AQUI *) Admitted.
Example test_hd_opt2 :   hd_opt  [[1];[2]]  = Some [1].
 (* PREENCHA AQUI *) Admitted.
(** [] *)

(* ###################################################### *)
(** * Funções como Dados *)
(* ###################################################### *)
(** ** Funções de Ordem Superior *)

(** Como muitas outras linguagens de programação modernas - incluindo 
    todas as _linguagens funcionais_ (ML, Haskell, Scheme, etc.) -- 
    Coq trata funções como cidadãos de primeira classe, permitindo 
    que funções sejam passadas como argumentos para outras funções, 
    retornadas como resultados, armazenadas em estruturas de dados, 
    etc.

	Funções que manipulam outras funções são muitas vezes chamadas funções de 
	_ordem superior_. Abaixo um exemplo simples: *)

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

(** O argumento [f] aqui é, por si só, uma função (de [X] para [X]); o corpo de
    [doit3times] aplica [f] três vezes para algum valor [n]. *)

Check @doit3times.
(* ===> doit3times : forall X : Type, (X -> X) -> X -> X *)

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity.  Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity.  Qed.

(* ###################################################### *)
(** ** Aplicação Parcial *)

(** De fato, as funções de múltipo argumento que já vimos são também
    exemplos de passar funções como dados. Para ver o porquê, relembre
    o tipo de [plus]. *)

Check plus.
(* ==> nat -> nat -> nat *)

(** Cada [->] nesta expressão na verdade é um operador _binário_
    em tipos.  (Isto é o mesmo que dizer que o Coq primitivamente
    suporta somente funções de um argumento -- você vê o porquê?)  Esse
    operador é _associativo à direita_, então o tipo de [plus] é realmente um
    atalho para [nat -> (nat -> nat)] -- isto é, isto pode ser lido como
    dizendo que "[plus] é uma função de um argumento que toma um [nat]
    e returna uma função de um argumento que toma outro [nat] e
    retorna um [nat]."  No exemplo acima, nós sempre aplicamos
    [plus] para os dois argumentos de uma vez, mas, se quisermos, podemos
    fornencer somente o primeiro.  Isto é chamado de _aplicação parcial_. *)

Definition plus3 := plus 3.
Check plus3.

Example test_plus3 :    plus3 4 = 7.
Proof. reflexivity.  Qed.
Example test_plus3' :   doit3times plus3 0 = 9.
Proof. reflexivity.  Qed.
Example test_plus3'' :  doit3times (plus 3) 0 = 9.
Proof. reflexivity.  Qed.

(* ###################################################### *)
(** ** Digressão: Currificação *)

(** **** Exercício: 2 estelas, avançado (currying)  *)
(** Em Coq, uma função [f : A -> B -> C] realmente tem o tipo [A
    -> (B -> C)]. Isto é, se você dar [f] um valor do tipo [A], ele dará
    uma função [f' : B -> C]. Se você então dar [f'] um valor do tipo [B], ele
    retornará um valor do tipo [C]. Isto permite para aplicações parcial, como em 
    [plus3]. Processando uma lista de argumentos com funções que retornam funções
    é chamando de _curring_, em honra ao lógico Haskell Curry.

    Por outro lado, podemos reinterpretar o tipo [A -> B -> C] como 
    [(A * B) -> C]. Isto é chamado de _uncurrying_. Para uma função 
    binária que tenha sofrido _uncurry_, ambos os argumentos devem 
    ser dados de uma vez como um par; não há possibilidade de 
    aplicação parcial.
    
    *)

(** Nós podemos definir currying da seguinte forma: *)

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

(** Como exercício, defina sua inversa, [prod_uncurry]. Em seguida, prove os
    teoremas abaixo para mostrar que as duas funções são inversas. *)

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z :=
  (* PREENCHA AQUI *) admit.

(** Exercício de pensamento. Antes de rodar esses comandos, você
    pode calcular os tipos de [prod_curry] e [prod_uncurry]?) *) 

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  (* PREENCHA AQUI *) Admitted.

Theorem curry_uncurry : forall (X Y Z : Type)
                               (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  (* PREENCHA AQUI *) Admitted.
(** [] *)

(* ###################################################### *)
(** ** Filtrar *)

(** Aqui está uma útil função de ordem superior, que toma uma lista
    de [X]s e um _predicado_ em [X] (uma função a partir de [X] para [bool])
    e "filtra" a lista, retornando uma nova lista contendo somente aqueles
    elementos que o predicado retorna [true]. *)

Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.

(** Por exemplo, se nós aplicarmos [filter] para o predicado [evenb]
    e uma lista de números [l], ele retorna uma lista contendo apenas os números
    pares de [l]. *)

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity.  Qed.

(** *** *)
Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity.  Qed.

(** *** *)

(** Nós podemos usar [filter] para fornecer uma versão concisa 
    da função [countoddmembers] do capítulo [Lists]. *)

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1:   countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity.  Qed.
Example test_countoddmembers'2:   countoddmembers' [0;2;4] = 0.
Proof. reflexivity.  Qed.
Example test_countoddmembers'3:   countoddmembers' nil = 0.
Proof. reflexivity.  Qed.

(* ###################################################### *)
(** ** Funções Anônimas *)

(** É um pouco chato ser forçado a definir a função [length_is_1] e dar-lhe um 
nome apenas para poder passá-lo como argumento para [filter], uma vez que, 
provavelmente, nunca mais a usaremos novamente. Além disso, este não é um 
exemplo isolado. Quando utilizamos funções de ordem superior, muitas vezes 
queremos passar, como argumentos, funções que nunca mais usaremos novamente: 
ter de denominar cada uma dessas funções pode ser uma ação bem tediosa.

    Felizmente, há uma maneira melhor. É também possível construir uma função
    "diretamente" sem declará-lo no nível topo ou nomeá-la; isto é análogo
    à notação que temos utilizado para escrever listas constantes, números
    naturais e etc. *)

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity.  Qed.

(** Aqui está o exemplo motivacional de antes, reescrito para usar
    uma função anônima. *)

Example test_filter2':
    filter (fun l => beq_nat (length l) 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity.  Qed.

(** **** Exercise: 2 stars (filter_even_gt7)  *)

(** Usar [filter] (no lugar de [Fixpoint]) para escrever uma função em Coq
    [filter_even_gt7] que toma uma lista de números naturais como entrada e
    retorna uma lista de números somente maiores ou iguais a
    7. *)

Definition filter_even_gt7 (l : list nat) : list nat :=
  (* PREENCHA AQUI *) admit.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
 (* PREENCHA AQUI *) Admitted.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
 (* PREENCHA AQUI *) Admitted.
(** [] *)

(** **** Exercício: nível 3 (partição)  *)
(** Use [filter] para escrever uma função Coq [partition]:
  partition : forall X : Type,
              (X -> bool) -> list X -> list X * list X
   Dado um conjunto [X], uma função teste do tipo [X -> bool] e um [list X],
   [partition] deve retornar um par de listas. O primeiro membro do par
   é a sublista da lista origanl contendo os elementos que satisfaz o teste,
   e o segundo é a sublista contendo aqueles que falharam no teste. A ordem
   dos elementos nos duas sublistas devem ser a mesma ordem da lista original. *)

Definition partition {X : Type} (test : X -> bool) (l : list X)
                     : list X * list X :=
(* PREENCHA AQUI *) admit.

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
(* PREENCHA AQUI *) Admitted.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
(* PREENCHA AQUI *) Admitted.
(** [] *)

(* ###################################################### *)
(** ** Mapear *)

(** Outra função útil de ordem superior é chamada [map]. *)

Fixpoint map {X Y:Type} (f:X->Y) (l:list X)
             : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

(** *** *)

(** Seus argumentos são uma função [f] e uma lista [ l = [n1, n2, n3, ...] ] e 
retorna a lista [ [f n1, f n2, f n3,...] ], no qual [f] foi aplicada em cada 
elemento de [l] sucessivamente. Por exemplo: *)

Example test_map1: map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity.  Qed.

(** Os tipos de elementos das listas de entrada e saída não precisam ser os
mesmos ([map] recebe _dois_ argumentos de tipo, [X] e [Y]). Esta versão de [map]
pode, portanto, ser aplicada a uma lista de números e uma função de números para
booleanos a fim de produzir uma lista de booleanos: *)

Example test_map2: map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity.  Qed.

(** Isso pode até ser aplicado a uma lista de numeros e
    uma função de números para _listas_ de boleanos para 
    produzir uma lista de listas de boleanos: *)

Example test_map3:
    map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity.  Qed.



(** ** Mapear para Opções *)
(** **** Exercise: 3 stars (map_rev)  *)
(** Mostrar que [map] e [rev] comutam.  Você pode precisar definir um
    lema auxiliar. *)


Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  (* PREENCHA AQUI *) Admitted.
(** [] *)

(** **** Exercício: nível 2 (flat_map)  *)
(** A função [map] mapeiaum [list X] para uma [list Y] usando uma função
    do tipo [X -> Y]. Nós podemos definir uma função similar, [flap_map],
    [X -> list Y]. Sua definição deve funcionar pelo 'achatamento' dos 
    resultados de [f], como em:
        flat_map (fun n => [n;n+1;n+2]) [1;5;10]
      = [1; 2; 3; 5; 6; 7; 10; 11; 12].
*)

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X)
                   : (list Y) :=
  (* PREENCHA AQUI *) admit.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
 (* PREENCHA AQUI *) Admitted.
(** [] *)

(** Listas não são o único tipo indutivo para o qual podemos escrever 
    uma função [map]. Aqui está a definição de [map] para o tipo 
    [option]: *)

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

(** **** Exercício: nível 2, opcional (implicit_args)  *)

(** As definições e usos de [filter] e [map] usam argumentos implícitos em 
vários lugares. Substitua as chaves ao redor dos argumentos implícitos com 
parênteses e, em seguida, preencha-os com parâmetros de tipos explícitos onde 
são necessários, usando o Coq para verificar que você preencheu corretamente. 
(Este exercício não é pra ser feito aqui; provavelmente é mais fácil fazê-lo 
numa _cópia_ deste arquivo, eliminando-o posteriormente.) [] *)

(* ###################################################### *)
(** ** Dobrar *)

(** Uma função de ordem superior ainda mais poderosa chama-se [fold]. Esta
função é a inspiração para a operação "[reduce]" que está no "coração" do
framework de programação distribuída map/reduce do Google. *)

Fixpoint fold {X Y:Type} (f: X->Y->Y) (l:list X) (b:Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(** *** *)

(** Intuitivamente, o comportamento da operação [fold] é inserir um 
    operador binário [f] entre todo par de elementos em uma lista dada.
    Por exemplo, [ fold plus [1;2;3;4] ] intuitivamente significa 
    [1+2+3+4]. Para fazer isso ser preciso, nós tambpem precisamos de 
    um "elemento inicial" que serve como uma segunda entrada inicial 
    para [f]. Então, por exemplo, 
   fold plus [1;2;3;4] 0
    yields
   1 + (2 + (3 + (4 + 0))).
    Aqui estão alguns outros exemplos:
*)

Check (fold andb).
(* ===> fold andb : list bool -> bool -> bool *)

Example fold_example1 : fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 : fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 : fold app  [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.


(** **** Exercise: 1 star, advanced (fold_types_different)  *)
(** Observe que o tipo de [fold] é parametrizado por _duas_ variavéis
    de tipos, [X] e [Y], e o parâmetro [f] é um operador binário
    que toma um [X] e um [Y] e retornar um [Y].  Você consegue pensar em uma
    situação em que pode ser útil para [X] e [Y] serem
    diferentes? *)

(* ###################################################### *)
(** ** Funções Para Construir Funções*)

(** A maioria das funções de ordem superior que nós temos falados até então
    levam funções como _argumentos_. Agora vamos olhar o mesmo exemplo
    envolvendo funções de _retorno_ como o resultado de outras funções.

    Para começar, aqui está uma função que recebe um valor [x] (tirado 
    de algum tipo [X]) e retorna uma função de [nat] para [X] que 
    retorna [x] sempre que é chamada, ignorando seu argumento [nat]. *)

Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

(** *** *)

(** Igualmente, porém de uma forma mais interessante, é mostrada abaixo uma 
função que possui, como argumentos, uma função [f] de números para algum tipo 
[X], um número [k] e um valor [x], e constrói uma função que se comporta 
exatamente como [f] exceto que, quando chamado com o argumento [k], ele retorna 
[x].*)

Definition override {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
  fun (k':nat) => if beq_nat k k' then x else f k'.

(** Por exemplo, podemos aplicar [override] duas vezes para obter a função de
números para booleanos que retorna [false] para [1] e [3] e [true] para todos os
outros argumentos. *)

Definition fmostlytrue := override (override ftrue 1 false) 3 false.

(** *** *)

Example override_example1 : fmostlytrue 0 = true.
Proof. reflexivity. Qed.

Example override_example2 : fmostlytrue 1 = false.
Proof. reflexivity. Qed.

Example override_example3 : fmostlytrue 2 = true.
Proof. reflexivity. Qed.

Example override_example4 : fmostlytrue 3 = false.
Proof. reflexivity. Qed.

(** *** *)

(** **** Exercício: nível 1 (override_example)  *)
(** Antes de começar a trabalhar na prova seguinte, tenha certeza que
    você entendeu exatamente o que o teorema está dizendo e pode você
    parafrasear isso em suas próprias palavras. A prova em si é simples. *)

Theorem override_example : forall (b:bool),
  (override (constfun b) 3 true) 2 = b.
Proof.
  (* PREENCHA AQUI *) Admitted.
(** [] *)

(** Nós vamos utilizar a função _overriding_ várias vezes em partes do resto do
    curso, e nós vamos acabar precisando saber um pouco sobre suas
    propriedades.  Para provar essas propriedades, porém, nós precisaremos 
    conhecer um pouco mais sobre as táticas do Coq; desenvolver elas é o tópico
    principal do próximo capítulo.  Por enquanto, porém, vamos introduzir
    somente uma tática muito útil que irá também nos ajudar a provar
    algumas propriedades das outras funções que introduzimos nesse
    capítulo. *)

(* ###################################################### *)

(* ###################################################### *)
(** * A Tática [unfold] *)

(** As vezes, uma prova ficará presa porque Coq não expande
    automaticamente a chamada de função para a sua definição.
    (Isto é uma caracteristica, não um erro: se Coq automaticamente
    expandir tudo que é possível, nossa prova de objetivos rapidamente
    ficará enorme -- difícil de ler e demorado para Coq manipular!) *)

Theorem unfold_example_bad : forall m n,
  3 + n = m ->
  plus3 n + 1 = m + 1.
Proof.
  intros m n H.
(* Neste ponto, nós gostaríamos de fazer [rewrite -> H], 
     uma vez que [Plus3 n] é por definição igual a [3 + n]. 
     No entanto, Coq não expande automaticamente [Plus3 n] 
     à sua definição. *)
  Abort.

(** A tática [unfold] pode ser usada para substituir explicitamente um nome 
definido pelo lado direito de sua definição. *)

Theorem unfold_example : forall m n,
  3 + n = m ->
  plus3 n + 1 = m + 1.
Proof.
  intros m n H.
  unfold plus3.
  rewrite -> H.
  reflexivity.  Qed.

(** Agora podemos provar uma primeira propriedade de [override]: Se
sobrescrevermos uma função em algum argumento [k] e, em seguida, consultramos
[k], receberemos de volta o valor sobrescrito. *)

Theorem override_eq : forall {X:Type} x k (f:nat->X),
  (override f k x) k = x.
Proof.
  intros X x k f.
  unfold override.
  rewrite <- beq_nat_refl.
  reflexivity.  Qed.

(** Essa prova foi simples, mas note que ela precisou do [unfold] 
    para expandir a definição de [override]. *)

(** **** Exercise: 2 stars (override_neq)  *)
Theorem override_neq : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  f k1 = x1 ->
  beq_nat k2 k1 = false ->
  (override f k2 x2) k1 = x1.
Proof.
  (* PREENCHA AQUI *) Admitted.
(** [] *)

(** Tal como o inverso de [unfold], Coq também fornece uma tática
    [fold], que pode ser utilizada para uma definição "inexpansível".  Ele é usado
    com muito menos frequência. *)

(* ##################################################### *)
(** * Exercícios Adicionais *)

(** **** Exercício: nível 2 (fold_length)  *)
(** Muitas funções comuns de listas podem ser implementadas em termo de 
    [fold]. Por exemplo, aqui está uma alternativa da definição de [length]: *)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

(** Prove a corretude de [fold_length]. *)

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
(* PREENCHER *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (fold_map)  *)
(** Nós podemos também definir [map] em termos de [fold]. Finalize [fold_map] 
mostrada abaixo. *)


Definition fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y :=
(* PREENCHA AQUI *) admit.

(** Escreva um teorema [fold_map_correct] em Coq afirmando que [fold_map]
é correto e prove-o. *)

(* PREENCHA AQUI *)
(** [] *)

(** **** Exercício: nível 2, avançado (index_informal)  *)
(** Relembre a definição da função [index]:
   Fixpoint index {X : Type} (n : nat) (l : list X) : option X :=
     match l with
     | [] => None 
     | a :: l' => if beq_nat n O then Some a else index (pred n) l'
     end.
   Escreva uma prova informal do seguinte teorema:
   forall X n l, length l = n -> @index X n l = None.
(* PREENCHA AQUI *)
*)
(** [] *)

(** **** Exercício: nível 4, avançado (church_numerals)  *)

Module Church.

(** Neste exercício, vamos explorar um modo alternativo de definir
    números naturais, utilizando os chamados _numerais de Church_, em
    homenagem ao matemático Alonzo Church. Nós podemos representar um número
    natural [n] como uma função que toma uma função [f] como um parâmetro
    e retorna [f] iterado [n] vezes. Mais formalmente, *)

Definition nat := forall X : Type, (X -> X) -> X -> X.

(** Vamos ver como escrever alguns número com esta notação. Qualquer
    função [f] interado uma vez não deve mudar. Assim,  *)

Definition one : nat := 
  fun (X : Type) (f : X -> X) (x : X) => f x.

(** [two] deve aplicar [f] duas vezes a seu argumento: *)

Definition two : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

(** [zero] é um pouco mais complicado: como poderemos aplicar a função zero 
vezes? A resposta é simples: apenas não toque no argumento. *)

Definition zero : nat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

(** De maneira mais geral, um número [n] será escrito como [fun X f x => f (f
... (f x) ...)], com [n] ocorrências de [f]. Perceba, em particular, como
a função [doit3times] que definimos anteriormente é, na verdade, apenas
a representação de [3].

Definition three : nat := @doit3times.

(** Complete as definições das seguintes funções. Tenha certeza de que
    os testes de unidade correspondentes passem, provando eles com 
    [reflexivity]. *)    


(** Successor de um número natural *)

Definition succ (n : nat) : nat :=
  (* PREENCHA AQUI *) admit.

Example succ_1 : succ zero = one.
Proof. (* PREENCHA AQUI *) Admitted.

Example succ_2 : succ one = two.
Proof. (* PREENCHA AQUI *) Admitted.

Example succ_3 : succ two = three.
Proof. (* PREENCHA AQUI *) Admitted.

(** Adição de dois número naturais *)

Definition plus (n m : nat) : nat :=
  (* PREENCHA AQUI *) admit.

Example plus_1 : plus zero one = one.
Proof. (* PREENCHA AQUI *) Admitted.

Example plus_2 : plus two three = plus three two.
Proof. (* PREENCHA AQUI *) Admitted.

Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. (* PREENCHA AQUI *) Admitted.

(** Multiplicação *)

Definition mult (n m : nat) : nat := 
  (* PREENCHA AQUI *) admit.

Example mult_1 : mult one one = one.
Proof. (* PREENCHA AQUI *) Admitted.

Example mult_2 : mult zero (plus three three) = zero.
Proof. (* PREENCHA AQUI *) Admitted.

Example mult_3 : mult two three = plus three three.
Proof. (* PREENCHA AQUI *) Admitted.

(** Exponenciação *)

(** Dica: Polimorfismo tem um papel crucial aqui. Porém, escolher o tipo certo 
para a iteração pode ser complicado. Se você chegar a um erro de 
"inconsistência do Universo", tente iterar sobre um tipo diferente: o próprio 
[nat] geralmente é problemático. *)

Definition exp (n m : nat) : nat :=
  (* PREENCHA AQUI *) admit.

Example exp_1 : exp two two = plus two two.
Proof. (* PREENCHA QUI *) Admitted.

Example exp_2 : exp three two = plus (mult two (mult two two)) one.
Proof. (* PREENCHA AQUI *) Admitted.

Example exp_3 : exp three zero = one.
Proof. (* PREENCHA AQUI *) Admitted.

End Church.

(** [] *)

(** $Date: 2014-12-31 11:17:56 -0500 (Wed, 31 Dec 2014) $ *)


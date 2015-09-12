(** * Listas: Trabalhando com Dados Estruturados *)

Require Export Induction.

Module NatList. 

(* ###################################################### *)
(** * Pares de Números *)

(** Em uma definição de tipo indutivo usando [Inductive], cada construtor pode
ter qualquer número de argumentos -- nenhum (como ocorre com [true] e [0]), um
(como ocorre com [S]), ou mais de um, como na seguinte definição: *)

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.

(** [ Dalay ] This declaration can be read: "There is just one way to
    construct a pair of numbers: by applying the constructor [pair] to
    two arguments of type [nat]." *)

(** Nós podemos construir um elemento de [natprod] dessa maneira: *)

Check (pair 3 5).

(** *** *)

(** Aqui estão duas simples definições de função para extrair o
    primeiro e o segundo componente de um par. (As definições também
    ilustram como fazer o casamento de padrões com dois argumentos.) *)

Definition fst (p : natprod) : nat := 
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat := 
  match p with
  | pair x y => y
  end.

Eval compute in (fst (pair 3 5)).
(* ===> 3 *)

(** *** *)

(** Dado que pares são bastante usados, é bom ser capaz de escrevê-los 
    com a notação matemática padrão [(x, y)] em vez de [pair xy]. 
    Podemos dizer ao Coq para permitir isso com uma declaração 
    [Notation]. *)

Notation "( x , y )" := (pair x y).

(** A nova notação pode ser usada tanto em expressões quanto no
 casamento de padrões (de fato, nós ja vimos isto no capítulo anterior
 -- esta notação é disponibilizada pela biblioteca padrão): *)
    
Eval compute in (fst (3,5)).

Definition fst' (p : natprod) : nat := 
  match p with
  | (x,y) => x
  end.
Definition snd' (p : natprod) : nat := 
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod := 
  match p with
  | (x,y) => (y,x)
  end.

(** *** *)

(** Vamos testar e provar alguns fatos simples sobre pares. Se definirmos os
lemas de uma forma particular (e um pouco peculiar), podemos prová-los apenas
usando reflexividade (e sua simplificação implícita): *)

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.  Qed.

(** [ Dalay ] Note that [reflexivity] is not enough if we state the lemma in a
    more natural way: *)

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* Não reduz nada! *)
Abort.

(** *** *)
(** Nós temos que expor a estrutura de [p], de tal maneira que [simpl] 
    possa realizar o casamento de padrão em [fst] e em [snd].  
    Nós podemos fazer isso através de [destruct].

    Notar que, ao contrário para [nat]s, [destruct] não gera uma
    submeta extra aqui.  Isso porque [natprod]s pode apenas ser contruído
    de uma única maneira.  *)

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p.  destruct p as [n m].  simpl.  reflexivity.  Qed.

(** **** Exercício: * ([ snd_fst_is_swap ])  *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: *, opcional ([ fst_swap_is_snd ])  *)
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(* ###################################################### *)
(** * Listas de Números *)

(** Generalizando a definição de pares um pouco, podemos descrever 
    o tipo de _listas_ de números da seguinte forma: "A lista é ou 
    a lista vazia ou então um par contendo um número e outra 
    lista." *)

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

(** Por exemplo, se encontra abaixo uma lista de três elementos: *)

Definition mylist := cons 1 (cons 2 (cons 3 nil)).


(** *** *)
(** Tal como acontece com os pares, é mais conveniente escrever listas usando
notações habituais de programação. As duas declarações à seguir nos permitem
usar [::] como um operador infixo [cons] e colchetes como uma notação "externa"
para a construção de listas. *)

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(** [ Dalay ] It is not necessary to fully understand these declarations,
    but in case you are interested, here is roughly what's going on.

    A anotação [right associativity] (_associatividade à direita_) diz ao Coq
    como utilizar parênteses em expressões envolvendo o uso de muitos [::], 
    então, por exemplo, as três próximas declarações significam exatamente a mesma coisa: *)

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

(** A parte [at level 60] fala para Coq como colocar em parênteses
    expressões que envolvem ambos [::] e algum outro operador infixo.
    Por exemplo, desde nós definimos [+] como uma notação infixa para a função [plus]
    no nível 50,
Notation "x + y" := (plus x y)  
                    (at level 50, left associativity).
   O operador [+] irá fazer uma ligação mais apertada do que [::], então [1 + 2 :: [3]]
   será analisada, como nós esperamos, como [(1 + 2) :: [3]] em vez de [1
   + (2 :: [3])].

   (A propósito, vale a pena notar de passagem que expressões como "[1
    + 2 :: [3]]" podem ser um pouco confusas quando você as lê em um 
    arquivo .v. Os colchetes internos, cerca de 3, indicam uma lista, 
    porém os colchetes externos, que são invisíveis na renderização 
    do HTML, estão lá para instruir à ferramenta "coqdoc" que a 
    parte entre colchetes deve ser exibida como código Coq em vez 
    de texto comum.)

A segunda e a terceira declaração de [Notation] acima introduzem a
 notação padrão de colchetes para listas; o lado direito da terceira
 declaração ilustra a sintaxe do Coq para declarar notações n-árias  e
 traduzi-las para sequências aninhadas de construtores binários. *)  
 
(** *** Repetição *)

(** Algumas funções são úteis para a manipulação de listas. Por exemplo,
  a função [repeat] recebe os números [n] e [count] e retorna uma lista com
  comprimento [count] e elementos [n]. *)

Fixpoint repeat (n count : nat) : natlist := 
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

(** *** Comprimento *)

(** [ Dalay ] The [length] function calculates the length of a list. *)

Fixpoint length (l:natlist) : nat := 
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

(** *** Concatenação *)
(** A função [app] "append" (_anexar_) concatena duas listas. *)

Fixpoint app (l1 l2 : natlist) : natlist := 
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

(** Atualmente, [app] será muito usado em algumas partes do que vem
    a seguir, então é conveniente ter um operador infixo para ele. *)

Notation "x ++ y" := (app x y) 
                     (right associativity, at level 60).

Example test_app1:             [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity.  Qed.
Example test_app2:             nil ++ [4;5] = [4;5].
Proof. reflexivity.  Qed.
Example test_app3:             [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity.  Qed.

(** Aqui estão dois exemplos menores de programação com listas. 
    A função [hd] retorna o primeiro elemento (o "cabeça") da lista,
    enquanto [tl] retorna tudo exceto o primeiro elemento (a "cauda"). 
    Obviamente, a lista vazia não tem primeiro elemento, por isso, 
    devemos fornecer um valor padrão a ser retornado nesse caso. *)

(** *** Cabeça (com default) e cauda *)

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil  
  | h :: t => t
  end.

Example test_hd1:             hd 0 [1;2;3] = 1.
Proof. reflexivity.  Qed.
Example test_hd2:             hd 0 [] = 0.
Proof. reflexivity.  Qed.
Example test_tl:              tl [1;2;3] = [2;3].
Proof. reflexivity.  Qed.

(** **** Exercício: ** ([ list_funs ])  *)

(** Complete as definições de [nonzeros], [oddmembers] e
[countoddmembers] abaixo. Dê uma olhada nos testes para entender o que
estas funções devem fazer. *)

Fixpoint nonzeros (l:natlist) : natlist :=
  (* PREENCHER *) admit.

Example test_nonzeros:            nonzeros [0;1;0;2;3;0;0] = [1;2;3].
 (* PREENCHER *) Admitted.

Fixpoint oddmembers (l:natlist) : natlist :=
  (* PREENCHER *) admit.

Example test_oddmembers:            oddmembers [0;1;0;2;3;0;0] = [1;3].
 (* PREENCHER *) Admitted.

Fixpoint countoddmembers (l:natlist) : nat :=
  (* PREENCHER *) admit.

Example test_countoddmembers1:    countoddmembers [1;0;3;1;4;5] = 4.
 (* PREENCHER *) Admitted.
Example test_countoddmembers2:    countoddmembers [0;2;4] = 0.
 (* PREENCHER *) Admitted.
Example test_countoddmembers3:    countoddmembers nil = 0.
 (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: 3 stars, avançado (alternar)  *)

(** Complete a definição de [alternate], que "compacta" duas listas em uma só,
  alternando entre elementos retirados da primeira lista e elementos da segunda
  lista. Veja os testes abaixo para exemplos mais específicos.

    [ Dalay ] Note: one natural and elegant way of writing [alternate] will fail
    to satisfy Coq's requirement that all [Fixpoint] definitions be "obviously
    terminating."  If you find yourself in this rut, look for a slightly more
    verbose solution that considers elements of both lists at the same time.
    (One possible solution requires defining a new kind of pairs, but this is
    not the only way.)  *)


Fixpoint alternate (l1 l2 : natlist) : natlist :=
  (* PREENCHER *) admit.

Example test_alternate1:        alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
 (* PREENCHER *) Admitted.
Example test_alternate2:        alternate [1] [4;5;6] = [1;4;5;6].
 (* PREENCHER *) Admitted.
Example test_alternate3:        alternate [1;2;3] [4] = [1;4;2;3].
 (* PREENCHER *) Admitted.
Example test_alternate4:        alternate [] [20;30] = [20;30].
 (* PREENCHER *) Admitted. 
(** [] *)

(* ###################################################### *)
(** ** Multiconjuntos com Listas *)

(** Uma [bag] (ou [multiconjunto]) é como um conjunto, mas cada
    elemento pode aparecer múltiplas vezes, em vez de unicamente.  Uma 
    implementação razoável de multiconjuntos é representar um multiconjunto 
    de números através de uma lista. *)

Definition bag := natlist.  

(** **** Exercício: *** (bag_functions)  *)

(** Complete as definições para as funções
    [count], [sum], [add], e [member] para multiconjunto. *)

Fixpoint count (v:nat) (s:bag) : nat := 
  (* PREENCHER *) admit.

(** Todas estas provas podem ser feitas usando apenas [reflexivity]. *)

Example test_count1:              count 1 [1;2;3;1;4;1] = 3.
 (* PREENCHER *) Admitted.
Example test_count2:              count 6 [1;2;3;1;4;1] = 0.
 (* PREENCHER *) Admitted.

(** A função [sum] para multiconjuntos é similar à função [união] para
conjuntos: [sum a b] contém todos os elementos de [a] e
[b]. (Geralmente os matemáticos definem [union] em multiconjuntos de
forma um pouquinho diferente, por isto que não estamos usando o mesmo
nome para esta operação.)
Para a função [sum] lhe daremos uma declaração que não determina
explicitamente os nomes dos argumentos. Além disso, é utilizada a
palavra-chave [Definition] ao invés de [Fixpoint]. Então, mesmo que
você tivesse nome para os argumentos, não seria possível processá-los
recursivamente.
O motivo de declarar esta questão desta forma é encorajá-lo a pensar
se [sum] pode ser implementado de uma maneira diferente -- talvez
através de funções que já foram definidas. *) 

Definition sum : bag -> bag -> bag := 
  (* PREENCHER *) admit.

Example test_sum1:              count 1 (sum [1;2;3] [1;4;1]) = 3.
 (* PREENCHER *) Admitted.

Definition add (v:nat) (s:bag) : bag := 
  (* PREENCHER *) admit.

Example test_add1:                count 1 (add 1 [1;4;1]) = 3.
 (* PREENCHER *) Admitted.
Example test_add2:                count 5 (add 1 [1;4;1]) = 0.
 (* PREENCHER *) Admitted.

Definition member (v:nat) (s:bag) : bool := 
  (* PREENCHER *) admit.

Example test_member1:             member 1 [1;4;1] = true.
 (* PREENCHER *) Admitted.
Example test_member2:             member 2 [1;4;1] = false.
 (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: ***, opcional (bag_more_functions)  *)

(** Aqui estão mais algumas funções de multiconjuntos com as quais você pode
praticar. *)

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  (* [ Dalay ] When remove_one is applied to a bag without the number to remove,
     it should return the same bag unchanged. *)
  (* PREENCHER *) admit.

Example test_remove_one1:         count 5 (remove_one 5 [2;1;5;4;1]) = 0.
 (* PREENCHER *) Admitted.
Example test_remove_one2:         count 5 (remove_one 5 [2;1;4;1]) = 0.
 (* PREENCHER *) Admitted.
Example test_remove_one3:         count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
 (* PREENCHER *) Admitted.
Example test_remove_one4:         count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
 (* PREENCHER *) Admitted.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  (* PREENCHER *) admit.

Example test_remove_all1:          count 5 (remove_all 5 [2;1;5;4;1]) = 0.
 (* PREENCHER *) Admitted.
Example test_remove_all2:          count 5 (remove_all 5 [2;1;4;1]) = 0.
 (* PREENCHER *) Admitted.
Example test_remove_all3:          count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
 (* PREENCHER *) Admitted.
Example test_remove_all4:          count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
 (* PREENCHER *) Admitted.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  (* PREENCHER *) admit.

Example test_subset1:              subset [1;2] [2;1;4;1] = true.
 (* PREENCHER *) Admitted.
Example test_subset2:              subset [1;2;2] [2;1;4;1] = false.
 (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: *** (bag_theorem)  *)

(** Escrever abaixo um teorema interessante, chamado [bag_theorem], sobre 
    multiconjuntos
    envolvendo as funções [count] e [add], e provar o teorema.  Note que, uma
    vez que este problema é aberto, é possível imaginar um teorema
    que é verdadeiro, mas cuja prova requisite técnicas que você ainda
    não aprendeu.  Sinta-se livre para pedir ajuda se você ficar travado! *)

(* PREENCHER *)
(** [] *)

(* ###################################################### *)
(** * Raciocínio Sobre Listas *)

(** Assim como os números, fatos simples sobre funções de 
    processamento de listas pode algumas vezes ser inteiramente provado
    por simplificação. Por exemplo, a simplificação realizada por [reflexivity] 
    é suficiente para este teorema... *)

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

(** ... porque o [[]] é substituído pela sua posição de correspondência
    na definição de [app], permitindo que a própria correspondência 
    seja simplificada. *)

(** Algumas vezes, também é possível, assim como com números, realizar
análise por casos nas possíveis formas (vazia ou não-vazia) de uma lista
desconhecida. *)

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n l'". 
    reflexivity.  Qed.

(** Aqui, o caso [nil] funciona porque nós optamos por definir [tl nil = nil].
Observe que a anotação [as] na tática [destruct] introduz dois nomes, [n]
e [l'], o que corresponde ao fato de que o construtor [cons] para listas tem
dois argumentos (a cabeça e a cauda da lista que está sendo construída). *)

(** [ Dalay ] Usually, though, interesting theorems about lists require
    induction for their proofs. *)

(* ###################################################### *)
(** ** Micro-Sermão *)

(** Simplesmente ler exemplos de transrição de prova não vai te levar muito 
    longe!
    É muito importante trabalhar os detalhes de cada uma das provas,
    quando usar o Coq e pensar sobre o que cada passo da prova realiza.  Senão,
    é mais ou menos garantido que os exercícios não farão
    sentido... *)

(* ###################################################### *)
(** ** Indução sobre Listas *)

(** Provas por indução em tipos de dados como [natlist] são
    talvez um pouco menos familiar do que indução de número natural padrão, 
    mas o ideia base é igualmente simples.  Cada declaração de [Inductive]
    define um conjunto de valores de dados que pode ser contruídos
    a partir de contrutores declarados: um booleano pode ou ser [true] ou
    [false]; um número pode ou ser [O] ou [S] aplicado a um número; uma
    lista pode ser ou [nil] ou [cons] aplicado a um número e a uma lista.

    [ Renan ] Moreover, applications of the declared constructors to one another
    are the _only_ possible shapes that elements of an inductively
    defined set can have, and this fact directly gives rise to a way
    of reasoning about inductively defined sets: a number is either
    [O] or else it is [S] applied to some _smaller_ number; a list is
    either [nil] or else it is [cons] applied to some number and some
    _smaller_ list; etc. So, if we have in mind some proposition [P]
    that mentions a list [l] and we want to argue that [P] holds for
    _all_ lists, we can reason as follows:

      - First, show that [P] is true of [l] when [l] is [nil].

      - Then show that [P] is true of [l] when [l] is [cons n l'] for
        some number [n] and some smaller list [l'], assuming that [P]
        is true for [l'].

Já que listas maiores só podem ser construídas a partir de listas
menores, chegando, em algum momento, em [nil], estas duas sentenças juntas
estabelecem a verdade de [P] para todas as listas [l]. Veja abaixo um
exemplo concreto: *)

Theorem app_assoc : forall l1 l2 l3 : natlist, 
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).   
Proof.
  intros l1 l2 l3. induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons n l1'".
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(** Mais uma vez, esta prova Coq não é especialmente esclarecedora como um
documento estático escrito - é fácil entender o que está acontecendo se você
está lendo a prova em uma sessão Coq interativa e pode ver a meta atual
e o contexto em cada ponto, mas este estado não é visível nas partes registradas
da prova Coq. Assim, uma prova em linguagem natural -- escrita para leitores
humanos -- terá de incluir indicações mais explícitas; em particular, isto
ajudará o leitor a permanecer orientado se nós lembrarmos à ele o que exatamente
é a hipótese de indução no segundo caso. *)

(** *** Versão Informal *)

(** _Theorem_: For all lists [l1], [l2], and [l3], 
   [(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)].

   _Prova_: Por indução sobre [l1].

   - Primeiro, supomos que [l1 = []].  Devemos provar que
       ([] ++ l2) ++ l3 = [] ++ (l2 ++ l3),
     o que segue diretamente da definição de  [++].

   - Segundo, supomos que [l1 = n::l1'], com
       (l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3)
     (a hipótese de indução). Devemos mostrar que
       ((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ (l2 ++ l3).
]]  
     Por definição de [++], isto segue de 
       n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3)),
     o que é uma consequência imediata da hipótese de indução.  []
*)

(** *** Um Outro Exemplo *)
(**
  [ Dalay ] Here is a similar example to be worked together in class: *)

Theorem app_length : forall l1 l2 : natlist, 
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons".
    simpl. rewrite -> IHl1'. reflexivity.  Qed.


(** *** Inversão de uma Lista *)

(** Para um exemplo um pouco mais intricado de uma prova por indução
    sobre listas, supor que nós definimos uma função "cons na direita"
    [snoc], como a que segue... *)

Fixpoint snoc (l:natlist) (v:nat) : natlist := 
  match l with
  | nil    => [v]
  | h :: t => h :: (snoc t v)
  end.

(** ... e use ele para definir função de lista reversa [rev]
    como isso: *)

Fixpoint rev (l:natlist) : natlist := 
  match l with
  | nil    => nil
  | h :: t => snoc (rev t) h
  end.

Example test_rev1:            rev [1;2;3] = [3;2;1].
Proof. reflexivity.  Qed.
Example test_rev2:            rev nil = nil.
Proof. reflexivity.  Qed.

(** *** Provas sobre inversão *)

(** [ Renan ] Now let's prove some more list theorems using our newly
    defined [snoc] and [rev].  For something a little more challenging
    than the inductive proofs we've seen so far, let's prove that
    reversing a list does not change its length.  Our first attempt at
    this proof gets stuck in the successor case... *)

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = []".
    reflexivity.
  Case "l = n :: l'".
    (* Isto é o caso difícil.  Como de praxe, começamos 
       simplificando. *)
       by simplifying. *)
    simpl. 
    (* Agora, parece que estamos travados: a meta é uma
       igualdade envolvendo [snoc], mas não temos 
       equações no contexto imediato, ou no ambiente
       global que tem a ver com [snoc]! 

       Podemos avançar um pouco usando IH para reescrever
       a meta... *)
    rewrite <- IHl'.
    (* ... mas agora não podemos avançar mais. *)
Abort.

(** Agora, consideremos a equação sobre [snoc] que teria nos permitido
progredir: vamos prová-la como um novo lema.
*)

Theorem length_snoc : forall n : nat, forall l : natlist,
  length (snoc l n) = S (length l).
Proof.
  intros n l. induction l as [| n' l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n' l'".
    simpl. rewrite -> IHl'. reflexivity.  Qed. 

(** Observe que descrevemos o lema o mais _geral_ possível: em particular,
quantificamos sobre _todas_ as [natlist]s, e não apenas aquelas que resultam da
aplicação de [rev]. Isso deve parecer natural, porque está claro que
a veracidade da meta não depende da lista que foi invertida. Além disso, é muito
mais fácil provar a propriedade mais geral. *)

(** [ Dalay ] Now we can complete the original proof. *)

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons".
    simpl. rewrite -> length_snoc. 
    rewrite -> IHl'. reflexivity.  Qed.

(** Para comparação, aqui está uma prova informal de dois destes teoremas:

    _Teorema_: Para todo número [n] e lista [l],
       [length (snoc l n) = S (length l)].
 
    _Prova_: Por indução em [l].

    - Primeiramente, suponhamos que [l = []].  Nós devemos mostrar que
        length (snoc [] n) = S (length []),
      o que segue diretamente das definições de
      [length] e [snoc].

    - Em seguida, suponhamos que [l = n'::l'], com
        length (snoc l' n) = S (length l').
      Nós devemos mostrar que
        length (snoc (n' :: l') n) = S (length (n' :: l')).
      Pela definição de [length] e [snoc], isto prossegue de
        S (length (snoc l' n)) = S (S (length l')),
]].
      Isto é uma consequência imediata da hipótese de indução. [] *)
                        
(** _Teorema_: Para toda lista [l], [length (rev l) = length l].
    
    _Prova_: Por indução em [l].  

      - Primeiro, suponhamos que [l = []].  Nós devemos mostrar que
          length (rev []) = length [],
        o que segue diretamente para a definição de [length] 
        e [rev].
    
      - Em seguinda, suponhamos que [l = n::l'], com
          length (rev l') = length l'.
        Nós devemos mostrar que
          length (rev (n :: l')) = length (n :: l').
        Pela definição de [rev], isto segue para
          length (snoc (rev l') n) = S (length l')
        o que, pelo lema anterior, isso é o mesmo que
          S (length (rev l')) = S (length l').
        Isto é direto da hipótese de indução. [] *)

(** Obviamente, o estilo dessas provas bastante cansativo
    e pedante.  Depois de alguns primeiros, nós devemos acha isso mais fácil
    para as provas seguintes que dão pouquissímos detalhes (desde nós podemos facilmente
    trabalhar com eles foram da nossa mente ou rabiscar em um papel se necessário) e
    apenas os melhores momentos dos passos não óbvios.  Em neste estilo mais comprimido, 
    a prova acima pode parecer como isto: *)

(** _Teorema_:
     Para todas as listas [l], [length (rev l) = length l].

    _Prova_: primeiro, observe que
       length (snoc l n) = S (length l)
     para qualquer [l].  Isto segue para uma indução sobre sobre [l].
     A principal propriedade agora segue por outra simples indução sobre [l],
     usando a observação junto com a hipótese de indução no caso onde
     [l = n'::l']. [] *)

(** [ Renan ] Which style is preferable in a given situation depends on
    the sophistication of the expected audience and on how similar the
    proof at hand is to ones that the audience will already be
    familiar with.  The more pedantic style is a good default for
    present purposes. *)

(* ###################################################### *)
(** ** O comando [SearchAbout] *)

(** Nós vimos que podemos usar teoremas já provados nas novas
provas, através de [rewrite], e posteriormente veremos outras formas
de reutilizar teoremas já definidos. Mas, para usar um teorema, devemos
saber seu nome, e relembrar o nome de todos os teoremas que poderíamos
usar pode ficar bastante difícil! Já é muitas vezes penoso lembrar
quais teoremas foram provados, sendo mais difícil ainda lembrar seus nomes.

O comando [SearchAbout] do Coq é bastante útil nesse caso. Digitar [SearchAbout
foo] fará com que Coq exiba uma lista de todos os teoremas que envolvem [foo].
Por exemplo, tente remover o seguinte comentário para ver uma lista dos
teoremas que provamos sobre [rev]: *)

(*  SearchAbout rev. *)

(** [ Dalay ] Keep [SearchAbout] in mind as you do the following exercises and
    throughout the rest of the course; it can save you a lot of time! *)

(** Também, se você está usando ProofGeneral, você pode
    executar um comando [SearchAbout] com [C-c C-a C-a]. Você pode colar sua
    resposta em seu buffer com [C-c C-;]. *)

(* ###################################################### *)
(** ** Lista de Exercícios, Parte 1 *)

(** **** Exercício: *** (list_exercises)  *)

(** Mais prática com listas. *)

Theorem app_nil_end : forall l : natlist, 
  l ++ [] = l.   
Proof.
  (* PREENCHER *) Admitted.


Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  (* PREENCHER *) Admitted.

(** Existe uma solução curta para o próximo exercício. Se você se encontrar perdido, 
    dê um passo para traz e tente olhar para um caminho mais simples. *)

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  (* PREENCHER *) Admitted.

Theorem snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
  (* PREENCHER *) Admitted.


Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  (* PREENCHER *) Admitted.

(** [ Renan ] An exercise about your implementation of [nonzeros]: *)

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: ** (beq_natlist)  *)

(** Complete a definição de [beq_natlist], que compara se listas de
números são iguais. Prove que [beq_natlist l l] retorna [true] para
toda lista [l]. *)

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  (* PREENCHER *) admit.

Example test_beq_natlist1 :   (beq_natlist nil nil = true).
 (* PREENCHER *) Admitted.
Example test_beq_natlist2 :   beq_natlist [1;2;3] [1;2;3] = true.
 (* PREENCHER *) Admitted.
Example test_beq_natlist3 :   beq_natlist [1;2;3] [1;2;4] = false.
 (* PREENCHER *) Admitted.

Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(* ###################################################### *)
(** ** Lista de Exercícios, Parte 2 *)

(** **** Exercício: ** (list_design)  *)

(** Exercício de planejamento:
     - Escreva um teorema não trivial [cons_snoc_app] envolvendo [cons] ([::]),
     [snoc], e [app] ([++]).
     - Prove-o. *)

(* PREENCHER *)
(** [] *)

(** **** Exercício: ***, avançado (bag_proofs)  *)

(** [ Dalay ] Here are a couple of little theorems to prove about your
    definitions about bags earlier in the file. *)

Theorem count_member_nonzero : forall (s : bag),
  ble_nat 1 (count 1 (1 :: s)) = true.
Proof.
  (* PREENCHER *) Admitted.

(** O lema a seguir sobre [ble_nat] deve te ajudar na próxima prova. *)

Theorem ble_n_Sn : forall n,
  ble_nat n (S n) = true.
Proof.
  intros n. induction n as [| n'].
  Case "0".  
    simpl.  reflexivity.
  Case "S n'".
    simpl.  rewrite IHn'.  reflexivity.  Qed.

Theorem remove_decreases_count: forall (s : bag),
  ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: ***, opcional (bag_count_sum)  *)  

(** Escreve abaixo um teorema interessante [bag_count_sum] sobre multiconjuntos
    envolvendo as funções [count] e [sum], e prove.*)

(* PREENCHER *)
(** [] *)

(** **** Exercício: 4 stars, advanced (rev_injective)  *)

(** [ Renan ] Prove that the [rev] function is injective, that is,

    forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.

There is a hard way and an easy way to solve this exercise.
*)

(* PREENCHER *)
(** [] *)


(* ###################################################### *)

(** * Opções *)

(** O tipo [natoption] pode ser usado como uma forma de retornar
  "códigos de erro" de funções. Por exemplo, suponha que queiramos
  escrever uma função que retorne o [n]-ésimo elemento de uma
  lista. Se seu tipo for [nat -> natlist -> nat], então a função terá
  que retornar algum número mesmo se o tamanho da lista for menor que [n]! *)  
						    
Fixpoint index_bad (n:nat) (l:natlist) : nat :=
  match l with
  | nil => 42  (* arbitrary! *)
  | a :: l' => match beq_nat n O with 
               | true => a 
               | false => index_bad (pred n) l' 
               end
  end.

(** *** *)
(** Por outro lado, se dermos à ela o tipo [nat -> natlist ->  natoption], então
poderemos retornar [None] quando a lista for muito curta e um [Some a] quando
a lista tiver elementos suficientes e [a] aparecer na posição [n]. *)

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.  


Fixpoint index (n:nat) (l:natlist) : natoption :=
  match l with
  | nil => None 
  | a :: l' => match beq_nat n O with 
               | true => Some a
               | false => index (pred n) l' 
               end
  end.

Example test_index1 :    index 0 [4;5;6;7]  = Some 4.
Proof. reflexivity.  Qed.
Example test_index2 :    index 3 [4;5;6;7]  = Some 7.
Proof. reflexivity.  Qed.
Example test_index3 :    index 10 [4;5;6;7] = None.
Proof. reflexivity.  Qed.

(** [ Dalay ] This example is also an opportunity to introduce one more
    small feature of Coq's programming language: conditional
    expressions... *)

(** *** *)

Fixpoint index' (n:nat) (l:natlist) : natoption :=
  match l with
  | nil => None 
  | a :: l' => if beq_nat n O then Some a else index' (pred n) l'
  end.

(** As condicionais do Coq são exatamante como aquelas encontradas em qualquer
    outra linguaguem, com uma pequena generalização.  Uma vez que o Coq não
    define o tipo booleano, ele permite expressões condicionais sobre
    _qualquer_ tipo indutivamente definido com exatamente dois construtores.  A
    condição é considerada verdadeira quando é avaliada para o primeiro
    construtor na definição de indução [Inductive] e falsa se é avaliada para o
    segundo. *)

(** A função abaixo retira um [nat] de [natoption], retornando
    um padrão fornecido no caso [None]. *)

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

(** **** Exercício: ** (hd_opt)  *)

(** [ Renan ] Using the same idea, fix the [hd] function from earlier so we don't
   have to pass a default element for the [nil] case.  *)

Definition hd_opt (l : natlist) : natoption :=
  (* PREENCHER *) admit.

Example test_hd_opt1 : hd_opt [] = None.
 (* PREENCHER *) Admitted.

Example test_hd_opt2 : hd_opt [1] = Some 1.
 (* PREENCHER *) Admitted.

Example test_hd_opt3 : hd_opt [5;6] = Some 5.
 (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: 1 star, opcional (option_elim_hd)  *)

(** Este exercício relaciona o seu novo [hd_opt] com o velho [hd]. *)

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_opt l).
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(* ###################################################### *)

(** * Dicionários *)

(** Como ilustração final de como as estruturas de dados fundamentais podem ser
definidas em Coq, aqui está a declaração de um tipo de dados _dicionário_
simples, chamado [dictionary], utilizando números tanto para as chaves quanto
para os valores armazenados nestas chaves. (Ou seja, um dicionário representa um
mapeamento finito de números para números.) *)

Module Dictionary.

Inductive dictionary : Type :=
  | empty  : dictionary 
  | record : nat -> nat -> dictionary -> dictionary. 

(** [ Dalay ] This declaration can be read: "There are two ways to construct a
    [dictionary]: either using the constructor [empty] to represent an
    empty dictionary, or by applying the constructor [record] to
    a key, a value, and an existing [dictionary] to construct a
    [dictionary] with an additional key to value mapping." *)

Definition insert (key value : nat) (d : dictionary) : dictionary :=
  (record key value d).

(** Aqui está a função [find] (_encontrar_), que procura um [dictionary]
    (_dicionário_) para a chave dada. Atribuindo [None] (_nada_) se a chave não
    for encontrada e [Some val] (_algum valor_) se a chave for mapeada até
    [val] no dicionário. Se a mesma chave for mapeada em múltiplos valores,
    [find] irá retorar o primeiro que encontrar. *)

Fixpoint find (key : nat) (d : dictionary) : natoption := 
  match d with 
  | empty         => None
  | record k v d' => if (beq_nat key k) 
                       then (Some v) 
                       else (find key d')
  end.



(** **** Exercício: * (dictionary_invariant1)  *)

(** Complete a prova seguinte. *)

Theorem dictionary_invariant1' : forall (d : dictionary) (k v: nat),
  (find k (insert k v d)) = Some v.
Proof.
 (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: * (dictionary_invariant2)  *)

(** [ Renan ] Complete the following proof. *)

Theorem dictionary_invariant2' : forall (d : dictionary) (m n o: nat),
  beq_nat m n = false -> find m d = find m (insert n o d).
Proof.
 (* PREENCHER *) Admitted.
(** [] *)



End Dictionary.

End NatList.



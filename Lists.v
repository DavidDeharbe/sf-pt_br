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

(** Essa declaração pode ser lida como: há somente um caminho para 
    construir um par de numeros: aplicando o construtor [pair] 
    (_par_) a dois argumentos do tipo [nat]. *)

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
    com a notação matemática padrão [(x, y)] em vez de [pair x y]. 
    Podemos instruir o Coq para permitir isso com uma declaração 
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

(** [ Note que [reflexivity] não é o suficiente se nós declararmos o lema
    de um modo mais natural: *)

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

(** Não é necessário entender completamente essas declarações, mas, no caso
    de você estar interessado, aqui está rapidamente o que está acontecendo.

    A anotação [right associativity] (_associatividade à direita_) diz ao Coq
    como utilizar parênteses em expressões envolvendo o uso de muitos [::], 
    então, por exemplo, as três próximas declarações significam exatamente a mesma coisa: *)

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

(** A parte [at level 60] instrui Coq como colocar interpretar
    expressões que envolvem ambos [::] e algum outro operador infixo.
    Por exemplo, desde nós definimos [+] como uma notação infixa para a 
    função [plus] no nível 50,
Notation "x + y" := (plus x y)  
                    (at level 50, left associativity).
   O operador [+] irá fazer uma ligação mais forte do que [::], então [1 + 2 :: [3]]
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

(** A função [length] (comprimento) calcula o comprimento de uma lista. *)

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

(** De fato, [app] será muito usado em algumas partes do que vem
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
    A função [hd] retorna o primeiro elemento (a "cabeça") da lista,
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

    Nota: uma maneira natural e elegante de escrever [alternate] falhará em 
    satisfazer o requisito do Coq de que toda definição de [Fixpoint]  
    "termina obviamente." Se você se encontra com esse problema, procure
    por uma solução levemente mais prolixa que considere elementos de ambas
    as listas ao mesmo tempo. (Uma solução possível requer definir o novo tipo 
    de par, mas esse não é a única solução. *)


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
    [count], [sum], [add], e [member] para multiconjuntos. *)

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
  (* Quando [remove_one] é aplicado a um conjunto sem o número para remover,
    ele deve retornar o mesmo conjunto sem modificações. *)
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
    envolvendo as funções [count] e [add], e provar o teorema. Note que, uma
    vez que este problema é aberto, é possível imaginar um teorema
    que é verdadeiro, mas cuja prova requisite técnicas que você ainda
    não aprendeu.  Sinta-se livre para pedir ajuda se você ficar travado! *)

(* PREENCHER *)
(** [] *)

(* ###################################################### *)
(** * Raciocínio Sobre Listas *)

(** Assim como os números, fatos simples sobre funções de 
    processamento de listas pode algumas vezes ser inteiramente provados
    por simplificação. Por exemplo, a simplificação realizada por [reflexivity] 
    é suficiente para este teorema... *)

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

(** ... porque o [[]] é substituído pela sua posição de casamento
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

(** Normalmente, porém, teoremas interessantes a respeito de listas requerem 
    indução para as suas provas. *)

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
    a partir de construtores declarados: um booleano pode ou ser [true] ou
    [false]; um número pode ou ser [O] ou [S] aplicado a um número; uma
    lista pode ser ou [nil] ou [cons] aplicado a um número e a uma lista.

    Além disso, aplicações dos construtores declarados um para com o outro 
    são as _únicas_ formas possíveis que elementos de um conjunto 
    indutivamente definido pode ter, e este fato dá diretamente origem a 
    uma forma de raciocinar sobre conjuntos indutivamente definidos: um 
    número é [O] ou então é [S] aplicado a algum número _menor_; uma 
    lista é [nil] ou então é [cons] aplicada a um número e alguma lista 
    _menor_; etc. Então, se temos em mente alguma proposição [P] que 
    menciona uma lista [l] e queremos argumentar que [P] é válida para 
    _todas_ as listas, podemos raciocinar da seguinte forma:

      - Em primeiro lugar, mostrar que [P] é verdade de [l] quando 
      [l] é [nil].

      - Em seguida, mostrar que [P] é verdade de [l] quando [l] é 
      [cons n l '] para algum número [n] e alguma lista menor [l'], 
      assumindo que [P] é verdadeiro para [l'].

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
   Aqui está um exemplo similar para ser trabalhado em grupo em sala. *)

Theorem app_length : forall l1 l2 : natlist, 
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* TRABALHADO EM SALA *)
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

(** ... e use ele para definir uma função de inversão de lista [rev]
    como segue: *)

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

(** Agora vamos provar mais alguns teoremas sobre listas usando os nossos 
    recém-definidos [snoc] e [rev]. Para algo um pouco mais desafiador 
    do que as provas indutivas que temos visto até agora, vamos provar 
    que inverter uma lista não altera a sua extensão. Nossa primeira 
    tentativa nesta prova fica presa no caso sucessor ... *)

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

(** Agora nós podemos completar a prova original. *)

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

(** Obviamente, o estilo dessas provas bastante detalhista
      e pedante.  Depois de algumas provas similares, 
      nós devemos achar mais fácil acompanhar provas que entram
      menos em detalhe (desde que nós possamos facilmente 
      acompanhar elas mentalmente ou rabiscando em um papel
      se necessário) e destacando apenas os os passos não óbvios.  
      Neste estilo mais comprimido, a prova acima pode parecer 
      como isto: *)

(** _Teorema_:
     Para todas as listas [l], [length (rev l) = length l].

    _Prova_: primeiro, observe que
       length (snoc l n) = S (length l)
     para qualquer [l].  Isto segue através de uma indução sobre [l].
     A principal propriedade agora segue por outra simples indução sobre [l],
     usando a observação junto com a hipótese de indução no caso onde
     [l = n'::l']. [] *)

(** Qual estilo é preferível em uma determinada situação depende 
    da sofisticação do público esperado e de quão semelhante a prova em
    questão é com relação àquelas com as quais o público já está familiarizado. 
    O estilo mais rebuscado é um bom padrão para os propósitos presentes. *)

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

(** Mantenha o [SearchAbout] em mente enquanto você faz os seguintes 
    exercícios e ao longo do resto do curso; isso pode salvar você 
    muitas vezes! *)

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

(** Existe uma solução curta para o próximo exercício. Se você se encontrar 
    perdido, dê um passo para trás e tente buscar um caminho mais simples. *)

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

(** Um exercício sobre sua implementação de [nonzeros]: *)

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

(** Aqui está alguns pequenos teoremas a provar a respeito das suas
    definições de conjuntos anteriormente nesse arquivo. *)

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

(** Prove que a função [rev] é injetiva, ou seja,

    forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.

Há uma maneira simples e outra difícil de resolver este exercício.
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

(** Esse éxemplo é também uma oportunidade para introduzir mais
    uma característica  da liguagem de programação Coq: expressões
    condicionais... *)

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

(** Usando a mesma ideia, ajuste a função [hd] anterior para que não
    precisemos ter que passar um elemento padrão para o caso [nil]. *)

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

(** Essa declaração pode ser lida como: "Existem duas maneiras de construir
    um [dictionary] (_dicionário_): ou usando o construtor [empty] (_vazio_)
    para representar um dicionário vazio, ou aplicando o construtor [record]
    (_gravar_) para uma chave, um valor, e um [dictionary] existente para 
    construir um [dictionary] com uma chave adicional para mapear valores." *)

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

(** Complete a seguinte prova. *)

Theorem dictionary_invariant2' : forall (d : dictionary) (m n o: nat),
  beq_nat m n = false -> find m d = find m (insert n o d).
Proof.
 (* PREENCHER *) Admitted.
(** [] *)



End Dictionary.

End NatList.



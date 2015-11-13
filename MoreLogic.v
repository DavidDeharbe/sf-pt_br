(** * MoreLogic: Elementos Adicionais de Lógica em Coq *)

Require Export "Prop".

(* ############################################################ *)
(** * Quantificação Existencial *)

(** [Claudia]Another critical logical connective is _existential
    quantification_.  We can express it with the following
    definition: *)

Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.

(** Isso é, [ex] é uma família de poposições indexadas por um tipo [X]
    e uma propriedade [P] sobre [X]. A fim de dar evidência para a asserção
    "Existe um [X] para o qual a propriedade [P] é obedecida" nós devemos 
    nomear uma _testemunha_ -- um valor específico [x] -- e então dar
    evidência para [P x], isto é, evidência que [x] tem a propriedade [P].

*)


(** *** *)
(** As facilidades das _Notações_ [Notation] do Coq podem ser utilizadas
    para introduzir notações mais familiares a fim de escrever proposições
    existencialmente quantificadas, em paralelo com a sintaxe construída para
    proposições universalmente quantificadas.  Em vez de escrever [ex nat
    ev] para expressar a proposição que existe algum número que é
    par, por exemplo, podemos escrever [exists x:nat, ev x].  (Não é
    necessário entender exatamente como a definição [Notation]
    funciona.) *)

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

(** *** *)
(** Nós podemos usar o conjunto de táticas habituais
    para manipulação existencial. Por exemplo, para provar um existencial
    nós podemos [aplicar] o construtor [ex_intro]. Desde que a premissa
    de [ex_intro] envolve uma variável ([witness]) que não aparece na
    conclusão, nós precisamos explícitamente informa-lo o valor quen nós
    usamos o [apply]. *)

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness:=2). 
  reflexivity.  Qed.

(** Note que nós temos que fornecer explicitamente a variável witness. *)

(** *** *)
(**Ou, no lugar de escrever [apply ex_intro with (witness:=e)] todas as vezes, podemos 
usar o atalho conveniente [exists e] que significa a mesma coisa. *)

Example exists_example_1' : exists n, n + (n * n) = 6.
Proof.
  exists 2. 
  reflexivity.  Qed.

(** *** *)
(** [Claudia]Conversely, if we have an existential hypothesis in the
    context, we can eliminate it with [inversion].  Note the use
    of the [as...] pattern to name the variable that Coq
    introduces to name the witness value and get evidence that
    the hypothesis holds for the witness.  (If we don't
    explicitly choose one, Coq will just call it [witness], which
    makes proofs confusing.) *)
  
Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H as [m Hm]. 
  exists (2 + m).  
  apply Hm.  Qed. 


(** Aqui está outro exemplo de como trabalhar com existenciais. *)
Lemma exists_example_3 : 
  exists (n:nat), even n /\ beautiful n.
Proof.
(* REALIZADO EM SALA *)
  exists 8.
  split.
  unfold even. simpl. reflexivity.
  apply b_sum with (n:=3) (m:=5).
  apply b_3. apply b_5.
Qed.

(** **** Exercício: nível 1, opcional (english_exists)  *)
(** Em inglês, o que a proposição 
      ex nat (fun n => beautiful (S n))
]] 
    significa? *)

(* PREENCHER *)

(*
*)
(** **** Exercício: nível 1 (dist_not_exists)  *)
(** Prove que "[P] é verdade para todo [x]" implica que " não existe [x] para
    qual [P] não é verdade." *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof. 
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 3, opcional (not_exists_dist)  *)
(** (A outra direção deste teorema requer a clássica "lei do terceiro 
    excluído".) *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 2 (dist_exists_or)  *)
(** Prove que a quantificação existencial é distribuída sobre a disjunção *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
   (* PREENCHER *) Admitted.
(** [] *)

(* ###################################################### *)
(** * Booleanos Portadores de Evidência *)

(** [Claudia]So far we've seen two different forms of equality predicates:
    [eq], which produces a [Prop], and the type-specific forms, like
    [beq_nat], that produce [boolean] values.  The former are more
    convenient to reason about, but we've relied on the latter to let
    us use equality tests in _computations_.  While it is
    straightforward to write lemmas (e.g. [beq_nat_true] and
    [beq_nat_false]) that connect the two forms, using these lemmas
    quickly gets tedious. *)

(** *** *)
(** Acontece que nós podemos obter os benefícios de ambas as formas de uma 
    só vez usando um construtor chamado [sumbool]. *)

Inductive sumbool (A B : Prop) : Set :=
 | left : A -> sumbool A B 
 | right : B -> sumbool A B.

Notation "{ A } + { B }" :=  (sumbool A B) : type_scope.

(** Pense em [sumbool] como sendo do tipo [boolean], mas no lugar de
    seus valores serem somente [true] e [false], eles carregam a _evidência_
    da verdade ou da falsidade. Isso significa que quando a [destruímos],
    ficamos com a evidência relevante como uma hipótese -- assim como
    com [or].  (Na realidade, a definição de [sumbool] é quase a mesma
    que [or].  A única diferença é que os valores de [sumbool]
    são declarados em [Set] em vez de [Prop]; isso é uma distinção
    técnica a qual nos permite calcular com eles.) *)
(** *** *)

(** Aqui está como nós definimos um [sumbool] para igualdade em [nat]s *)

Theorem eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  (* REALIZADO EM SALA *)
  intros n.
  induction n as [|n'].
  Case "n = 0".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      left. reflexivity.
    SCase "m = S m'".
      right. intros contra. inversion contra.
  Case "n = S n'".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      right. intros contra. inversion contra.
    SCase "m = S m'". 
      destruct IHn' with (m := m') as [eq | neq].
      left. apply f_equal.  apply eq.
      right. intros Heq. inversion Heq as [Heq']. apply neq. apply Heq'.
Defined. 
  
(** Lido como um teorema, isso diz que a igualdade em [nat]s é decidível, 
    ou seja, dados dois valores [nat], sempre podemos produzir ou uma 
    prova de que eles são iguais ou uma prova de que eles não são. Lido 
    computacionalmente, [eq_nat_dec] recebe dois valores [nat] e retorna 
    um [sumbool] construído com [left] caso eles sejam iguais ou com 
    [right] caso eles não sejam; esse resultado pode ser testado com um 
    [match] ou, melhor, com um [if-then-else], exatamente como um [boolean] 
    simples. (Observe que terminamos essa prova com [Defined] em vez de 
    [Qed]. A única diferença que isso faz é que a prova se torna 
    _transparente_, significando que a sua definição estará disponível 
    quando Coq tentar fazer reduções, o que é importante para a 
    interpretação computacional.)
     *) 

(** *** *)
(** Abaixo um exemplo simples ilustrando as vantagens da forma [sumbool]. *)

Definition override' {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
  fun (k':nat) => if eq_nat_dec k k' then x else f k'.

Theorem override_same' : forall (X:Type) x1 k1 k2 (f : nat->X),
  f k1 = x1 -> 
  (override' f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f. intros Hx1.
  unfold override'.
  destruct (eq_nat_dec k1 k2).   (* observe what appears as a hypothesis *)
  Case "k1 = k2".
    rewrite <- e.
    symmetry. apply Hx1.
  Case "k1 <> k2". 
    reflexivity.  Qed.

(** [Claudia]Compare this to the more laborious proof (in MoreCoq.v) for the
    version of [override] defined using [beq_nat], where we had to use
    the auxiliary lemma [beq_nat_true] to convert a fact about
    booleans to a Prop. *)

(** **** Exercício: nível 1 (override_shadow')  *)
Theorem override_shadow' : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  (override' (override' f k1 x2) k1 x1) k2 = (override' f k1 x1) k2.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)





(* ####################################################### *)
(** * Exercícios Adicionais *)

(** **** Exercício: nível 3 (all_forallb)  *)
(** Indutivamente defina uma propriedade [all] de listas, parametrizadas
    por um tipo [X] e uma propriedade [P : X -> Prop], de modo que [all X P l]
    afirma que [P] é verdade para cada elemento da lista [l]. *)

Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
  (* PREENCHER *)
.

(** Recorde a função [forallb], do exercício
    [forall_exists_challenge] no capítulo [Poly]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

(** Usando a propriedade [all], escreva abaixo uma especificação para [forallb],
    e prova que ele satisfaz a especificação. Tente fazer a sua especificação a mais precisa
    possível.

    Existem quaisquer propriedades importantes da função [forallb] que não são 
    capturadas por sua especificação? *)

(* PREENCHER *)
(** [] *)

(** **** Exercício: nível 4, avançado (filter_challenge)  *)
(** Um dos principais propósitos do Coq é provar que os programas correspondem às suas 
especificações. Para este fim, provemos que nossa definição de [filter] está de acordo 
com uma especificação. Aqui está a especificação, escrita informalmente em português.

    [Claudia]Suppose we have a set [X], a function [test: X->bool], and a list
    [l] of type [list X].  Suppose further that [l] is an "in-order
    merge" of two lists, [l1] and [l2], such that every item in [l1]
    satisfies [test] and no item in [l2] satisfies test.  Then [filter
    test l = l1].

    Uma lista [l] é uma "mistura em ordem" de [l1] e [l2] se ela contém
    todos os elementos de [l1] e [l2], na mesma ordem que [l1] e [l2], mas 
    possivelmente intercalados. Por exemplo,
    [1,4,6,2,3]
    é uma mistura em ordem de
    [1,6,2]
    e
    [4,3].
    Seu trabalho é traduzir essa especificação em um teorema Coq e provar
    isso. (Dica: Você vai precisar começar definindo o que significa para
    uma lista ser uma misturada de duas outras. Faça isso com uma relação 
    indutiva, não um [Fixpoint].)  *)

(* PREENCHER *)
(** [] *)

(** **** Exercício: nível 5, avançado, opcional (filter_challenge_2)  *)
(** Uma maneira diferente de formalmente caracterizar o comportamento de
    [filter] é a seguinte: Entre todas subsequências de [l] com a propriedade
    que [test] avalia para [true] em todos os membros, [filter test
    l] é o mais longo.  Expresar essa afirmação de maneira formal e prova-la. *)

(* PREENCHER *)
(** [] *)

(** **** Exercício: nível 4, avançado (no_repeats)  *)
(** A seguinte proposição definida indutivamente... *)

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

(** ... nos fornece uma maneira precisa de dizer que um valor [a] aparece 
    pelo menos uma vez como um membro de uma lista [l].

	Para aquecer, é mostrado a seguir dois lemas a serem provados sobre [appears_in].
*)

Lemma appears_in_app : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  (* PREENCHER *) Admitted.

Lemma app_appears_in : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  (* PREENCHER *) Admitted.


(** [Claudia]Now use [appears_in] to define a proposition [disjoint X l1 l2],
    which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in common. *)

(* PREENCHER *)

(** Em seguida, use [appears_in] para definir uma proposição indutiva
    [no_repeats X l], que deve ser provável exatamente quando [l] é uma 
    lista (com elementos do tipo [X]) onde cada membro é diferente dos 
    outros. Por exemplo, [no_repeats nat [1,2,3,4]] e [no_repeats bool []] 
    devem ser prováveis, enquanto [no_repeats nat [1,2,1]] e 
    [no_repeats bool [true, true]] não devem ser.  *)

(* PREENCHER *)

(** Finalmente, enuncie e prove um ou mais teoremas interessantes relacionando
    [disjoint], [no_repeats] e [++] (list append). *)

(* PREENCHER *)
(** [] *)

(** **** Exercício: nível 3 (nostutter)  *)
(** Formular definições indutivas de predicados é uma habilidade importante 
    que você vai precisar neste curso. Tente resolver este exercício sem nenhuma ajuda.
    
    Dizemos que uma lista de números "gagueja" se ela repete o mesmo 
    número consecutivamente. O predicado "[nostutter mylist]" significa 
    que [mylist] não gagueja. Formular uma definição indutiva para 
    [nostutter]. (Isso é diferente do predicado [no_repeats] no exercício 
    acima; a sequência de [1;4;1] repete mas não gagueja.) *)

Inductive nostutter:  list nat -> Prop :=
 (* PREENCHER *)
.

(** 
Tenha certeza de que cada um desses testes sejam bem-sucedidos, mas você é livre para 
mudar a prova se a que lhe for dada não funcionar para você. A sua definição pode ser 
diferente da minha e ainda assim ser correta, talvez precisando, sendo este o caso, que 
os exemplos tenham provas diferentes.

    As provas sugeridas para os exemplos (nos comentários) usam um número de 
    táticas que nós ainda não falamos, para tentar torná-los robustos em relação 
    a diferentes formas possíveis de definir [nostutter]. Você deve poder apenas 
    descomentar e usá-las como são. mas se você preferir, você pode também
    provar cada exemplo com táticas mais básicas. *)

Example test_nostutter_1:      nostutter [3;1;4;1;5;6].
(* PREENCHER *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_2:  nostutter [].
(* PREENCHER *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_3:  nostutter [5].
(* PREENCHER *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
(* PREENCHER *) Admitted.
(* 
  Proof. intro.
  repeat match goal with 
    h: nostutter _ |- _ => inversion h; clear h; subst 
  end.
  contradiction H1; auto. Qed.
*)
(** [] *)

(** **** Exercício: nível 4, avançado (pigeonhole principle)  *)
(** O "princípio da casa de pombos" enuncia um fato básico sobre a contagem:
   se distribuirmos mais que [n] itens em [n] escaninhos, alguns 
   escaninhos devem conter no mínimo dois itens.  Como é um caso frequente,
   esse fato, aparentemente trivial, sobre números requer maquinária não
   trivial para provar, mas agora sabemos o suficiente... *)

(** Primeiro, um par de lemas útil(nós ja provamos eles para
    listas de naturais, mas não para listas arbitrárias). *)

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof. 
  (* PREENCHER *) Admitted.

Lemma appears_in_app_split : forall (X:Type) (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  (* PREENCHER *) Admitted.

(** Agora defina um predicado [repeats] (análogo a [no_repeats] no exercício 
    acima), de tal modo que [repeats X l] afirme que [l] contém pelo menos um 
    elemento repetido (do tipo [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  (* PREENCHER *)
.

(** Agora temos aqui uma maneira de formalizar o princípio da casa dos pombos. A lista 
[l2] representa uma lista de rótulos da casa dos pombos e a lista [l1] representa os 
rótulos atribuídos a uma lista de itens: se houver mais itens que rótulos, pelo menos 
dois itens precisam ter o mesmo rótulo. Esta prova é muito mais fácil se você usar a 
hipótese [excluded_middle] para mostrar que [appears_in] é decidível, isto é, [forall x
    l, (appears_in x l) \/ ~ (appears_in x l)]. Entretanto também possível realizar a 
    prova _sem_ precisar assumir que [appears_in] é decidível: se você conseguir avançar 
    desta forma então não será mais necessária a hipótese [excluded_middle].*)

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X), 
   excluded_middle -> 
   (forall x, appears_in x l1 -> appears_in x l2) -> 
   length l2 < length l1 -> 
   repeats l1.  
Proof.
   intros X l1. induction l1 as [|x l1'].
  (* PREENCHER *) Admitted.
(** [] *)

(* PREENCHER *)

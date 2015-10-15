(** * MoreCoq: Mais Acerca das Táticas de Coq *)

Require Export Poly.

(** Este capítulo apresenta várias outras estratégias e táticas de prova que,
juntas, permitem-nos provar teoremas sobre os programas funcionais que temos
escrito. Em particular, nós vamos raciocinar sobre funções que manipulam números
naturais e listas.


    [Dalay]In particular, we will see:
    - how to use auxiliary lemmas, in both forwards and backwards reasoning;
    - how to reason about data constructors, which are injective and disjoint;
    - how to create a strong induction hypotheses (and when
      strengthening is required); and
    - how to reason by case analysis.
 *)

(* ###################################################### *)
(** * A tática [apply] ( aplique_) *)

(** Nós usualmente encontraremos situações onde a meta a ser provada é
    exatamente igual a hipótese no contexto ou algum
    lema provado anteriormente. *)

Theorem silly1 : forall (n m o p : nat),
     n = m  ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  (* Nesse ponto, poderiamos acabar a prova com 
     "[rewrite -> eq2. reflexivity.]" como nós fizemos 
     várias vezes antes. Mas nós podemos realizar o
     mesmo efeito com um passo simples, utilizando a tática 
     [apply]: *)
  apply eq2.  Qed.

(** [Francisco]The [apply] tactic also works with _conditional_ hypotheses
    and lemmas: if the statement being applied is an implication, then
    the premises of this implication will be added to the list of
    subgoals needing to be proved. *)

Theorem silly2 : forall (n m o p : nat),
     n = m  ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2. 
  apply eq2. apply eq1.  Qed.

(** Você pode achar instrutivo observar esta prova e ver se há uma 
    maneira de completá-la usando apenas [rewrite] em vez de 
    [apply].*)

(** Tipicamente, quando usamos [apply H], a sentença [H] começará com um 
[forall] ligando algumas _variáveis universais_. Quando o Coq casa a meta atual 
com a conclusão de [H], ele tenta encontrar os valores apropriados para estas 
variáveis. Por exemplo, quando aplicamos [apply eq2] na prova abaixo, a 
variável universal [q] em [eq2] é instanciada com [n] e [r] é instanciada com 
[m]. *)  

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m)  ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.  Qed.

(** **** Exercício: nível 2, opcional (silly_ex)  *)
(** Complete a seguinte prova usando [simpl]. *)

Theorem silly_ex : 
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** [Dalay]To use the [apply] tactic, the (conclusion of the) fact
    being applied must match the goal _exactly_ -- for example, [apply]
    will not work if the left and right sides of the equality are
    swapped. *)

Theorem silly3_firsttry : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  simpl.
  (* Here we cannot use [apply] directly *)
Abort.

(** Neste caso podemos usar a tática [symmetry], que troca os lados
    direito e o esquerdo de uma igualdade na meta. *)

Theorem silly3 : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl. (* Na realidade, esse [simpl] é desnecessário, uma vez que 
            [apply] irá primeiramente realizar simplificação. *)
  apply H.  Qed.       

(** **** Exercício: nível 3 (apply_exercise1)  *)
(** [Francisco]Hint: you can use [apply] with previously defined lemmas, not
    just hypotheses in the context.  Remember that [SearchAbout] is
    your friend. *)

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 1, opcional (apply_rewrite)  *)
(** Resumidamente explicar a diferença entre as táticas [apply] e 
    [rewrite]. Existem situações em que ambas podem ser aplicadas 
    de maneira útil?
  (* PREENCHER *)
*)
(** [] *)


(* ###################################################### *)
(** * A tática [apply ... with ...] ( aplique ... com ..._) *)

(** Os exemplo bobo abaixo usa duas reescritas em sequência para ir de [[a,b]] 
a [[e,f]]. *)

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2. 
  rewrite -> eq1. rewrite -> eq2. reflexivity.  Qed.

(** Uma vez que este é um padrão comum, poderíamos abstraí-lo como um lema,
registrando de uma vez por todas o fato de que a igualdade é transitiva. *)

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2. 
  reflexivity.  Qed.

(** [Dalay]Now, we should be able to use [trans_eq] to
    prove the above example.  However, to do this we need
    a slight refinement of the [apply] tactic. *)

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2. 
  (* If we simply tell Coq [apply trans_eq] at this point,
     it can tell (by matching the goal against the
     conclusion of the lemma) that it should instantiate [X]
     with [[nat]], [n] with [[a,b]], and [o] with [[e,f]].
     However, the matching process doesn't determine an
     instantiation for [m]: we have to supply one explicitly
     by adding [with (m:=[c,d])] to the invocation of
     [apply]. *)
  apply trans_eq with (m:=[c;d]). apply eq1. apply eq2.   Qed.

(** Na realidade, nós usualmente não temos que incluir o nome [m]
    na cláusula [with]; Coq é frequentemente esperto o bastante para
    descobrir que instanciação nós estamos fornecendo. Nós podemos, em vez 
    disso, escrever: [apply trans_eq with [c,d]]. *)

(** **** Exercício: nível 3, opcional (apply_with_exercise)  *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o). 
Proof.
  (* PREENCHER *) Admitted.
(** [] *)


(* ###################################################### *)
(** * A tática [inversion] (_inversão_) *)

(** [Francisco]Recall the definition of natural numbers:
     Inductive nat : Type :=
       | O : nat
       | S : nat -> nat.
    É claro a partir desta definição que cada número tem uma de duas formas: 
    ou é o construtor [O] ou é construído através da aplicação do construtor 
    [S] a outro número. Mas há mais aqui do que parece: implícita na definição 
    (e no nosso entendimento informal de como declarações de tipo de dados 
    funcionam em outras linguagens de programação) estão dois outros fatos:

	- O construtor [S] é _injetiva_. Isto é, podemos obter [S n = S m] apenas 
	se [n = m].

	- Os construtores [O] e [S] são _disjuntas_. Isto é, [0] não é igual a [S 
	n] para qualquer [n]. *)

(** Princípios semelhantes aplicam-se a todos os tipos definidos indutivamente:
todos os construtores são injetores, e os valores construídos a partir de
construtores distintos nunca são iguais. Para as listas, o construtor [cons]
é injetor e [nil] é diferente de todas as listas não-vazias. Para booleanos,
  [true] e [false] são diferentes. (Uma vez que nem [true] nem [false] recebem
  quaisquer argumentos, a injetividade deles não é um problema.) *)

(** [Dalay]Coq provides a tactic called [inversion] that allows us to exploit
    these principles in proofs.
 
    A tática [inversion] é utilizada da seguinte maneira.  Supondo que [H] é 
    uma hipótese no contexto (or um lema provado anteriormente) da
    forma
      c a1 a2 ... an = d b1 b2 ... bm
    para os contrutores [c] e [d] e argumentos [a1 ... an] e
    [b1 ... bm].  Então [inversion H] intrui Coq a "inverter" essa igualdade
    e extrair a informação que ela contém sobre os termos:

    - [Francisco]If [c] and [d] are the same constructor, then we know, by the
      injectivity of this constructor, that [a1 = b1], [a2 = b2],
      etc.; [inversion H] adds these facts to the context, and tries
      to use them to rewrite the goal.

    - Se [c] e [d] são construtores diferentes, então a hipótese [H] 
      é contraditória. Ou seja, uma suposição falsa se infiltrou no 
      contexto, e isso significa que qualquer meta é demonstrável! 
      Neste caso, [inversion H] marca a meta atual como concluída 
      e a coloca para fora da pilha de metas. *)

(** A tática [inversion] é provavelmente mais fácil de entender vendo-a em ação 
do que através de descrições gerais como a mostrada acima. Você verá abaixo 
teoremas exemplos que demonstram o uso de [inversion] e exercícios para testar 
sua compreensão a respeito. *)

Theorem eq_add_S : forall (n m : nat),
     S n = S m ->
     n = m.
Proof.
  intros n m eq. inversion eq. reflexivity.  Qed.

Theorem silly4 : forall (n m : nat),
     [n] = [m] ->
     n = m.
Proof.
  intros n o eq. inversion eq. reflexivity.  Qed.

(** Por conveniência, a tática [inversion] também pode destruir igualdades entre
valores complexos, conectando múltiplas variáveis à medida em que é aplicada. *)

Theorem silly5 : forall (n m o : nat),
     [n;m] = [o;o] ->
     [n] = [m].
Proof.
  intros n m o eq. inversion eq. reflexivity. Qed.

(** **** Exercício: nível 1 (sillyex1)  *) 
Example sillyex1 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = z :: j ->
     y :: l = x :: j ->
     x = y.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

Theorem silly6 : forall (n : nat),
     S n = O ->
     2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Theorem silly7 : forall (n m : nat),
     false = true ->
     [n] = [m].
Proof.
  intros n m contra. inversion contra.  Qed.

(** **** Exercício: nível 1 (sillyex2)  *)
Example sillyex2 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = [] ->
     y :: l = z :: j ->
     x = z.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** [Dalay]While the injectivity of constructors allows us to reason
    [forall (n m : nat), S n = S m -> n = m], the reverse direction of
    the implication is an instance of a more general fact about
    constructors and functions, which we will often find useful: *)

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A), 
    x = y -> f x = f y. 
Proof. intros A B f x y eq. rewrite eq.  reflexivity.  Qed. 




(** **** Exercício: nível 2, opcional (practice)  *)
(** Algumas provas, não triviais mas também não tão complexas, para
    serem trabalhadas em classe, ou para você trabalhar como exercícios. *)
 

Theorem beq_nat_0_l : forall n,
   beq_nat 0 n = true -> n = 0.
Proof.
  (* PREENCHER *) Admitted.

Theorem beq_nat_0_r : forall n,
   beq_nat n 0 = true -> n = 0.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)


(* ###################################################### *)
(** * Aplicação de Táticas nas Hipóteses *)

(** [Francisco]By default, most tactics work on the goal formula and leave
    the context unchanged.  However, most tactics also have a variant
    that performs a similar operation on a statement in the context.

    Por exemplo, a tática [simpl in H] executa simplificação na hipótese 
    chamada [H] no contexto. *)

Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b  ->
     beq_nat n m = b. 
Proof.
  intros n m b H. simpl in H. apply H.  Qed.

(** Similarmente a tática [apply L in H] casa uma sentença condicional [L] 
(digamos, com a forma [L1 -> L2]) com uma hipótese [H] no contexto. Porém, ao 
contrário de um simples [apply] (que reescreve uma meta casada com [L2] pela 
submeta [L1]), [apply L in H] casa [H] contra [L1] e, se no caso de sucesso, o 
substitui por [L2].
 
    Em outras palavras, [apply L in H] nos dá uma forma de "raciocínio progressivo " -- a partir de [L1 -> L2] e uma hipótese casando com [L1], temos
    uma hipótese casando com [L2]. Por outro lado, [apply L] é um "raciocínio
    regressivo" -- isto indica que se sabemos que [L1 -> L2] e estamos tentando
    provar [L2], basta que provemos [L1].

    [Dalay]Here is a variant of a proof from above, using forward reasoning
    throughout instead of backward reasoning. *)

Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
     true = beq_nat n 5  ->
     true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H. 
  apply H.  Qed.

(** Raciocínio progressivo começa a partir do que é _dado_ (premissas,
    teoremas provados anteriormente) e iterativamente retira conclusões a 
    partir delas até a meta ser alcançada.  Raciocínio regressivo começa a 
    partir da _meta_, e iterativamente raciocína sobre o que implicaria a meta,
    até premissas ou teoremas previamente provados serem alcançados.
    Se você já viu uma prova informal antes (por exemplo, em uma aula de
    matemática ou ciência da computação), eles provavelmente utilizaram 
    raciocínio progressivo.  No geral, Coq tende a favorecer o raciocínio
    regressivo, mas em algumas situações o estilo forward pode ser mais fácil 
    de usar ou pensar sobre.  *)

(** **** Exercício: nível 3 (plus_n_n_injective)  *)
(** [Francisco]Practice using "in" variants in this exercise. *)

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
    (* Hint: use the plus_n_Sm lemma *)
    (* PREENCHER *) Admitted.
(** [] *)

(* ###################################################### *)
(** * Alterando a Hipótese de Indução *)

(** Às vezes é importante controlar a forma exata da hipótese de 
    indução quando da realização de provas indutivas em Coq. 
    Em particular, precisamos ter cuidado sobre quais suposições 
    devemos mover (usando [intros]) da meta para o contexto 
    antes de chamar a tática [induction]. Por exemplo, suponha que 
    queremos mostrar que a função [double] é injetiva - ou seja, 
    que ela sempre mapeia diferentes parâmetros para diferentes 
    resultados:
    Theorem double_injective: forall n m, double n = double m -> n = m.
    A maneira que nós _começamos_ esta prova é um pouco delicada: se começarmos com
      intros n. induction n.
]] 
    tudo estará bem. Porém, se começarmos com
      intros n m. induction n.
    nós ficaremos presos no meio do caso indutivo... *)

Theorem double_injective_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction n as [| n'].
  Case "n = O". simpl. intros eq. destruct m as [| m'].
    SCase "m = O". reflexivity.
    SCase "m = S m'". inversion eq. 
  Case "n = S n'". intros eq. destruct m as [| m'].
    SCase "m = O". inversion eq.
    SCase "m = S m'".  apply f_equal. 
      (* Here we are stuck.  The induction hypothesis, [IHn'], does
         not give us [n' = m'] -- there is an extra [S] in the
         way -- so the goal is not provable. *)
      Abort.

(** O que deu errado? *)

(** O problema é que, no momento em que invocamos a hipótese indutiva, nós já 
tínhamos introduzido [m] no contexto -- intuitivamente, dissemos ao Coq "vamos 
considerar um [n] e um [m] específicos..." e agora devemos provar que, se 
[double n = double m] para estes [n] e [m] _específicos_, então [n = m].

    A tática seguinte, [induction n] diz à Coq que: iremos provar a meta por
    indução sobre [n]. Ou seja, iremos provar que a proposição

      - [P n]  =  "se [double n = double m], então [n = m]"

    vale para todo [n] através da prova de que

      - [P O]              

         (i.e., "se [double O = double m] então [O = m]")

      - [P n -> P (S n)]  

        (i.e., "se [double n = double m] então [n = m]" implica que "se
        [double (S n) = double m] então [S n = m]").

    [Dalay]If we look closely at the second statement, it is saying something
    rather strange: it says that, for a _particular_ [m], if we know

      - "if [double n = double m] then [n = m]"

    then we can prove

       - "if [double (S n) = double m] then [S n = m]".

    Para ver como isso é estranho, vamos pensar em um [m] em particular --
    digamos, [5].  A afirmação é então está dizendo que, se nós sabemos que

      - [Q] = "se [double n = 10] então [n = 5]"

    então nós podemos provar que

      - [R] = "se [double (S n) = 10] então [S n = 5]".

    [Francisco]But knowing [Q] doesn't give us any help with proving [R]!  (If we
    tried to prove [R] from [Q], we would say something like "Suppose
    [double (S n) = 10]..." but then we'd be stuck: knowing that
    [double (S n)] is [10] tells us nothing about whether [double n]
    is [10], so [Q] is useless at this point.) *)

(** Para resumir: tentar realizar esta prova por indução em [n] quando [m] 
    já está no contexto não funciona porque estamos tentando provar uma 
    relação que envolve _todos_ os [n], exceto um _único_ [m]. *)

(** A prova boa de [double_injective] deixa [m] na meta num ponto tal que a 
tática [induction] é aplicada em [n]: *) 

Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = O". simpl. intros m eq. destruct m as [| m'].
    SCase "m = O". reflexivity.
    SCase "m = S m'". inversion eq. 
  Case "n = S n'". 
	(* Perceba que ambas as metas e a hipótese indutiva 
	  
	  
	  
    (* Notice that both the goal and the induction
       hypothesis have changed: the goal asks us to prove
       something more general (i.e., to prove the
       statement for _every_ [m]), but the IH is
       correspondingly more flexible, allowing us to
       choose any [m] we like when we apply the IH.  *)
    intros m eq.
    (* Now we choose a particular [m] and introduce the
       assumption that [double n = double m].  Since we
       are doing a case analysis on [n], we need a case
       analysis on [m] to keep the two "in sync." *)
    destruct m as [| m'].
    SCase "m = O". 
      (* The 0 case is trivial *)
      inversion eq.  
    SCase "m = S m'".  
      apply f_equal. 
      (* At this point, since we are in the second
         branch of the [destruct m], the [m'] mentioned
         in the context at this point is actually the
         predecessor of the one we started out talking
         about.  Since we are also in the [S] branch of
         the induction, this is perfect: if we
         instantiate the generic [m] in the IH with the
         [m'] that we are talking about right now (this
         instantiation is performed automatically by
         [apply]), then [IHn'] gives us exactly what we
         need to finish the proof. *)
      apply IHn'. inversion eq. reflexivity. Qed.

(** O que isto nos ensina é que precisamos ter cuidado no uso da indução para
tentar provar algo muito específico: se estamos provando uma propriedade de [n]
e [m] por indução sobre [n], podemos precisar manter [m] genérico. *)

(** [Dalay]The proof of this theorem (left as an exercise) has to be treated similarly: *)

(** **** Exercício: nível 2 (beq_nat_true)  *)
Theorem beq_nat_true : forall n m,
    beq_nat n m = true -> n = m.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 2, avançado (beq_nat_true_informal)  *)
(** Dar um minuciosa prova informal de [beq_nat_true], sendo o mais
    explicito possível sobre quantificadores. *)

(* PREENCHER *)
(** [] *)


(** [Francisco]The strategy of doing fewer [intros] before an [induction] doesn't
    always work directly; sometimes a little _rearrangement_ of
    quantified variables is needed.  Suppose, for example, that we
    wanted to prove [double_injective] by induction on [m] instead of
    [n]. *)

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction m as [| m'].
  Case "m = O". simpl. intros eq. destruct n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". inversion eq. 
  Case "m = S m'". intros eq. destruct n as [| n'].
    SCase "n = O". inversion eq.
    SCase "n = S n'".  apply f_equal.
        (* Stuck again here, just like before. *)
Abort.

(**  O problema é que, para fazer indução em [m], devemos primeiro 
    introduzir [n]. (Se nós simplesmente dissermos [induction m] 
    sem introduzir nada antes, Coq irá introduzir automaticamente [n] para nós!)   *)

	(** O que podemos fazer sobre isso? Uma possibilidade é reescrever a 
	declaração do lema para que [m] seja quantificada antes de [n]. Isto 
	funcionará, mas não é legal: não queremos reescrever as declarações dos 
	lemas apenas para poderem ser provadas com uma certa estratégia -- queremos 
	estas declarações da forma mais simples e natural possível. *)

(**  Ao invés disso, o que podemos fazer em primeiro lugar é introduzir todas as
variáveis quantificadas e, em seguida, _re-generalizar_ uma ou mais delas,
  levando-os para fora do contexto e colocando-as de volta no início da meta.
  A tática [generalize dependent] faz isto. *)

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. 
  (* Tanto [n] quanto [m] estão no contexto *)
  generalize dependent n.
  (* Agora [n] está volta à meta e podemos aplicar indução sobre [m] e obter uma
  IH genérica o suficente. *)
  induction m as [| m'].
  Case "m = O". simpl. intros n eq. destruct n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". inversion eq.
  Case "m = S m'". intros n eq. destruct n as [| n'].
    SCase "n = O". inversion eq.
    SCase "n = S n'". apply f_equal.
      apply IHm'. inversion eq. reflexivity. Qed.

(** [Dalay]Let's look at an informal proof of this theorem.  Note that
    the proposition we prove by induction leaves [n] quantified,
    corresponding to the use of generalize dependent in our formal
    proof.

_Theorem_: For any nats [n] and [m], if [double n = double m], then
  [n = m].

_Proof_: Let [m] be a [nat]. We prove by induction on [m] that, for
  any [n], if [double n = double m] then [n = m].

  - Primeiramente, suponha [m = 0], e suponha que [n] é um número tal
    que [double n = double m].  Nós devemos mostrar que [n = 0].

    Uma vez que [m = 0], pela definição de [double] nós temos [double n =
    0].  Existem dois casos a considerar para [n].  Se [n = 0] acabamos, 
    uma vez que é isso que queremos mostrar.  Senão, se [n = S
    n'] para algum [n'], derivamos uma contradição: pela definição de
    [double] teriamos [double n = S (S (double n'))], mas isso contradiz
    a hipótese que [double n = 0].

  - [Francisco]Otherwise, suppose [m = S m'] and that [n] is again a number such
    that [double n = double m].  We must show that [n = S m'], with
    the induction hypothesis that for every number [s], if [double s =
    double m'] then [s = m'].
 
    By the fact that [m = S m'] and the definition of [double], we
    have [double n = S (S (double m'))].  There are two cases to
    consider for [n].

    Se [n = 0], então por definição [double n = 0], uma contradição.
    Assim, podemos assumir que [n = S n'] para algum [n'], e novamente 
    pela definição de [double] nós temos [S (S (double n')) = S (S 
    (double m'))], o que implica por inversão que [double n' = double 
    m'].
    
    Instanciar a hipótese de indução com [n'], portanto, permite-nos 
    concluir que [n' = m'], e segue-se imediatamente que [S n' = S m']. 
    Uma vez que [S n' = n] e [S m' = m], isso é justamente o que 
    queríamos mostrar. [] *)

(** Abaixo se encontra outro exemplo de [inversion] e do uso de uma hipótese de 
indução geral apropriada. Esta uma forma ligeiramente indireta de declarar um 
fato que já provamos acima. As igualdades extras no força a fazer mais cálculos 
em equações e exercitar algumas das táticas que já vimos recentemente. *)

Theorem length_snoc' : forall (X : Type) (v : X)
                              (l : list X) (n : nat),
     length l = n ->
     length (snoc l v) = S n. 
Proof.
  intros X v l. induction l as [| v' l'].

  Case "l = []". 
    intros n eq. rewrite <- eq. reflexivity.

  Case "l = v' :: l'". 
    intros n eq. simpl. destruct n as [| n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
      apply f_equal. apply IHl'. inversion eq. reflexivity. Qed.

(** Pode ser tentador começar a provar o teorema acima através da introdução de
[n] e [eq] no contexto. No entanto, isto nos leva a uma hipótese de indução que
não é suficientemente forte. Compare a prova acima com a seguinte tentativa
(abortada): *)

Theorem length_snoc_bad : forall (X : Type) (v : X)
                              (l : list X) (n : nat),
     length l = n ->
     length (snoc l v) = S n. 
Proof.
  intros X v l n eq. induction l as [| v' l'].

  Case "l = []". 
    rewrite <- eq. reflexivity.

  Case "l = v' :: l'". 
    simpl. destruct n as [| n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
      apply f_equal. Abort. (* apply IHl'. *) (* A IH não se aplica! *)


(** [Dalay]As in the double examples, the problem is that by
    introducing [n] before doing induction on [l], the induction
    hypothesis is specialized to one particular natural number, namely
    [n].  In the induction case, however, we need to be able to use
    the induction hypothesis on some other natural number [n'].
    Retaining the more general form of the induction hypothesis thus
    gives us more flexibility.

    No geral, uma boa regra de ouro é fazer a hipótese de indução
    ser a mais geral possível. *)

(** **** Exercício: nível 3 (gen_dep_practice)  *)
(** [Francisco]Prove this by induction on [l]. *)

Theorem index_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     index n l = None.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 3, avançado, opcional (index_after_last_informal)  *)
(** Escrever uma prova informal correspondente à sua prova
    do Coq sobre [index_after_last]:
 
     _Theorem_: For all sets [X], lists [l : list X], and numbers
      [n], if [length l = n] then [index n l = None].
 
     _Proof_:
     (* PREENCHER *)
[]
*)

(** **** Exercício: nível 3, opcional (gen_dep_practice_more)  *)
(** Prove o seguinte teorema através de indução sobre [l]. *)

Theorem length_snoc''' : forall (n : nat) (X : Type) 
                              (v : X) (l : list X),
     length l = n ->
     length (snoc l v) = S n. 
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 3, opcional (app_length_cons)  *)
(** [Dalay]Prove this by induction on [l1], without using [app_length]
    from [Lists]. *)

Theorem app_length_cons : forall (X : Type) (l1 l2 : list X) 
                                  (x : X) (n : nat),
     length (l1 ++ (x :: l2)) = n ->
     S (length (l1 ++ l2)) = n.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 4, opcional (app_length_twice)  *)
(** Provar por indução sobre [l], sem utilizar app_length. *)

Theorem app_length_twice : forall (X:Type) (n:nat) (l:list X),
     length l = n ->
     length (l ++ l) = n + n.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)


(** **** Exercício: nível 3, opcional (double_induction)  *)
(** [Francisco]Prove the following principle of induction over two naturals. *)

Theorem double_induction: forall (P : nat -> nat -> Prop), 
  P 0 0 ->
  (forall m, P m 0 -> P (S m) 0) ->
  (forall n, P 0 n -> P 0 (S n)) ->
  (forall m n, P m n -> P (S m) (S n)) ->
  forall m n, P m n.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)


(* ###################################################### *)
(** * Aplicação de [destruct] a Expressões Compostas *)

(** Temos visto muitos exemplos em que a tática [destruct] é usada 
    para realizar análise de caso do valor de alguma variável. Mas 
    às vezes precisamos raciocinar por casos sobre o resultado de 
    alguma _expressão_. Nós também podemos fazer isso com [destruct].

    Aqui estão alguns exemplos: *)

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun. 
  destruct (beq_nat n 3).
    Case "beq_nat n 3 = true". reflexivity.
    Case "beq_nat n 3 = false". destruct (beq_nat n 5).
      SCase "beq_nat n 5 = true". reflexivity.
      SCase "beq_nat n 5 = false". reflexivity.  Qed.

	(** Após aplicar [unfold] em [sillyfun] na prova acima, percebemos que 
	estamos presos em [if (beq_nat n 3) then ... else ...]. Bem, [n] pode tanto 
	igual a como diferente de [3], então usamos [destruct (beq_nat n 3)] para 
	podermos provar nos dois casos.

    Em geral, a tática [destruct] pode ser usado para realizar a análise de caso
    dos resultados de cálculos arbitrários. Se [e] é uma expressão cujo tipo
    é algum tipo [T] definido indutivamente, então, para cada construtor [c] de
    [T], [destruct e] gera uma sub-meta em que todas as ocorrências de [e] (na
    meta e no contexto) são substituídas por [c].

*)

(** **** Exercício: nível 1 (override_shadow)  *)
Theorem override_shadow : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 3, opcional (combine_split)  *)
(** [Dalay]Complete the proof below *)

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** Algumas vezes, fazer um [destruct] em uma expressão composta (uma
    não variavél) irá apagar informação que precisamos para completar a prova. *)
(** [Francisco]For example, suppose
    we define a function [sillyfun1] like this: *)

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

(** E suponha que queremos convencer o Coq da observação bastante óbvia 
    de que [sillyfun1 n] resulta [true] apenas quando [n] é ímpar. 
    Por analogia com as provas que fizemos com [sillyfun] acima, é 
    natural começar a prova da seguinte forma: *)

Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3).
  (* preso... *)
Abort.

	(** Ficamos presos neste ponto pois o contexto não contém informação 
	suficiente para provar a meta! O problema é que a substituição realizada 
	por [destruct] é brutal demais -- ele jogou fora todas as ocorrências de 
	[beq_nat n 3], mas precisamos manter na memória esta expressão e como ela 
	foi destruída. O motivo é que precisamos posteriormente raciocinar sobre 
	esta sentença, uma vez que, neste ramo da análise de casos, [beq_nat n 3 = 
	true] se [n = 3], concluindo que [n] é ímpar.

    O que nós gostaríamos de fazer, de fato, seria substituir todas as
    ocorrências existentes de [beq_nat n 3], mas, ao mesmo tempo, adicionar uma
    equação para o contexto que registre em qual caso estamos. O marcador [eqn:]
    permite-nos introduzir uma equação como essa (com qualquer que seja o nome
    que escolhermos). *)

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3) eqn:Heqe3.
  (* Agora, temos o mesmo estado no qual ficamos bloqueados na tentativa
  anterior, exceto pelo fato de que o contexto contém uma premissa adicional de
  igualdade, que é exatamente do que precisamos para avançar. *)
    Case "e3 = true". apply beq_nat_true in Heqe3.
      rewrite -> Heqe3. reflexivity.
    Case "e3 = false".
     (* Quando chegamos ao segundo teste de igualdade no corpo do função sobre
     a qual estamos reciocinando, podemos usar [eqn:] novamente da mesma forma,
       permitindo-nos terminar a prova. *)
      destruct (beq_nat n 5) eqn:Heqe5. 
        SCase "e5 = true".
          apply beq_nat_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        SCase "e5 = false". inversion eq.  Qed.


(** **** Exercício: nível 2 (destruct_eqn_practice)  *)
Theorem bool_fn_applied_thrice : 
  forall (f : bool -> bool) (b : bool), 
  f (f (f b)) = f b.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 2 (override_same)  *)
Theorem override_same : forall (X:Type) x1 k1 k2 (f : nat->X),
  f k1 = x1 -> 
  (override f k1 x1) k2 = f k2.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(* ################################################################## *)
(** * Revisão *)

(** [Dalay]We've now seen a bunch of Coq's fundamental tactics.  We'll
    introduce a few more as we go along through the coming lectures,
    and later in the course we'll introduce some more powerful
    _automation_ tactics that make Coq do more of the low-level work
    in many cases.  But basically we've got what we need to get work
    done.

    Aqui está o que nós já vimos:

      - [intros]: 
        move hipóteses/variavéis da meta para o contexto 

      - [reflexivity]:
        finaliza a prova (quando a meta parece como [e = e])

      - [Francisco][apply]:
        prove goal using a hypothesis, lemma, or constructor

      - [apply... in H]: 
        apply a hypothesis, lemma, or constructor to a hypothesis in
        the context (forward reasoning)

      - [apply... with...]:
        explicitly specify values for variables that cannot be
        determined by pattern matching

      - [simpl]:
        simplifica cálculos na meta 

      - [simpl in H]:
        ... or a hypothesis 

      - [rewrite]:
        use an equality hypothesis (or lemma) to rewrite the goal 

      - [rewrite ... in H]:
        ... ou uma hipótese

      - [symmetry]: 
	      muda uma meta com a forma [t=u] para [u=t]

      - [symmetry in H]: 
	      muda uma hipótese com a forma [t=u] para [u=t]

      - [unfold]:
        substitui uma constante definida pelo seu lado direito na meta 

      - [unfold... in H]:
        ... or a hypothesis  

      - [destruct... as...]:
        case analysis on values of inductively defined types 

      - [Dalay][destruct... eqn:...]:
        specify the name of an equation to be added to the context,
        recording the result of the case analysis

      - [induction... as...]:
        induction on values of inductively defined types 

      - [inversion]:
        reason by injectivity and distinctness of constructors

      - [assert (e) as H]:
        introduz um "lema local" [e] e o chama de [H] 

      - [generalize dependent x]:
        move a variavél [x] (e tudo mais que depender dela)
        do contexto de volta para uma hipótese explícita na fórmula
        da meta
*)

(* ###################################################### *)
(** * Exercícios Adicionais *)

(** **** Exercício: nível 3 (beq_nat_sym)  *)
Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 3, avançado, opcional (beq_nat_sym_informal)  *)
(** [Francisco]Give an informal proof of this lemma that corresponds to your
    formal proof above:

   Theorem: For any [nat]s [n] [m], [beq_nat n m = beq_nat m n].

   Proof:
   (* PREENCHER *)
[]
 *)

(** **** Exercício: nível 3, opcional (beq_nat_trans)  *)
Theorem beq_nat_trans : forall n m p,
  beq_nat n m = true ->
  beq_nat m p = true ->
  beq_nat n p = true.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 3, avançado (split_combine)  *)
(** Acabamos de provar que, para todas as listas de pares, [combine] 
    é o inverso de [split]. Como você formalizaria a afirmação de que 
    [split] é o inverso de [combine]? Quando essa propriedade é verdadeira?

	Complete a definição de [split_combine_statement] abaixo com uma 
	propriedade que determina que [split] é o inverso de [combine]. Em seguida, 
	prove que a propriedade se mantém. (Evite usar [intros] mais do que o 
	necessário para não perder a hipótese indutiva mais geral. Dica: qual 
	propriedade você precisa de [l1] e [l2] para que [split] [combine l1 l2 = 
	(l1,l2)] seja verdadeira?) *)

Definition split_combine_statement : Prop :=
(* PREENCHER *) admit.

Theorem split_combine : split_combine_statement.
Proof.
(* PREENCHER *) Admitted.



(** [] *)

(** **** Exercício: nível 3 (override_permute)  *)
Theorem override_permute : forall (X:Type) x1 x2 k1 k2 k3 (f : nat->X),
  beq_nat k2 k1 = false ->
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 3, avançado (filter_exercise)  *)
(** Este exercício é um pouco desafiador. Preste atenção à forma da sua IH. *)

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 4, avançado (forall_exists_challenge)  *)
(** [Dalay]Define two recursive [Fixpoints], [forallb] and [existsb].  The
    first checks whether every element in a list satisfies a given
    predicate:
      forallb oddb [1;3;5;7;9] = true

      forallb negb [false;false] = true
  
      forallb evenb [0;2;4;5] = false
  
      forallb (beq_nat 5) [] = true
    O segundo verifica se existe um elemento na lista que
    satisfaz um dado predicado:
      existsb (beq_nat 5) [0;2;3;6] = false
 
      existsb (andb true) [true;true;false] = true
 
      existsb oddb [1;0;0;0;0;3] = true
 
      existsb evenb [] = false
    [Francisco]Next, define a _nonrecursive_ version of [existsb] -- call it
    [existsb'] -- using [forallb] and [negb].
 
    Prove theorem [existsb_existsb'] that [existsb'] and [existsb] have
    the same behavior.
*)

(* PREENCHER *)
(** [] *)





(** * Logic: Lógica em Coq *)

Require Export MoreCoq. 



(** [Claudia]Coq's built-in logic is very small: the only primitives are
    [Inductive] definitions, universal quantification ([forall]), and
    implication ([->]), while all the other familiar logical
    connectives -- conjunction, disjunction, negation, existential
    quantification, even equality -- can be encoded using just these.

    [Dalay]This chapter explains the encodings and shows how the tactics
    we've seen can be used to carry out standard forms of logical
    reasoning involving these connectives.

*)

(* ########################################################### *)
(** * Proposições *)

(** Nos capítulos anteriores, nós vimos vários exemplos de alegações
    fatuais (_proposições_) e meios de apresentar evidências das suas
    verdades (_provas_).  Em particular, nós temos trabalhados extensivamente 
    com _proposições de igualdades_ da forma [e1 = e2], com
    implicações ([P -> Q]), e com proposições quantificadas
    ([forall x, P]).  
*)


(** [Francisco]In Coq, the type of things that can (potentially) 
    be proven is [Prop]. *)

(** Aqui está um exemplo de uma proposição demonstrável: *)

Check (3 = 3).
(* ===> Prop *)

(** Abaixo se encontra um exemplo de proposição impossível de ser provada: *)

Check (forall (n:nat), n = 2).
(* ===> Prop *)

(** [Claudia]Recall that [Check] asks Coq to tell us the type of the indicated 
  expression. *)

(* ########################################################### *)
(** * Provas e Evidência *)

(** [Dalay]In Coq, propositions have the same status as other types, such as
    [nat].  Just as the natural numbers [0], [1], [2], etc. inhabit
    the type [nat], a Coq proposition [P] is inhabited by its
    _proofs_.  We will refer to such inhabitants as _proof term_ or
    _proof object_ or _evidence_ for the truth of [P]. 

    Em Coq, quando nós afirmamos e então provamos um lema como:

Lemma silly : 0 * 3 = 0.  
Proof. reflexivity. Qed.

    [Francisco]the tactics we use within the [Proof]...[Qed] keywords tell Coq
    how to construct a proof term that inhabits the proposition.  In
    this case, the proposition [0 * 3 = 0] is justified by a
    combination of the _definition_ of [mult], which says that [0 * 3]
    _simplifies_ to just [0], and the _reflexive_ principle of
    equality, which says that [0 = 0].


*)

(** *** *)

Lemma silly : 0 * 3 = 0.
Proof. reflexivity. Qed.

(** Podemos ver que expressão de prova Coq constrói para um dado lema usando
a diretiva [Print]: *)

Print silly.
(* ===> silly = eq_refl : 0 * 3 = 0 *)

(** Aqui, o termo de prova [eq_refl] testemunha a igualdade. (Depois haverá 
mais sobre igualdades!)*) 

(** ** Implicações _são_ Funções *)

(** [Claudia]Just as we can implement natural number multiplication as a
function:

[
mult : nat -> nat -> nat 
]

[Dalay]The _proof term_ for an implication [P -> Q] is a _function_ that
takes evidence for [P] as input and produces evidence for [Q] as its
output.
*)     

Lemma silly_implication : (1 + 1) = 2  ->  0 * 3 = 0.
Proof. intros H. reflexivity. Qed.

(** Nós podemos ver que o termo prova do lema abaixo é de fato
uma função: *)

Print silly_implication.
(* ===> silly_implication = fun _ : 1 + 1 = 2 => eq_refl
     : 1 + 1 = 2 -> 0 * 3 = 0 *)

(** ** Definição de Proposições *)

(** [Francisco]Just as we can create user-defined inductive types (like the
    lists, binary representations of natural numbers, etc., that we
    seen before), we can also create _user-defined_ propositions.

    Pergunta: Como você define o significado de uma proposição?  
*)

(** *** *)

(** O significado de uma proposição é dada pelas _regras_ e _definições_ que 
afirmam como construir uma _evidência_ para a verdade da proposição a partir de 
outra evidência.

    [Claudia]- Typically, rules are defined _inductively_, just like any other
      datatype.

    [Dalay]- Sometimes a proposition is declared to be true without
      substantiating evidence.  Such propositions are called _axioms_.

    Neste, e nos capítulos subsequentes, nós veremos de maneira mais detalhada
    mais sobre como esses termos de prova funcionam.
*)

(* ########################################################### *)
(** * Conjunção ("e" Lógico) *)

(** [Francisco]The logical conjunction of propositions [P] and [Q] can be
    represented using an [Inductive] definition with one
    constructor. *)

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q). 

(** A intuição por trás dessa definição é simples: para construir 
    evidência para [and P Q], devemos fornecer evidência para [P] 
    e evidência para [Q]. Mais precisamente:
    
    - [conj p q] pode ser tomada como uma evidência para [and P Q] se [p] for 
    evidência para [P] e [q] for evidência para [Q]; e

    [Claudia]- this is the _only_ way to give evidence for [and P Q] --
      that is, if someone gives us evidence for [and P Q], we
      know it must have the form [conj p q], where [p] is
      evidence for [P] and [q] is evidence for [Q]. 

   [Dalay]Since we'll be using conjunction a lot, let's introduce a more
   familiar-looking infix notation for it. *)

Notation "P /\ Q" := (and P Q) : type_scope.

(** (A anotação [type_scope] diz ao Coq que essa notação
    irá aparecer em preposições, não em valores.) *)

(** [Francisco]Consider the "type" of the constructor [conj]: *)

Check conj.
(* ===>  forall P Q : Prop, P -> Q -> P /\ Q *)

(** Observe que ele recebe 4 entradas -- a saber, as proposições [P] 
    e [Q] e evidências para [P] e [Q] -- e retorna como saída a 
    evidência de [P /\ Q]. *)

(** ** "Introdução" de conjunções *)

(** Além da elegância de construir tudo a partir de uma fundação minúscula, o 
que é legal sobre definir conjuntos desta maneira é que podemos provar 
sentenças 
envolvendo conjunções usando as táticas que já conhecemos. Por exemplo, se a 
sentença da meta for uma conjunção, podemos prová-lo aplicando o construtor 
simples [conj] (como pode ser visto a partir do tipo de [conj]), solucionando a 
meta atual e deixando as duas partes das conjunção como submetas a 
serem provadas separadamente. *)

Theorem and_example : 
  (0 = 0) /\ (4 = mult 2 2).
Proof.
  apply conj.
  Case "left". reflexivity.
  Case "right". reflexivity.  Qed.

(** [Claudia]Just for convenience, we can use the tactic [split] as a shorthand for
    [apply conj]. *)

Theorem and_example' : 
  (0 = 0) /\ (4 = mult 2 2).
Proof.
  split.
    Case "left". reflexivity.
    Case "right". reflexivity.  Qed.

(** ** "Eliminação" de conjunções *)
(** [Dalay]Conversely, the [destruct] tactic can be used to take a
    conjunction hypothesis in the context, calculate what evidence
    must have been used to build it, and add variables representing
    this evidence to the proof context. *)

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
(** Na prova a seguir, notar como o _aninhamento padrão_ no
    [destruct] quebra a hipótese [H : P /\ (Q /\ R)] em
    [HP: P], [HQ : Q], and [HR : R].  Terminar a prova a partir desse ponto: *)

Theorem and_assoc : forall P Q R : Prop, 
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  destruct H as [HP [HQ HR]].
(* PREENCHER *) Admitted.
(** [] *)



(* ###################################################### *)
(** * Se e Somente Se *)

(** [Francisco]The handy "if and only if" connective is just the conjunction of
    two implications. *)

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
(** Usando a prova acima de que [<->] é simétrico ([iff_sym]) 
    como um guia, provar que também é reflexivo e transitivo. *)

Theorem iff_refl : forall P : Prop, 
  P <-> P.
Proof. 
  (* PREENCHER *) Admitted.

Theorem iff_trans : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  (* PREENCHER *) Admitted.

(** Dica: se você possui uma hipótese com uma bi-implicação no contexto, você 
pode usar [inversion] para quebrá-la em duas implicações separadas. (Reflita o 
por que que isto funciona.) *)
(** [] *)


(** [Claudia]Some of Coq's tactics treat [iff] statements specially, thus
    avoiding the need for some low-level manipulation when reasoning
    with them.  In particular, [rewrite] can be used with [iff]
    statements, not just equalities. *)

(* ############################################################ *)
(** * Disjunção ("ou" Lógico) *)

(** ** Implementação da Disjunção *)

(** [Dalay]Disjunction ("logical or") can also be defined as an
    inductive proposition. *)

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q. 

Notation "P \/ Q" := (or P Q) : type_scope.

(** Considerar o "tipo" do construtor [or_introl]: *)

Check or_introl.
(* ===>  forall P Q : Prop, P -> P \/ Q *)

(** [Francisco]It takes 3 inputs, namely the propositions [P], [Q] and
    evidence of [P], and returns, as output, the evidence of [P \/ Q].
    Next, look at the type of [or_intror]: *)

Check or_intror.
(* ===>  forall P Q : Prop, Q -> P \/ Q *)

(** É como [or_introl] mas requer evidência para [Q] em vez de evidência 
    para [P]. *)

(** Intuitivamente, aqui estão duas formas de fornecer uma evidência para [P \/ 
Q]:

    [Claudia]- give evidence for [P] (and say that it is [P] you are giving
      evidence for -- this is the function of the [or_introl]
      constructor), or

    [Dalay]- give evidence for [Q], tagged with the [or_intror]
      constructor. *)

(** *** *)
(** Desde que [P \/ Q] tenha dois contrutores, realizar um [destruct] em
    uma hipótese do tipo [P \/ Q] gera duas submetas. *)

Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  destruct H as [HP | HQ].
    Case "left". apply or_intror. apply HP.
    Case "right". apply or_introl. apply HQ.  Qed.

(** [Francisco]From here on, we'll use the shorthand tactics [left] and [right]
    in place of [apply or_introl] and [apply or_intror]. *)

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

(** Nós já vimos vários lugares onde estruturas análogas podem ser 
    encontradas nos mundos computacional ([Type]) e lógico ([Prop])
    de Coq. Aqui está mais um: os operadores booleanos [andb] e [orb] 
    são claramente análogos dos conectivos lógicos [/\] e [\/]. Essa 
    analogia pode ser tornada mais precisa através dos seguintes 
    teoremas, que mostram como traduzir conhecimento sobre os
    comportamentos de [andb] e [orb] para certas entradas em fatos 
    proposicionais sobre essas entradas. *)

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

(** Falsidade lógica pode ser representada no Coq como uma proposição definida 
indutivamente sem nenhum construtor.*)

Inductive False : Prop := . 

(** [Claudia]Intuition: [False] is a proposition for which there is no way
    to give evidence. *)


(** [Dalay]Since [False] has no constructors, inverting an assumption
    of type [False] always yields zero subgoals, allowing us to
    immediately prove any goal. *)

Theorem False_implies_nonsense :
  False -> 2 + 2 = 5.
Proof. 
  intros contra.
  inversion contra.  Qed. 

(** Como isso funciona? A tática [inversion] quebra [contra] em cada um dos
    seus possíveis casos, e gera uma submeta para cada caso. Como [contra] é
    evidência para [False], ela _não_ tem casos possíveis, conseqüentemente,
    não tem casos possíveis na submeta e a prova está feita. *)

(** *** *)
(** [Francisco]Conversely, the only way to prove [False] is if there is already
    something nonsensical or contradictory in the context: *)

Theorem nonsense_implies_False :
  2 + 2 = 5 -> False.
Proof.
  intros contra.
  inversion contra.  Qed.

(** Na verdade, uma vez que a prova de [False_implies_nonsense] na 
    verdade não tem nada a ver com a coisa específica sem sentido 
    que está sendo provada; ela pode ser facilmente generalizada 
    para funcionar para um [P] arbitrário: *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* REALIZADO EM SALA *)
  intros P contra.
  inversion contra.  Qed.

(** A expressão latina _ex falso quodlibet_ significa, literalmente, "a partir de uma 
contradição, qualquer coisa segue." Esse teorema também conhecido como o _princípio da 
explosão_. *)

(* #################################################### *)
(** ** Veracidade *)

(** [Claudia]Since we have defined falsehood in Coq, one might wonder whether
    it is possible to define truth in the same way.  We can. *)

(** **** Exercício: nível 2, avançado (True)  *)
(** [Dalay]Define [True] as another inductively defined proposition.  (The
    intution is that [True] should be a proposition for which it is
    trivial to give evidence.) *)

(* PREENCHER *)
(** [] *)

(** Entretanto, diferentemente de [False], o qual vamos utilizar 
    extensivamente, [True] é utilizado muito raramente. Por si própria, ela é
    trivial (e portanto desinteressante) para provar como uma meta, e carrega
    informação inútil como uma hipótese. Mas ela pode ser útil ao definir
    [Prop]s complexos utilizando condicionais, ou como um parâmetro para 
    [Prop]s de ordem superior. *)

(* #################################################### *)
(** * Negação *)

(** [Francisco]The logical complement of a proposition [P] is written [not
    P] or, for shorthand, [~P]: *)

Definition not (P:Prop) := P -> False.

(** A intuição é que, se [P] não é verdade, então qualquer coisa 
    (até mesmo [False]) segue da suposição de [P]. *)

Notation "~ x" := (not x) : type_scope.

Check not.
(* ===> Prop -> Prop *)

(** É preciso um pouco de prática para se acostumar a trabalhar com negação no Coq. Mesmo 
que você consiga ver perfeitamente por que um certo fato é verdadeiro pode ser, a 
princípio, um pouco difícil organizar as coisas para que o Coq possa enxergar uma 
solução! Abaixo se encontram provas de alguns fatos familiares a respeito de negação para 
lhe aquecer. *) 

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
(** [Claudia]Write an informal proof of [double_neg]:

   _Theorem_: [P] implies [~~P], for any proposition [P].

   _Proof_:
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
(** [Dalay]Write an informal proof (in English) of the proposition [forall P
    : Prop, ~(P /\ ~P)]. *)

(* PREENCHER *)
(** [] *)

(** *** Lógica Construtiva *)
(** Note que alguns teoremas que são verdadeiros em lógica clássica _não_ são
    prováveis na lógica (construtiva) do Coq.  Por exemplo, vamos observar como
    essa prova fica travada... *)

Theorem classic_double_neg : forall P : Prop,
  ~~P -> P.
Proof.
  (* REALIZADO EM SALA *)
  intros P H. unfold not in H. 
  (* E agora? Não tem como inventar evidência para [~P] 
     a partir de evidência para [P]. *) 
  Abort.

(** **** Exercício: 5 stars, avançado, opcional (classical_axioms)  *)
(** [Francisco]For those who like a challenge, here is an exercise
    taken from the Coq'Art book (p. 123).  The following five
    statements are often considered as characterizations of
    classical logic (as opposed to constructive logic, which is
    what is "built in" to Coq).  We can't prove them in Coq, but
    we can consistently add any one of them as an unproven axiom
    if we wish to work in classical logic.  Prove that these five
    propositions are equivalent. *)

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
qualquer Prop [P] _particular_. Por quê? Porque nós não podemos provar 
a negação de tal axioma; se pudéssemos, teríamos tanto [~ (P \/ ~P)] 
e [~ ~ (P \/ ~P)], uma contradição.

 *)

Theorem excluded_middle_irrefutable:  forall (P:Prop), ~ ~ (P \/ ~ P).  
Proof.
  (* PREENCHER *) Admitted.


(* ########################################################## *)
(** ** Desigualdade *)

(** Afirmar [x <> y] é apenas o mesmo que afirmar [~(x = y)].

Notation "x <> y" := (~ (x = y)) : type_scope.

(** [Claudia]Since inequality involves a negation, it again requires
    a little practice to be able to work with it fluently.  Here
    is one very useful trick.  If you are trying to prove a goal
    that is nonsensical (e.g., the goal state is [false = true]),
    apply the lemma [ex_falso_quodlibet] to change the goal to
    [False].  This makes it easier to use assumptions of the form
    [~P] that are available in the context -- in particular,
    assumptions of the form [x<>y]. *)

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



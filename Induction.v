(** * Indução: Prova por Indução *)
 

(** [Claudia] The next line imports all of our definitions from the
    previous chapter. *)

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

(** [Diego] [Case] is not built into Coq: we need to define it ourselves.
    There is no need to understand how it works -- you can just skip
    over the definition to the example that follows.  It uses some
    facilities of Coq that we have not discussed -- the string
    library (just for the concrete syntax of quoted strings) and the
    [Ltac] command, which allows us to declare custom tactics.  Kudos
    to Aaron Bohannon for this nice hack! *)

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
(** Here's an example of how [Case] is used.  Step through the
   following proof and observe how the context changes. *)

Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".  (* <----- here *)
    reflexivity.
  Case "b = false".  (* <---- and here *)
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

    [Renan] For nested case analyses (e.g., when we want to use a [destruct]
    to solve a goal that has itself been generated by a [destruct]),
    there is an [SCase] ("subcase") tactic. *)

(** **** Exercício 2: ** (andb_true_elim2)  *)
(** Prove [andb_true_elim2], marking cases (and subcases) when
    you use [destruct]. *)

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

    [Claudia] This is a good place to mention one other piece of (possibly
    obvious) advice about line lengths.  Beginning Coq users sometimes
    tend to the extremes, either writing each tactic on its own line
    or entire proofs on one line.  Good style lies somewhere in the
    middle.  In particular, one reasonable convention is to limit
    yourself to 80-character lines.  Lines longer than this are hard
    to read and can be inconvenient to display and print.  Many
    editors have features that help enforce this. *)

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

(** [Diego] And reasoning by cases using [destruct n] doesn't get us much
   further: the branch of the case analysis where we assume [n = 0]
   goes through, but in the branch where [n = S n'] for some [n'] we
   get stuck in exactly the same way.  We could use [destruct n'] to
   get one step further, but since [n] can be arbitrarily large, if we
   try to keep on like this we'll never be done. *)

Theorem plus_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [| n'].
  Case "n = 0".
    reflexivity. (* so far so good... *)
  Case "n = S n'".
    simpl.       (* ...but here we are stuck again *)
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

    [Renan] In Coq, the steps are the same but the order is backwards: we
    begin with the goal of proving [P(n)] for all [n] and break it
    down (by applying the [induction] tactic) into two separate
    subgoals: first showing [P(O)] and then showing [P(n') -> P(S
    n')].  Here's how this works for the theorem we are trying to
    prove at the moment: *)

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

(** [Claudia] Prove the following lemmas using induction. You might need
    previously proven results. *)

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
(** [Diego] Briefly explain the difference between the tactics
    [destruct] and [induction].  

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

(** [Renan] The [assert] tactic introduces two sub-goals.  The first is
    the assertion itself; by prefixing it with [H:] we name the
    assertion [H].  (Note that we could also name the assertion with
    [as] just as we did above with [destruct] and [induction], i.e.,
    [assert (0 + n = n) as H].  Also note that we mark the proof of
    this assertion with a [Case], both for readability and so that,
    when using Coq interactively, we can see when we're finished
    proving the assertion by observing when the ["Proof of assertion"]
    string disappears from the context.)  The second goal is the same
    as the one at the point where we invoke [assert], except that, in
    the context, we have the assumption [H] that [0 + n = n].  That
    is, [assert] generates one subgoal where we must prove the
    asserted fact and a second subgoal where we can use the asserted
    fact to make progress on whatever we were trying to prove in the
    first place. *)

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

(** [Claudia] To get [plus_comm] to apply at the point where we want it, we can
    introduce a local lemma stating that [n + m = m + n] (for
    the particular [m] and [n] that we are talking about here), prove
    this lemma using [plus_comm], and then use this lemma to do the
    desired rewrite. *)

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

(** [Diego] Prove the following simple fact: *)

Theorem evenb_n__oddb_Sn : forall n : nat,
  evenb n = negb (evenb (S n)).
Proof.
  (* PREENCHER AQUI *) Admitted.
(** [] *)

(** * Mais Exercícios *)

(** **** Exercício: ***, opcional (more_exercises)  *)
(** [Diego] Take a piece of paper.  For each of the following theorems, first
    _think_ about whether (a) it can be proved using only
    simplification and rewriting, (b) it also requires case
    analysis ([destruct]), or (c) it also requires induction.  Write
    down your prediction.  Then fill in the proof.  (There is no need
    to turn in your piece of paper; this is just to encourage you to
    reflect before hacking!) *)

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
(** [Renan] The [replace] tactic allows you to specify a particular subterm to
   rewrite and what you want it rewritten to.  More precisely,
   [replace (t) with (u)] replaces (all copies of) expression [t] in
   the goal by expression [u], and generates [t = u] as an additional
   subgoal. This is often useful when a plain [rewrite] acts on the wrong
   part of the goal.  

   Use the [replace] tactic to do a proof of [plus_swap'], just like
   [plus_swap] but without needing [assert (n + m = m + n)]. 
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

    (b)[Diego]You might naturally think that we should also prove the
        opposite direction: that starting with a binary number,
        converting to a natural, and then back to binary yields the
        same number we started with.  However, it is not true!
        Explain what the problem is.

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

(** [Renan]The question of what, exactly, constitutes a "proof" of a
    mathematical claim has challenged philosophers for millennia.  A
    rough and ready definition, though, could be this: a proof of a
    mathematical proposition [P] is a written (or spoken) text that
    instills in the reader or hearer the certainty that [P] is true.
    That is, a proof is an act of communication.

 
 Agora, os atos de comunicação podem envolver diferentes tipos de
 leitores. De um lado, o "leitor" pode ser um programa como o Coq, em
 que, no caso, a "crença" transmitida é uma simples verificação
 mecânica de que [P] pode ser derivada a partir de um conjunto de
 regras lógicas formais, e a prova é uma receita que guia o programa
 em sua verificação. Estas receitas são as provas _formais_.

    [Claudia]Alternatively, the reader can be a human being, in which case the
    proof will be written in English or some other natural language,
    thus necessarily _informal_.  Here, the criteria for success are
    less clearly specified.  A "good" proof is one that makes the
    reader believe [P].  But the same proof may be read by many
    different readers, some of whom may be convinced by a particular
    way of phrasing the argument, while others may not be.  One reader
    may be particularly pedantic, inexperienced, or just plain
    thick-headed; the only way to convince them will be to make the
    argument in painstaking detail.  [Dalay]But another reader, more familiar
    in the area, may find all this detail so overwhelming that they
    lose the overall thread.  All they want is to be told the main
    ideas, because it is easier to fill in the details for themselves.
    Ultimately, there is no universal standard, because there is no
    single way of writing an informal proof that is guaranteed to
    convince every conceivable reader.  In practice, however,
    mathematicians have developed a rich set of conventions and idioms
    for writing about complex mathematical objects that, within a
    certain community, make communication fairly reliable.  The
    conventions of this stylized form of communication give a fairly
    clear standard for judging proofs good or bad.

    [Diego]Because we are using Coq in this course, we will be working
    heavily with formal proofs.  But this doesn't mean we can ignore
    the informal ones!  Formal proofs are useful in many ways, but
    they are _not_ very efficient ways of communicating ideas between
    human beings. *)

(** For example, here is a proof that addition is associative: *)

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

(** [Renan]The overall form of the proof is basically similar.  This is
    no accident: Coq has been designed so that its [induction] tactic
    generates the same sub-goals, in the same order, as the bullet
    points that a mathematician would write.  But there are
    significant differences of detail: the formal proof is much more
    explicit in some ways (e.g., the use of [reflexivity]) but much
    less explicit in others (in particular, the "proof state" at any
    given point in the Coq proof is completely implicit, whereas the
    informal proof reminds the reader several times where things
    stand). *)

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

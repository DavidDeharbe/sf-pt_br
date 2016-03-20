(** * Rel: Propriedades das Relações *)

Require Export SfLib.

(** Esse curto capítulo, opcional, desenvolve algumas definições básicas e
    teoremas sobre relações binárias em Coq. Como as definições chaves são
    repetidas nos locais onde são usadas (no capítulo [Smallstep]), os leitores
    que já tem familiaridade com essas ideias podem tranquilamente passar
    rapidamente ou até desconsiderar esse capítulo. No entanto, as relações
    também são uma excelente fonte de exercícios para desenvolver habilidades
    com as funcionalidades básicas de raciocínio do Coq; portanto, é
    interessante estudá-lo logo após o capítulo [Logic]. *)

(** Uma _relação_ (binária) em um conjunto [X] é uma família de proposições
    tendo dois elementos de [X] como parâmetros -- i.e., uma proposição sobre
    pares do elementos de [X]. *)

Definition relation (X: Type) := X->X->Prop.

(** De forma talvez confusa, a biblioteca padrão Coq sequestra o termo genêrico
    "relação" para essa instância específica. Para manter consistência com a
    biblioteca faremos o mesmo. Logo, daqui em diante o identificador [Coq]
    sempre fará referência a uma relação binária entre um conjunto e ele mesmo,
    enquanto a palavra portuguesa "relação" pode fazer referência ou para o
    conceito específico ao Coq, ou o conceito mais geral de uma relação entre um
    número qualquer de conjuntos possivelmente diferentes. O contexto da
    discussão vai sempre deixar claro o significado preciso. *)

(** Um exemplo de relação em [nat] é [le], a relação menor-ou-igual-a que
    usualmente é denotada da seguinte forma [n1 <= n2]. *)

Print le.
(* ====> Inductive le (n : nat) : nat -> Prop :=
             le_n : n <= n
           | le_S : forall m : nat, n <= m -> n <= S m *)
Check le : nat -> nat -> Prop.
Check le : relation nat.

(* ######################################################### *)
(** * Propriedades Básicas das Relações *)

(** Como qualquer pessoa que fez um curso de matemática discreta na graduação
    sabe, tem muito a dizer sobre relações em geral -- formas de classificar
    relações (que são reflexivas, transitivas, etc.), teoremas que podem ser
    demonstrado genericamente sobre classes de relações, construções que derivam
    uma relação a partir de outra, etc.  Por exemplo... *)

(** A relação [R] em um conjunto [X] é uma _função parcial_ se, para cada [x],
    há pelo menos um [y] tal que [R x y] -- ou seja, se [R x y1] e [R x y2]
    juntos implicam [y1 = y2]. *)

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2. 

(** Por exemplo, a relação [next_nat] definida mais cedo é uma função
    parcial. *)

Print next_nat.
(* ====> Inductive next_nat (n : nat) : nat -> Prop := 
           nn : next_nat n (S n) *)
Check next_nat : relation nat.

Theorem next_nat_partial_function : 
   partial_function next_nat.
Proof. 
  unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1. inversion H2.
  reflexivity.  Qed. 

(** Porém, a relação [<=] em [nat] não é uma função parcial.  Resumidamente:
    assume, para uma contradição, que [<=] é uma função parcial. No entanto,
    como [0 <= 0] e [0 <= 1], segue que [0 = 1].  Isto é contraditório, e a
    hipótese era contraditória. *)

Theorem le_not_a_partial_function :
  ~ (partial_function le).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense.
   Case "Proof of assertion".
   apply Hc with (x := 0). 
     apply le_n. 
     apply le_S. apply le_n. 
  inversion Nonsense.   Qed.

(** **** Exercício: nível 2, opcional  *)

(** Mostre que [total_relation] definido anteriormente não é uma função
    parcial. *)

(* PREENCHER *)
(** [] *)

(** **** Exercício: nível 2, opcional  *)
(** Mostre que [empty_relation] definido anteriormente é uma função parcial. *)

(* PREENCHER *)
(** [] *)

(** Uma relação _reflexiva_ em um conjunto [X] é tal que cada elemento de [X]
    é relacionado com ele mesmo. *)

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof. 
  unfold reflexive. intros n. apply le_n.  Qed.

(** A relação [R] é _transitiva  se [R a c] é satisfeita cada vez
    que [R a b] e [R b c] o são. *)

Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
  transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  Case "le_n". apply Hnm.
  Case "le_S". apply le_S. apply IHHmo.  Qed.

Theorem lt_trans:
  transitive lt.
Proof. 
  unfold lt. unfold transitive. 
  intros n m o Hnm Hmo.
  apply le_S in Hnm. 
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  apply Hnm.
  apply Hmo. Qed.

(** **** Exercício: nível 2, opcional  *)
(** É possível demonstrar [lt_trans] de forma mais trabalhosa, por
    indução, sem usar [le_trans]. Fazer isto. *)

Theorem lt_trans' :
  transitive lt.
Proof.
  (* Demonstrar por indução na evidência que [m] é menor que [o]. *)
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
    (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 2, opcional  *)
(** Demonstrar a mesma propriedade por indução em [o]. *)

Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
  (* PREENCHER *) Admitted.
(** [] *)

(** A transitividade de [le], por sua vez, pode ser usada para demonstrar
    para algumas propriedades que serão úteis mais tarde (por exemplo,
    para a prova da antisimetria abaixo)... *)

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof. 
  intros n m H. apply le_trans with (S n).
    apply le_S. apply le_n.
    apply H.  Qed.

(** **** Exercício: nível 1, opcional  *)
Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 2, opcional (le_Sn_n_inf)  *)
(** Prover uma demonstração informal do teorema seguinte:
 
    Teorema: Para cada [n], [~(S n <= n)]
 
    Uma demonstração formal disto constitui um exercício opcional
    a seguir, mas tente desenvolver uma demonstração informal antes
    de iniciar a demonstração formal.
 
    Demonstração:
    (* PREENCHER *)
    []
 *)

(** **** Exercício: nível 1, opcional  *)
Theorem le_Sn_n : forall n,
  ~ (S n <= n).
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** Reflexividade e transitividade são os conceitos principais que são usados
    nos capítulos subsequentes, mas, para ter um pouco mais de prática com
    relações em Coq, seguem mais alguns conceitos recorrentes.

    A relação [R] é _simétrica_ se [R a b] implica [R b a]. *)

Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

(** **** Exercício: nível 2, opcional  *)
Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** Uma relação [R] é  antisimétrica  se [R a b] e [R b a] juntos
    implicam [a = b] -- ou seja, os únicos "cíclos" em [R] são os
    triviais. *)

Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

(** **** Exercício: nível 2, opcional  *)
Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 2, opcional  *)
Theorem le_step : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
Proof. 
  (* PREENCHER *) Admitted.
(** [] *)

(** A relação é de _equivalência_ se é reflexiva, simétrica e transitiva. *)

Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

(** A relação é uma  ordem parcial  quando é reflexiva,  anti_-simétrica, e
    transitiva. Na biblioteca padrão Coq é simplesmente chamada "order". *)

Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

(** Uma pré-ordem é quase idêntica a uma ordem parcial, mas não precisa ser
    antisimétrica. *)

Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).

Theorem le_order :
  order le.
Proof.
  unfold order. split. 
    Case "refl". apply le_reflexive.
    split. 
      Case "antisym". apply le_antisymmetric. 
      Case "transitive.". apply le_trans.  Qed.

(* ########################################################### *)
(** * Fecho Transitivo e Reflexivo *)

(** O _fecho transitivo e reflexivo  de uma relação [R] é a menor relação que
    contem [R] e que é reflexiva e transitiva. Formalmente a definição do módulo
    Relations na biblioteca padrão Coq: *)

Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
    | rt_step : forall x y, R x y -> clos_refl_trans R x y
    | rt_refl : forall x, clos_refl_trans R x x
    | rt_trans : forall x y z,
          clos_refl_trans R x y ->
          clos_refl_trans R y z ->
          clos_refl_trans R x z.

(** Por exemplo, o fecho reflexivo e transitivo da relação [next_nat] coincide
    com a relação [le]. *)

Theorem next_nat_closure_is_le : forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros n m. split.
    Case "->".
      intro H. induction H.
      SCase "le_n". apply rt_refl.
      SCase "le_S".
        apply rt_trans with m. apply IHle. apply rt_step. apply nn.
    Case "<-".
      intro H. induction H.
      SCase "rt_step". inversion H. apply le_S. apply le_n.
      SCase "rt_refl". apply le_n.
      SCase "rt_trans".
        apply le_trans with y.
        apply IHclos_refl_trans1.
        apply IHclos_refl_trans2. Qed.

(** A definição acima do fecho reflexivo e transitivo é natural -- enuncia,
    explicitamente, que o fecho reflexivo e transitivo de [R] é a menor relação
    que inclui [R] e que é fechada pelas regras de reflexividade e
    transitividade. Mas acontece que esta definição não é muito conveniente para
    realizar demonstrações -- o "não-determinismo" da regra [rt_trans] as vezes
    leva induções complexas.  Uma definição mais útil é... *)

Inductive refl_step_closure {X:Type} (R: relation X) : relation X :=
  | rsc_refl  : forall (x : X), refl_step_closure R x x
  | rsc_step : forall (x y z : X),
                    R x y ->
                    refl_step_closure R y z ->
                    refl_step_closure R x z.

(** (Observe que, tirando o nome dos construtores, esta definição é a mesma
    que a relação [multi] utilizada em vários outros capítulos.) *)

(** (As definições [Tactic Notation] seguintes são explicadas em um outro
    capítulo. Você pode ignorar as mesmas caso não tenha lido estas explicações
    ainda.) *)

Tactic Notation "rt_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "rt_step" | Case_aux c "rt_refl" 
  | Case_aux c "rt_trans" ].

Tactic Notation "rsc_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "rsc_refl" | Case_aux c "rsc_step" ].

(** Nossa nova definição do fecho reflexivo e transitivo empacota as regras
    [rt_step] e [rt_trans] em uma única regra, a saber [rsc_step]. A premissa
    a esquerda desta regra é um uso único de [R], o que leva a um princípio
    de indução bem mais simples.

    Mas, antes de prosseguir, devemos verificar que as definições de fato
    definem a mesma relação... 

    Primeiramente, nós demonstramos dois lemas evidenciando que 
    [refl_step_closure] espelha o comportamento dois dois 
    construtores de [clos_refl_trans] que desapereceram.
 *)

Theorem rsc_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> refl_step_closure R x y.
Proof.
  intros X R x y H.
  apply rsc_step with y. apply H. apply rsc_refl.   Qed.

(** **** Exercício: nível 2, opcional (rsc_trans)  *)
Theorem rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      refl_step_closure R x y  ->
      refl_step_closure R y z ->
      refl_step_closure R x z.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** Em seguida, utilizamos esses fatos para demonstrar que as duas
    definições do fecho reflexivo e transitivo levam à definição da
    mesma relação. *)

(** **** Exercício: nível 3, opcional (rtc_rsc_coincide)  *)
Theorem rtc_rsc_coincide : 
         forall (X:Type) (R: relation X) (x y : X),
  clos_refl_trans R x y <-> refl_step_closure R x y.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)


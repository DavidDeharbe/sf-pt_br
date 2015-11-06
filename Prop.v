(** * Prop: Proposições e Evidência *)

Require Export Logic.

(* ####################################################### *)
(** * Proposições Definidas Indutivamente *)

(** [Claudia] In chapter [Basics] we defined a _function_ [evenb] that tests a
    number for evenness, yielding [true] if so.  We can use this
    function to define the _proposition_ that some number [n] is
    even: *)

Definition even (n:nat) : Prop := 
  evenb n = true.

(** [Dalay] That is, we can define "[n] is even" to mean "the function [evenb]
    returns [true] when applied to [n]."  

    Note que aqui temos dado um nome para
    uma proposição utilizando uma [Definition], assim como temos dado
    nomes para expressões de outros tipos. Ela não é fundamentalmente um
    novo tipo de proposição;  Ela ainda é apenas uma igualdade. *)

(** Uma outra alternativa é definir o conceito de uniformidade
    diretamente. Em vez de ser via a função [evenb] ("um número é par se
    um determinado rendimento de computação é [verdadeiro]"), nós podemos
    dizer que o conceito de uniformidade significa quedando duas maneiras
    diferentes de apresentar _evidência_ de que um número é par. *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).


(** A primeira linha declara que [ev] é uma proposição -- ou, mais 
    formalmente, uma família de proposições "indexadas por" números 
    naturais. (Ou seja, para cada número [n], a afirmação de que "[n] 
    é par" é uma proposição.) Tal família de proposições é muitas 
    vezes chamada de _propriedade_ de números.

	As duas últimas linhas declaram as duas formas de fornecer provas de que 
	[m] é par. Em primeiro lugar, [0] é par e [ev_0] é evidência disso. 
	Segundo, se [m = S (S n)] para algum [n] e podemos prover a evidência [e] 
	de que [n] é par então [m] também é par e [ev_SS n e] é a evidência. 
*)


(** **** Exercício: nível 1 (double_even)  *)

Theorem double_even : forall n,
  ev (double n).
Proof.
  (* PREENCHER *) Admitted.
(** [] *)



(* ##################################################### *)

(** [Claudia] For [ev], we had already defined [even] as a function (returning a
   boolean), and then defined an inductive relation that agreed with
   it. However, we don't necessarily need to think about propositions
   first as boolean functions, we can start off with the inductive
   definition.
*)

(** [Dalay] As another example of an inductively defined proposition, let's
    define a simple property of natural numbers -- we'll call it
    "[beautiful]." *)

(** Informalmente, um número é [beautiful] se ele é [0], [3], [5], ou a
    soma de dois números [beautiful].  

    Mais pedantemente, nós podemos definir o número [beautiful]
    dando quarto regras:

       - Regra [b_0]: O número [0] é [beautiful].
       - Regra [b_3]: O número [3] é [beautiful]. 
       - Regra [b_5]: O número [5] é [beautiful]. 
       - Regra [b_sum]: Se [n] e [m] são ambos [beautiful], logo a soma
         deles também é. *)

(** Veremos muitas definições como esta durante o resto do curso, e 
    para fins de discussões informais, é útil ter uma notação leve 
    que as torne fácil de ler e escrever.  _Regras de inferência_ são 
    um exemplo de tal notação: *)
(**
                              -----------                               (b_0)
                              beautiful 0
                              
                              ------------                              (b_3)
                              beautiful 3

                              ------------                              (b_5)
                              beautiful 5    

                       beautiful n     beautiful m
                       ---------------------------                      (b_sum)
                              beautiful (n+m)   
*)

(** *** *)

	

(**  

Cada uma das regras textuais acima é reformatado aqui como uma regra de 
inferência; a leitura pretendida é que, se as _premissas_ acima da linha forem 
verdadeiras, então a _conclusão_ abaixo da linha também é. Por exemplo, a regra 
[b_sum] informa que se [n] e [m] são ambos números bonitos ([beautiful]), então 
conclui-se que [n+m] também é [beautiful]. Se uma regra não possui premissas 
então significa que a conclusão é válida incondicionalmente.

    [Claudia]These rules _define_ the property [beautiful].  That is, if we
    want to convince someone that some particular number is [beautiful],
    our argument must be based on these rules.  For a simple example,
    suppose we claim that the number [5] is [beautiful].  To support
    this claim, we just need to point out that rule [b_5] says so.
    Or, if we want to claim that [8] is [beautiful], we can support our
    claim by first observing that [3] and [5] are both [beautiful] (by
    rules [b_3] and [b_5]) and then pointing out that their sum, [8],
    is therefore [beautiful] by rule [b_sum].  This argument can be
    expressed graphically with the following _proof tree_: *)
(**
         ----------- (b_3)   ----------- (b_5)
         beautiful 3         beautiful 5
         ------------------------------- (b_sum)
                   beautiful 8   
*)
(** *** *)
(** 
    [Dalay] Of course, there are other ways of using these rules to argue that
    [8] is [beautiful], for instance:
         ----------- (b_5)   ----------- (b_3)
         beautiful 5         beautiful 3
         ------------------------------- (b_sum)
                   beautiful 8   
*)

(** **** Exercício: nível 1 (varieties_of_beauty)  *)
(** Existem quantas maneiras diferentes para mostrar que [8] é [beautiful]? *)

(* PREENCHER *)
(** [] *)

(* ####################################################### *)
(** ** Construindo Evidência *)

(** Em Coq, nós podemos expressar a definição de [beautiful]
    como se segue: *)

Inductive beautiful : nat -> Prop :=
  b_0   : beautiful 0
| b_3   : beautiful 3
| b_5   : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).

(** *** *)
(** 
    As regras introduzidas desta forma têm o mesmo status que os teoremas
    provados; ou seja, elas são verdadeiras axiomaticamente. 
    Assim, podemos usar a tática [apply] de Coq com nomes de regras 
    para provar que números particulares são [beautiful]. *)

Theorem three_is_beautiful: beautiful 3.
Proof.
   (* Segue diretamente da regra [b_3]. *)
   apply b_3.
Qed.

Theorem eight_is_beautiful: beautiful 8.
Proof.
   (* Primeiramente usamos a regra [b_sum], instruindo Coq como
      instanciar [n] e [m]. *)
   apply b_sum with (n:=3) (m:=5).
   (* Para solucionar as submetas geradas por [b_sum], devemos prover
      evidência para [beautiful 3] e [beautiful 5]. Felizmente, temos
      regras para ambas. *)
   apply b_3.
   apply b_5.
Qed.

(** *** *)
(** Como pensado, nós também podemos provar teoremas que possuem hipóteses 
sobre [beautiful]. *)

Theorem beautiful_plus_eight: forall n, beautiful n -> beautiful (8+n).
Proof.
  intros n B.
  apply b_sum with (n:=8) (m:=n).
  apply eight_is_beautiful.
  apply B.
Qed.

(** **** Exercício: nível 2 (b_times2)  *)
Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
Proof.
    (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 3 (b_timesm)  *)
Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof.
   (* PREENCHER *) Admitted.
(** [] *)


(* ####################################################### *)
(** * Uso de Evidência em Provas *)
(** ** Indução sobre Evidência *)

(** [Claudia]Besides _constructing_ evidence that numbers are beautiful, we can
    also _reason about_ such evidence. *)

(** [Dalay]The fact that we introduced [beautiful] with an [Inductive]
    declaration tells Coq not only that the constructors [b_0], [b_3],
    [b_5] and [b_sum] are ways to build evidence, but also that these
    four constructors are the _only_ ways to build evidence that
    numbers are beautiful. *)

(** Em outras palavras, se alguém nos dá a evidência [E] para a asserção
    [beautiful n], então sabemos que [E] deve ter um desses quatro formatos:

      - [E] é [b_0] (e [n] é [O]),
      - [E] é [b_3] (e [n] é [3]), 
      - [E] é [b_5] (e [n] é [5]), ou
      - [E] é [b_sum n1 n2 E1 E2] (e [n] é [n1+n2], em que [E1] é
        evidência que [n1] é beautiful e [E2] é evidência que [n2]
        é beautiful). *)

(** *** *)    
(** Isto nós permite _analisar_ qualquer hipótese da forma
    [beautiful n] para ver como ele foi construído, usando a tática que
    nós já conhecemos. Em particular, nós podemos usar a tática de
    [induction] que nós já vimos para raciocinar sobre o _dado_ definido
    indutivamente para racionar sobre a _evidência_ definida indutivamente.

    Para ilustrar isso, vamos definir uma outra propriedade de números: *)

Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n).

(** **** Exercício: nível 1 (gorgeous_tree)  *)
(** Escreva a definição de para números [gorgeous] usando a notação de regras 
de inferência.
 
(* PREENCHER *)
[]
*)


(** **** Exercício: nível 1 (gorgeous_plus13)  *)
Theorem gorgeous_plus13: forall n, 
  gorgeous n -> gorgeous (13+n).
Proof.
   (* PREENCHER *) Admitted.
(** [] *)

(** *** *)
(** [Claudia]It seems intuitively obvious that, although [gorgeous] and
    [beautiful] are presented using slightly different rules, they are
    actually the same property in the sense that they are true of the
    same numbers.  Indeed, we can prove this. *)


Theorem gorgeous__beautiful_FAILED : forall n, 
  gorgeous n -> beautiful n.
Proof.
   intros. induction n as [| n'].
   Case "n = 0". apply b_0.
   Case "n = S n'". (* Estamos travados! *)
Abort.

(** [Dalay]The problem here is that doing induction on [n] doesn't yield a
    useful induction hypothesis. Knowing how the property we are
    interested in behaves on the predecessor of [n] doesn't help us
    prove that it holds for [n]. Instead, we would like to be able to
    have induction hypotheses that mention other numbers, such as [n -
    3] and [n - 5]. This is given precisely by the shape of the
    constructors for [gorgeous]. *)


(** *** *)

(** Vamos ver o que acontece se nós tentarmos provar isso por indução sobre a
    evidência [H] em vez de sobre [n]. *)

Theorem gorgeous__beautiful : forall n, 
  gorgeous n -> beautiful n.
Proof.
   intros n H.
   induction H as [|n'|n'].
   Case "g_0".
       apply b_0.
   Case "g_plus3". 
       apply b_sum. apply b_3.
       apply IHgorgeous.
   Case "g_plus5".
       apply b_sum. apply b_5. apply IHgorgeous. 
Qed.


(* Estes exercícios também requisitão o uso de indução na evidência. *)

(** **** Exercício: nível 2 (gorgeous_sum)  *)
Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
 (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 3, avançado (beautiful__gorgeous)  *)
Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
 (* PREENCHER *) Admitted.
(** [] *)




(** **** Exercício: nível 3 stars, opcional (g_times2)  *)
(** Prove o teorema [g_times2] abaixo sem usar [gorgeous__beautiful]. 
    Você pode achar o seguinte lema auxiliar útil. *)

Lemma helper_g_times2 : forall x y z, x + (z + y) = z + x + y.
Proof.
   (* PREENCHER *) Admitted.

Theorem g_times2: forall n, gorgeous n -> gorgeous (2*n).
Proof.
   intros n H. simpl. 
   induction H.
   (* PREENCHER *) Admitted.
(** [] *)



(** Abaixo se encontra uma prova de que a definição indutiva de números pares 
implicam na definição computacional. *)

Theorem ev__even : forall n,
  ev n -> even n.
Proof.
  intros n E. induction E as [| n' E'].
  Case "E = ev_0". 
    unfold even. reflexivity.
  Case "E = ev_SS n' E'".  
    unfold even. apply IHE'.  
Qed.

(** **** Exercício: nível 1 (ev__even)  *) 
(** [Claudia]Could this proof also be carried out by induction on [n] instead
    of [E]?  If not, why not? *)

(* PREENCHER *)
(** [] *)

(** [Dalay]Intuitively, the induction principle [ev n] evidence [ev n] is
    similar to induction on [n], but restricts our attention to only
    those numbers for which evidence [ev n] could be generated. *)

(** **** Exercício: nível 1 (l_fails)  *)
(** A tentativa de prova a seguir não irá funcionar.
     Theorem l : forall n,
       ev n.
     Proof.
       intros n. induction n.
         Case "O". simpl. apply ev_0.
         Case "S".
           ...
   Intuitivamente, nós esperamos que a prova falhe porque 
   nem todo número é par. Contudo, o que exatamente causa a falha da prova?

(* PREENCHER *)
*)
(** [] *)

(** Aqui está outro exercício que requer indução em evidências. *)
(** **** Exercício: nível 2 (ev_sum)  *)

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof. 
  (* PREENCHER *) Admitted.
(** [] *)



(* ####################################################### *)
(** ** Inversão em Evidência *)

(** Ter evidências para uma proposição é útil durante uma prova pois podemos 
_olhar_ para as evidências a fim de obter mais informações. Por exemplo, 
considere a prova de que se [n] é par], então [pred (pred n)] é também. Neste 
caso, nós não precisamos efetuar uma prova indutiva. A tática [inversion] 
fornece todas as informações que precisamos.

*)

Theorem ev_minus2: forall n,  ev n -> ev (pred (pred n)). 
Proof.
  intros n E.
  inversion E as [| n' E'].
  Case "E = ev_0". simpl. apply ev_0. 
  Case "E = ev_SS n' E'". simpl. apply E'.  Qed.

(** **** Exercício: nível 1, opcional (ev_minus2_n)  *)
(** [Claudia]What happens if we try to use [destruct] on [n] instead of [inversion] on [E]? *)

(* PREENCHER *)
(** [] *)

(** *** *)
(** [Dalay]Here is another example, in which [inversion] helps narrow down to
the relevant cases. *)

Theorem SSev__even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. 
  inversion E as [| n' E']. 
  apply E'. Qed.

(** ** Revisitando a Tática Inversion *)

(** O uso do [inversion] pode parecer um pouco misterioso no início.
    Até agora, temos utilizado o [inversion] somente em proposições de 
    igualdade, para utilizar injectividade de contrutores ou para discriminar
    entre diferentes contrutores.  Mas nós podemos ver que
    [inversion] também pode ser aplicada para análisar evidências
    de proposições indutivamente definidas.

    (Você também deve esperar que [destruct] seria uma tática
    mais adequada de usar aqui. De fato, é possível fazer o uso do [destruct], 
    mas ele frequentemente descarta informações úteis. e o qualtificador
    [eqn:] não ajuda muito nesse caso.)    

    Aqui está como [inversion] funciona no geral.  Suponha que o nome 
    [I] refere-se a uma suposição [P] no contexto atual, onde [P] 
    foi definida por uma declaração [Inductive]. Então, para cada 
    um dos construtores de [P], [inversion I] gera uma submeta em 
    que [I] foi substituída pelas condições exatas e específicas 
    nas quais esse construtor poderia ter sido usado para provar [P].
    Algumas dessas submetas serão autocontraditórias; [inversion] 
    as elimina. As que permanecem representam os casos que devem 
    ser provados para estabelecer a meta original.

	Neste caso em particular, o [inversion] analisou a construção [ev (S (S 
	n))]e determinou que isso somente poderia ser construído usando [ev_SS], 
	gerando uma nova submeta com os argumentos do construtor como novas 
	hipóteses. (A tática também produziu uma igualdade a mais que é inútil 
	nesta prova.) Começaremos a explorar nas próximas provas esse comportamento 
	mais geral da inversão. *)

(** **** Exercício: nível 1 (inversion_practice)  *)
Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  (* PREENCHER *) Admitted.

(** [Claudia]The [inversion] tactic can also be used to derive goals by showing
    the absurdity of a hypothesis. *)

Theorem even5_nonsense : 
  ev 5 -> 2 + 2 = 9.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 3, avançado (ev_ev__ev)  *)
(** [Dalay]Finding the appropriate thing to do induction on is a
    bit tricky here: *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 3, opcional (ev_plus_plus)  *)
(** Aqui está um exercício que somente requer aplicação de lemas já existentes.
    Nem indução ou até mesmo análise por caso é necessária, mas algumas das 
    reescritas podem ser tediosas. *)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  (* PREENCHER *) Admitted.
(** [] *)


(* ####################################################### *)
(** * Discussões e Variantes *)
(** ** Definição Computacional ou Definição Indutiva *)

(** Nós temos visto que a proposição "[n] é par" pode ser
    fraseado de duas maneiras diferentes -- indiretamente, via um teste
    da função booleana [evenb], ou diretamente, descrevendo indutivamente
    que constitui a evidência para uniformidade. Essas maneiras de definir
    uniformidade são igualmente fáceis de declarar e trabalhar com eles.
    Ao qual a escolhe se dá basicamente em questão de gosto.

    No entanto, para muitas outras propriedades de interesse, a 
    definição indutiva direta é preferível, uma vez que escrever 
    uma função de teste pode ser difícil ou mesmo impossível.
	
	Uma dessas propriedades é [beautiful]. Esta não é uma definição 
	perfeitamente sensata para um conjunto de números mas não podemos traduzir 
	sua definição diretamente para um Fixpoint do Coq (ou para uma função 
	recursiva em qualquer outra linguagem de programação comum). Podemos ser 
	capazes de encontrar uma maneira mais inteligente de testar esta 
	propriedade usando um [Fixpoint](de fato não é tão difícil encontrar uma 
	forma nesse caso), mas em geral isso pode exigir um pensamento 
	arbitrariamente profundo. Aliás, se a propriedade no qual estamos 
	interessados não for computável então não 
	podemos defini-lo como um [Fixpoint], não importa quantas tentativas 
	realizemos, pois o Coq exige que todos os [Fixpoint] correspondam a 
	computações que finalizáveis.
	
    [Claudia]On the other hand, writing an inductive definition of what it
    means to give evidence for the property [beautiful] is
    straightforward. *)




(* ####################################################### *)
(** ** Estruturas de Dados com Parâmetros *)

(** [Dalay]So far, we have only looked at propositions about natural numbers. However, 
   we can define inductive predicates about any type of data. For example, 
   suppose we would like to characterize lists of _even_ length. We can 
   do that with the following definition.  *)

Inductive ev_list {X:Type} : list X -> Prop :=
  | el_nil : ev_list []
  | el_cc  : forall x y l, ev_list l -> ev_list (x :: y :: l).

(** É claro, essa proposição é equivalente a dizer que o tamanho
da lista é par. *)

Lemma ev_list__ev_length: forall X (l : list X), ev_list l -> ev (length l).
Proof. 
    intros X l H. induction H.
    Case "el_nil". simpl. apply ev_0.
    Case "el_cc".  simpl.  apply ev_SS. apply IHev_list.
Qed.

(** Contudo, por causa da evidência [ev] contém menos informações que
    a evidência de [ev_list], a conversão direta deve ser declarada muito
    cuidadosamente. *)

Lemma ev_length__ev_list: forall X n, ev n -> forall (l : list X), n = length l -> ev_list l.
Proof.
  intros X n H. 
  induction H.
  Case "ev_0". intros l H. destruct l.
    SCase "[]". apply el_nil. 
    SCase "x::l". inversion H.
  Case "ev_SS". intros l H2. destruct l. 
    SCase "[]". inversion H2. destruct l.
    SCase "[x]". inversion H2.
    SCase "x :: x0 :: l". apply el_cc. apply IHev. inversion H2. reflexivity.
Qed.
    

(** **** Exercício: nível 4 (palíndromos)  *)
(** Um palíndromo é uma sequência que se lê da mesma forma de trás para
    frente e de frente para trás.

    - Definir uma proposição indutiva [pal] em [list X] que 
      capture o que significa ser um palíndromo. (Dica: Você vai 
      precisar de três casos. Sua definição deve basear-se na 
      estrutura da lista; ter um único construtor 
        c: forall l, l = rev l -> pal l 
      pode parecer óbvio, mas não vai funcionar muito bem.)
 
    - Provar [pal_app_rev] que 
       forall l, pal (l ++ rev l).
    - Provar [pal_rev] que 
       forall l, pal l -> l = rev l.
*)

(* PREENCHER *)
(** [] *)

(* Mais uma vez, o sentido inverso é muito mais difícil devido à falta de 
provas *) 

(** **** Exercício: nível 5, opcional (palindrome_converse)  *)
(** [Claudia]Using your definition of [pal] from the previous exercise, prove
    that
     forall l, l = rev l -> pal l.
*)

(* PREENCHER *)
(** [] *)



(* ####################################################### *)
(** ** Relações *)

(** [Dalay]A proposition parameterized by a number (such as [ev] or
    [beautiful]) can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

Module LeModule.  


(** Um exemplo útil é relação "menor que ou igual à"
    em números. *)

(** A definição seguinte deve ser razoavelmente intuitivo. Isto
    diz que existe duas maneiras de dar evidência que um número é menor ou 
    igual a outro: Ou observe que eles são os mesmos número, ou dado evidência
    que o primeiro é menor ou igual ao predecessor do segundo. *)

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).


(** Provas de fatos sobre [<=] usando os construtores [le_n] e [le_S] 
    seguem os mesmos padrões de provas sobre propriedades, como [ev] 
    no capítulo [Prop].  Podemos usar [apply] nos construtores para 
    provar metas com [<=] (por exemplo, para mostrar que [3<=3] ou 
    [3<=6]), e podemos usar táticas como [inversion] para extrair 
    informações das hipóteses com [<=] no contexto (por exemplo, 
    para provar que [(2 <= 1) -> 2+2=5]). *)

(** *** *)

(** Aqui se encontram alguns testes de sanidade para a definição. (Note que, 
apesar destes testes serem do mesmo tipo dos "testes unitários" criados para as 
funções de testes escritas nos primeiros capítulos, nós devemos construir suas 
provas explicitamente -- [simpl] e [reflexivity] não irão realizar suas funções 
aqui pois as provas não são apenas uma questão de simplificação de cálculos.
*)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* REALIZADO EM SALA *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* REALIZDO EM SALA *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof. 
  (* REALIZDO EM SALA *)
  intros H. inversion H. inversion H2.  Qed.

(** *** *)
(** [Claudia]The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

End LeModule.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** [Dalay]Here are a few more simple relations on numbers: *)

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn : forall n:nat, next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 : forall n, ev (S n) -> next_even n (S n)
  | ne_2 : forall n, ev (S (S n)) -> next_even n (S (S n)).

(** **** Exercício: nível 2 (total_relation)  *)
(** Definir uma relação binária indutiva [total_relation] que exista
    entre qualquer par de números naturais. *)

(* PREENCHER *)
(** [] *)

(** **** Exercício: nível 2 (empty_relation)  *)
(** Defina uma releção binária indutiva [empty_relation] (em números)
    que não mantém. *)

(* PREENCHER *)
(** [] *)

(** **** Exercício: nível 2, opcional (le_exercises)  *)
(** Aqui estão uma série de fatos, sobre as relações [<=] e [<], que iremos 
    precisar mais tarde no curso. As provas são bons exercícios práticos. *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  (* PREENCHER *) Admitted.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  (* PREENCHER *) Admitted.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof. 
  (* PREENCHER *) Admitted.


Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof. 
  (* PREENCHER *) Admitted.


Theorem le_plus_l : forall a b,
  a <= a + b.
Proof. 
  (* PREENCHER *) Admitted.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof. 
 unfold lt. 
 (* PREENCHER *) Admitted.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  (* PREENCHER *) Admitted.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof. 
  (* PREENCHER *) Admitted.

Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
  (* Dica: Pode ser mais fácil provar por indução sobre [m]. *)
  (* PREENCHER *) Admitted.

Theorem ble_nat_true_trans : forall n m o,
  ble_nat n m = true -> ble_nat m o = true -> ble_nat n o = true.                               
Proof.
  (* Dica: Este teorema é facilmente provado sem [induction]. *)
  (* PREENCHER *) Admitted.

(** **** Exercício: nível 2, opcional (ble_nat_false)  *)
Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  (* PREENCHER *) Admitted.
(** [] *)


(** **** Exercício: nível 3 (R_provability2)  *)
Module R.
(** Podemos definir relações ternárias, quaternárias, n-árias da mesma forma 
que relações binárias. Por exemplo, considere a relação ternária sobre números 
a seguir: *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0 
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

(** [Claudia]- Which of the following propositions are provable?
      - [R 1 1 2]
      - [R 2 2 6]

    [Dalay]- If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.
  
    - Se nós utilizarmos o construtor [c4] a partir da definição de [R],
      poderá o conjunto de proposições prováveis mudar?  Brevemente (1
      sentença) explique sua resposta.

(* PREENCHER *)
[]
*)

(** **** Exercício: nível 3, opcional (R_fact)  *)  
(** Relação [R] realmente codifica uma função familiar. Declare e
    prove dois teoremas que formalmente conecte a relação e a função.
    Isto é, se [R m n o] é verdadeiro, o que nós podemos dizer sobre [m],
    [n], e [o], e vice versa?
*)

(* PREENCHER *)
(** [] *)

End R.

(** **** Exercício: nível 4, avançado (subsequence)  *)
(** Uma lista é uma _subsequência_ de outra lista se todos os elementos da 
    primeira lista ocorrem na mesma ordem na segunda lista, possivelmente 
    com alguns elementos extras entre eles. Por exemplo, 
    [1,2,3]
    é uma subsequência de cada uma das listas
    [1,2,3]
    [1,1,1,2,2,3]
    [1,2,7,3]
    [5,6,1,9,9,2,7,3,8]
    mas _não_ é uma subsequência de nenhuma das listas
    [1,2]
    [1,3]
    [5,6,2,1,7,3,8]

    [Claudia]- Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    [Dalay]- Prove [subseq_refl] that subsequence is reflexive, that is, 
      any list is a subsequence of itself.  

    - Provar [subseq_app] que para qualquer lista [l1], [l2], e [l3], 
      se [l1] é uma subsequência de [l2], então [l1] também é uma subsequência
      de [l2 ++ l3].

    - (Opcional, difícil) Prove [subseq_trans] que subsequência é
      transitivo -- isto é, se [l1] é subsequência de [l2] e [l2] é uma 
      subsequência de [l3], então [l1] é uma subsequência de [l3].
      Dica: escolha sua indução cuidadosamente.
*)

(* PREENCHER *)
(** [] *)

(** **** Exercício: nível 2, opcional (R_provability)  *)
(** Suponha que fornecemos a Coq as seguintes definições:
    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.
    Quais das proposições seguintes são demonstráveis?

    - [R 2 [1,0]]
    - [R 1 [1,2,1,0]]
    - [R 6 [3,2,1,0]]
*)

(** [] *)


(* ##################################################### *)
(** * Programação através de Proposições *)
(** Como visto anteriormente, uma _proposição_ é uma sentença expressando uma 
afirmação sobre um fato como, por exemplo "dois mais dois é igual a quatro." No 
Coq, as proposições são escritas como expressões do tipo [Prop]. *)

Check (2 + 2 = 4).
(* ===> 2 + 2 = 4 : Prop *)

Check (ble_nat 3 2 = false).
(* ===> ble_nat 3 2 = false : Prop *)

Check (beautiful 8).
(* ===> beautiful 8 : Prop *)

(** *** *)
(** [Claudia]Both provable and unprovable claims are perfectly good
    propositions.  Simply _being_ a proposition is one thing; being
    _provable_ is something else! *)

Check (2 + 2 = 5).
(* ===> 2 + 2 = 5 : Prop *)

Check (beautiful 4).
(* ===> beautiful 4 : Prop *)

(** [Dalay]Both [2 + 2 = 4] and [2 + 2 = 5] are legal expressions
    of type [Prop]. *)

(** *** *)
(** Nós temos principalmente visto um lugar que proposições podem aparecer em
    Coq: em declarações de [Theorem] (e [Lemma] e [Example]). *)

Theorem plus_2_2_is_4 : 
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(** Mas eles podem ser usados em muitas outras maneiras. Por exemplo,
    nós também temos visto que nós pode dar um nome para uma proposição usando
    um [Definition], assim como nós temos dado nomes para expressões de outros
    tipos. *)

Definition plus_fact : Prop  :=  2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)

(** Podemos usar esse nome em qualquer situação onde é esperada uma 
    proposição -- por exemplo, como uma alegação em uma declaração [Theorem]. *)

Theorem plus_fact_is_true : 
  plus_fact.
Proof. reflexivity.  Qed.

(** *** *)
(** Temos visto várias maneiras de construir proposições.

	- Podemos definir uma nova proposição primitivamente usando [Inductive].
	
	- Dadas duas expressões [e1] e [e2] do mesmo tipo podemos formar a 
	proposição [e1 = e2], afirmando que seus valores são iguais.
	
	- Podemos combinar proposições usando implicação e quantificação *)

(** *** *)
(** [Claudia]We have also seen _parameterized propositions_, such as [even] and
    [beautiful]. *)

Check (even 4).
(* ===> even 4 : Prop *)
Check (even 3).
(* ===> even 3 : Prop *)
Check even. 
(* ===> even : nat -> Prop *)

(** *** *)
(** [Dalay]The type of [even], i.e., [nat->Prop], can be pronounced in
    three equivalent ways: (1) "[even] is a _function_ from numbers to
    propositions," (2) "[even] is a _family_ of propositions, indexed
    by a number [n]," or (3) "[even] is a _property_ of numbers."  *)

(** Proposições -- incluindo proposições parametrizadas -- são
    cidadãos de primeira classe em Coq.  Por exemplo, nós podemos definir
    funções a partir de números para proposições... *)

Definition between (n m o: nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.

(** ... e então aplica-las parcialmente: *)

Definition teen : nat->Prop := between 13 19.

(** Nós podemos passar proposição par -- incluindo proposições
    parametizados -- como argumentos para funções: *)

Definition true_for_zero (P:nat->Prop) : Prop :=
  P 0.

(** *** *)
(** Aqui estão mais dois exemplos de passagem de proposições parametrizadas 
    como argumentos para uma função.

	A primeira função, [true_for_all_numbers], toma uma proposição [P] como 
	argumento e constrói a proposição de que [P] é verdadeira para todos os 
	números naturais. *)

Definition true_for_all_numbers (P:nat->Prop) : Prop :=
  forall n, P n.

(** [Claudia]The second, [preserved_by_S], takes [P] and builds the proposition
    that, if [P] is true for some natural number [n'], then it is also
    true by the successor of [n'] -- i.e. that [P] is _preserved by
    successor_: *)

Definition preserved_by_S (P:nat->Prop) : Prop :=
  forall n', P n' -> P (S n').

(** *** *)
(** [Dalay]Finally, we can put these ingredients together to define
a proposition stating that induction is valid for natural numbers: *)

Definition natural_number_induction_valid : Prop :=
  forall (P:nat->Prop),
    true_for_zero P ->
    preserved_by_S P -> 
    true_for_all_numbers P. 





(** **** Exercício: nível 3 (combine_odd_even)  *)
(** Completar a definição da função [combine_odd_even] abaixo. 
    Ela toma como argumento duas propriedades dos números, [Podd] e
    [Peven]. Como resultado, ela deve retornar uma nova propriedade [P] tal
    que [P n] é equivalente a [Podd n] quando [n] é impar, e caso contrário é
    equivalente a [Peven n]. *)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  (* PREENCHER *) admit.

(** Para testar a sua definição, veja se você pode provar
    os fatos a seguir: *)

Theorem combine_odd_even_intro : 
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  (* PREENCHER *) Admitted.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  (* PREENCHER *) Admitted.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  (* PREENCHER *) Admitted.

(** [] *)

(* ##################################################### *)
(** Mais uma digressão rápida, para as almas aventureiras: se podemos 
    definir proposições parametrizadas utilizando [Definition], então 
    podemos também defini-las usando [Fixpoint]? Claro que sim!  No 
    entanto, este tipo de "parametrização recursiva" não corresponde 
    a nada coisa muito familiar da matemática cotidiana. O exercício 
    seguinte dá um pequeno exemplo. *)

(** **** Exercício: nível 4, opcional (true_upto_n__true_everywhere)  *)
(** Defina uma função recursiva [true_upto_n__true_everywhere] que      
[true_upto_n_example] funcione. *)

(* 
Fixpoint true_upto_n__true_everywhere
(* PREENCHER *)

Example true_upto_n_example :
    (true_upto_n__true_everywhere 3 (fun n => even n))
  = (even 3 -> even 2 -> even 1 -> forall m : nat, even m).
Proof. reflexivity.  Qed.
*)
(** [] *)




(** * Prop: Proposições e Evidência *)

Require Export Logic.

(* ####################################################### *)
(** * Proposições Definidas Indutivamente *)

(** No capítulo [Embasamento], definimos uma função _evenb_ que testa
    a paridade de um número, retornando [true] em caso positivo. Podemos
    utilizar esta função para definir a _proposição_ que algum número [n]
    é par: *)

Definition even (n:nat) : Prop := 
  evenb n = true.

(** Isso é, nós podemos definir "[n] é par" significando que "a função [evenb]
    retorna [true] quando aplicada sobre [n]."

    Note que aqui temos dado um nome para
    uma proposição utilizando uma [Definition], assim como temos dado
    nomes para expressões de outros tipos. Ela não é fundamentalmente um
    novo tipo de proposição;  ainda é somente uma igualdade. *)

(** Uma outra alternativa é definir o conceito de paridade diretamente. Em vez
    de ser via a função [evenb] ("um número é par se um determinado rendimento
    de computação é [verdadeiro]"), nós podemos dizer que o conceito de paridade
    significa dando duas maneiras diferentes de apresentar _evidência_ de que um
    número é par. *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).


(** A primeira linha declara que [ev] é uma proposição -- ou, mais formalmente,
    uma família de proposições "indexadas por" números naturais (ou seja, para
    cada número [n], a afirmação de que "[n] é par" é uma proposição.) Tal
    família de proposições é muitas vezes chamada de _propriedade_ de números.

    As duas últimas linhas declaram as duas formas de fornecer provas de que [m]
    é par. Em primeiro lugar, [0] é par e [ev_0] é evidência disso.  Segundo, se
    [m = S (S n)] para algum [n] e podemos prover a evidência [e] de que [n] é
    par então [m] também é par e [ev_SS n e] é a evidência.  *)


(** **** Exercício: nível 1 (double_even)  *)

Theorem double_even : forall n,
  ev (double n).
Proof.
  (* PREENCHER *) Admitted.
(** [] *)



(* ##################################################### *)

(** Para [ev], nós já tinhamos definido [even] como uma função (retornando um
   booleano), e então definimos uma relação indutiva que concordava com esta
   função. Porém, nós não necessariamente precisamos pensar primeiro sobre
   proposições como funções booleanas, ao invés disto, podemos começar já com
   a definição indutiva.
*)

(** Como um outro exemplo de uma proposição definida indutivamente, vamos
    definir uma simples propriedade de números naturais -- nós chamaremos
    ela de "[beautiful]" ("bonito"). *)

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

	

(** Cada uma das regras textuais acima é reformatado aqui como uma regra de
    inferência; a leitura pretendida é que, se as _premissas_ acima da linha
    forem verdadeiras, então a _conclusão_ abaixo da linha também é. Por
    exemplo, a regra [b_sum] informa que se [n] e [m] são ambos números bonitos
    ([beautiful]), então conclui-se que [n+m] também é [beautiful]. Se uma regra
    não possui premissas então significa que a conclusão é válida
    incondicionalmente.

    Estas regras _definem_ a propriedade [beautiful]. Isto é, se nós queremos
    convencer alguém do que algum determinado número é [beautiful], nossa
    argumentação deve estar baseada nestas regras. Para um exemplo simples,
    supõe que afirmamos que o número [5] é [beautiful]. Para sustentar esta
    afirmação, basta apontarmos que a regra [b_5] afirma exatamente isto. Se
    quisermos afirmar que [8] é [beautiful], podemos suportar esta afirmação
    observando primeiramente que [3] e [5] são [beautiful] (através das regras
    [b_3] e [b_5]) e então apontar que a soma deles, [8], é necessariamente
    [beautiful], pela regra [b_sum]. A _árvore de demonstração  seguinte é
    a expressão gráfica desta argumentação: *)

(**
         ----------- (b_3)   ----------- (b_5)
         beautiful 3         beautiful 5
         ------------------------------- (b_sum)
                   beautiful 8   
*)
(** *** *)
(** 
    Logicamente, há outras maneiras de usar essas regras para argumentar que
    [8] é [beautiful], por exemplo:
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
(** Nós também podemos provar teoremas que possuem hipóteses sobre
    [beautiful]. *)

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
(** * Uso de Evidência em Demonstrações *)

(** ** Indução sobre Evidência *)

(** Além de _construir  evidência de que números são [beautiful], nós podemos
    também _raciocinar sobre  tal evidência. *)

(** O fato de que nós introduzimos [beatiful] com uma declaração
    indutiva diz ao Coq não somente que os construtores [b_0], [b_3],
    [b_5] e [b_sum] são modos de construir evidência, mas também que 
    esses quatro construtores são os únicos meios de construir evidência 
    de que esses números são bonitos. *)

(** Em outras palavras, se alguém nos dá a evidência [E] para a asserção
    [beautiful n], então sabemos que [E] deve ter um desses quatro formatos:

      - [E] é [b_0] (e [n] é [O]),
      - [E] é [b_3] (e [n] é [3]), 
      - [E] é [b_5] (e [n] é [5]), ou
      - [E] é [b_sum n1 n2 E1 E2] (e [n] é [n1+n2], em que [E1] é
        evidência que [n1] é beautiful e [E2] é evidência que [n2]
        é beautiful). *)

(** *** *)    
(** Isto nós permite _analisar_ qualquer hipótese da forma [beautiful n] para
    ver como ele foi construído, usando a tática que nós já conhecemos. Em
    particular, nós podemos usar a tática [induction], que nós já utilizamos
    para raciocinar sobre _dados_ definidos indutivamente, a fim de racionar 
    também sobre _evidência_ definida indutivamente.

    Para ilustrar isso, vamos definir uma outra propriedade de números: *)

Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n).

(** **** Exercício: nível 1 (gorgeous_tree)  *)
(** Escreva a definição para números [gorgeous] usando a notação de regras 
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
(** Intuitivamente, parece óbvio que, embora [gorgeous] e [beautiful] 
    foram apresentados com regras ligeiramente diferentes, são na verdade
    a mesma propriedade, no sentido que caracterizam exatamente os mesmos
    números. De fato, nós podemos provar isto. *)

Theorem gorgeous__beautiful_FAILED : forall n, 
  gorgeous n -> beautiful n.
Proof.
   intros. induction n as [| n'].
   Case "n = 0". apply b_0.
   Case "n = S n'". (* Estamos travados! *)
Abort.

(** O problema aqui é que fazer indução em [n] não produz uma hipótese de
    indução útil. Sabendo como a propriedade que nós estamos interessados se
    comporta no predecessor de [n] não nos ajuda a provar que ela funciona em
    [n]. Ao invés disso, nós gostaríamos de poder ter hipóteses de indução que
    mencionem outros números, como [n - 3] and [n - 5]. Isso é dado precisamente
    pelo formato dos construtores para [gorgeous]. *)

(** *** *)

(** Vamos ver o que acontece se nós tentarmos provar isso por indução com a
    evidência [H] em vez de [n]. *)

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


(* Os exercícios seguintes também necessitam utilizar indução na evidência. *)

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
    implica a definição computacional. *)

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
(** Esta prova pode ser realizada por indução em [n] ao invés de [E]? 
    Caso não, por que? *)

(* PREENCHER *)
(** [] *)

(** Intuitivamente, o princípio da indução na evidência [ev n] é similar à
    indução em [n], mas restringe a nossa atenção a somente esses números para
    os quais a evidência [ev n] pode ser gerada. *)

(** **** Exercício: nível 1 (l_fails)  *)
(** A tentativa de prova a seguir não irá funcionar.
     Theorem l : forall n,
       ev n.
     Proof.
       intros n. induction n.
         Case "O". simpl. apply ev_0.
         Case "S".
           ...
   Intuitivamente, nós esperamos que a prova falhe porque nem todo número é 
   par. Contudo, o que exatamente causa a falha da prova?

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
    considere a prova de que se [n] é par], então [pred (pred n)] também o
    é. Neste caso, nós não precisamos efetuar uma prova indutiva. A tática
    [inversion] fornece todas as informações que precisamos.

*)

Theorem ev_minus2: forall n,  ev n -> ev (pred (pred n)). 
Proof.
  intros n E.
  inversion E as [| n' E'].
  Case "E = ev_0". simpl. apply ev_0. 
  Case "E = ev_SS n' E'". simpl. apply E'.  Qed.

(** **** Exercício: nível 1, opcional (ev_minus2_n)  *)
(** O que acontece se tentamos aplicar [destruct] a [n] ao invés de
   [inversion] on [E]? *)

(* PREENCHER *)
(** [] *)

(** *** *)
(** Aqui está outro exemplo, no qual [inversion] ajuda a limitar os
    casos relevantes. *)

Theorem SSev__even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. 
  inversion E as [| n' E']. 
  apply E'. Qed.

(** ** Revisitando a Tática [inversion] *)

(** O uso do [inversion] pode parecer um pouco misterioso no início.  Até agora,
    temos utilizado o [inversion] somente em proposições de igualdade, para
    utilizar injectividade de contrutores ou para discriminar entre diferentes
    contrutores.  Mas nós podemos ver que [inversion] também pode ser aplicada
    para análisar evidências de proposições definidas indutivamente.

    (Você também deve esperar que [destruct] seria uma tática mais adequada de
    usar aqui. De fato, é possível fazer o uso do [destruct], mas ele
    frequentemente descarta informações úteis, e o qualificador [eqn:] não ajuda
    muito nesse caso).

    Aqui está como [inversion] funciona em geral.  Suponha que o nome [I]
    refere-se a uma hipótese [P] no contexto atual, onde [P] foi definida por
    uma declaração [Inductive]. Então, para cada um dos construtores de [P],
    [inversion I] gera uma submeta em que [I] foi substituída pelas condições
    exatas e específicas nas quais esse construtor poderia ter sido usado para
    provar [P].  Algumas dessas submetas serão autocontraditórias; [inversion]
    as elimina. As que permanecem representam os casos que devem ser
    demonstrados para estabelecer a meta original.

    Neste caso em particular, o [inversion] analisou a construção [ev (S (S n))]
    e determinou que isso somente poderia ser construído usando [ev_SS], gerando
    uma nova submeta com os argumentos do construtor como novas hipóteses (a
    tática também produziu uma igualdade a mais que é inútil nesta prova).
    Começaremos a explorar nas próximas provas esse comportamento mais geral da
    inversão. *)

(** **** Exercício: nível 1 (inversion_practice)  *)
Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  (* PREENCHER *) Admitted.

(** A tática [inversion] pode também ser utilizada para demonstrar metas 
    evidenciando a absurdidade de uma hipótese. *)

Theorem even5_nonsense : 
  ev 5 -> 2 + 2 = 9.
Proof.
  (* PREENCHER *) Admitted.
(** [] *)

(** **** Exercício: nível 3, avançado (ev_ev__ev)  *)
(** Encontrar a coisa apropriada para fazer indução é um pouco
    complicado aqui: *)

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

(** Nós temos visto que a proposição "[n] é par" pode ser fraseada de duas
    maneiras diferentes -- indiretamente, via um teste da função booleana
    [evenb], ou diretamente, descrevendo indutivamente que constitui a evidência
    para paridade. Essas maneiras de definir paridade são igualmente fáceis de
    declarar e trabalhar com eles.  A escolha se dá basicamente em questão de
    gosto.

    No entanto, para muitas outras propriedades de interesse, a 
    definição indutiva direta é preferível, uma vez que escrever 
    uma função de teste pode ser difícil ou mesmo impossível.

    Uma dessas propriedades é [beautiful]. Esta é uma definição perfeitamente
    sensata de um conjunto de números, porém não podemos traduzir sua definição
    diretamente para um [Fixpoint] Coq (ou para uma função recursiva em qualquer
    outra linguagem de programação comum). Poderiamos talvez ser astutos o
    suficiente para achar uma maneira esperta testar esta propriedade usando um
    [Fixpoint] (de fato não é tão difícil encontrar uma forma nesse caso), mas
    em geral isso pode exigir muita reflexão. Aliás, se a propriedade na qual
    estamos interessados não for computável então não podemos defini-la como um
    [Fixpoint], não importa quantas tentativas realizemos, pois o Coq exige que
    todos os [Fixpoint] correspondam a computações que terminam.

    Em compensação, é imediato escrever uma definição indutiva do que significa
    dar evidência para a propriedade [beautiful]. *)


(* ####################################################### *)
(** ** Estruturas de Dados com Parâmetros *)

(** Até agora, nós temos somente olhado para proposições a respeito de números
    naturais. Porém, nós podemos definir predicados indutivos a respeito de
    qualquer tipo de dado. por exemplo, suponha que nós queremos caracterizar
    listas de tamanhos pares. Nós podemos fazer isso com a seguinte definição.
    *)

Inductive ev_list {X:Type} : list X -> Prop :=
  | el_nil : ev_list []
  | el_cc  : forall x y l, ev_list l -> ev_list (x :: y :: l).

(** Obviamente, essa proposição é equivalente a dizer que o tamanho da lista é
    par. *)

Lemma ev_list__ev_length: forall X (l : list X), ev_list l -> ev (length l).
Proof. 
    intros X l H. induction H.
    Case "el_nil". simpl. apply ev_0.
    Case "el_cc".  simpl.  apply ev_SS. apply IHev_list.
Qed.

(** Contudo, como a evidência [ev] contém menos informações que a evidência de
    [ev_list], deve-se tomar cuidados para enunciar a direção inversa. *)

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

(* Mais uma vez, o sentido inverso é muito mais difícil devido à carência de
   evidência. *)

(** **** Exercício: nível 5, opcional (palindrome_converse)  *)

(** Utilizando a sua definição de [pal] do exercício anterior, prove que
     forall l, l = rev l -> pal l.
*)

(* PREENCHER *)
(** [] *)



(* ####################################################### *)
(** ** Relações *)

(** A proposição parametrizada por um número (como [ev] ou [beautiful]) pode ser
    pensada como uma _propriedade_ -- isto é, ela define um subconjunto de
    [nat], precisamente composto por aqueles números para os quais a proposição
    pode ser provada. Do mesmo modo, uma proposição de dois argumentos pode ser
    pensada como uma _relação_ -- isto é, ela define um conjunto de pares para
    os quais a proposição é provada. *)

Module LeModule.  


(** Um exemplo útil é relação "menor que ou igual à" em números. *)

(** A definição seguinte deve ser razoavelmente intuitiva. Isto
    diz que existe duas maneiras de dar evidência que um número é menor ou 
    igual a outro: ou eles são o mesmo número, ou existe evidência
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
    apesar destes testes serem do mesmo tipo dos "testes unitários" criados para
    as funções de testes escritas nos primeiros capítulos, nós devemos construir
    suas provas explicitamente -- [simpl] e [reflexivity] não irão realizar suas
    funções aqui pois as provas não são apenas uma questão de cálculos de
    simplificação.  *)

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
(** A relação "estritamente menor que" [n < m] pode agora ser definida 
    com base [le]. *)

End LeModule.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** Seguem algumas outras relações simples sobre números: *)

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
    que nunca é satisfeita. *)

(* PREENCHER *)
(** [] *)

(** **** Exercício: nível 2, opcional (le_exercises)  *)
(** Segue uma série de fatos sobre as relações [<=] e [<], que serão necessários
    na sequência do curso. As provas são bons exercícios práticos. *)

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
(** Podemos definir relações ternárias, quaternárias, n-árias da mesma forma que
    relações binárias. Por exemplo, considere a seguinte relação ternária sobre
    números: *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0 
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

(** - Quais das seguintes proposições são demonstráveis?
      - [R 1 1 2]
      - [R 2 2 6]

    - Se nós desistirmos do construtor [c5] da definição de [R],
      O conjunto de proposições prováveis iria mudar? Explique sucintamente
      (uma sentença) a sua resposta.
  
    - Se nós utilizarmos o construtor [c4] a partir da definição de [R],
      poderá mudar o conjunto de proposições demonstráveis? Explique
      brevemente (uma sentença) sua resposta.

(* PREENCHER *)
[]
*)

(** **** Exercício: nível 3, opcional (R_fact)  *)  
(** Relação [R] codifica uma função familiar. Declare e
    prove dois teoremas que formalmente conecte a relação e a função.
    Isto é, se [R m n o] é verdadeiro, o que nós podemos dizer sobre [m],
    [n] e [o], e vice versa?
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

    - Define uma proposição indutiva [subseq] sobre [list nat] que
      identifica o significado de ser uma subsequência (dica: você
      precisará de três casos).

    - Prove que subsequência é reflexiva, isso é, qualquer lista é
      uma subsequência de si mesma.  

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
    afirmação sobre um fato como, por exemplo "dois mais dois é igual a quatro."
    No Coq, as proposições são escritas como expressões do tipo [Prop]. *)

Check (2 + 2 = 4).
(* ===> 2 + 2 = 4 : Prop *)

Check (ble_nat 3 2 = false).
(* ===> ble_nat 3 2 = false : Prop *)

Check (beautiful 8).
(* ===> beautiful 8 : Prop *)

(** *** *)
(** Tanto afirmações demonstráveis quanto as não demonstráveis são proposiçòes
    perfeitamente aceitáveis. Simplesmente _ser uma proposição é uma coisa, e
    ser _demonstrável  é outra! *)

Check (2 + 2 = 5).
(* ===> 2 + 2 = 5 : Prop *)

Check (beautiful 4).
(* ===> beautiful 4 : Prop *)

(** Ambas [2 + 2 = 4] e [2 + 2 = 5] São expressões legais do tipo [Prop]. *)

(** *** *)
(** Nós temos principalmente visto um lugar que proposições podem aparecer em
    Coq: em declarações de [Theorem] (e [Lemma] e [Example]). *)

Theorem plus_2_2_is_4 : 
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(** Mas eles podem ser usados em muitas outras maneiras. Por exemplo, nós também
    temos visto que nós podemos dar um nome para uma proposição usando um
    [Definition], assim como nós temos dado nomes para expressões de outros
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
(** Nós também investigamos as _proposições com parâmetros_, como [even] e
    [beautiful]. *)

Check (even 4).
(* ===> even 4 : Prop *)
Check (even 3).
(* ===> even 3 : Prop *)
Check even. 
(* ===> even : nat -> Prop *)

(** *** *)
(** O tipo de [even], isto é, [nat->prop], pode ser pronunciado de
    três modos equivalentes: (1) "[even] é uma _função_ de números 
    para proposições," (2) "[even] é uma _família_ de proposições, 
    indexada por um número [n]," ou (3) "[even] é uma _propriedade_
    dos números."  *)

(** Proposições -- incluindo proposições parametrizadas -- são
    cidadãos de primeira classe em Coq.  Por exemplo, nós podemos definir
    funções a partir de números para proposições... *)

Definition between (n m o: nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.

(** ... e então aplicá-las parcialmente: *)

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

(** A segunda função, [preservada_por_S], tem [P] como parâmetro, e constroi
    uma proposição tal que, quando [P] é verdade para algum número natural
    [n'], então também é verdade para o sucessor de [n'] -- ou seja, que [P]
    é _preservada pela relação sucessor :

Definition preserved_by_S (P:nat->Prop) : Prop :=
  forall n', P n' -> P (S n').

(** *** *)
(** Finalmente, nós podemos pôr esses ingredientes juntos para definir uma
    proposição declarando que indução é válida para números naturais: *)

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

(** Para testar a sua definição, veja se você pode provar os fatos a seguir: *)

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
    podemos também definí-las usando [Fixpoint]? Claro que sim!  No 
    entanto, este tipo de "parametrização recursiva" não corresponde 
    a nada muito familiar da matemática cotidiana. O exercício 
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




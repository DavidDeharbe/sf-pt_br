(** * Programação Funcional em Coq: Exercícios *)

(** ** Pontos cardeais *)

(** Definir um tipo para representar os quatro pontos cardeais: 
    Norte, Sul, Leste e Oeste.

    Definir uma função para calcular o oposto de um ponto cardeal (Norte e 
    Sul são opostos, Leste e Oeste são opostos).

    Aplicar esta função para avaliar o resultado da sua aplicação a cada um 
    dos pontos cardeais. (Use o comando [Eval compute in]).

    Escrever condições que expressam o resultado da aplicação desta função 
    a cada um dos pontos cardeais. Provar essas condições.  (Use o command [Theorem] seguido e [Proof]).

    Escrever um teorema que afirma que, para qualquer ponto cardeal, se 
    tomarmos duas vezes o ponto oposto, voltamos ao ponto original. 
    Provar este teorema. (Use o command [Theorem] seguido e [Proof]).
*)

(** ** Funções de uma variável *)

(** Funções matemáticas de uma variável são a báse do cálculo. Uma operação
    muito importante é a de derivação. Neste exercício, utilizaremos a 
    linguagem Coq para representar funções de uma variável e dar uma
    definição da derivação. *)

(** Para iniciar, o tipo [univariate] define algumas classes de funções de
    uma variável. [Var] representa a função identidade, que a uma valor
    X, associa o mesmo valor X. [Const k] representa as funções constantes:
    quaisquer que seja o valor da entrada, retornam sempre o mesmo valor. 
    Aqui nós limitamos a valores naturais. *)

Inductive univariate: Type :=
  | Var : univariate                         (* a função identidade *)
  | Const (k : nat) : univariate             (* as funções constantes *)
  | Sum (f1: univariate) (f2: univariate) : univariate (* a soma de duas funções *)
  | Product (f1 : univariate) (f2 : univariate) : univariate (* o produto de duas funções *)
  .

(** Definir, utilizando o comando [Define], algumas funções, como dobro, 
    quadrado, cubo. Utilize a sua imaginação... *)

(** Em seguida, definimos uma função [evaluate] para avaliar o valor de 
    uma função [fn] para uma determinada entrada [x].  *)

Fixpoint evaluate (fn : univariate) (x : nat) : nat :=
  match fn with
  | Var => x
  | Const k => k
  | Sum f1 f2 => (evaluate f1 x) + (evaluate f2 x)
  (* ==> completar *)
  .

(** Complete a definição para o caso do produto.

    Utilizar o comando [Eval compute in] para avaliar o valor das funções
    que você definiu anteriormente para 0, 1 e 4. *)

(** Completar a definição da função [derive] dada a seguir: *)

Fixpoint derive (fn : univariate) : univariate :=
  match fn with
  | Var => Const 1
  | Const _ => Const 0
  | Sum f1 f2 => Sum (derive f1) (derive f2)
  (* ==> completar *)
  .

(** Utilizar os comandos [Check], [Eval compute in], [Example] para
    testar as suas definições e ganhar confiança que estão corretas. *)

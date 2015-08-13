(** * Prefácio *)

(** * Boas vindas *)

(** Esse livro eletrônico é um curso em Fundações de Software, a base
    base matemática de softwares confiáveis. Esse tópico inclui
    conceitos básicos de lógica, prova de teoremas assistida por
    computador, o assistente de provas Coq, programação funcional,
    semântica operacional, lógica de Hoare e sistemas de tipagem
    estática. A leitura é direcionada a um grande conjunto de
    leitores, desde os graduandos avançados até estudantes de PhD e
    pesquisadores.  Não é requisitado nenhum conhecimento específico
    anterior em lógica ou linguagens de programação, porém uma certa
    maturidade em matemática será útil.

    A principal novidade no curso é que ele é cem por cento formalizado
    e verificado: o texto inteiro é literalmente um script para Coq. Ele
    é feito para ser lido juntamente com uma sessão interativa com Coq.
    Todos os detalhes do texto são totalmente formalizados em Coq, e os
    exercícios foram planejados para serem feitos usando o Coq.

    Os arquivos são organizados em uma sequência de capítulos centrais,
    cobrindo por volta de um semestre de material e organizado em uma 
    narrativa linear e coerente, seguida de diversos apêndices envolvendo
    tópicos adicionais. Todos os capítulos centrais são adequados para 
    ambos os níveis de alunos, graduandos e graduados.*)

(** * Visão Geral *)

(** Building reliable software is hard.  The scale and complexity of
    modern systems, the number of people involved in building them,
    and the range of demands placed on them make it extremely
    difficult even to build software that is more or less correct,
    much less to get it 100%% correct.  At the same time, the
    increasing degree to which information processing is woven into
    every aspect of society continually amplifies the cost of bugs and
    insecurities.

    Computer scientists and software engineers have responded to these
    challenges by developing a whole host of techniques for improving
    software reliability, ranging from recommendations about managing
    software projects and organizing programming teams (e.g., extreme
    programming) to design philosophies for libraries (e.g.,
    model-view-controller, publish-subscribe, etc.) and programming
    languages (e.g., object-oriented programming, aspect-oriented
    programming, functional programming, ...) and to mathematical
    techniques for specifying and reasoning about properties of
    software and tools for helping validate these properties.

    The present course is focused on this last set of techniques.  The
    text weaves together five conceptual threads:

    (1) basic tools from _logic_ for making and justifying precise
        claims about programs;

    (2) the use of _proof assistants_ to construct rigorous logical
        arguments;

    (3) the idea of _functional programming_, both as a method of
        programming and as a bridge between programming and logic;

    (4) formal techniques for _reasoning about the properties of
        specific programs_ (e.g., the fact that a loop terminates on
        all inputs, or that a sorting function or a compiler obeys a
        particular specification); and

    (5) the use of _type systems_ for establishing well-behavedness
        guarantees for _all_ programs in a given programming
        language (e.g., the fact that well-typed Java programs cannot
        be subverted at runtime).

    Each of these topics is easily rich enough to fill a whole course
    in its own right; taking all of them together naturally means that
    much will be left unsaid.  But we hope readers will find that the
    themes illuminate and amplify each other in useful ways, and that
    bringing them together creates a foundation from which it will be
    easy to dig into any of them more deeply.  Some suggestions for
    further reading can be found in the [Postscript] chapter. *)

(** ** Lógica *)

(** Lógica é o campo de estudo cujo o assunto é _provas_ -- argumentos
    incontestáveis para a verdade de proposições particulares.
    Volumes foram escritos sobre o papel fundamental da lógica em
    ciência da computação. Manna e Waldinger chamaram a lógica de "o
    cálculo da ciência da computação," enquanto o artigo _On the
    Unusual Effectiveness of Logic in Computer Science_ de Halpern et
    al. cataloga dezenas de maneiras em que lógica oferece ferramentas
    e idéias pivotais. De fato, eles observam que "na verdade, lógica
    tem se tornado significativamente mais efetivo em ciência da
    computação do que tem sido em matemática. Isso é notável,
    especialmente porque grande parte do impulso para o
    desenvolvimento da lógica durante os último cem anos veio da
    matemática".

    Em particular, a noção fundamental de provas indutivas está
    onipresente em toda a ciência da computação. Você certamente já
    viu antes, quer seja em matemática discreta ou em análise de
    algoritmos; mas neste curso você vai examiná-las muito mais
    profundamente do que você provavelmente tem feito até agora. *)

(** ** Assistentes de Prova *)

(** O fluxo de ideias entre a lógica e a Ciência da Computação não
    seguiu em uma única direção: a Ciência da Computação também
    realizou contribuições importantes para a lógica. Uma dessas foi o
    desenvolvimento de ferramentas de software para auxiliar na
    construção de provas de proposições lógicas. Essas ferramentas se
    dividem em duas grandes categorias:

    - _Provadores automáticos de teoremas_ trabalham em modo
    completamente automático: o usuário entrega uma proposição e
    recebe em retorno _true_ (verdadeiro), _false_ (falso), ou _ran
    out of time_ (estouro de tempo). Apesar de suas capacidades serem
    limitadas a tipos bastante específicos de raciocínio, os
    provadores têm amadurecido tremendamente nos últimos anos e agora
    são utilizados em uma enorme variadade de configurações. Exemplos
    dessas ferramentas incluem solucionadores SAT, solucionadores SMT,
    e verificadores de modelo.

    - _Assistentes de Prova_ são ferramentas híbridas que automatizam os mais
    rotineiros aspectos dos construtores de prova enquanto dependem da
    orientação humana para aspectos mais difíceis. Assistentes de prova
    amplamente utilizados incluem Isabelle, Agda, Twelf, ACL2, PVS, e Coq, entre
    muitos outros.

    Esse curso é baseado em torno de Coq, um assistente de prova que tem
    estado em desenvolvimento desde 1983 por laboratórios franceses de
    pesquisas e universidades. Coq fornece um rico ambiente para
    desenvolvimento interativo de raciocínio formal com verificação de
    máquina. O núcleo do sistema Coq é um simples verificador de prova que
    garante que somente passos corretos de dedução sejam realizados. Além
    desse núcleo, o ambiente Coq prove facilidades de alto nível para
    desenvolvimento de prova, incluindo táticas poderosas para construção de
    provas complexas semi-automaticamente, além de uma grande biblioteca de
    definições comuns e lemas.

    Coq tornou possível uma grande variedade de contribuições tanto
    para a Ciência da Computação como para a Matemática:

    - Como uma _plataforma para modelagem de linguagem de programação_,
    o Coq se tornou uma ferramenta padrão para pesquisadores que
    precisam descrever e raciocinar sobre definições de linguagens
    complexas. Foi utilizado, por exemplo, para verificar a segurança da
    plataforma JavaCard, obtendo o mais alto nível da certificação
    _common criteria_, e para especificações formais do x86 e dos
    conjuntos de instruções da LLVM.

    - Como um _ambiente para desenvolver software certificado
    formalmente_, Coq foi utilizado para construir o CompCert, um
    compilador com otimizações para C inteiramente verificado, para
    provar a exatidão de algoritmos sutis envolvendo números de ponto
    flutuante, e como a base para o Certicrypt, um ambiente para
    raciocínio sobre a segurança de algoritmos criptografados.

    - Como um _ambiente realista para programação com tipos dependentes_,
    inspirando numerosas inovações. Por exemplo, o projeto Ynot em Harvard
    "raciocínio de Hoare relacional" (uma extensão da _lógica de Hoare_ que
    veremos mais tarde nesse curso) em Coq.

    - Como um _assistente de prova para lógica de ordem superior_, foi
    utilizado para validar uma série de resultados importantes na
    matemática. Por exemplo, sua capacidade de incluir computações
    complexas dentro de provas tornou possível desenvolver a primeira
    prova de teorema formalmente verificada do teorema das 4
    cores. Essa prova havia sido controversa entre matemáticos porque
    parte dela inclui a verificação de um grande número de
    configurações usando um programa. Na formalização do Coq, tudo é
    verificado, incluindo a precisão da parte computacional. Mais
    recentemente, um esforço ainda maior levou à formalização através
    de Coq do teorema de Feit-Thompson -- o primeiro avanço
    significativo para classificar de grupos finitos simples.

    A propósito, caso você esteja se perguntando sobre o nome Coq,
    aqui está o que o website oficial diz: "Alguns cientistas
    franceses da computação têm a tradição de nomear seus softwares
    como espécies de animais: Caml, Elan, Foc ou Phox são exemplos
    dessa convenção. Em francês, 'coq' significa galo, e, além disso
    soa como as iniciais de _Calculus of Constructions_ (CoC), no qual
    é baseado." O galo é um simbolo nacional da França, e "Coq" são as
    três primeiras letras do nome de Thierry Coquand, um dos primeiros
    desenvolvedores do Coq. *)

(** ** Programação funcional *)

(** O termo _programação funcional_ refere-se tanto a uma coleção de
    idiomatismos de programação que podem ser usados em praticamente
    qualquer linguagem de programação quanto a uma família de
    linguagens de programação projetadas para enfatizar esses
    idiomatismos, incluindo Haskell, OCaml, Standard ML, F##, Scala,
    Scheme, Racket, Common Lisp, Clojure, Erlang, e Coq.
	
    A programação funcional tem sido desenvolvida ao longo de muitas
    décadas - de fato, as suas raízes remontam ao cálculo lambda da
    Igreja, que foi inventado na década de 1930, antes da era dos
    computadores começar! Porém, desde o início dos anos 90, ela se
    tornou uma onda de interesse crescente entre os engenheiros
    industriais e projetistas de linguagens, desempenhando um papel
    fundamental nos sistemas de alto valor em empresas como Jane
    St. Capital, Microsoft, Facebook, e Ericsson.
	
    O princípio mais básico da programação funcional é que, tanto
    quanto possível, a computação deve ser _pura_, no sentido de que o
    único efeito da execução deve ser o de produzir um resultado: a
    computação deve ser livre de _efeitos colaterais_, tais como
    entradas e saídas, atribuições a variáveis mutáveis,
    redirecionamento de ponteiros, etc. Por exemplo, enquanto uma
    função _imperativa_ de ordenação pode receber uma lista de números
    e reorganizar seus ponteiros para colocar a lista em ordem, uma
    função de ordenação pura receberia a lista original e retornaria
    uma _nova_ lista contendo os mesmos números na ordem de
    classificação.
	
    Um benefício significativo deste estilo de programação é que ele
    torna os programas mais fáceis de entender e de se analizar. Se
    cada operação em uma estrutura de dados produz uma nova estrutura
    de dados, deixando a antiga intacta, então não há necessidade de
    se preocupar sobre como essa estrutura está sendo compartilhada e
    se uma mudança por uma parte do programa pode quebrar um
    invariante em que outra parte do programa se baseia. Essas
    considerações são particularmente críticas em programas
    concorrentes, onde cada pedaço de estado mutável que é
    compartilhado entre _threads_ é uma fonte em potencial de erros
    perniciosos. Na verdade, uma grande parte do recente interesse em
    programação funcional por parte da indústria é devido ao seu
    comportamento simples na presença de concorrência.
	
    Outro motivo para o entusiasmo atual sobre a programação funcional
    está relacionado com o primeiro: programas funcionais são
    frequentemente muito mais fáceis de paralelizar do que suas
    contrapartes imperativas.  Se a execução de um algoritmo não
    possui qualquer outro efeito além de produzir um resultado, então
    não importa _onde_ ele é executado.  Da mesma forma, se uma
    estrutura de dados nunca é modificada destrutivamente, então ela
    pode ser copiada livremente, entre núcleos ou em toda a rede. De
    fato, o idiomatismo MapReduce, que está no cerne de processadores
    de consulta maciçamente distribuídos como o Hadoop e é usado pelo
    Google para indexar toda a web, é um exemplo clássico de
    programação funcional.
	
    Para os fins deste curso, a programação funcional tem ainda uma
    outra atração significativa: ela serve como uma ponte entre a
    lógica e a ciência da computação. De fato, o próprio Coq pode ser
    vista como uma combinação de uma pequena porém extremamente
    expressiva linguagem de programação funcional com um conjunto de
    ferramentas para indicar e provar afirmações lógicas. Além disso,
    quando chegamos a olhar mais de perto, descobrimos que esses dois
    lados do Coq são na verdade aspectos da mesma maquinaria
    subjacente - ou seja, _provas são programas_. *)

(** ** Program Verification *)

(** The first third of the book is devoted to developing the
    conceptual framework of logic and functional programming and
    gaining enough fluency with Coq to use it for modeling and
    reasoning about nontrivial artifacts.  From this point on, we
    increasingly turn our attention to two broad topics of critical
    importance to the enterprise of building reliable software (and
    hardware): techniques for proving specific properties of
    particular _programs_ and for proving general properties of whole
    programming _languages_.

    For both of these, the first thing we need is a way of
    representing programs as mathematical objects, so we can talk
    about them precisely, and ways of describing their behavior in
    terms of mathematical functions or relations.  Our tools for these
    tasks are _abstract syntax_ and _operational semantics_, a method
    of specifying the behavior of programs by writing abstract
    interpreters.  At the beginning, we work with operational
    semantics in the so-called "big-step" style, which leads to
    somewhat simpler and more readable definitions, in those cases
    where it is applicable.  Later on, we switch to a more detailed
    "small-step" style, which helps make some useful distinctions
    between different sorts of "nonterminating" program behaviors and
    which is applicable to a broader range of language features,
    including concurrency.

    The first programming language we consider in detail is _Imp_, a
    tiny toy language capturing the core features of conventional
    imperative programming: variables, assignment, conditionals, and
    loops. We study two different ways of reasoning about the
    properties of Imp programs.

    First, we consider what it means to say that two Imp programs are
    _equivalent_ in the sense that they give the same behaviors for
    all initial memories.  This notion of equivalence then becomes a
    criterion for judging the correctness of _metaprograms_ --
    programs that manipulate other programs, such as compilers and
    optimizers.  We build a simple optimizer for Imp and prove that it
    is correct.

    Second, we develop a methodology for proving that Imp programs
    satisfy formal specifications of their behavior.  We introduce the
    notion of _Hoare triples_ -- Imp programs annotated with pre- and
    post-conditions describing what should be true about the memory in
    which they are started and what they promise to make true about
    the memory in which they terminate -- and the reasoning principles
    of _Hoare Logic_, a "domain-specific logic" specialized for
    convenient compositional reasoning about imperative programs, with
    concepts like "loop invariant" built in.

    This part of the course is intended to give readers a taste of the
    key ideas and mathematical tools used for a wide variety of
    real-world software and hardware verification tasks.
*)

(** ** Sistemas de Tipo *)

(** O nosso tópico final principal, cobrindo o último terço do curso, 
    é Sistemas de Tipo, um conjunto poderoso de ferramentas para
    estabelecer propriedade de todos os programas em uma dada 
    linguagem.

    Sistemas de tipos são os mais bem estabelecidos e populares 
    exemplos de uma classe bem sucedida de técnicas de verificação 
    formal, conhecida como métodos formais leves. Essas são técnicas
    de raciocínio de poder modesto -- modesto o suficiente a ponto de
    verificadores automáticos poderem ser construídos em compiladores, 
    linkeditores, ou analisadores de programas e assim serem aplicadas até
    por programadores não familiarizados com as teorias básicas. (Outros
    exemplos de métodos formais leves incluem verificadores de modelos de 
    software e hardware, verificadores de contratos, e técnicas de 
    monitoramento em tempo de execução para detectar quando algum 
    componente de um sistema não está se comportando de acordo com a 
    especificação).

    Esse tópico fecha o círculo: a linguagem cujas propriedades nós 
    estudamos nessa parte, chamada de _cálculo-lambda simplesmente 
    tipado_, é essencialmente um modelo simplificado do Coq!

*)

(** * Practicalities *)

(** ** Dependências entre capítulos *)

(** Um diagrama da dependência entre os capítulos e alguns caminhos
    sugeridos através do material pode ser encontrados no arquivo <deps.html>. *)

(** ** Requisitos de Sistema *)

(** Coq executa em Windows, Linux e OS X. Você precisará de:

       - A instalação atual do Coq, disponível a partir da home page do Coq. 
         Tudo deve funcionar corretamente com a versão 8.4.

       - Uma IDE para interagir com o Coq. Atualmente, existem duas escolhas:

           - Proof General é uma IDE baseada no Emacs. Ela tende 
             a ser preferida por usuários que já estão confortáveis 
             com o Emacs. Ela requer uma instalação separada (Google 
             "Proof General").

           - CoqIDE é uma IDE stand-alone simples. Ela é distribuída 
             com o Coq, mas, em algumas plataformas, para compilá-lo
             é necessária a instalação de pacotes adicionais para as 
             bibliotecas GUI e etc. *)

(** ** Exercícios *)

(** Cada capítulo inclui numerosos exercícios. Cada exercício é marcado
    com uma "classificação de estrelas," a qual pode ser interpretada
    da seguinte maneira:

       - Uma estrela: exercícios fáceis que ressaltam pontos no texto e
         que, para muitos leitores, deve tomar somente um ou dois 
         minutos. Crie o hábito de fazer esses exercícios no momento
         em que chegar neles.

       - Duas estrelas: exercícios simples (cinco ou dez minutos).

       - Três estrelas: exercícios que requerem um pouco mais de 
         raciocínio (de dez minutos a meia-hora).

       - Quatro e cinco estrelas: exercícios mais difíceis (a partir de 
         meia-hora).

    Além disso, alguns exercícios são marcados como "avançado", e alguns
    outros são marcados como "opcional." Fazer somente os exercícios
    não-opcionais e não-avançados deve proporcionar uma boa cobertura 
    do assunto central. Exercícios opcionais proporcionam um pouco mais 
    de prática com conceitos chaves e introduzem temas secundários que 
    podem ser do interesse de alguns leitores. Exercícios avançados são 
    para leitores que querem um desafio extra (e, como retribuição, um
    contato mais profundo com o material).

    _Por favor, não publique soluções para os exercícios em locais
    públicos_: _Fundações de Software_ é largamente utilizado tanto
    para estudos pessoais quanto para cursos universitários. Ter as
    soluções facilmente disponíveis torna o livro muito menos útil
    para cursos, os quais tem as atividades normalmente graduadas. Os
    autores especialmente solicitam que os leitores não publiquem as
    soluções para os exercícios em qualquer lugar que possa ser
    encontrado por mecanismos de busca.  *)

(** ** Baixando os arquivos Coq *)

(** Um arquivo tar contendo os fontes completos para a "versão de lançamento"
    destas notas (como uma coleção de scripts de Coq e arquivos HTML) está
    disponível aqui:
<<
        http://www.cis.upenn.edu/~bcpierce/sf   
>>
    Se você estiver usando as notas como parte de uma aula, você pode ter
    acesso a uma versão local estendida dos arquivos, que você deve usar
    em vez da versão de lançamento.
*)

(** * Nota para instrutores *)

(** Se você pretende utilizar esse material em seu próprio curso, com certeza
    encontrará coisas que gostará de modificar, aprimorar ou adicionar.
    Suas contribuições são bem-vindas!

    Por favor, envie um e-mail para Benjamin Pierce, descrevendo-se e
    informando como gostaria de fazer uso do material, incluindo o resultado
    de fazer "htpasswd -s -n NAME", onde NAME é seu nome de
    usuário.  Nós vamos configurar seus direitos de acesso em leitura/escrita 
    ao nosso repositório _subversion  e adicioná-lo na lista de contato de desenvolvedores; no repositório você encontrará
    um [README] com futuras instruções. *)

(** * Traduções *)

(** Graças aos esforços de uma equipe de tradutores voluntários,
    _Fundações de Software_ pode agora ser apreciado em Japonês em
    [http://proofcafe.org/sf] *)


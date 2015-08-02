(** * Preface *)

(* ###################################################################### *)
(** * Welcome *)

(** This electronic book is a course on _Software Foundations_, the
    mathematical underpinnings of reliable software.  Topics include
    basic concepts of logic, computer-assisted theorem proving, the
    Coq proof assistant, functional programming, operational
    semantics, Hoare logic, and static type systems.  The exposition
    is intended for a broad range of readers, from advanced
    undergraduates to PhD students and researchers.  No specific
    background in logic or programming languages is assumed, though a
    degree of mathematical maturity will be helpful.

    The principal novelty of the course is that it is one hundred per
    cent formalized and machine-checked: the entire text is literally
    a script for Coq.  It is intended to be read alongside an
    interactive session with Coq.  All the details in the text are
    fully formalized in Coq, and the exercises are designed to be
    worked using Coq.

    The files are organized into a sequence of core chapters, covering
    about one semester's worth of material and organized into a
    coherent linear narrative, plus a number of "appendices" covering
    additional topics.  All the core chapters are suitable for both
    upper-level undergraduate and graduate students. *)


(* ###################################################################### *)
(** * Overview *)

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

(** ** Logic *)

(** Logic is the field of study whose subject matter is _proofs_ --
    unassailable arguments for the truth of particular propositions.
    Volumes have been written about the central role of logic in
    computer science.  Manna and Waldinger called it "the calculus of
    computer science," while Halpern et al.'s paper _On the Unusual
    Effectiveness of Logic in Computer Science_ catalogs scores of
    ways in which logic offers critical tools and insights.  Indeed,
    they observe that "As a matter of fact, logic has turned out to be
    significiantly more effective in computer science than it has been
    in mathematics.  This is quite remarkable, especially since much
    of the impetus for the development of logic during the past one
    hundred years came from mathematics."

    In particular, the fundamental notion of inductive proofs is
    ubiquitous in all of computer science.  You have surely seen them
    before, in contexts from discrete math to analysis of algorithms,
    but in this course we will examine them much more deeply than you
    have probably done so far. *)

(** ** Assistentes de Prova *)

(** O fluxo de idéias entre a lógica e a Ciência da Computação não
    seguiu em uma única direção: A CC também realizou contribuições importantes para
    a lógica.  Uma destas foi o desenvolvimento de ferramentas de software
    para auxiliar na construção de provas de preposições lógicas.  Estas ferramentas
    se dividem em duas grandes categorias:

       - _Automated theorem provers_ fornecem a operação "push-button":
         o operador entrega uma preposição e recebe em retorno _true_,
         _false_, ou _ran out of time_.  Apesar de suas as capacidades
         serem limitadas para tipos bastante específicos de raciocínio, eles têm
         amadurecido tremendamente nos últimos anos e agora são utilizadas em
         uma enorme variadade de configurações. Exemplos destas ferramentas incluem solucionadores
         SAT, solucionadores SMT, e verificadores de modelo.

       - _Proof assistants_ são ferramentas híbridas que automatizam os mais 
         rotineiros aspectos dos construtores de prova enquanto dependem de orientação
         humana para aspectos mais difíceis.  Assistentes de prova
         largamente utilizados incluem Isabelle, Agda, Twelf, ACL2, PVS, e Coq,
         entre muitos outros.

    Esse curso é baseado em torno do Coq, um assistente de prova que tem estado
    em desenvolvimento desde 1983 por laboratório franceses de pesquisas
    e universidades.  Coq concede um rico ambiente para desenvolvimento 
    interativo de maquina-raciocínio formal verificado.  O núcleo do
    sistema Coq é um simples verificador de prova que garante somente
    passos corretos de dedução são realizados.  Além desse núcleo,
    o ambiente Coq provêm meio de alto nível para
    desenvolvimento de prova, incluindo táticas poderosas para construção
    de complexos de prova semiautomáticos, além de uma grande biblioteca de definições
    comuns e normas.

    Coq tem sido um fator crítico para uma grande variedade de trabalhos em
    da Ciência da Computação e da matemática:

    - Como uma _plataforma para modelagem de liguagem de programação_, o Coq se tornou
      uma ferramenta padrão para pesquisadores que precisam descrever e raciocinar
      sobre definições de liguagens complexas.  Têm sido utilizado, por
      exemplo, para checar a segurança da plataforma JavaCard,
      obtendo o mais alto nível de certificação common criteria, //common criteria certification,
      e para especificações formais do x86 e do conjuntos de intruções
      do LLVM.

    - Como um _ambiente para desenvolver software certificado formalmente_,
      Coq foi utilizado para construir o CompCert, um otimizador de compilação
      totalmente verificado para C, para provar a exatidão de algoritmos sutis
      envolvendo números de ponto flutuante, e como a base para o
      Certicrypt, um ambiente para raciocínio sobre a segurança de
      algoritmos criptografados.

    - Como um _ambiente realista para programação com tipos
      dependentes_, inspirando numerosas inovações.  Por exemplo, o
      projeto Ynot em Harvard "relational Hoare reasoning" (uma
      extensão da _lógica de Hoare_ que veremos mais tarde nesse curso)
      em Coq.

    - Como um _assistente de prova para lógica de ordem superior_, foi utilizado
      para validar uma série de resultados importantes na matemática.  Por
      exemplo, sua capacidade de incluir computações complexas dentro
      de provas tornou possível desenvolver a primiera prova do teorema
      formalmente verificada do teorema das 4 cores.  Essa prova havia sido
      controversa entre matemáticos porque parte dela inclue
      checar grande número de configurações usando um programa.  Na
      formalização do Coq, tudo é checado, incluindo a
      precisão da parte computacional.  Mais recentemente, um esforço
      ainda maior levou a formalização através do Coq do
      Teorema de Feit-Thompson -- o primeiro maior passo na
      classificação de grupos finitos simples.

   A propósito, no caso de você está se perguntando sobre nome Coq, aqui está
   o que o web site oficial diz: "Alguns cientistas franceses da computação
   tem a tradição de nomear seus softwares como espécies de animais: Caml,
   Elan , Foc ou Phox são exemplos dessa convenção. Em francês,
   'coq' significa galo, e além disse soa como as iniciais de
   Calculus of Constructions (CoC), no qual é baseado."  O galo
   é um simbolo nacional da França, e "Coq" são as três primeiras
   letras do nome de Thierry Coquand, um dos primeiros
   desenvolvedores do Coq. *)

(** ** Functional Programming *)

(** The term _functional programming_ refers both to a collection of
    programming idioms that can be used in almost any programming
    language and to a family of programming languages designed to
    emphasize these idioms, including Haskell, OCaml, Standard ML,
    F##, Scala, Scheme, Racket, Common Lisp, Clojure, Erlang, and Coq.

    Functional programming has been developed over many decades --
    indeed, its roots go back to Church's lambda-calculus, which was
    invented in the 1930s before the era of the computer began!  But
    since the early '90s it has enjoyed a surge of interest among
    industrial engineers and language designers, playing a key role in
    high-value systems at companies like Jane St. Capital, Microsoft,
    Facebook, and Ericsson.

    The most basic tenet of functional programming is that, as much as
    possible, computation should be _pure_, in the sense that the only
    effect of execution should be to produce a result: the computation
    should be free from _side effects_ such as I/O, assignments to
    mutable variables, redirecting pointers, etc.  For example,
    whereas an _imperative_ sorting function might take a list of
    numbers and rearrange its pointers to put the list in order, a
    pure sorting function would take the original list and return a
    _new_ list containing the same numbers in sorted order.

    One significant benefit of this style of programming is that it
    makes programs easier to understand and reason about.  If every
    operation on a data structure yields a new data structure, leaving
    the old one intact, then there is no need to worry about how that
    structure is being shared and whether a change by one part of the
    program might break an invariant that another part of the program
    relies on.  These considerations are particularly critical in
    concurrent programs, where every piece of mutable state that is
    shared between threads is a potential source of pernicious bugs.
    Indeed, a large part of the recent interest in functional
    programming in industry is due to its simple behavior in the
    presence of concurrency.

    Another reason for the current excitement about functional
    programming is related to the first: functional programs are often
    much easier to parallelize than their imperative counterparts.  If
    running a computation has no effect other than producing a result,
    then it does not matter _where_ it is run.  Similarly, if a data
    structure is never modified destructively, then it can be copied
    freely, across cores or across the network.  Indeed, the MapReduce
    idiom that lies at the heart of massively distributed query
    processors like Hadoop and is used by Google to index the entire
    web is a classic example of functional programming.

    For purposes of this course, functional programming has yet
    another significant attraction: it serves as a bridge between
    logic and computer science.  Indeed, Coq itself can be viewed as a
    combination of a small but extremely expressive functional
    programming language plus with a set of tools for stating and
    proving logical assertions.  Moreover, when we come to look more
    closely, we find that these two sides of Coq are actually aspects
    of the very same underlying machinery -- i.e., _proofs are
    programs_.  *)

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

(** ** Type Systems *)

(** Our final major topic, covering the last third of the course, is
    _type systems_, a powerful set of tools for establishing
    properties of _all_ programs in a given language.

    Type systems are the best established and most popular example of
    a highly successful class of formal verification techniques known
    as _lightweight formal methods_.  These are reasoning techniques
    of modest power -- modest enough that automatic checkers can be
    built into compilers, linkers, or program analyzers and thus be
    applied even by programmers unfamiliar with the underlying
    theories.  (Other examples of lightweight formal methods include
    hardware and software model checkers, contract checkers, and
    run-time property monitoring techniques for detecting when some
    component of a system is not behaving according to specification).

    This topic brings us full circle: the language whose properties we
    study in this part, called the _simply typed lambda-calculus_, is
    essentially a simplified model of the core of Coq itself!

*)

(* ###################################################################### *)
(** * Practicalities *)

(* ###################################################################### *)
(** ** Dependências entre capítulos *)

(** Um diagrama da dependência entre os capítulos e alguns caminhos
    sugeridos através do material pode ser encontrados no arquivo <deps.html>. *)

(* ###################################################################### *)
(** ** System Requirements *)

(** Coq runs on Windows, Linux, and OS X.  You will need:

       - A current installation of Coq, available from the Coq home
         page.  Everything should work with version 8.4.

       - An IDE for interacting with Coq.  Currently, there are two
         choices:

           - Proof General is an Emacs-based IDE.  It tends to be
             preferred by users who are already comfortable with
             Emacs.  It requires a separate installation (google
             "Proof General").

           - CoqIDE is a simpler stand-alone IDE.  It is distributed
             with Coq, but on some platforms compiling it involves
             installing additional packages for GUI libraries and
             such. *)

(* ###################################################################### *)
(** ** Exercises *)

(** Each chapter includes numerous exercises.  Each is marked with a
    "star rating," which can be interpreted as follows:

       - One star: easy exercises that underscore points in the text
         and that, for most readers, should take only a minute or two.
         Get in the habit of working these as you reach them.

       - Two stars: straightforward exercises (five or ten minutes).

       - Three stars: exercises requiring a bit of thought (ten
         minutes to half an hour).

       - Four and five stars: more difficult exercises (half an hour
         and up).

    Also, some exercises are marked "advanced", and some are marked
    "optional."  Doing just the non-optional, non-advanced exercises
    should provide good coverage of the core material.  Optional
    exercises provide a bit of extra practice with key concepts and
    introduce secondary themes that may be of interest to some
    readers.  Advanced exercises are for readers who want an extra
    challenge (and, in return, a deeper contact with the material).

    _Please do not post solutions to the exercises in public places_:
    Software Foundations is widely used both for self-study and for
    university courses.  Having solutions easily available makes it
    much less useful for courses, which typically have graded homework
    assignments.  The authors especially request that readers not post
    solutions to the exercises anyplace where they can be found by
    search engines.
*)

(* ###################################################################### *)
(** ** Downloading the Coq Files *)

(** A tar file containing the full sources for the "release version"
    of these notes (as a collection of Coq scripts and HTML files) is
    available here:
<<
        http://www.cis.upenn.edu/~bcpierce/sf   
>>
    If you are using the notes as part of a class, you may be given
    access to a locally extended version of the files, which you
    should use instead of the release version.
*)

(* ###################################################################### *)
(** * Nota para instrutores *)

(** Se você pretende utilizar esse material em seu próprio curso, com certeza
    encontrará coisas que gostará de modificar, aprimorar ou adicionar.
    Suas contribuições são bem-vindas!

    Por favor, enviei um e-mail para Benjamin Pierce, descrevendo-se e
    informando como gostaria de fazer uso do material, incluindo o resultado
    de fazer "htpasswd -s -n NAME", onde NAME é seu nome de
    usuário.  Nós vamos configurar sua leitura/acesso com a nossa subversão do
    repositório e adiciona-lo na lista de contato de desenvolvedores; no repositório você encontrará
    um [README] com futuras instruções. *)

(* ###################################################################### *)
(** * Translations *)

(** Thanks to the efforts of a team of volunteer translators, _Software 
    Foundations_ can now be enjoyed in Japanese at [http://proofcafe.org/sf]
*)

(** $Date: 2014-12-31 15:31:47 -0500 (Wed, 31 Dec 2014) $ *)


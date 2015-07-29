# sf-pt_br
Fundações do Software (livro eletrônico)

(Informations in English at the bottom)

## Introdução

Este projeto tem como objetivo a elaboração de uma tradução do livro 
eletrônico "Software Foundations" para o Português do Brasil. Os autores da
versão original, em inglês, são Benjamin C. Pierce, Chris Casinghino, Marco 
Gaboardi, Michael Greenberg, Cătălin Hriţcu, Vilhelm Sjöberg, Brent Yorgey.
Este livro é disponível no seguinte local: <http://www.cis.upenn.edu/~bcpierce/sf/current/index.html>.

Os autores da tradução são os discentes e docente da disciplina "Semântica de 
Linguagens de Programação", código DIM0889, oferecida no período 2015.2 pelo 
Programa de Pós-graduação em Sistemas e Computação da Universidade Federal do
Rio Grande do Norte.

A versão inicial deste projeto é composta pelos arquivos da versão original,
em inglês.

## Estado da tradução

Segue o conteúdo do livro. As partes em inglês ainda não foram traduzidas. 
As partes em português já foram traduzidas. As partes com ambos idiomas estão
em processo de tradução.


- Preface

    - Welcome [Dalay] Boas-Vindas
    - Overview
        - Logic [ Francisco ]
        - Proof Assistants [ Diego ]
        - Functional Programming [ Renan ]
        - Program Verification [ Dalay ]
        - Type Systems [ Francisco ]
    - Practicalities
        - Chapter Dependencies [ Diego ]
        - System Requirements [ Renan ]
        - Exercises [ Dalay ]
        - Downloading the Coq Files [ Francisco ]
    - Note for Instructors [ Diego ]
    - Translations [ Renan ]

- Basics: Functional Programming in Coq

    - Introduction
    - Enumerated Types
        - Days of the Week
        - Booleans
        - Function Types
        - Numbers
    - Proof by Simplification
    - Proof by Rewriting
    - Proof by Case Analysis
    - More Exercises
    - More on Notation (Advanced)
    - Fixpoint and Structural Recursion (Advanced)

- Induction: Proof by Induction

    - Naming Cases
    - Proof by Induction
    - Proofs Within Proofs
    - More Exercises
    - Formal vs. Informal Proof (Advanced)


- Lists: Working with Structured Data

    - Pairs of Numbers
    - Lists of Numbers
        - Bags via Lists
    - Reasoning About Lists
        - Micro-Sermon
        - Induction on Lists
        - SearchAbout
        - List Exercises, Part 1
        - List Exercises, Part 2
    - Options
    - Dictionaries


- Poly: Polymorphism and Higher-Order Functions

    - Polymorphism
        - Polymorphic Lists
        - Polymorphic Pairs
        - Polymorphic Options
    - Functions as Data
        - Higher-Order Functions
        - Partial Application
        - Digression: Currying
        - Filter
        - Anonymous Functions
        - Map
        - Map for options
        - Fold
        - Functions For Constructing Functions
    - The unfold Tactic
    - Additional Exercises


- MoreCoq: More About Coq's Tactics

    - The apply Tactic
    - The apply ... with ... Tactic
    - The inversion tactic
    - Using Tactics on Hypotheses
    - Varying the Induction Hypothesis
    - Using destruct on Compound Expressions
    - Review
    - Additional Exercises


- Logic: Logic in Coq

    - Propositions
    - Proofs and Evidence
Implications are functions
Defining propositions
    - Conjunction (Logical "and")
"Introducing" conjunctions
"Eliminating" conjunctions
    - Iff
    - Disjunction (Logical "or")
Implementing disjunction
Relating ∧ and ∨ with andb and orb
    - Falsehood
Truth
    - Negation
Inequality


- Prop: Propositions and Evidence

    - Inductively Defined Propositions
        - Constructing Evidence
    - Using Evidence in Proofs
        - Induction over Evidence
        - Inversion on Evidence
        - The Inversion Tactic Revisited
    - Discussion and Variations
        - Computational vs. Inductive Definitions
        - Parameterized Data Structures
        - Relations
    - Programming with Propositions


- MoreLogic: More on Logic in Coq

    - Existential Quantification
    - Evidence-Carrying Booleans
    - Additional Exercises

- ProofObjects: Working with Explicit Evidence in Coq

    - Proof Scripts and Proof Objects
    - Quantification, Implications and Functions
    - Giving Explicit Arguments to Lemmas and Hypotheses
    - Programming with Tactics (Advanced)


- MoreInd: More on Induction

    - Induction Principles
        - Induction Hypotheses
        - More on the induction Tactic
        - Generalizing Inductions.
    - Informal Proofs (Advanced)
        - Informal Proofs by Induction
    - Induction Principles in Prop (Advanced)
    - Additional Exercises
        - Induction Principles for other Logical Propositions
        - Explicit Proof Objects for Induction
        - The Coq Trusted Computing Base


- SfLib: Software Foundations Library

    - From the Coq Standard Library
    - From Basics.v
    - From Props.v
    - From Logic.v
    - From Later Files
    - Some useful tactics


- Rel: Properties of Relations

    - Basic Properties of Relations
    - Reflexive, Transitive Closure


- Imp: Simple Imperative Programs

    - Arithmetic and Boolean Expressions
        - Syntax
        - Evaluation
        - Optimization
    - Coq Automation
        - Tacticals
        - Defining New Tactic Notations
        - The omega Tactic
        - A Few More Handy Tactics
    - Evaluation as a Relation
        - Inference Rule Notation
        - Equivalence of the Definitions
        - Computational vs. Relational Definitions
    - Expressions With Variables
        - Identifiers
        - States
        - Syntax
        - Evaluation
    - Commands
        - Syntax
        - Examples
    - Evaluation
        - Evaluation as a Function (Failed Attempt)
        - Evaluation as a Relation
        - Determinism of Evaluation
    - Reasoning About Imp Programs
    - Additional Exercises


- ImpParser: Lexing and Parsing in Coq

    - Internals
        - Lexical Analysis
        - Parsing
    - Examples


- ImpCEvalFun: Evaluation Function for Imp

    - Evaluation Function
    - Equivalence of Relational and Step-Indexed Evaluation
    - Determinism of Evaluation (Simpler Proof)


- Extraction: Extracting ML from Coq

    - Basic Extraction
    - Controlling Extraction of Specific Types
    - A Complete Example
    - Discussion


- Equiv: Program Equivalence

    - Behavioral Equivalence
        - Definitions
        - Examples
        - The Functional Equivalence Axiom
    - Properties of Behavioral Equivalence
        - Behavioral Equivalence is an Equivalence
        - Behavioral Equivalence is a Congruence
    - Program Transformations
        - The Constant-Folding Transformation
        - Soundness of Constant Folding
    - Proving That Programs Are Not Equivalent
    - Extended exercise: Non-deterministic Imp
    - Doing Without Extensionality (Advanced)
    - Additional Exercises


- Hoare: Hoare Logic, Part I

    - Hoare Logic
        - Assertions
        - Notation for Assertions
        - Hoare Triples
        - Proof Rules
    - Hoare Logic: So Far
        - Hoare Logic Rules (so far)
        - Exercise: HAVOC
        - Complete List of Hoare Logic Rules


- Hoare2: Hoare Logic, Part II

    - Decorated Programs
        - Example: Swapping Using Addition and Subtraction
        - Example: Simple Conditionals
        - Example: Reduce to Zero (Trivial Loop)
        - Example: Division
    - Finding Loop Invariants
        - Example: Slow Subtraction
        - Exercise: Slow Assignment
        - Exercise: Slow Addition
        - Example: Parity
        - Example: Finding Square Roots
        - Example: Squaring
        - Exercise: Factorial
        - Exercise: Min
        - Exercise: Power Series
    - Weakest Preconditions (Advanced)
    - Formal Decorated Programs (Advanced)
        - Syntax
        - Extracting Verification Conditions
        - Examples


- HoareAsLogic: Hoare Logic as a Logic

- Smallstep: Small-step Operational Semantics

    - A Toy Language
    - Relations
        - Values
        - Strong Progress and Normal Forms
    - Multi-Step Reduction
        - Examples
        - Normal Forms Again
        - Equivalence of Big-Step and Small-Step Reduction
        - Additional Exercises
    - Small-Step Imp
    - Concurrent Imp
    - A Small-Step Stack Machine
    - Auto: More Automation

- The auto and eauto tactics

    - Searching Hypotheses
    - Types: Type Systems

- Typed Arithmetic Expressions

    - Syntax
        - Operational Semantics
      - Normal Forms and Values
        - Typing
        - Canonical forms
        - Progress
        - Type Preservation
        - Type Soundness
    - Aside: the normalize Tactic
        - Additional Exercises

- Stlc: The Simply Typed Lambda-Calculus

    - The Simply Typed Lambda-Calculus
        - Overview
        - Syntax
    -   Operational Semantics
    -   Typing

- StlcProp: Properties of STLC

    - Canonical Forms
    - Progress
    - Preservation
        - Free Occurrences
        - Substitution
        - Main Theorem
    - Type Soundness
    - Uniqueness of Types
    - Additional Exercises
        - Exercise: STLC with Arithmetic

- MoreStlc: More on the Simply Typed Lambda-Calculus

    - Simple Extensions to STLC
        - Numbers
        - let-bindings
        - Pairs
        - Unit
        - Sums
        - Lists
        - General Recursion
        - Records
    - Exercise: Formalizing the Extensions
        - Examples
        - Properties of Typing

- Sub: Subtyping

    - Concepts
        - A Motivating Example
        - Subtyping and Object-Oriented Languages
        - The Subsumption Rule
        - The Subtype Relation
        - Exercises
    - Formal Definitions
        - Core Definitions
        - Subtyping
        - Typing
        - Typing examples
    - Properties
        - Inversion Lemmas for Subtyping
        - Canonical Forms
        - Progress
        - Inversion Lemmas for Typing
        - Context Invariance
        - Substitution
        - Preservation
        - Records, via Products and Top
        - Exercises
    - Exercise: Adding Products

- Typechecking

    - MoreStlc: A Typechecker for STLC
        - Comparing Types
        - The Typechecker
        - Properties

- Records: Adding Records to STLC

    - Adding Records
    - Formalizing Records
        - Examples
        - Properties of Typing

- References: Typing Mutable References

    - Definitions
    - Syntax
    - Pragmatics
        - Side Effects and Sequencing
        - References and Aliasing
        - Shared State
        - Objects
        - References to Compound Types
        - Null References
        - Garbage Collection
    - Operational Semantics
        - Locations
        - Stores
        - Reduction
    - Typing
        - Store typings
        - The Typing Relation
    - Properties
        - Well-Typed Stores
        - Extending Store Typings
        - Preservation, Finally
        - Substitution lemma
        - Assignment Preserves Store Typing
        - Weakening for Stores
        - Preservation!
        - Progress
    - References and Nontermination
    - Additional Exercises

- RecordSub: Subtyping with Records

    - Core Definitions
    - Subtyping
        - Definition
        - Subtyping Examples and Exercises
        - Properties of Subtyping
    - Typing
        - Typing Examples
        - Properties of Typing
        - Exercises on Typing

- Norm: Normalization of STLC

    - Language
    - Normalization
        - Membership in R_T is invariant under evaluation
        - Closed instances of terms of type T belong to R_T

- LibTactics: A Collection of Handy General-Purpose Tactics

    - Additional notations for Coq
        - N-ary Existentials
    - Tools for programming with Ltac
        - Identity continuation
        - Untyped arguments for tactics
        - Optional arguments for tactics
        - Wildcard arguments for tactics
        - Position markers
        - List of arguments for tactics
        - Databases of lemmas
        - On-the-fly removal of hypotheses
        - Numbers as arguments
        - Testing tactics
        - Check no evar in goal
        - Tagging of hypotheses
        - Tagging of hypotheses
        - Deconstructing terms
        - Action at occurence and action not at occurence
        - An alias for eq
    - Backward and forward chaining
        - Application
        - Assertions
        - Instantiation and forward-chaining
        - Experimental tactics for application
        - Adding assumptions
        - Application of tautologies
        - Application modulo equalities
    - Introduction and generalization
        - Introduction
        - Generalization
        - Naming
    - Rewriting
        - Rewriting
        - Replace
        - Renaming
        - Unfolding
        - Simplification
        - Evaluation
        - Substitution
        - Tactics to work with proof irrelevance
        - Proving equalities
    - Inversion
        - Basic inversion
        - Inversion with substitution
        - Injection with substitution
        - Inversion and injection with substitution —rough implementation
        - Case analysis
    - Induction
    - Decidable equality
    - Equivalence
    - N-ary Conjunctions and Disjunctions
    - Tactics to prove typeclass instances
    - Tactics to invoke automation
        - jauto, a new automation tactics
        - Definitions of automation tactics
        - Definitions for parsing compatibility
        - Parsing for light automation
        - Parsing for strong automation
    - Tactics to sort out the proof context
        - Hiding hypotheses
        - Sorting hypotheses
        - Clearing hypotheses
    - Tactics for development purposes
        - Skipping subgoals
    - Compatibility with standard library

- UseTactics: Tactic Library for Coq: A Gentle Introduction

    - Tactics for introduction and case analysis
        - The tactic introv
        - The tactic inverts
    - Tactics for n-ary connectives
        - The tactic splits
        - The tactic branch
        - The tactic ∃
    - Tactics for working with equality
        - The tactics asserts_rewrite and cuts_rewrite
        - The tactic substs
        - The tactic fequals
        - The tactic applys_eq
    - Some convenient shorthands
        - The tactic unfolds
        - The tactics false and tryfalse
        - The tactic gen
        - The tactics skip, skip_rewrite and skip_goal
        - The tactic sort
    - Tactics for advanced lemma instantiation
        - Working of lets
        - Working of applys, forwards and specializes
        - Example of instantiations
    - Summary

- UseAuto: Theory and Practice of Automation in Coq Proofs

    - Basic Features of Proof Search
        - Strength of Proof Search
        - Basics
        - Conjunctions
        - Disjunctions
        - Existentials
        - Negation
        - Equalities
    - How Proof Search Works
        - Search Depth
        - Backtracking
        - Adding Hints
        - Integration of Automation in Tactics
    - Examples of Use of Automation
        - Determinism
        - Preservation for STLC
        - Progress for STLC
        - BigStep and SmallStep
        - Preservation for STLCRef
        - Progress for STLCRef
        - Subtyping
    - Advanced Topics in Proof Search
        - Stating Lemmas in the Right Way
        - Unfolding of Definitions During Proof-Search
        - Automation for Proving Absurd Goals
        - Automation for Transitivity Lemmas
    - Decision Procedures
        - Omega
        - Ring
        - Congruence
    - Summary

- PE: Partial Evaluation

    - Generalizing Constant Folding
        - Partial States
        - Arithmetic Expressions
        - Boolean Expressions
    - Partial Evaluation of Commands, Without Loops
        - Assignment
        - Conditional
        - The Partial Evaluation Relation
        - Examples
        - Correctness of Partial Evaluation
    - Partial Evaluation of Loops
        - Examples
        - Correctness
    - Partial Evaluation of Flowchart Programs
        - Basic blocks
        - Flowchart programs
        - Partial evaluation of basic blocks and flowchart programs

- Postscript

    - Looking back...
    - Looking forward...

## Information in English

The goal of this project is to produce a Brazilian Portuguese translation
of the electronic book "Software Foundations", by Benjamin C. Pierce, Chris 
Casinghino, Marco Gaboardi, Michael Greenberg, Cătălin Hriţcu, Vilhelm Sjöberg, 
Brent Yorgey. This book is available at <http://www.cis.upenn.edu/~bcpierce/sf/current/index.html>.


#lang scribble/base

@title{Klein Lang}

@author{Gavin Gray}

@section{Design}

The current design of the Klein language is very much @italic{unfinished}.
This project is a way for me to go through several aspects of language and
compiler design testing new features at each level. The following features are
what the language is going to gradually gain over time.
@itemize[
@item{A strong static typing system provided via Hindly-Milner type inference.}
@item{First class continuations.}
@item{Extensible parser and rich macro system.}
@item{A VM and tracing jit compiler.}
@item{ Generational garbage collector.}
]

The first stage of the language will focus on type checking an s-expressioned
version of Klein, denoted KleinS. KleinS does not allow users to specify any
types, rather everything must be inferred. This language will then get lowered
to a continuation passing style language, denoted HCPS because it is the
higher-level version of the real intermediate language: LCPS. The first target
of KleinS will be OCaml. Targeting OCaml will allow for fairly efficient
binaries, free optimization, and most important, a second way to test the KleinS
type checker. A successfully typed KleinS program should @italic{never} result
in a poorly typed OCaml program.

@subsection{KleinS Semantics}

@subsubsection{Numbers}

The current tower of numbers is very crude. Particularly sharp, is the choice of
classes to which a number belongs. Currently, there are two types of numbers:
@racket{integer?} and @racket{float?}. An integer is represented by an exact 32
bit number, and the float type corresponds to the IEEE 754 standard. The current
hierarchy of classes is:
@itemize[
@item{Numeric}
@item{Fractional}
]

Later, I intend to expand this stack with special case values, and many common
numeric types that you would see in a
@link["https://docs.racket-lang.org/guide/numbers.html"]{Racket implementation}.

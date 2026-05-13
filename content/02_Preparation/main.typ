#import "../utils.typ" : *
#import "@preview/curryst:0.6.0": rule, prooftree
#import "@preview/subpar:0.2.2" as subpar: grid as spg
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/diagraph:0.3.6": raw-render as grender

#set raw(lang: "lean")

// TODO: embed fonts

// TODO: Fill out a chapter introduction.
// Talk more about the background that is needed
// I.e. dependent type theory, coinduction, lean and other similar things.

In this section I will discuss prerequisites for the implementation of the dissertation.
I will discuss the background needed to understand the state-machine encoding,
and other relevant topics.

#set terms(tight: true)

== Dependent type theory<sec:dependent>

// TODO: Rephrase this
// We can start by adding a type for Types,
// giving us a higher-order logic.
Given functions between sets $A, B : Type$ $,A -> B$,
we can generalize this by changing $B : Type$ to be a function $B : A -> Type$,
then letting us write the dependent function $(x : A) -> B(x)$ ($Pi$-type).
We can also do the dual construction,
and get dependent pairs ($Sigma$-type).
The inference rules for these can be seen in @dtt:fg:psir.
If you are unfamiliar with dependent types,
it is often helpful to view them through this relationship.
For a more in-depth look at dependent type theory,
read the HoTTBook Section 1 up to Chapter 6 @cite:hottbook.

// TODO: You would rather understand a general notion of a dependent type,
// than just seeing the rules
// Vectors as lists of fixed lengths,
// (ls : List A) ×' ls.length = 10,
// Come up with an example that works for sigma types.

#spg(
  figure(
    prooftree(
      rule(
        name : [$Pi$f],
        [$A : Type$],
        [$B : A -> Type$],
        [$(x : A) -> B(x)$]
      )
    ),
    caption: [$Pi$-forming rule]
  ),
  figure(
    prooftree(
      rule(
        name : [$Pi$i],
        [$Gamma, x : A tack.r v : B(x)$],
        [$Gamma tack.r lambda x. v : (x : A) -> B(x)$]
      )
    ),
    caption: [$Pi$-intro rule]
  ),
  figure(
    prooftree(
      rule(
        name : [$Pi$e],
        [$Gamma tack.r f : (x : A) -> B(x)$],
        [$Gamma tack.r v : A$],
        [$Gamma tack.r f v : B[x "/" v]$]
      )
    ),
    caption: [$Pi$-elimination rule]
  ),
  figure(
    prooftree(
      rule(
        name : [$Sigma$f],
        [$A : Type$],
        [$B : A -> Type$],
        [$(x : A) times B(x)$]
      )
    ),
    caption: [$Sigma$-forming rule]
  ),
  figure(
    prooftree(
      rule(
        name : [$Sigma$i],
        [$Gamma tack.r a : A$],
        [$Gamma tack.r b : B[x "/" a]$],
        [$Gamma tack.r chevron.l a, b, chevron.r : (x : A) times B(x)$]
      )
    ),
    caption: [$Sigma$-intro rule]
  ),
  figure(
    prooftree(
      rule(
        name : [$Sigma$e],
        [$Gamma tack.r v : (a : A) times B(a)$],
        [$Gamma tack.r a : A, b : B[x "/" b] tack.r x : C$],
        [$Gamma tack.r "let" chevron.l a, b chevron.r := v "in" x : C$]
      )
    ),
    caption: [$Sigma$-elimination rule#footnote([
      Technically this is not the most general eliminator for Sigma's,
      as $C$ can depend on the content of the type.
      For symmetry and simplicity I omit this.
    ])]
  ),
  columns: (auto,auto,auto),
  caption: [Inference rules for $Pi$ and $Sigma$ types],
  label: <dtt:fg:psir>
)

These rules are analogous to the rules for $forall, exists$ from the natural deduction system.
In fact they are related through the Curry-Howard correspondence as seen in @dtt:eq:pt.
Going from dependent types to the propositional rules,
we must equate all proofs/terms.
This process is called propositional truncation,
as we truncate away data @cite:hottbook (Chapter 3.7).
The other direction 'categorification'.
Categorification is the process of finding a categorical object that truncates down to the logical structure.
#cite(<cite:cltt>, form:"prose") is a great resource on this.

#figure(
  $ Pi, Sigma stretch(harpoons.rtlb)^"propositional truncation"_"Categorification" forall, exists $,
  caption: [Curry-Howard correspondence]
)<dtt:eq:pt>

// === Categorically
//
// Dependent type theory is an extension on the simply typed lambda calculus.
// It is for locally cartesian closed categories,
// what ST$lambda$C is for cartesian categories;
// the semantics of a dependent calculus will be in terms of some LCCC.

#let mpf(a, b) = $chevron.l #a, #b chevron.r$

////////////////////////////////////////////////////////////////////////////////

== Universe levels

Consider Russells Paradox `let R := { x ∣ x ∉ x } in R ∈ R`.
A way to resolve this is by making a hierarchy of sets `Set 0 : Set 1 : ...`.

#definition[
  A *universe* is a type, whos terms are themselves types @nlab:type_universe.
]

We also have a paradox like this for types, Girard's paradox,
which can be seen in @cite:girad (Lecture 20).
For this we make a hierarchy of types `Type 0 : Type 1 : ...`#footnote[
  There are a few different semantics for doing this (universes à la Russell, Tarski, Coquand).
  It would be beyond this dissertation to go into this
].

#definition[
  We call an index into the hierarchy of universes a *universe level*.
  These universe levels form a join semilattice with a successor.
]

#definition[
  A definition is *universe polymorphic* if it uses some free universe levels #U.
]

Through this dissertation universe levels are written calligraphically (#U, #V, $cal(W)$).
Given types `X : Type 𝓤` and `Y : Type 𝓥`,
we have that `X × Y`, `X ⊕ Y` and `X → Y` all reside in `Type max 𝓤 𝓥`.
$Sigma$- and $Pi$-types also behave like this.
Bumps are only introduced when objects hold a `Type 𝓤`.

#example[
  Given two types `X : Type 2` and `Y : Type 3`,
  the function space between these two types resides at the level `max 2 3`,
  that is `X → Y : Type 3`.
]

If we have a type `X : Type 𝓤` and we want it to reside it some universe `max 𝓤 𝓥`,
we need to make a type-constructor `ULift.{𝓥} : Type 𝓤 → max 𝓤 𝓥`.
Working with `ULift`s can quickly become verbose.
To avoid this many logics add a form of subtyping on universe hierarchies.
Computationally this behaves like `ULift`s, but hides the lift.

#definition[
  A logic is *cumulative* if for some `X : Type 𝓤`,
  then we also definitionally have `X : Type max 𝓤 𝓥` for any #V.
]

Many problems will be caused throughout this dissertation by universe levels.
Therefore often I will simply give a less general,
more universe stable type.

== Lean

// TODO!: Mention Rocq

Lean @cite:lean is a popular dependently typed proof assistant.
Lean is known for many reasons, 3 of them are:

+ Lean has Mathlib @cite:mathlib, one of the world's largest repositories of formalized mathematics @sec:lean:mathlib.
+ Lean has a rich tactic language in which most proofs are written @sec:lean:tactic.
+ Lean has a compiler, and can be used as a general purpose programming language @sec:lean:compiler.

#figure(
  diagram(
    node((0,0), [Source code]),
    edge("->", [Parsing]),
    node((0,1), [Syntax tree]),
    edge("->", [Elaboration]),
    node((0,2), [Type theory]),
    edge("->", [Recursion #linebreak()elimination]),
    edge((-1,3),"->", [Compilation]),
    node((1,3), [Kernel]),
    node((-1,3), [Executable]),
  ),
  caption: [Lean compiler layout#footnote[
    Taken from #link("https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/")
  ]]
)<lean:fg:comp>

When talking about Lean we also use the term _definitionally equal_ to mean $beta$,$eta$-equivalent,
and _propositionally equal_ if two terms are identified by a generalized algebraic data type.
Additionally, we have _heterogeneous equality_ where the types are only propositionally equal.

=== Mathlib <sec:lean:mathlib>

One of the primary use-cases of Lean is for the vast mathematics library known as Mathlib.
Mathlib has many subcomponents in it such as category theory, analysis and geometry.
It also has a full formalization of the QPF paper @cite:qpf done by J. Avigard and A. Keizer.
This includes definitions of polynomial functors @sec:poly which we will use as part of the implementation.

=== The tactic language <sec:lean:tactic>

Many languages have metaprogramming features.
Lean has a very complex compiler that is able to provide type information at certian metaprogram expansion.
This is possible by taking place at during the elaboration stage as seen in @lean:fg:comp.
Tactics are a form of metaprogramming aimed at constructing proof terms.
Some of the tactics used in this project are:

+ `refine term` / `exact term` specify a term from term-mode rather than a tactic,
+ `intro var` becomes `refine fun var => ?_`,
+ `apply term` becomes `refine term ?_`,
+ `change sig` definitional type unfolding `refine (?_ : sig)`,
+ `rw [e₁, e₂]` rewrite, replacing occurances of the left hand side of equalities with the right hand side,
+ `simp [e₁, e₂]` simplifies expressions using passed equalities,
+ `induction obj` do an inductive case split,
+ `cases obj` do a case split,
+ `rcases obj with pattern` recursive case split,
+ `by_cases` law of excluded middle,
+ `ext` extensionality,
+ `congr` congruence,
+ `grind` SMT-solver,
+ `sorry` is a placeholder 'sorry I could not solve this'.

=== The Lean compiler <sec:lean:compiler>

We have a dichotomy between the logical and computation sides of a proofs/programs as seen in @lean:fg:comp.
A classic example of where this occurs is in compiling the elimination principle for strong-induction#footnote[
  This is now,
  for the case of natural numbers,
  fixed as of Lean 4.27.
  https://www.youtube.com/watch?v=LOUbbiV0mWc
  https://lean-lang.org/doc/reference/latest/releases/v4.27.0/
].
We talk about this being a difference between the kernel
(the small safe piece of code we believe to be correct)
and the compiler (which is much larger and more complex).

Lean requires all induction to be structural,
so to do induction over a general well-founded relation,
we need some inductive data type (@sec:ind),
Lean calls this `Acc` and defines it as seen in @lean:ls:acc.
On this Lean defines a function `WellFounded.fixF` (@lean:ls:fixf),
which allows for strong induction.
This function is quadratic in its runtime,
therefore as a consequence the kernel takes quadratic runtime to execute.

#spg(
  figure(
  ```lean
inductive Acc {α : Sort u} (r : α → α → Prop) : α → Prop where
  /--
  A value is accessible if for all `y` such that `r y x`, `y` is also accessible.
  Note that if there exists no `y` such that `r y x`, then `x` is accessible.
  Such an `x` is called a _base case_.
  -/
  | intro (x : α) (h : (y : α) → r y x → Acc r y) : Acc r x
```,
  caption: [Definition for `Acc` taken from Lean's GitHub @cite:lean]
  ),
  <lean:ls:acc>,
  figure(
    ```lean
def WellFounded.fixF
    {α : Sort u} {r : α → α → Prop} {C : α → Sort v}
    (F : (x : α) → ((y : α) → r y x → C y) → C x) (x : α) (a : Acc r x)
    : C x := ...
    ```,
    caption: [Type signature of `WellFounded.fixF`]
  ),
  <lean:ls:fixf>,
  caption: [Some strong-induction primitives from Lean]
)


It would be unacceptable for a program using strong recursion to be quadratic for a general purpose programming language,
therefore the compiler removes the usage of `fixF`,
and generates the expected calls in the intermediate representation (LCNF).

We can see that given the source-code @lean:ls:def,
it generates a definition @lean:ls:ker with `Nat.fix` (a variant of `fixF`),
but in the output LCNF we get @lean:ls:ir,
which does not contain any mention of `Nat.fix`,
but we see the recursive call,
demonstrating how the logical and computation definitions diverge.

#let (gcda, gcdb) = partL(read("./Gcd.lean"), 9)

#[
#show raw.where(block: true): set text(size: 6pt)
#spg(
  figure(raw(gcda, block: true), caption : [GCD source code]),
  <lean:ls:def>,
  figure(raw(gcdb, block: true), caption : [generated kernel code]),
  <lean:ls:ker>,
  figure(
    ```lean
[Compiler.result] size: 9
  def gcd a b : tobj :=
    let _x.1 := 0;
    let _x.2 := Nat.decEq b _x.1;
    cases _x.2 : tobj
    | Bool.false =>
      let _x.3 := Nat.mod a b;
      dec a;
      let _x.4 := gcd b _x.3;
      return _x.4
    | Bool.true =>
      dec b;
      return a
    ```,
    caption: [Generated intermediate #box[representation]]
  ),
  <lean:ls:ir>,
  columns: (auto, auto, auto),
  caption: [Gcd as Source, Kernel and LCNF]
)]

This general trick inspired the project,
as it demonstrates that there is precedent in Lean4 to have separate logical and executional models.
This is further highlighted by the existence of the `@[implemented_by]` attribute,
which lets the programmer off-load the runtime behaviour of a function to another possibly unsafe definition.
When a definition is marked as `@[implemented_by x]`,
the code-generator treats it as `x` when compiling the code.
// The semantics of `@[implemented_by]` is simply calling the alternative function when not evaluating in the kernel.
Safety of programs using `@[implemented_by]` is a complex endeavour to verify,
as Lean has a tactic called `native_decide` that runs the generated code outside of the kernel.

// JH: You cant store a type in a struct


== Polynomial functors<sec:poly>

#definition[
A *functor* is pair of a map `(α : Type) → F α` sending types to types,
and a map between types to functions between the functor at those types `(α β : Type) → (α → β) → F α → F β`,
such that the map distributes over composition and preserves identities.
]
#example[
An example of a functor in programming is `List`s,
given a `List String` we can use the function `len : String → Nat`,
to make a function `map len : List String → List Nat`:
]

Polynomial functors are functors with a collection of constructors (the head type),
where the children correspond to how many of the polymorphic argument are wanted.
Alternatively they are functors generated from taking `Sum`s and `Product`s over `const`ants and projections.
The formal definition can be seen in @pfunc-math.

#definition[
  A *univariate polynomial functor* $P(alpha)$ is given by:
  a head-type $H$,
  along with a child family $c_h$ parameterised by the head $h:H$.
  A polynomial functor applied at type $alpha$,
  is a sigma-type of the head,
  and the child family
  @nlab:polynomial_functor.
  As seen in @sec:dependent,
  the object of this type will be a pair of a head and child functions.
]<pfunc:d:pfunc>

#figure(
  $ P(α) eq.delta (h : H) times c_h arrow.r alpha $,
  caption: [Formal definition of polynomial functor]
)
<pfunc-math>

This dissertation will mainly focus on multivariate polynomial functors.
Instead of having a single child,
multivariate polynomial functors have a $n$-tuple of children for an $n$-polynomial functor.

Polynomial functors have all finite products (@pf:fg:const, @pf:fg:prod) and coproducts (@pf:fg:const, @pf:fg:sum).
Polynomial functors have fixed points corresponding to `inductive`s,
and cofixed-points as `coinductive`s @cite:keizer @cite:qpf. // #cite(<cite:keizer>, form: "prose") #cite(<cite:qpf>, form: "prose").
// Polynomial functors are also closed under (co)fixed points so I will write them using Lean `inductive` syntax,
// the fix point corresponds to .
In the figures there are ellipsis,
in reality multivariate polynomials operate on Type-vectors which come from the category formed by the products $Type^n$ for some $n : NN$,
these are not ergonomic to work.
// The justification for writing polynomials using an inductive notation can be found in 
// For an explanation of the notation see @a:gpfunctors.

=== Common polynomials

Some examples of common polynomials are projection (@pf:fg:prj),
constant functors (@pf:fg:const),
binary products (@pf:fg:prod),
and binary sums (@pf:fg:sum).
One crucial and complex polynomial not shown here is composition.
Composition takes an $n$-polynomial, and $n$ lots of $m$-polynomials, and outputs an $m$-polynomial.
For example, taking the 3-polynomial $F$ and 3 2-polynomials $G_1$,$G_2$,$G_3$,
the constructor of the composition takes a $F (G_1 alpha beta) (G_2 alpha beta) (G_3 alpha beta)$.
The polynomial notation for this can be found in @cite:mathlib @cite:qpf.
For those familiar, the composition polynomial works exactly like composition in primitive recursive functions.

// We can, using these functors,
// make a polynomial compiler from any syntax of the form `P :: var | P × P | P + P | const n` where `var` ranges over named variables.
// This compiler is structurally recursive on the syntax.
// When you see a var do `Prj` (@pf:fg:prj), a const `Const` (@pf:fg:const),
// and for the binary operators first a composition then either `Sum` or `Prod`.

#let code-math(code, mmath, c, ccode : [Inductive Notation], cmath : [Polynomial], lab : none) = [
  #set math.equation(numbering: none)
  #spg(
  figure(code, caption: ccode),
  figure(mmath, caption: cmath),
  columns: (1fr, 1fr),
  caption: c,
  label: lab
) ]

#code-math(```lean
inductive Prj (i : Fin n) (a_1 ... a_n : Type)
  where
  | mk (t : a[i]) ```,
  $ lambda (i : underline(n)). mpf(1, lambda j quad h. "if" i = j "then" 1 "else" 0) $ ,
  [Projection polynomial],
  lab : <pf:fg:prj>,
)
#code-math(```lean
inductive Const (T : Type) (a_1 ... a_n : Type) 
  where
  | mk (t : T) ```,
  $ lambda (T : Type). mpf(T, lambda i quad h. 0) $ ,
  [Constant polynomial],
  lab : <pf:fg:const>,
)
#code-math(```lean
inductive Prod (A B : Type) where
  | mk : A → B → Sum A B
  ```,
  $ mpf(1, lambda i quad (). 1) $,
  [Product polynomial],
  lab : <pf:fg:prod>,
)
#code-math(```lean
inductive Sum (A B : Type) where
  | inl : A → Sum A B
  | inr : B → Sum A B
  ```,
  $ mpf(BB, lambda mat(0, "true", |->, 1; 1, "false", |->, 1; \_, \_, |->, 0 )) $,
  [Sum polynomial],
  lab : <pf:fg:sum>,
)

// #figure(
//   diagram(
//     cell-size: 6mm,
//     // debug : 1,
//     show_decl("p1", (0,0), pfunc.prj),
//     show_decl("p2", (3,0), pfunc.sum),
//     show_decl("p3", (7,0), pfunc.list),
//
//     show_map("mp", (0,4), (($x$,),), (($alpha$,),), (($f$,),)),
//     show_obj("il", (2,4), pfunc.sum, "inl", (($excl.inv$, $bold(K)v$),), gap : 1, term : $"inl" v$),
//     show_obj("ir", (5,4), pfunc.sum, "inr", (($bold(K)v$, $excl.inv$),), gap : 1, term : $"inr" v$)
//   )
// )

////////////////////////////////////////////////////////////////////////////////

== Recursion and Inductive data type<sec:ind>

#set raw(lang: "ocaml")

#definition[
  An *inductive data type*, is a type with a collection of constructors,
  and an eliminator consuming the tree and producing some data.
  Objects of inductive data types are *well-founded* trees of data.
]<rec:ind:def>

Recalling algebraic data types from languages such as OCaml, Haskell and Rust.
These are structures freely generated from a set of constructors.
The classic example is a list,
given as two constructors,
`val cons : 'a -> 'a list -> 'a list` and `val nil : 'a list`,
and a way to consume lists `val fold : 'a -> ('b -> 'a -> 'a) -> 'b list -> 'a`.
We write this as seen in @cr:ls:list.
// TODO: Write that in these languages they arent actually inductive
// in lean we care about termination.
// If we restrict ourselfs to well-founded trees.
If we restrict these data types to well-founded trees,
these are exactly inductive data types#footnote[
  In OCaml, Haskell and Rust, data types do not correspond directly to inductive types since we can have non-well-founded trees,
  an example is `let rec degen = Cons((), degen)`.
].
Any pure function that terminates must return a finite tree of constructors.
Fold is guaranteed to terminate for any finite tree

In Lean, recursive functions are compiled into a call to some recursor for a type.
For lists this recursor is a dependent generalization of `fold`.
All structurally recursive functions can be compiled into a call to `fold`.
We also have two operations `mk : F (M F) → M F` and `dest : M F → F (M F)`.
These form an equivalence (#cite(<cite:lambek>, form: "prose") Corollary 2.4),
giving us the result that the cofix-point of `F`, written as `M F`, is equivalent to `F (M F)`.
In practice this means we can unfold `M F`.

#let (ilr, ilc) = partL(read("./IList.ml"), 8)

#figure(
  raw(ilr, lang: "ocaml", block: true),
  caption: [Definition of list in OCaml]
)<cr:ls:list>

// === Semantics
//
// Given the family of endofunctors on $Type$.
// Consider the polynomial given by $L_A = 1 plus.o (underline(A) times.o id)$.
// Now recall the definition of the category of #box[$L_A$-algebras]#footnote([TODO: Cite algebra definition]).
// The lists we are used to are exactly the initial object in this category.
// The initial map takes an algebra $f : L_A (B) -> B$ and yields a map $"fold" : mu L_A -> B$#footnote([TODO: Cite Neel]).
// This is exactly what we want,
// as expanding the definition or $L_A (B)$ and distrubuting this over the arrows we get the signature above.
//
== Corecursion and coinductive types<sec:coind>

#definition[
  A *coinductive data type* is a type with a collection of constructors,
  and a generating function.
  Objects of a coinductive data types are potentially infinite trees of data.
]

Where inductive data types have a `val fold : (('a, 'b) f → 'b) → (('a, 'g) f as 'g) → 'b` (rec) to consume them,
coinductive types have an `val unfold : ('b → ('a, 'b) f) → 'b → (('a, 'g) f as 'g)` (corec) to produce them.
Intuitively, view it as if a fix F yields a bounded structure,
then cofix F yields an unbounded structure#footnote[
  That is $"fix" (1 + (A times -))$ gives lists,
  then $"cofix" (1 + (A times -))$ gives potentially infinite lists.
].
Another way to view coinductive types are as a state-machine,
here the corecursor takes center stage.
We can say a coinductive data type is a data type generated by some corecursor state-machine.

=== In OCaml <sec:cf:ocaml>

We can make colists (lazy lists) by thunking (putting under a unit function) recursive occurrences,
this thunking allows infinite structures to exist in finite memory.
Then all we need to do is add a definition of `unfold`, `mk` and `dest` (@cr:ls:colist).
We also have constructors and destructors forming inverses as for recursive data types#footnote[The dual of Lambek's theorem @cite:lambek].

#figure(
  raw(ilc, lang: "ocaml", block: true),
  caption: [Definition of colist in OCaml]
)<cr:ls:colist>

#set raw(lang: "lean")

The keen eyed will notice and call out that `unfold` is not structurally recursive,
nor even decreasing at all.
This is the key difference between inductive types and coinductive types;
coinductive types can be 'infinitely big'.
Despite not being terminating,
the definition is _productive_.
Termination is having a complete structure in finite time,
productivity is being able to always compute the next layer in finite time.

#definition[
  *Productivity* is the property of a corecursive function to always be able to compute the next layer in finite time.
]

=== Streams

Streams are similar to colists.
The difference is they have no 'nil' constructor.
An inductive data type of this form is empty#footnote[
  See the following Lean

  #let ns = read("./NoStream.lean")
  #h(1.5em)
  #box[
  #raw(ns, lang:"lean")]
], though it is inhabited for coinductive data types.
Streams and colists are also common in general purpose programming,
Java has Stream,
Rust and Python have Iterator.
This backs up our use cases put forward in the introduction.
We will give concrete implementations of them for each of the encodings as follows.

=== The #MT <sec:m>

The cofixed-point of a polynomial functor `F`, is called an #MT
#footnote[Often phrased as types who's semantics are terminal $F$-coalgebra.];
a possibly infinitely deep tree, in which each layer is an unfolding of some polynomial `F`.
This means the implementations must have both
a corecursor `corec : {α : Type} → (f : α → F α) → α → M F`,
and a destructor `dest : M F → F (M F)`.
These are the functions mentioned in @sec:cf:ocaml.
Often we also want to ship a way to `mk` a new layer,
but we can define this from the two operators above.

There are different approaches to encode #MTs in Lean.
Prior art is the progressive approximation encoding (@sec:m:pa) (as seen in Mathlib),
and this dissertation introduces the state-machine encoding (@sec:m:sme).

==== Progressive approximation encoding <sec:m:pa>

A simple way to encode #MTs,
are as functions emitting finite and growing trees that must at every level agree.
This corresponds to the limit over the natural number category as the dual of #cite(<cite:adamek>, form: "prose") (see section "Free algebra algorithm").
Agreement is given by them being the same up to the previous depth as seen in @m:fg:agree.
Agreement can be thought of as the structure 'crystalising',
since it exclusively 'grows' from the crystal edge.

#figure(
  diagram(cell-size:5mm, $
  0 edge("rrrrrrrrr", "..") & & & edge("lld") edge("d") edge("dr") & & & & edge("lld") edge("d") edge("dr") &
  \
  1 edge("rrrrrrrrr", "..") & & & & & edge("d") edge("dr") & & & edge("d")
  \
  2 edge("rrrrrrrrr", "..")
  $),
  caption: [Agreement of two trees of height 1 and 2]
)<m:fg:agree>

#let streamf = partL(read("./Stream.lean"), 12, 13, 26, 36)

In Lean, for a specific functor,
we begin setting up the definition of approximation.
With this we define the coinductive type as the agreeing functions.

#figure(
  raw(streamf.at(0), lang: "lean", block: true),
  caption: [Definition of approx for stream]
)

For the corecursor, we need to implement a function to emit the finite and growing trees,
and a proof that the trees agree.
This is also where the performance hit is incurred,
as we have to regenerate the tree every time we want to reach the new depth.

#figure(
  raw(streamf.at(2), lang: "lean", block: true),
  caption: [Objects of the corecursor for streams]
)

The destructor builds an instance of the functor,
where the correct path is selected from the corecursor.

#figure(
  raw(streamf.at(3), lang: "lean", block: true),
  caption: [Destructor for streams]
)

Proving the coinduction principle (@sec:bisim) is harder.
We do not need to worry about implementing and proving this as Mathlib @cite:mathlib @cite:keizer already provides an implementation of this.

==== State-Machine encoding <sec:m:sme>

// TODO!: Try to move this to implementation,
// Consider struct of arrays.

// The State-Machine encoding is the new alternative implementation.
// First one defines a class of preobject,
// followed by a definition of bisimilarity that we then quotient over.
// This definition will be expanded on in @sec:s:sme, and again @sec:impl-sm.

Given some polynomial functor `P`, the state-machine encoding of `M P` is given by:
some _carrier_ type `α : Type`,
a function (coalgebra) `f : α → P α`,
and some initial state `a : α`.
Once this is done there are 2 key problems:
+ The object constructed is only weakly terminal and equivalently no coinduction principle,
+ the object resides in a higher universe.
Focusing on the first 1st problem, this is solved by quotienting over bisimilarity.
The reason this works has to do with how bisimilarity 'hides' the generating type.
This makes destructuring the only operation you can do to access the type.
The 2nd problem is tackled in @sec:abi.

== Bisimilarity <sec:bisim>

// Often called strong bisimilarity

#definition[
*Bisimilarity* is an equivalence relation on coinductive types.
Two coinductive objects are bisimilar if,
for every possible choice in a structure A,
there exists a corresponding choice in structure B,
and vice versa,
such that you can repeat this procedure.
]

// TODO: a common way to define bisimilarity is define what a bisimulation is,
// Then we say that two things are bisimilar if there exists some bisimulation,
// TODO: stay at the same abstraction level.
// TODO: Look at the Appendix for a fuller definition.

Bisimilarity is not a well-founded relation.
This means we need to define it as a coinductive predicate instead of an inductive one.
Then the proof principal for this will be giving an invariant,
showing the invariant is a bisimulation,
and the initial values are contained within the invariant.

A classic example would be to check if the two state-machines are equal.
In @bs:fg:f you see two state-machines for two different regular expressions.
One could use bisimilarity to show these are the same.
The invariant for this would probably be $(a=q_0 and b=q_0) or (a=q_0 and b=q_2) or (a=q_1 and b=q_1) or (a=q_1 and b=q_3)$.
This also contains the initial state $a = q_0 and b=q_0$.
We also need to show the invariant is a bisimilarity which is a bit more involved.

// TODO: mention ITrees

#[
#spg(
  figure(
    grender(```dot
digraph ab_star {
    rankdir=LR;
    node [shape=circle, width=0.2, fontsize=8, margin=0.08];
    start [shape=point, width=0.05];
    q_0 [shape=doublecircle];

    start -> q_0;
    q_0 -> q_1 [label="a"];
    q_1 -> q_0 [label="b"];
}
    ```,
  ), caption: [DFA for `(ab)*`]),
  <bs:fg:ab>,
  figure(
    grender(```dot
digraph ab_ab_star_star_nfa {
    rankdir=LR;
    node [shape=circle, width=0.2, fontsize=8, margin=0.08];
    start [shape=point, width=0.05];
    q_0 [shape=doublecircle];

    start -> q_0;

    q_0 -> q_1 [label="a"];
    q_1 -> q_2 [label="b"];
    q_2 -> q_0 [label="ε"];
    q_2 -> q_3 [label="a"];
    q_3 -> q_2 [label="b"];
}
    ```
  ), caption: [NFA for `(ab(ab*))*`]),
  <bs:fg:abab>,
  columns: (auto, auto),
  caption: [
    Two bisimilar state-machines
  ],
  label: <bs:fg:f>
)
]

On streams, a bisimulation equates heads and relates tails.
This can be seen in @bs:ls:sbs.
Coinductive types have coinduction principle `bisim : Bisim a b → a = b`.
In Rocq this has to be an axiom, in Lean it is provable.
#cite(<cite:bisim>, form: "prose") is an insightful read on this topic.

#figure(
  raw(takeL(read("../../sme/Sme/Stream/SDefs.lean"), 68, 74), block: true),
  caption: [Bisimilarity on streams]
)<bs:ls:sbs>

////////////////////////////////////////////////////////////////////////////////

== The Free Monad

As mentioned in @sec:coind, every corecursive function has to be productive.
In the current library definition,
this means we need to define the function using the corecursor
`corec {β α} : (β → P (α ::: β)) → β → M P α`.
This can be cumbersome as one can only define one layer of the coinductive data type at a time.
One can image that after the first layer (which is required for productivity),
we have a choice to either `recall` the corecursor from that point,
or `cont`inue a deeper structure (visualized in @futu:fg:cp).
A structure like this would allow for defining multiple layers of a coinductive.

#let trl = sym.triangle.stroked.l

#figure(
  diagram(
    node((0,.5), $P α -$, name: <lp1>),
    node((.5,.5), $trl$, name: <lp1>),
    node((1,.5), $β ⊕ -$, name: <ls1>),
    node((1.5,.5), $trl$, name: <lp1>),
    node((0,1), "cons", name: <c1>),
    edge("->"),
    node((1,2), "recall", name: <r1>),
    edge(<r1>, (1,2.5), ".."),
    edge(<c1>, <n1>, "->"),
    node((1,1), "cont", name: <n1>),
    edge(<n1>, <c2>, "->"),
    node((2,.5), $P α -$, name: <lp1>),
    node((2.5,.5), $trl$, name: <lp1>),
    node((3,.5), $β ⊕ -$, name: <ls1>),
    node((3.5,.5), $trl$, name: <lp1>),
    node((2,1), "cons", name: <c2>),
    edge(<c2>, <n2>, "->"),
    edge("->"),
    node((3,2), "recall", name: <r2>),
    edge(<r2>, (3,2.5), (-.5,2.5), (-.5,1), <c1>, "..>"),
    node((3,1), "cont", name: <n2>),
    edge("->"),
    node((4,1), $...$, name: <el>),
    node((4,.5), $...$, name: <el>),
  ),
  caption: [Choice points for a producing a stream]
)<futu:fg:cp>

Making a structure like this is possible with a bit of setup.

#definition[
  A *Monad* `M` is a functor,
  with an additional operator `>>= : (α → M β) → M α → M β`,
  and a function `return : α → M α` satisfying the rules
  `(return ∘ f) >>= a = map f a`, `f >>= return v = f v` and `x >>= f >>= g = x >>= λx ↦ f x >>= g`.
]

Given a monad `M`, we can simply interpret it as a functor,
but what if we want to go the other way;
take a `F` and make the most general (or _universal_) monad out of it.
The process for this involves keeping 'as much structure as possible',
one way of doing this is have two constructor `return : α → Free F α`,
and `bind : F (Free F α) → Free F α`.
When doing this construction as a coinductive it is called the `Free`-monad.
This has a bind operator that corresponds to pasting trees together.
When referring to it, it will be generalized to a $n+1$-polynomial,
and written `Free P α β`,
the definition of this will be given in the implementation section.

Using the Free monad one can define a futumorphism
`futu {β} : (β → P (α ::: Free P α β)) → M P α` @cite:fantomorph @cite:futu @cite:urs.
This turns out to be exactly the structure wanted.

== Interaction Trees

Denotational semantics stands as an alternative to operational semantics,
where rather than having some relation of program steps,
one maps syntax to some mathematical object which can be reasoned about directly.
For lambda calculi we have categorical semantics,
but for imperative languages it can be much harder to find a denotational object.

Interaction trees @cite:itree are a form of coinductive free-monad,
in which you have a set of visible effects.
ITrees have three constructors, returning a value (monad unit),
having a silent transition (for non-termination),
and emitting a visible effect.
A definition for this can be seen in @it:ls:rocq.
The effects of the ITree correspond to the effects of the imperative language.
Some examples could be printing, reading and writing to variables, and reading user input.
ITrees have a 'monadic interpretation' where the effects are transformed to operations in some monad.
Further, ITrees have an equivalence relation called weak bisimilarity,
this is bisimilarity modulo silent steps,
two objects are related if they have the same visible effects and return values.

We will speak more about ITrees in @sec:itree

#figure(
```lean
coinductive ITree (E : Type → Type) (R : Type) : Type :=
| ret : R → ITree E R
| tau : ITree E R → ITree E R
| vis {A : Type} : E A → (A → ITree E R) → ITree E R
```,
    caption: [Notational defintion for ITrees]
)<it:ls:rocq>

== Methodology<sec:method>

// TODO: actuall write this as a methodology
// TODO: Rephrase.

Writing in a proof assistant is different to writing in a general purpose language,
this is especially the case in Lean as it is a hybrid of both styles.
A notable and immediate difference is the prevalence of software testing of programs.
Instead of having tests that can be flakey and sparse,
in Lean you have checked proofs.

In a conventional programming language,
you can follow Test Driven Development where you constantly refine the specification with additional tests,
which you check as you go through the code.
In Proof Driven Development (PDD) @cite:pdd you work similarly to TDD,
but now when you have your function,
instead of knowing it works for finite cases,
you can be guaranteed that it satisfies the equation.
Furthermore, the proofs can serve to enrich the main artifact.
This will be seen in the ITree implementation as well as the futumorphic productivity.
Lean makes working in this style a delightful experience using constructs such as `#check`, `#print` and `#eval`,
one can see exactly what a function is and what it is doing.
These can also be turned into conventional tests using `#guard_msgs in`,
which raises a compile error upon an output changing.
PDD was originally demonstrated for Idris,
which in many ways is similar to Lean as it is a hybrid language,
therefore I will apply this approach as I write the code.

Lean also has great automation features which I use at many points in the dissertation,
these are the unification solver `exact?`, SMT solver `grind`, and the simplifer `simp`.
These all stand as principled ways to develop programs and proofs that would otherwise be tedious for a human.
I use these regularly to speed up the development process.
When working with simp one must be aware of non-terminal `simp`s; `simp`s that do not close a goal,
for these we use the `simp?` tactic to limit the set of available lemmas.
The reason for this has to do with how adding more lemmas can break the normal form `simp` leads to.
Lean's built in linter can handle this.

== Tools used

#let TeX = {
  [T]; "\u{2060}"
  box({h(-0.1667em); box(move(dy: 0.2153em)[E]); h(-0.125em)})
  "\u{2060}"; [X]
}

#let typst = {
  set text(
    size: 1.05em,
    font: "Buenard",
    weight: "bold",
    fill: rgb("#239dad"),
  )
  box({
    text("t")
    text("y")
    h(0.035em)
    text("p")
    h(-0.025em)
    text("s")
    h(-0.015em)
    text("t")
  })
}

To aid the development and communication process I used `git`,
hosting the repository on GitHub.
I also shipped a compiled version of this dissertation publicly,
so my supervisors could read it and have it update live on the web.
The dissertation is written in #typst as it is a feature rich, well documented, and popular #TeX alternative.

== Requirement Analysis <sec:rq>


#quote(block:true, attribution: <rfc2119>)[
The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD", "SHOULD NOT", "RECOMMENDED",  "MAY", and "OPTIONAL" in this document are to be interpreted as described in #link("https://datatracker.ietf.org/doc/html/rfc2119")[RFC 2119].
]

Here the success criteria have become MUSTs,
and improvements have become SHOULD and MAY.
I have done this for the core and each of the extensions of the project.

// TODO: Meantion original critrea

#let moscow(nm, m, s, c, x) = [
// #let f(l) = (n) => box(width: 3em)[#strong(nm + l + [#n])]
// TODO: Make this look more like whats above
#let f(l) = nm + l + "1"
#set enum(numbering: f("M"))
#m
#set enum(numbering: f("S"))
#s
#set enum(numbering: f("O"))
#c
#set enum(numbering: f("N"))
#x
]

=== State-Machine encoding (Core)

#moscow("S", [
+ The SME Stream MUST be implemented in its high universe form. <rq:sme:stream:impl>
+ The equivelence between SME Stream and PA Stream MUST be implemented. <rq:sme:stream:equiv>
+ The SME M MUST be implemented in its high universe form. <rq:sme:impl>
+ The SME M MUST be constant time under destructuring. <rq:sme:fast>
+ The equivelence between SME M and PA MUST be implemented. <rq:sme:equiv>
+ The SME M MUST be able to express the NT monad, @pl:sec:ntm. <rq:sme:ntm>
], [
+ The SME M SHOULD have a coinduction principle. <rq:sme:cind>
], [
+ The SME M MAY have a low universe shifted version @pl:sec:abi. <rq:sme:abi>
+ The SME M MAY have an Interaction tree library @pl:sec:itree. <rq:sme:itree>
+ The SME M MAY have a Productivity Transform @pl:sec:prod. <rq:sme:prod>
// + The SME M MAY be zero cost. <rq:sme:zc>
// + The SME M MAY have a Choice Tree library @pl:sec:ctree. <rq:sme:ct>
], [
+ The SME M MUST NOT have a syntax macro as in @cite:keizer. <rq:sme:macro>
+ There MUST NOT be any work towards coinduction-up-to systems.
])

=== Non-Termination-Monad (Core)<pl:sec:ntm>

#moscow("N", [
+ The NTMonad MUST be implemented using the SME. <rq:ntm:impl>
+ The NTMonad MUST have a monadic bind and return. <rq:ntm:mon>
], [
+ The NTMonad SHOULD be a lawful monad. <rq:ntm:lfm>
], [
], [
])

=== AltRepr Type (Extension)<pl:sec:abi>

#moscow("\u{0410}", [
+ The AltRepr Type MUST be implemented. <rq:abi:impl>
+ The AltRepr Type MUST have an eliminator. <rq:abi:elim>
+ The AltRepr Type MUST have the computational behaviour of the higher type. <rq:abi:opt>
], [
// + The AltRepr Type MUST have the computational behaviour of the higher type.
], [
+ The AltRepr Type MAY be zero-cost. <rq:abi:zc>
], [
// +
])

=== Interaction Trees (Extension)<pl:sec:itree>

#moscow("\u{0406}", [
+ ITrees MUST be implemented. <rq:it:impl>
+ ITrees MUST have strong bisimilarity. <rq:it:sbisim>
+ ITrees MUST have bind and return constructs. <rq:it:mon>
+ ITrees MUST have KTrees (continuation trees). <rq:it:kt>
], [
+ ITrees SHOULD have flow combinators implemented. <rq:it:comb>
+ ITrees SHOULD have a coinduction principle. <rq:it:coind>
+ ITrees SHOULD be a lawful monad. <rq:it:lmon>
], [
+ ITrees MAY have weak bisimilarity implemented. <rq:it:wbisim>
+ ITrees MAY have the monadic interpretation. <rq:it:moni>
], [
+ ITrees MUST NOT implement the family of effects put forward in @cite:itree. <rq:it:eff> 
])

=== Free Monad (Extension)<pl:sec:prod>

#moscow("F", [
+ Free Monad MUST have a futumorphism. <rq:ft:corec>
+ Free Monad MUST have an injector. <rq:ft:inject>
], [
+ Free Monad SHOULD have proof-principles for unfolding the futumorphism. <rq:ft:unfold>
+ Free Monad SHOULD have proof-principles for the injector. <rq:ft:pinject>
], [
+ Free Monad MAY have a universe polymorphic futumorphism. <rq:ft:corecu>
// + Free Monad MAY have a universe transliterator. rq:ft:corecu
// + Free Monad MAY have the ability to reason about _closed_ trees.
], [
+ Free Monad MUST NOT be hetrogenous @cite:coco.
])

// === Choice Trees (Extention)<pl:sec:ctree>
//
// #moscow("C", [
// + 
// ], [
// + 
// ], [
// + 
// ], [
// + 
// ])
//

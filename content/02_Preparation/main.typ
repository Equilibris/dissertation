#import "../utils.typ" : *
#import "../../typ/pfunc.typ" as pfunc: show_map, show_obj, show_decl
#import "@preview/curryst:0.6.0": rule, prooftree
#import "@preview/subpar:0.2.2" as subpar: grid as spg
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/diagraph:0.3.6": raw-render as grender

#set raw(lang: "lean")

////////////////////////////////////////////////////////////////////////////////

== Dependent type theory

We can start by adding a type for Types,
giving us a higher order logic.
Recall back to discrete maths @cite:dm,
how functions between sets $A, B : Type$ $,A -> B$ correspond with a form of arbitrary product,
$B^A eq.triple product_(x : A) B$.
We can generalize this by changing $B$ to be a function $B : A -> Type$,
then letting us write the #box[$Pi$-type]#footnote([
  Some call this a 'dependent product',
  or 'dependent function',
  but this sometimes confuses people so I will simply call it either a Pi,
  or a forall.
]) $product_(x : A) B(x)$.
We can also do the dual construction,
and get #box[$Sigma$-types].
The inference rules for these can be seen in @dtt:fg:psir.
These rules should be familiar as they are the analogous to the rules for $forall, exists$ in the 1st order sequent calculus,
their relationship can be seen in @dtt:eq:pt.
If you are unfamiliar with dependent types,
I recommend viewing them using this relationship.
For a more in depth look at dependent type theory,
read @cite:hottbook.

#spg(
  figure(
    prooftree(
      rule(
        name : [$Pi$f],
        [$A : Type$],
        [$B : A -> Type$],
        [$product_(x : A) B(x)$]
      )
    ),
    caption: [$Pi$-forming rule]
  ),
  figure(
    prooftree(
      rule(
        name : [$Pi$i],
        [$Gamma, x : A tack.r v : B(x)$],
        [$Gamma tack.r lambda x. v : product_(x : A) B(x)$]
      )
    ),
    caption: [$Pi$-intro rule]
  ),
  figure(
    prooftree(
      rule(
        name : [$Pi$e],
        [$Gamma tack.r f : product_(x : A) B(x)$],
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
        [$sum_(x : A) B(x)$]
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
        [$Gamma tack.r chevron.l a, b, chevron.r : sum_(x : A) B(x)$]
      )
    ),
    caption: [$Sigma$-intro rule]
  ),
  figure(
    prooftree(
      rule(
        name : [$Sigma$e],
        [$Gamma tack.r v : sum_(a : A) B(a)$],
        [$Gamma tack.r a : A, b : B[x "/" b] tack.r x : C$],
        [$Gamma tack.r "let" chevron.l a, b chevron.r := v "in" x : C$]
      )
    ),
    caption: [$Sigma$-elimination rule#footnote([
      Technically this isn't the most general eliminator for Sigma's,
      as $C$ can depend on the content of the type.
      For symmetry and simplicity I omit this.
    ])]
  ),
  columns: (auto,auto,auto),
  caption: [Inference rules for $Pi$ and $Sigma$ types],
  label: <dtt:fg:psir>
)
#let ch = footnote([
  #cite(<cite:cltt>, form:"prose") calls this 'categorification',
  as it is only one direction of Curry-Howard.
  @dtt:eq:pt can also just simply be said as 'Curry-Howard',
  but I prefer to highlight the directions of the relationship.
])
$ Pi, Sigma stretch(harpoons.rtlb)^("propositional truncation")_("Categorification"^ch) forall, exists $<dtt:eq:pt>

// === Categorically
//
// Dependent type theory is an extension on the simply typed lambda calculus.
// It is for locally cartesian closed categories,
// what ST$lambda$C is for cartesian categories;
// the semantics of a dependent calculus will be in terms of some LCCC.

#let mpf(a, b) = $chevron.l #a, #b chevron.r$
#let Type = $"Type"$

////////////////////////////////////////////////////////////////////////////////

== Lean

Lean @cite:lean is a popular dependently typed proof assistant,
it is famous for a few reasons.

+ It has Mathlib @cite:mathlib, one of the world's largest repositories of formalized mathematics.
+ It is a proof assistant made for (classical) mathematicians.
+ It has a rich tactic language in which most proofs are written.
+ It has a compiler, and can be used as a general purpose programming language. <lean:li:compiler>

We will mainly focus on point @lean:li:compiler,
as a consequence of this point,
we sometimes have a tension between the logical and computation sides of a proofs/programs.
A classic example of where this occurs is in the elimination principle for strong-induction#footnote[
  This is now,
  for the case of natural numbers,
  fixed as of lean 4.27.
  https://www.youtube.com/watch?v=LOUbbiV0mWc
  https://lean-lang.org/doc/reference/latest/releases/v4.27.0/
].

Lean requires all induction to be structural,
so to do induction over a general well-founded relation,
we need some inductive (@sec:ind),
Lean calls this `Acc` and defines it as seen in @lean:ls:acc.
On this they define a function `WellFounded.fixF`
which allows for strong induction.
This function is quadratic in its runtime,
therefore as a consequence the kernel takes quadratic runtime to execute.

#figure(
  ```lean
inductive Acc {α : Sort u} (r : α → α → Prop) : α → Prop where
  /--
  A value is accessible if for all `y` such that `r y x`, `y` is also accessible.
  Note that if there exists no `y` such that `r y x`, then `x` is accessible.
  Such an `x` is called a _base case_.
  -/
  | intro (x : α) (h : (y : α) → r y x → Acc r y) : Acc r x ```,
  caption: [Definition for `Acc` taken from Lean's GitHub @cite:lean]
)<lean:ls:acc>


It would be unacceptable for a program using strong recursion to be quadratic for a general purpose programming language,
therefore the compiler decides to compile away the usage of `fixF`,
and generates the expected calls in the intermediate representation (LCNF).

We can see that given the source-code @lean:ls:def,
it generates a definition @lean:ls:ker with `Nat.fix` (a variant of `fixF`),
but in the output LCNF we get @lean:ls:ir,
which does not contain any mention of `Nat.fix`,
but rather the expected recursive call.

#let (gcda, gcdb) = partL(read("./Gcd.lean"), 9)

#pad(x: -1cm)[
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
  columns: (1fr, 1fr, 1fr),
  caption: [Gcd as Source, Kernel and LCNF]
)]

This general trick was what inspired me to start this project,
as it demonstrates that there is precedent in Lean4 to have separate logical and executional models.
This is further highlighted by the existence of the `@[implemented_by]` attribute,
which lets you off-load the runtime behaviour of a function to another possibly unsafe definition.
The semantics of `@[implemented_by]` is simply calling the alternative function when not evaluating in the kernel.
Safety of programs using `@[implemented_by]` is a very complex endeavour to verify,
as Lean has a tactic called `native_decide` that runs the generated code outside of the kernel.
I have been told by some of the maintainers of @cite:mathlib,
that all definitions that use `@[implemented_by]` should also be `@[irreducible]`.

== Polynomial functors<sec:poly>

Polynomial functors can be thought of as types generic in some set of arguments,
with a collection of constructors (the head type),
where the children correspond to how many of the polymorphic argument are wanted.
The formal definition is as follows:

A polynomial functor on #Type is:
a head-type,
along with a child family parameterised by the head.
An object of a polynomial functor is a select head type,
and a function form the corresponding child parameterised by the head as seen in @pfunc-math @nlab:polynomial_functor.

$ (h : H) times c_h arrow.r alpha eq.triple sum_(h : H) alpha^(c_h) $ <pfunc-math>

This is a univariate polynomial functor,
this dissertation will mainly focus on multivariate polynomial functors.
Where rather than having a single child,
we have a $n$-tuple of children for an $n$-polynomial functor.

Polynomial functors have all finite products (@pf:fg:const, @pf:fg:prod) and coproducts (@pf:fg:const, @pf:fg:sum).
Polynomial functors are also closed under (co)fixed points so I will write them using a notation like inductives,
in the next examples I have an ellipsis,
in reality multivariate polynomials operate on Type-vectors which come from the category formed by the products $Type^n$ for some $n$,
these are an absolute pain to work with as I will discuss in the implementation#footnote[TODO: Add exact section when it is written].
The justification for writing polynomials using an inductive notation can be found in #cite(<cite:keizer>, form: "prose") and #cite(<cite:qpf>, form: "prose").

// For an explanation of the notation see @a:gpfunctors.

=== Common polynomials

Some examples of common polynomials can be seen in the following figures,
one crucial polynomial I am not providing code for which is complex to define here,
is composition.
The composition polynomial works exactly like composition in primitive recursive functions,
it takes an $n$-polynomial, and $n$ lots of $m$-polynomials, and outputs an $m$-polynomial.
The polynomial notation for this can be found in @cite:mathlib.

We can, using these functors,
make a polynomial compiler from any syntax of the form `P :: var | P × P | P + P | const n` where `var` ranges over named variables.
This compiler is structurally recursive on the syntax.
When you see a var do `Prj` (@pf:fg:prj), a const `Const` (@pf:fg:const),
and for the binary operators first a composition then either `Sum` or `Prod`.

#let code-math(code, math, c, ccode : [Inductive Notation], cmath : [Polynomial], lab : none) = pad(x:-1cm)[#spg(
  figure(code, caption: ccode),
  figure(math, caption: cmath),
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

== Recursion and Inductives<sec:ind>

#set raw(lang: "ocaml")

We are familiar with algebraic datatypes from OCaml.
These are structures freely generated from a set of constructors.
The classic example is a list,
given as two constructors,
`val cons : 'a -> 'a list -> 'a list` and `val nil : 'a list`,
and a way to consume lists `val fold : 'a -> ('b -> 'a -> 'a) -> 'b list -> 'a` (in lean we say `rec` instead of `fold`).
We write this as seen in @cr:ls:list.
This is what is known as an inductive datatype.
Inductive datatypes are well-founded trees#footnote[
  In OCaml, datatypes do not correspond directly to inductives since we can have non-well-founded trees,
  an example is `let rec degen = Cons((), degen)`,
].
Any function that terminates,
must by definition return a finite tree of constructors.
This means fold is guaranteed to terminate too.
All structurally recursive functions can be compiled into a call to fold.
We also have two operations mk and dest.
These form an equivalence (#cite(<cite:lambek>, form: "prose") Corollary 2.4),
giving us the result that the fix-point satisfies $F (mu F) tilde.eq mu F$.

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
== Corecursion and coinductives<sec:coind>

Coinductive datatypes are datatypes we allow to be infinitely deep.
Where inductive datatypes have a `fold : (('a, 'b) f → 'b) → (('a, 'g) f as 'g) → 'b` (rec) to consume them,
coinductives have an `unfold : ('b → ('a, 'b) f) → 'b → (('a, 'g) f as 'g)` (corec) to produce them.
The intuition for this,
is to view it as if a fix F yields an X,
then cofix F yields a lazy X#footnote[
  That is $"fix" (1 + (A times -))$ gives lists,
  then $"cofix" (1 + (A times -))$ gives lazy lists.
].
Another way to view coinductives are as a state-machine,
here the corecursor takes center stage,
we can say a coinductive datatype is a datatype generated by some corecursor state-machine.

=== In OCaml <sec:cf:ocaml>

We can think back to what we did in Foundations of Computer Science,
we made lazy lists simply by thunking recursive occurrences,
this thunking allows infinite structures to exist in finite memory.
This happens because OCaml is CBV.
If we were in Haskell (or any call by name / push-value language),
the definition of icolist would be that of ilist.
Then all we need to do is add a definition of `unfold`, `mk` and `dest`.
All these can be seen in @cr:ls:colist.
We have a coinductive version of Lambek's theorem now too.

#figure(
  raw(ilc, lang: "ocaml", block: true),
  caption: [Definition of colist in OCaml]
)<cr:ls:colist>

The keen eyed will notice and call out that `unfold` is not structurally recursive,
nor even decreasing at all.
This is the key difference between inductives and coinductives;
coinductives can be 'infinitely big'.
Despite not being terminating,
the definition is _productive_ (think of this as coterminating).
Termination is having a complete structure in finite time,
productivity is growing in finite time.

// TODO: Make this into one big section,

=== Streams

Streams are similar to lists,
the only difference is they have no 'nil' constructor.
As one might expect there cant exist any inductive of this form#footnote[
  See the following lean

  #let ns = read("./NoStream.lean")
  #raw(ns, lang:"lean")
].
Though this is a perfectly well-defined coinductive.
Streams and colists are also common in general purpose programming,
Java has Stream,
Rust and Python have Iterator.
This backs up our use cases put forward in the introduction.
We will give concrete implementations of them for each of the encodings as follows.

// === The conaturals
//
// The conaturals arise naturally from failiure:
// Consider a category whos objects are 'fallable computations' $(S : Type, sigma : S -> 1 plus.o S)$,
// and arrows between them are 'failiure preserving' functions,
// that is given $(S,sigma)$ and $(T, tau)$ the arrow is an $f : S -> T$ and a proof $tau compose f = (bb(1) plus.o_m f) compose sigma$.
// Then the terminal object in this category will be conaturals.
// This question is provided by Fiore and Pitts TODO: CITE.
//
// Some phrase this object as 'the natural numbers adjoin infinity',
// this is a subtily different structure.
// There is a non-computable#footnote[
//   This is exactly the halting oracle for PCF actually.
// ] eqvuielence between them.
// The tradeoff is productive generation versus decidable equality,
// and in this case it is much more natural to choose productive generation as it makes the denotation computable.
// One can imagine these structures as sequences of arcs that get closer and closer to a circle,
// then we add one additonal element $omega$ which closes it completely as seen in @cr:fg:conats.
// Another useful way to view conatural numbers is turing machines,
// quotiented by how many steps it takes for them to terminate.
// In this definition there trivially is a unique non-terminiating machine.
// We will use this exact notation when we get to @sec:ntmonad
//
// #let spiral(n, ps,  L : 1.81, k : 1.4, r : 1.0) = {
//   n += 1
//   let pts = ()
//   let angle = -calc.pi / 2
//   for i in range(n) {
//     pts.push((
//       calc.cos(angle * 1rad) * r + ps.at(0),
//       -calc.sin(angle * 1rad) * r + ps.at(1),
//     ))
//     angle -= L / calc.pow(k, i)      // advance CW
//   }
//   let o = pts.map(node)
//   for i in range(n - 1) {
//     let sweep = L / calc.pow(k, i)
//     // For a circular arc subtending φ, bend ≈ φ/2.
//     // Positive bend = curve left of travel direction = CW bulge.
//     // Negate if your arcs bow inward instead of outward.
//     let b = sweep / 2 * (180 / calc.pi) * 1deg
//     o.push(edge(pts.at(i), pts.at(i + 1), "|-|", bend: b))
//   }
//   o
// }
//
// // ── Draw ────────────────────────────────────
// #spg(
//   figure(diagram(spiral(2, (0, 0))), caption: [$n = 2$]),
//   figure(diagram(spiral(6, (0, 0))), caption: [$n = 6$]),
//   figure(diagram(spiral(15, (0, 0))), caption: [$n = omega$]),
//   caption: [A selection of conatural numbers],
//   columns: (1fr,1fr,1fr),
//   label: <cr:fg:conats>
// )

#let MT = [$M$-type]
#let MTs = [$M$-types]

=== The #MT <sec:m>

// The $M$ type is the name given to the types who's semantics are terminal $F$-coalgebra;
The $M$ type is the name given to the cofixed-point of a polynomial functor
#footnote[Often phrased as types who's semantics are terminal $F$-coalgebra.] ;
possibly infinitely deep trees in which each layer is an unfolding of $F$.
This means the implementations must have both:
a corecursor $"corec" : {alpha : "Type"} arrow.r (f : alpha arrow.r F alpha) arrow.r alpha arrow.r M F$,
and a destructor $"dest" : "M" F arrow.r F (M F)$.
These are the functions mentioned in @sec:cf:ocaml.
Often we also want to ship a way to `mk` a new layer,
but we can define this from the two operators above.

When it comes to encoding #MTs in Lean,
there are a few different approaches.
We will focus on two encodings of #MT's,
the State-Machine encoding @sec:m:sme and Progressive Approximation @sec:m:pa (as seen in @cite:mathlib).

==== Progressive approximation encoding <sec:m:pa>

A simple way to encode #MTs,
are as functions emitting trees that must at every level agree.
This corresponds to the limit over the natural number category as the dual of #cite(<cite:adamek>, form: "prose") (see section "Free algebra algorithm").
Agreement is given by them being the same up to the previous depth as seen in @m:fg:agree.
I like to think about agreement as the structure 'crystalizing',
since it can only 'grow' from the ends.

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

In Lean, this encoding is easy to set up.
It can be seen in @m:ls:pa.
The main component which is hard to define is a coinduction theorem (@sec:bisim).
#cite(<cite:bisim>, form: "prose") is an insightful read on this topic.
Luckily for us we do not need to worry about implementing and proving this as @cite:mathlib already provides an implementation of this.
This was ported to Lean4 as part of @cite:keizer.

A major problem with this implementation is the complexity of access.
As you can see in @m:ls:pa in the definition of `corec.o`,
we have to regenerate the entire tree to get a corecursor to the next depth.
There are a few different approaches to solve this that we will compare and contrast in @sec:smevpa.

#let streamf = read("./Stream.lean")
#figure(
  raw(streamf, lang: "lean", block: true),
  caption: [PA Stream in Lean]
)<m:ls:pa>

=== State-machine encoding <sec:m:sme>

The state-machine encoding is the naïve way to implement the #MT.
Given some polynomial functor $F$,
the state-machine encoding is given by:
some type $alpha : "Type"$,
a function $f : alpha arrow.r F alpha$,
and some witness $a : alpha$.
Once this is done there are 3 key problems:
1) The object constructed is only weakly terminal,
2) the object created has no coinduction principle,
3) the object resides in a higher universe.
Let us focus on the first two problems (the 3rd problem is tackled in @sec:abi),
both of these are solved by quotienting over bisimilarity.
The reason this works has to do with how bisimilarity 'hides' the generating type,
making the only operation you can do to access the data a destructure.

== Inductive predicate

An inductive predicate is a least fixed point;
a universal quantification over all relations of a given shape.
An example of an inductive predicate is evenness.
This is defined as a higher-order predicate called the `Shape` in this case,
we use this to restrict the relations we are talking about.
Then we take the universal over this shape and we get what is shown in @ipred:fg:iseven.
It can be shown that this definition is equal to the one generated by the expected Lean code.

#code-math(raw(read("./IsEven.lean"), lang: "lean", block: true),
  ccode: [],
  $
  "shape"_P  &eq.delta P 0 and forall n, P n -> P (n + 2) \
  "Even" (n) &eq.delta forall P, "shape"_P -> P n \
  e_0 : "Even" 0 &eq.delta lambda P "hP". pi_1 ("hP")
  $,
  cmath: [],
  [Evenness inductive predicate, from first principles],
  lab: <ipred:fg:iseven>
)

== Coinductive predicate

Given what we saw in the last section and how we have seen the duality for coinductive and inductive data;
all we must do is dualize this construction.
So we change the universal to an existential, disjuncts to conjuncts,
and flip the arrows (each of these swap left and right adjoints).
This gives us a proof principal with three components.
We now need to define an invariant,
we need to prove the invariant satisfies the restriction,
and that our value is contained in the invariant.

Proving coinductive predicates is very challenging as it requires coming up with the invariant.
This is a kind of proof I had no experience in,
and it took me a while to pick up.
An additional difficulty is,
if you get the invariant wrong,
you have to start completely again and try to come up with something better.
This means that for some of my proofs I wrote hundreds of lines of code that have not made it into the dissertation.

Some languages have facilities to make this better,
these are collectively known as coinduction-up-to.
These are techniques where you can reuse earlier proofs and automatically expand the invariant.
For Rocq a popular library for this is Paco#footnote[TODO CITE],
a lot of harder coinduction proofs use this technique.
Lean does not have this feature,
and it is out of scope for me to add it.
In its place I spend a lot of time picking the shape of the Invariant I need.

=== Bisimilarity <sec:bisim>

Bisimilarity is an equivalence relation on coinductive types.
Two coinductives are bisimilar if,
for every possible choice in a structure A,
there exists a corresponding choice in structure B,
such that you can repeat this procedure.

Bisimilarity is not a well founded relation.
This means we need to define it as a coinductive predicate rather than an inductive one.
Then the proof principal for this will be giving an invariant,
showing the invariant is a bisimilarity,
and our values are contained within the invariant.

A classic example would be to check if the two state-machine are equal.
In @bs:fg:f you see two state-machine for two different regexs.
One could use bisimilarity to show these are the same.
The invariant for this would probably be $(a=q_0 and b=q_0) or (a=q_0 and b=q_2) or (a=q_1 and b=q_1) or (a=q_1 and b=q_3)$.
This also contains the initial state $a = q_0 and b=q_0$.
We also need to show the invariant is a bisimilarity which is a bit more involved.

#pad(x:-1cm)[
#spg(
  figure(
    grender(```dot
digraph ab_star {
    rankdir=LR;
    node [shape=circle];
    start [shape=point];
    q_0 [shape=doublecircle];

    start -> q_0;
    q_0 -> q_1 [label="a"];
    q_1 -> q_0 [label="b"];
}
    ```), caption: [DFA for `(ab)*`]),
  <bs:fg:ab>,
  figure(
    grender(```dot
digraph ab_ab_star_star_nfa {
    rankdir=LR;
    node [shape=circle];
    start [shape=point];
    q_0 [shape=doublecircle];

    start -> q_0;

    q_0 -> q_1 [label="a"];
    q_1 -> q_2 [label="b"];
    q_2 -> q_0 [label="ε"];
    q_2 -> q_3 [label="a"];
    q_3 -> q_2 [label="b"];
}
    ```), caption: [NFA for `(ab(ab*))*`]),
  <bs:fg:abab>,
  columns: (auto, auto),
  caption: [
    Two bisimilar state machines
  ],
  label: <bs:fg:f>
)
]

On streams bisimilarity corresponds to saying that the heads of the streams are equal and then the tails are bisimilar.
A coinductive type has a coinduction principle if bisimilarity implies equality.
Streams and in general cofixed-points of polynomials satisfy this.

////////////////////////////////////////////////////////////////////////////////

== Methodology

// TODO: actuall write this as a methodology

Writing in a proof-assistant is quite different to writing in a general purpose language,
this is especially the case in Lean as it is a hybrid of both styles.
A notable and immediate difference is the prevalence of software testing of programs.
Rather than having tests that can be flakey or incomplete,
in Lean you have checked proofs.

In a conventional programming language,
you can follow Test Driven Development where you constantly refine the specification with additional tests,
which you check as you go through the code.
In Proof Driven Development (PDD, @cite:pdd) you work similarly to TDD,
but now when you have your function,
rather than knowing it works for finite cases,
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
these are the unification solver `exact?` and SMT solver `grind`.
These both stand as principled (as opposed to LLM Slop) ways to develop programs and proofs that would otherwise be tedious for a human.
I use these regularly to speed up the development process.

== Tools used

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
The dissertation is written in #typst as it is a feature rich, well documented, and popular TeX alternative.

== Requirement Analysis <sec:rq>

To expand on the success criteria given in the proposal,
I specified the project using MoSCoW.
Here the success criteria have become MUSTs,
and improvements have become SHOULD.
I have done this for the core and each of the extensions of the project.

#let moscow(nm, m, s, c, x) = [
// #let f(l) = (n) => box(width: 3em)[#strong(nm + l + [#n])]
// TODO: Make this look more like whats above 
#let f(l) = nm + l + "1"
#set enum(numbering: f("M"))
#m
#set enum(numbering: f("S"))
#s
#set enum(numbering: f("C"))
#c
#set enum(numbering: f("W"))
#x
]

=== State machine encoding (Core)

#moscow("S", [
+ The SME Stream MUST be implemented in its high universe form. <rq:sme:stream:impl>
+ The equivelence between SME Stream and PA Stream MUST be implemented. <rq:sme:stream:equiv>
+ The SME M MUST be implemented in its high universe form. <rq:sme:impl>
+ The SME M MUST be constant time under destructuring. <rq:sme:fast>
+ The SME M MUST be able to express the NT monad, @pl:sec:ntm. <rq:sme:ntm>
+ The equivelence between SME M and PA MUST be implemented. <rq:sme:equiv>
], [
+ The SME M SHOULD have a coinduction principle. <rq:sme:cind>
], [
+ The SME M COULD have a low universe shifted version @pl:sec:abi. <rq:sme:abi>
+ The SME M COULD have an Interaction tree library @pl:sec:itree. <rq:sme:itree>
+ The SME M COULD have a Productivity Transform @pl:sec:prod. <rq:sme:prod>
+ The SME M COULD be zero cost. <rq:sme:zc>
// + The SME M COULD have a Choice Tree library @pl:sec:ctree. <rq:sme:ct>
], [
+ The SME M WONT have a syntax macro as in @cite:keizer. <rq:sme:sm>
+ There WONT be any work towards coinduction-up-to systems.
])

=== Non-termination-monad (Core)<pl:sec:ntm>

#moscow("N", [
+ The NTMonad MUST be implemented using the SME. <rq:ntm:impl>
+ The NTMonad MUST have a monadic bind and return. <rq:ntm:mon>
+ The NTMonad MUST be linear in compression. <rq:ntm:fast>
], [
+ The NTMonad SHOULD be a lawful monad. <rq:ntm:lfm>
], [
+ The NTMonad COULD be set up to use @pl:sec:prod. <rq:ntm:prod>
], [
+ The NTMonad WONT have a syntax macro. <rq:ntm:sm>
])

=== ABI Type (Extention)<pl:sec:abi>

#moscow("\u{0410}", [
+ The ABI Type MUST be implemented. <rq:abi:impl>
+ The ABI Type MUST have an eliminator.
+ The ABI Type MUST have the computational behaviour of the higher type.
], [
// + The ABI Type MUST have the computational behaviour of the higher type.
], [
+ The ABI Type COULD be zero-cost.
], [
// + 
])

=== Interaction Trees (Extention)<pl:sec:itree>

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
+ ITrees COULD have weak bisimilarity implemented. <rq:it:wbisim>
+ ITrees COULD have the monadic interpretation. <rq:it:moni>
], [
+ ITrees WONT implement the family of effects put forward in @cite:itree.
])

=== Futumorphic productivity (Extention)<pl:sec:prod>

#moscow("F", [
+ Futumorphic productivity MUST have an in-universe corecursor.
+ Futumorphic productivity MUST have an injector.
], [
+ Futumorphic productivity SHOULD have proof-principles for unfolding the corecursor.
+ Futumorphic productivity SHOULD have proof-principles for the injector.
], [
+ Futumorphic productivity COULD have a cross universe corecursor.
+ Futumorphic productivity COULD have a universe transliterator.
+ Futumorphic productivity COULD have the ability to reason about _closed_ trees.
], [
+ Futumorphic productivity WONT be as expressive as @cite:coco.
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

#import "../utils.typ" : *
#import "../../typ/pfunc.typ" as pfunc: show_map, show_obj, show_decl
#import "@preview/curryst:0.6.0": rule, prooftree
#import "@preview/subpar:0.2.2" as subpar: grid as spg
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

////////////////////////////////////////////////////////////////////////////////

== Dependent type theory

We can start by adding a type for Types,
giving us a higher order logic.
Recall back to discrete maths #footnote([TODO: Cite DM]),
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
For a more in depth at dependent type theory,
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
      For symetry and simplicity I omit this.
    ])]
  ),
  columns: (auto,auto,auto),
  caption: [Inference rules for $Pi$ and $Sigma$ types],
  label: <dtt:fg:psir>
)
#let ch = footnote([
  Steve Awodey calls this 'categorification' @cite:cltt,
  as it is only one direction of Curry-Howard.
  I know @dtt:eq:pt is just a more verbose way of writing 'Curry-Howard',
  but I find it useful to be verbose here.
])
$ Pi, Sigma stretch(harpoons.rtlb)^("propositional truncation")_("Categorification"^ch) forall, exists $<dtt:eq:pt>

=== Categorically

Dependent type theory is an extention on the simply typed lambda calculus.
It is for locally cartesian closed categories,
what ST$lambda$C is for cartesian categories;
the semantics of a dependent calculus will be in terms of some LCCC.

#let mpf(a, b) = $chevron.l #a, #b chevron.r$
#let Type = $"Type"$

////////////////////////////////////////////////////////////////////////////////

== Polynomial functors

A (multivariate) polynomial functor on set#footnote([
  For the readers familiar with category theory,
  simply think of categorical dependent products,
  and (co)limits when I use the set-theoretic language.
]) is:
a head-type,
along with a (collection of) child family(ies) parameterised by the head.
An object of a polynomial functor is a select head type,
and the functions form the corresponding child(ren) parameterised by the head as seen in @pfunc-math
#footnote([
  More can be read on the ncatlab article @nlab:polynomial_functor,
  we restrict ourselves to Set,
  so I recommend skipping to that section.
]).
// Equally this is the justification for why it is called a polynomial.
Moraly polynomial functors can be thought of as types generic in some set of arguments,
with a collection of constructors (the head type),
where the children correspond to how many of the polymorphic argument are wanted.

$ (h : H) times c_h arrow.r alpha eq.triple sum_(h : H) alpha^(c_h) $ <pfunc-math>

Polynomial functors have all finite products and coproducts.
Polynomial functors are also closed under (co)fixed points so I will write them using a notation a la inductives,
I will use notation provided in @cite:keizer.
For an explanation of the notation see @a:gpfunctors.

=== Common pfunctors

==== Constant

#let code-math(code, math, c, ccode : [Inductive Notation], cmath : [Polynomial], lab : none) = spg(
  figure(text(size: 8pt)[#code], caption: ccode),
  figure(math, caption: cmath),
  columns: (1fr, 1fr),
  caption: c,
  label: lab
)

#code-math(```lean
inductive Const
  (T : Type) (a_1 ... a_n : Type) where
  | mk (t : T) ```,
  $ (T : Type) -> mpf(T, lambda i. lambda h. 0) $ ,
  [Constant pfunctor]
)

==== Prj

==== Sum

#code-math(```lean
inductive Sum (A B : Type) where
  | inl : A -> Sum A B
  | inr : B -> Sum A B
  ```,
  $ mpf(BB, lambda { 0, "true" 0 |-> 1, "false" 1 |-> 1, \_ " " \_ |-> 0 }) $,
  [Constant pfunctor]
)

==== Option

==== Functions from fixed types

==== W

==== M

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

=== Lean formalization <pfunctorlean>

=== F-(co)algebras<pfunctofalg>

////////////////////////////////////////////////////////////////////////////////

== Recursion and Inductives<sec:coind>

We are all familiar with algebraic datatypes from OCaml.
These are structures freely generated from a set of constructurs.
The classic example is a list,
given as two constructors,
`cons : 'a -> 'a list -> 'a list` and `nil : 'a list`,
and a way to consume lists `fold : 'a -> ('b -> 'a -> 'a) -> 'b list -> 'a`.
We write this as seen in @cr:ls:list.
This is what is known as an inductive datatype.
Inductive datatypes are well-founded trees#footnote([
  OCaml is quite stupid and allows for non well-founded trees,
  an example is `let rec degen = Cons((), degen)`.
  This is because inductives and coinductives are 'coincident' in OCaml.
  We will come back to this in the next section.
]);
any function that terminates,
must by definition return at most a finite (but unbounded) amount of constructors.
This means fold is guarangteed to terminate too.
All (primitive) recursive functions can be compiled into a call to fold#footnote([TODO: Cite McBride's work]).
We also have two operations mk and dest.
These form an equivalence (Lambek's Theorem)

#let il = read("./IList.ml")
#let eind = 8

#figure(
  raw(takeL(il,0,eind), lang: "ocaml", block: true),
  caption: [Definition of list in OCaml]
)<cr:ls:list>

=== Categorically

#let Set = $bold("Set")$

Given the family of endofunctors on $Set$.
Consider the polynomial given by $L_A = 1 plus.o (underline(A) times.o id)$,
or in its expanded form in @cr:list.
Now recall the definition of the category of #box[$L_A$-algebras]#footnote([TODO: Cite algebra definition]).
The lists we are used to are exactly the initial object in this category.
The initial map takes an algebra $f : L_A (B) -> B$ and yields a map $"fold" : mu L_A -> B$#footnote([TODO: Cite Neel]).
This is exactly what we want,
as expanding the definition or $L_A (B)$ and distrubuting this over the arrows we get the signature above.

$
L_A & (quad X quad &) &= & quad 1 quad        & plus.o quad & (& A       & times.o quad & X &) \
L_A & (quad f quad &) &= & (iota_l compose !) & plus.o_m    & (& bb(1)_A & times.o_m    & f &)
$<cr:list>

== Corecursion and coinductives

// TODO: Write about how they are just state-machine ish
// TODO: What that means is ... sayind dual is useless  
// Step 1: finish this section

Coinductives are the duals of inductives,
they have an operation `unfold` which is the dual of the operation `fold`.

The intuition for this if you have never seen `unfold`'s or coinductives,
simply view it as if a fix F yields an X,
then cofix F yields a lazy X#footnote([
  I. e. $"fix" L_A$ gives lists,
  then $"cofix" L_A$ gives lazy lists.
]).

=== In OCaml

If we were in Haskell (or any call by name / push-value langauge),
the definition of icolist would be exactly that of ilist.
We can think back to what we did in Foundations of Computer Science,
when we made lazy lists we also had to change recursive occurances to be thunked,
this thunking allows infinite structures to exist in finite memory.
This happens because OCaml is CBV.
Then I carry over the definitions mk and dest with minimal change,
and also add the unfold operator i mentioned.
All this can be seen in @cr:ls:colist.
Equally we have a similar theorem to Lambek;
mk and dest are inverses.

#figure(
  raw(takeL(il, eind, 17), lang: "ocaml", block: true),
  caption: [Definition of colist in OCaml]
)<cr:ls:colist>

The keen eyes will notice and call out that `unfold` is not structurally recursive,
or even decreasing at all.
This is the key difference between inductives and coinductives;
coinductives can be 'infinitely big'.
Though it is not decreasing,
assuming gen is terminating it is _productive_
(think of this as coterminating).

=== Streams

Streams are similar to lists,
the only difference is they have no 'nil' constructor.
As one might expect there cant exist any inductive of this form#footnote[
  See the following lean

  #let ns = read("./NoStream.lean")
  #raw(ns, lang:"lean")
].
Though this is a perfectly well-defined coinductive.
Streams are also common in general purpose programming,
Java has Stream,
Rust and Python have Iterator.
From this we can see the use of them.
We will give concrete implementations of them for each of the encodings as follows.

=== The conaturals

The conaturals arise naturally from failiure:
Consider a category whos objects are 'fallable computations' $(S : Type, sigma : S -> 1 plus.o S)$,
and arrows between them are 'failiure preserving' functions,
that is given $(S,sigma)$ and $(T, tau)$ the arrow is an $f : S -> T$ and a proof $tau compose f = (bb(1) plus.o_m f) compose sigma$.
Then the terminal object in this category will be conaturals.
This question is provided by Fiore and Pitts TODO: CITE.

Some phrase this object as 'the natural numbers adjoin infinity',
this is a subtily different structure.
There is a non-computable#footnote[
  This is exactly the halting oracle for PCF actually.
] eqvuielence between them.
The tradeoff is productive generation versus decidable equality,
and in this case it is much more natural to choose productive generation as it makes the denotation computable.
One can imagine these structures as sequences of arcs that get closer and closer to a circle,
then we add one additonal element $omega$ which closes it completely as seen in @cr:fg:conats.
Another useful way to view conatural numbers is turing machines,
quotiented by how many steps it takes for them to terminate.
In this definition there trivially is a unique non-terminiating machine.
We will use this exact notation when we get to @sec:ntmonad

#let spiral(n, ps,  L : 1.81, k : 1.4, r : 1.0) = {
  n += 1
  let pts = ()
  let angle = -calc.pi / 2
  for i in range(n) {
    pts.push((
      calc.cos(angle * 1rad) * r + ps.at(0),
      -calc.sin(angle * 1rad) * r + ps.at(1),
    ))
    angle -= L / calc.pow(k, i)      // advance CW
  }
  let o = pts.map(node)
  for i in range(n - 1) {
    let sweep = L / calc.pow(k, i)
    // For a circular arc subtending φ, bend ≈ φ/2.
    // Positive bend = curve left of travel direction = CW bulge.
    // Negate if your arcs bow inward instead of outward.
    let b = sweep / 2 * (180 / calc.pi) * 1deg
    o.push(edge(pts.at(i), pts.at(i + 1), "|-|", bend: b))
  }
  o
}

// ── Draw ────────────────────────────────────
#spg(
  figure(diagram(spiral(2, (0, 0))), caption: [$n = 2$]),
  figure(diagram(spiral(6, (0, 0))), caption: [$n = 6$]),
  figure(diagram(spiral(15, (0, 0))), caption: [$n = omega$]),
  caption: [A selection of conatural numbers],
  columns: (1fr,1fr,1fr),
  label: <cr:fg:conats>
)

=== The $M$ type <sec:m>

The $M$ type is the name given to the types whos semantics are terminal $F$-coalgebra;
possibly infinitely deep trees in which each layer is an unfolding of $F$ (co-Amadek'sTODO:CITE).
This means the implementations must have both:
A a corecursor $"corec" : {alpha : "Type"} arrow.r (f : alpha arrow.r F alpha) arrow.r alpha arrow.r M F$,
and a destructurer $"dest" : "M" F arrow.r F (M F)$.
Two encodings of $M$-type's are seen in @sec:m:sme and @sec:m:pa.

==== Progressive approximation encoding <sec:m:pa>

A simple way to encode $M$-types,
are as functions emitting trees that must at every level 'agree',
this corresponds to the expected limit over the natural number poset category from co-Amadek's.
Agreement is given by them being the same up to the previous depth as seen in @m:fg:agree.
I like to think about agreement as the structure 'crystalizing',
since it can only 'grow' from the ends.
This is really easy to implement in lean.

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

===== In lean

In Lean, this encoding is very easy to set up.
It can be seen in @m:ls:pa.
The main component which is hard to define is a coinduction theorem (@sec:coindp),
Marcelo Fiore has written on this exact topic and is a very insightful read @cite:bisim
(I recommend reading up to Section 6).
Luckily for us we dont need to worry about implementing and proving this as @cite:mathlib already provides an implementation of this.
This was ported to Lean4 as part of @cite:keizer.

A major problem with this implementation is the complexity of access.
As you can see in @m:ls:pa in the definition of `corec.o`,
we have to regenerate the entire tree to get a corecursor to the next depth.
There are a few different approches to solve this that we will compare and contrast in @sec:smevpa

#let streamf = read("./Stream.lean")
#figure(
  raw(streamf, lang: "lean", block: true),
  caption: [PA Stream in lean]
)<m:ls:pa>

=== State-machine encoding <sec:m:sme>

The state-machine encoding is the naïve way to implement the terminal coalgebra.
Given some polynomial functor $F$, the state-machine encoding is given by:
some type $alpha : "Type"$,
a function $f : alpha arrow.r F alpha$,
and some witness $a : alpha$.
Once this is done there are 3 key problems:
1) The object constructed is only weakly terminal,
2) the object created has no coinduction principle,
3) the object resides in a higher universe.
Let us first focus on the first two problems,
both of these are solved by quotienting over bisimilarity.
The reason this works has to do with how bisimilarity 'hides' the generating type,
making the only operation you really can do to access the data a destructure.


== Inductive predicate

An inductive predicate is a least fixed point,
it is a universal quantification over all relations of a given shape.
An example of an inductive predicate is whether a number is even.
We begin by defining this as a higher order predicate,
the shape,
we define this as seen in @ipred:fg:iseven.
It can be shown that this definition is equivalent to the usual one.

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

// TODO: Fix this section

Given what we saw in the last section and what we have seen when speaking about conductive data we now now all we must do is dualize this construction.
So we change the universal to an existential and the disjuckt to a conjunct.
This gives us a proof principal with tree components.
We now need to define the entry predicate,
we need to proof it satisfy the restriction and finally that it contains our value.

=== Coinduction up-to

When proving coinductive predicates it is often useful not to include the entire relation upfront.
Instead we use libraries such as CITATION PACO.
This allows for providing an initial relation then later automatically extending it to for example include reflexivity.
Sadly Lean does not have such libraries.

== Bisimilarity

In this section we will talk about the equivalence relation on co inductive types called bisimilarities.
Morally two things are bisimilar if for every possible choice in a structure A there exists a corresponding choice in structure B such that you can repeat this procedure from the new point.

Onstreams this corrensponds to saying that the heads of the streams are equal and then the tails are bisimilar.
As you may note this is not a well founded relation.
This means we ned to define it as a coinductive predicate rather than an inductive one.
Then the proof principal for this will be giving a relation,
showing it is a bisimilary and that it holds on our values.

=== Coinduction principle<sec:coindp>

A coinductive type has a conduction principle is bisimilarites implies equality.
For the SME this will be harder to show.

////////////////////////////////////////////////////////////////////////////////

== Tools used

== Requirement Analysis <sec:rq>

To expand on the success critera given in the proposal,
I specified the project using MoSCoW.
Here the success critera have become MUSTs,
and improvements have become SHOULD.
I have done this for the core and each of the extentions of the project.

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
+ The SME M COULD have a Choice Tree library @pl:sec:ctree. <rq:sme:ct>
+ The SME M COULD be zero cost. <rq:sme:zc>
], [
+ The SME M WONT have a syntax macro a la @cite:keizer. <rq:sme:sm>
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
+ 
], [
+ 
], [
+ 
], [
+ 
])

=== Interaction Trees (Extention)<pl:sec:itree>

#moscow("\u{0406}", [
+ ITrees MUST be implemented. <rq:it:impl>
+ ITrees MUST have strong bisimilarity. <rq:it:sbisim>
+ ITrees MUST have bind and return constructs. <rq:it:mon>
+ ITrees MUST have KTrees. <rq:it:kt>
], [
+ ITrees SHOULD have flow combinators implemented. <rq:it:comb>
+ ITrees SHOULD have a coinduction principle. <rq:it:coind>
+ ITrees SHOULD be a lawful monad. <rq:it:lmon>
], [
+ ITrees COULD have weak bisimilarity implemented. <rq:it:wbisim>
+ ITrees COULD have the monadic interpretation. <rq:it:moni>
], [
+ 
])

=== Futumorphic productivity (Extention)<pl:sec:prod>

#moscow("F", [
1. 
], [
1. 
], [
1. 
], [
1. 
])

=== Choice Trees (Extention)<pl:sec:ctree>

#moscow("C", [
+ 
], [
+ 
], [
+ 
], [
+ 
])


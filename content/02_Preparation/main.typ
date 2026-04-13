#import "../utils.typ" : *
#import "../../typ/pfunc.typ" as pfunc: show_map, show_obj, show_decl
#import "@preview/curryst:0.6.0": rule, prooftree
#import "@preview/subpar:0.2.2" as subpar: grid as spg
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

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
  I know @dtt:eq:pt is just a more verbose way of writing 'Curry-Howard',
  but I find it useful to be verbose here.
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
we sometimes have a tension between the logical and computation sides of a proof.
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
This function is at least quadratic in its runtime,
therefore as a consequence the kernel takes this quadratic runtime to execute.

#figure(
  ```lean
inductive Acc {α : Sort u} (r : α → α → Prop) : α → Prop where
  /--
  A value is accessible if for all `y` such that `r y x`, `y` is also accessible.
  Note that if there exists no `y` such that `r y x`, then `x` is accessible.
  Such an `x` is called a _base case_.
  -/
  | intro (x : α) (h : (y : α) → r y x → Acc r y) : Acc r x ```,
  caption: [Definition for `Acc` taken from @cite:lean's GitHub]
)<lean:ls:acc>


It would be unacceptable for a program using strong recursion to be quadratic for a general purpose programming language,
therefore the compiler decides to simply not compile the definition using `fixF`,
and generates the expected intermediate representation.

We can see that given the source-code @lean:ls:def,
it generates a definition @lean:ls:ker with `Nat.fix` (a variant of `fixF`),
but in the output lean intermediate-representation we get @lean:ls:ir,
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
as it demonstrates that there is precident in Lean4 to have seperate logical and executional models.
This is further highlighted by the existence of the `@[implemented_by ...]` attribute,
which lets you off-load the runtime behaviour of a function to another possibly unsafe definition.
The semantics of `@[implemented_by]` is simply calling the alternative function when not evaluation in the kernel.
Safety of programs using `@[implemented_by]` is a very complex endeavour to find,
as lean has a tactic called `native_decide` that runs the generated code outside of the kernel.
I have been told by some of the maintainers of @cite:mathlib,
that all definitions that use `@[implemented_by]` should also be `@[irreducible]`.

== Polynomial functors<sec:poly>

I will give two definitions now in the next paragraphs,
these will be unary and (multivariate) polynomial functors respectively.

Morally polynomial functors can be thought of as types generic in some set of arguments,
with a collection of constructors (the head type),
where the children correspond to how many of the polymorphic argument are wanted.
The formal definition is as follows:

A (multivariate) polynomial functor on #Type#footnote[
  For the readers familiar with category theory,
  simply think of categorical dependent products,
  and (co)limits when I use the set-theoretic language.
] is:
a head-type,
along with a (collection of) child family(ies) parameterised by the head.
An object of a polynomial functor is a select head type,
and the functions form the corresponding child(ren) parameterised by the head as seen in @pfunc-math
#footnote[
  More can be read on the ncatlab article @nlab:polynomial_functor,
  we restrict ourselves to Set,
  so I recommend skipping to that section.
].
// Equally this is the justification for why it is called a polynomial.

$ (h : H) times c_h arrow.r alpha eq.triple sum_(h : H) alpha^(c_h) $ <pfunc-math>

Polynomial functors have all finite products (@pf:fg:const @pf:fg:prod) and coproducts (@pf:fg:const @pf:fg:sum).
Polynomial functors are also closed under (co)fixed points so I will write them using a notation a la inductives,
in the next examples I have an ellipsis,
in reality multivariate polynomials operate on type-vectors which come from the category formed by the products $Type^n$ for some $n$,
these are an absolute pain to work with as I will discuss in the implementation#footnote[TODO ADD EXACT SECTION].
The justification for writing pfunctors using an inductive notation can be found in #cite(<cite:keizer>, form: "prose") and #cite(<cite:qpf>, form: "prose").

// For an explanation of the notation see @a:gpfunctors.

=== Common polynomials

Some examples of common polynomials can be seen in the following figures,
one crucial polynomial I am not mentioning which is maybe the most useful one but also most complex one,
is composition.
The composition polynomial works exactly like composition in primitive recursive functions,
it takes a $n$-polynomial, and $n$ lots of $m$-polynomials, and outputs an $m$-polynomial.
The polynomial notation for this can be found in @cite:mathlib.

We can now using these functors make a polynomial compiler from any syntax of the form `P :: var | P × P | P + P | const n` where `var :: x | y | ...`,
this compiler is trivially structurally recursive on the syntax,
simply when you see a var do `Prj` (@pf:fg:prj), a const `Const` (@pf:fg:const),
and for the binary operators first a composition then the expected polynomial.

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

We are all familiar with algebraic datatypes from OCaml.
These are structures freely generated from a set of constructors.
The classic example is a list,
given as two constructors,
`val cons : 'a -> 'a list -> 'a list` and `val nil : 'a list`,
and a way to consume lists `val fold : 'a -> ('b -> 'a -> 'a) -> 'b list -> 'a` (in lean we say `rec` instead of `fold`).
We write this as seen in @cr:ls:list.
This is what is known as an inductive datatype.
Inductive data-types are well-founded trees#footnote[
  In OCaml, data-types do not correspond directly to inductives since we can have non-well-founded trees,
  an example is `let rec degen = Cons((), degen)`,
];
any function that terminates,
must by definition return at most a (unbounded) finite tree of constructors.
This means fold is guaranteed to terminate too.
All (structural) recursive functions can be compiled into a call to fold#footnote[NOTE FOR REVIEW: does this need a citation?].
We also have two operations mk and dest.
These form an equivalence (#cite(<cite:lambek>, form: "prose") Corollary 2.4),
giving us the result that the fix-point is exactly that $F (mu F) tilde.eq mu F$.

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

// TODO: Write about how they are just state-machine ish
// TODO: What that means is ... sayind dual is useless  
// Step 1: finish this section

Coinductive datatypes are datatypes we allow to be infinitely deep.
Where inductive datatypes have a `fold : (('a, 'b) f → 'b) → (('a, 'g) f as 'g) → 'b` (rec) to consume them,
coinductives have an `unfold : ('b → ('a, 'b) f) → 'b → (('a, 'g) f as 'g)` (corec) to produce them.
The intuition for this if you have never seen `unfold`'s or coinductives,
simply view it as if a fix F yields an X,
then cofix F yields a lazy X#footnote[
  I. e. $"fix" (1 + (A times -))$ gives lists,
  then $"cofix" (1 + (A times -))$ gives lazy lists.
].
Another way to view coinductives are as a state-machine,
here the corecursor takes center stage,
we can say a coinductive datatype is a datatype generated by some corecursor state-machine.

=== In OCaml

We can think back to what we did in Foundations of Computer Science,
we made lazy lists simply by thunking recursive occurrences,
this thunking allows infinite structures to exist in finite memory.
This happens because OCaml is CBV.
If we were in Haskell (or any call by name / push-value language),
the definition of icolist would be exactly that of ilist.
Then all we need to do is add a definition of `unfold`, `mk` and `dest`.
All these can be seen in @cr:ls:colist.
We have a coinductive version of Lambek's theorem now too.

#figure(
  raw(ilc, lang: "ocaml", block: true),
  caption: [Definition of colist in OCaml]
)<cr:ls:colist>

The keen eyes will notice and call out that `unfold` is not structurally recursive,
nor even decreasing at all.
This is the key difference between inductives and coinductives;
coinductives can be 'infinitely big'.
Though it is not decreasing,
assuming gen is terminating it is _productive_
(think of this as coterminating).
As termination is having a complete structure in finite time,
productivity is growing in finite time.

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
The $M$ type is the name given to the cofixed-point I mentioned
#footnote[Often phrases as types who's semantics are terminal $F$-coalgebra.];
possibly infinitely deep trees in which each layer is an unfolding of $F$ (dual of Lambek's @cite:lambek).
This means the implementations must have both:
A corecursor $"corec" : {alpha : "Type"} arrow.r (f : alpha arrow.r F alpha) arrow.r alpha arrow.r M F$,
and a destructor $"dest" : "M" F arrow.r F (M F)$.
These are the what we mentioned above,
often we also want to ship a way to `mk` a new layer,
but we can define this from the two operators above.

When it comes to encoding #MTs in lean,
there are a few different approaches.
We will focus on two encodings of #MT's,
the State-Machine encoding @sec:m:sme and Progressive Approximation @sec:m:pa (as seen in @cite:mathlib).

==== Progressive approximation encoding <sec:m:pa>

A simple way to encode #MTs,
are as functions emitting trees that must at every level 'agree',
this corresponds to the expected limit#footnote[TODO: is this a colimit] over the natural number poset category from the dual of #cite(<cite:adamek>, form: "prose")'s "Free" algebra algorithm.
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
#cite(<cite:bisim>, form: "prose") is a very insightful read on this topic.
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
Given some polynomial functor $F$,
the state-machine encoding is given by:
some type $alpha : "Type"$,
a function $f : alpha arrow.r F alpha$,
and some witness $a : alpha$.
Once this is done there are 3 key problems:
1) The object constructed is only weakly terminal,
2) the object created has no coinduction principle,
3) the object resides in a higher universe.
Let us first focus on the first two problems (the 3rd problem is tackled in @sec:abi),
both of these are solved by quotienting over bisimilarity.
The reason this works has to do with how bisimilarity 'hides' the generating type,
making the only operation you really can do to access the data a destructure.

== Inductive predicate

An inductive predicate is a least fixed point;
it is a universal quantification over all relations of a given shape.
An example of an inductive predicate is whether a number is even.
We begin by defining this as a higher order predicate,
the shape,
we define this as seen in @ipred:fg:iseven.
It can be shown that this definition is equal to the one generated by the expected lean code.

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
we now know all we must do is dualize this construction.
So we change the universal to an existential, disjuncts to conjuncts,
and flip the arrows (each of these swap left and right adjoints).
This gives us a proof principal with three components.
We now need to define an invariant,
we need to proof the invariant satisfy the restriction,
and that our value is contained in the invariant.

Proving coinductive predicates is very challenging as it requires coming up with the invariant,
this is a kind of proof I initially had very little experience in and took me a while to pick up.
An additional difficulty is,
if you get the invariant wrong,
you just have to start completely again and try to come up with something better.
This means that for some of my proofs I hundreds of lines of code that have not made it into the dissertation.

Some languages have facilities to make this better,
these are collectively refered to as coinduction-up-to.
These are techniques where you can write parts of a proof somewhere in a certian style,
then reuse them other proofs.
For Rocq a popular library for this is Paco TODO CITE,
for which a lot of the harder proofs often use.
Lean does not have this feature,
and it is out of scope for me to add it.

// === Coinduction up-to
//
// When proving coinductive predicates it is often useful not to include the entire relation upfront.
// Instead we use libraries such as CITATION PACO.
// This allows for providing an initial relation then later automatically extending it to for example include reflexivity.
// Sadly Lean does not have such libraries.

== Bisimilarity

In this section we will talk about the equivalence relation on co inductive types called bisimilarities.
Morally two things are bisimilar if for every possible choice in a structure A there exists a corresponding choice in structure B such that you can repeat this procedure from the new point.

On streams this corrensponds to saying that the heads of the streams are equal and then the tails are bisimilar.
As you may note this is not a well founded relation.
This means we need to define it as a coinductive predicate rather than an inductive one.
Then the proof principal for this will be giving a relation,
showing it is a bisimilary and that it holds on our values.

=== Coinduction principle<sec:coindp>

A coinductive type has a conduction principle is bisimilarites implies equality.
For the SME this will be harder to show.

////////////////////////////////////////////////////////////////////////////////

== Methodology

Writing in a proof-assistant is quite different than writing in a general purpose language,
this is especially the case in Lean as it is a hybrid of both styles.
A notable and immediate difference is the prevalence of software testing of programs.
Rather than having tests that can be flakey or incomplete,
in lean you have checked proofs.
From this in a conventional programming language,
you can for example follow TDD where you constantly refine the specification with additional tests,
which you check as you go through the code.
Proof Driven Development (PDD, @cite:pdd) perfect for this in Lean after seeing success in Idris.
In PDD you work similarly to TDD,
but now when you have your function,
rather than knowing it works for finite cases,
you can be guaranteed that it works.
Furthermore, the proofs can serve to enrich the main artifact.
This will be seen in the ITree implementation as well as the futumorphic productivity.
Lean makes working in this style a delightful experience using constructs such as `#check`, `#print` and `#eval`,
one can see exactly what a function is / is doing.
These can also be turned more conventional tests using `#guard_msgs in`,
which raises a compile error upon an output changing.
Lean also has great automation features which I use at many points in the dissertation,
these are the unification solver `exact?` and SMT solver `grind`.
These both stand as principled (as opposed to LLM Slop) ways to develop programs and proofs that would otherwise be tedious for a human.

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
+ The SME M WONT have a syntax macro a la @cite:keizer. <rq:sme:sm>
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
+ Futumorphic productivity MUST have a in universe corecursor.
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

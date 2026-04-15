#import "../utils.typ": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/colorful-boxes:1.4.3": colorbox
#import "@preview/diagraph:0.3.6": render as grender
#import "@preview/tdtr:0.5.5" : tidy-tree-graph, tidy-tree-draws
#import "@preview/pintorita:0.1.4"
#import "@preview/subpar:0.2.2" as subpar: grid as spg
#show raw.where(lang: "pintora"): it => pintorita.render(it.text)

#set raw(lang: "lean")

// TODO
#let impl(content, path) = align[Addressing: #content, Path: #raw(path)]

This chapter describes the implementation of each of the requirements stated in @sec:rq.
I will break it down into a common section,
then go by induvidual components.
I will also mention which parts are in process of being upstreamed and which parts are already in @cite:mathlib.

// TODO: Fix these
unnacc
- rq:sme:fast
- rq:sme:ct

== Repository overview

The Lean component of this repository,
and how they relate to each of the requirements can be seen in the list below.
Additionally the import graph can be seen in @rep:fg:import

// TODO Make this take up less page space. Make it alternate between horizontal and vertical

#let box(boxc) = node.with(snap: -1, fill: boxc.lighten(90%), stroke: boxc)

#let sl = 2
#figure(
  diagram(
    cell-size: 4mm,
    box(teal)(enclose : (<slib>, <dt>)),

    node((1,1-sl), [PA Impl], name: <spa>),
    edge("->"),
    node((2,0-sl), [Equiv], name : <seq>),
    edge("<-"),
    node((2,1-sl), [SME Impl], name: <ssme>),
    box(teal)(align(top + left)[Stream], enclose: (<spa>, <seq>, <ssme>, (0,-1)), snap: -1, name: <s>),

    node((1,1), [PreM], name: <prem>),
    edge("->"),
    node((2,1), [SM], name : <sm>),
    edge("->"),
    node((3,0), [HpLuM], name: <hplum>),
    edge("<-"),
    node((2,0), [Equiv], name: <peq>),
    edge(<sm>, <peq>, "->"),
    box(teal)(align(top+left)[Polynomial], enclose: (<prem>,<sm>,<hplum>,<peq>, (0,1)),name : <slib>),

    edge(<hplum>, (3,2), <dtd>, "->"),

    node((2,2), [DT Defs], name: <dtd>),
    edge("->"),
    node((1,3), [DT Corec],name : <dtc>),
    edge(<dtd>,<dtf>,"->"),
    node((2,3), [DT Inject], name: <dtf>),
    box(teal)(align(top+left)[Deep thunks], enclose: (<dtf>,<dtd>,<dtc>, (0,2)), name: <dt>),

    edge(<hplum>, (3, 4), (2,4), <clib>, "->"),
    edge(<dtc>,   (1, 4), (2,4), <clib>, "->"),
    edge(<dtf>,   (2,4), <clib>, "-"),

    node((2,5), [Coinduction library], name: <clib>),

    node((3, -1), [ABI], name: <abi>),
    edge(<abi>, <hplum>, "->"),
    box(teal)([ABI], enclose: (<abi>,) ),

    edge(<abi>, (3.5, -1), <abil>, "->"),
    node((3.5,5), [ABI Type], name: <abil>),

    edge(<hplum>, <itd>, "->"),
    node((4,0), [ITree Defs], name:<itd>),
    edge("->"),
    node((4,1), [Monad], name:<itm>),
    edge("->"),
    node((4,2), [Iter], name:<iti>),
    node((5,0), [WBisim], name:<wbs>),
    edge("->"),
    node((5,1), [Congr], name:<wbsc>),
    edge("->"),
    node((5,2), [Congr Iter], name:<wbsi>),
    edge(<itd>, <wbs> , "->",),
    edge(<itm>, <wbsc>, "->",),
    edge(<iti>, <wbsi>, "->",),

    box(teal)(enclose: (<itd>, <wbsi>) ),
  )
)

// #colorbox(title: [Main lean section])[
// #tidy-tree-graph(
//   draw-edge: tidy-tree-draws.horizontal-vertical-draw-edge
// )[
// - SME
//   - ABI.lean
//   // - Basic.lean
//   // - Examples
//   //   - AMP
//   //     - Product.lean
//   //     - Supo1.lean
//   //   - FunctionPFunctor.lean
//   - ITree @rq:it:impl, @rq:sme:itree
//     - Bisim.lean @rq:it:sbisim
//       - Interp.lean @rq:it:moni
//         - KTree.lean @rq:it:kt
//     - Monad.lean @rq:it:mon, @rq:it:lmon
//       - MonadIter.lean
//         - Combinators.lean @rq:it:comb
//     - WBisim.lean @rq:it:wbisim
//       - Congr.lean
//         - Defs.lean
//            - IterCongr.lean
//               - Monad.lean
//                 - Step.lean
//   - M
//     - DT.lean @rq:sme:prod
//       - Defs.lean
//         - DTSum.lean
//           - Corec.lean
//             - Bind.lean
//               - Closed.lean
//                 - Factorize.lean
//                   - CorecEq.lean
//                     - Flat.lean
//                       - Inject.lean
//                         - ULift.lean
//     - PreM.lean @rq:sme:impl, @rq:sme:cind
//       - SM.lean @rq:sme:impl, @rq:sme:cind
//         - Equiv.lean @rq:sme:equiv
//           - HpLuM.lean @rq:sme:abi, @rq:sme:cind
//             - HpLuCofix.lean
//   - NTMonad @rq:sme:ntm
//   - PFunctor
//     - EquivP.lean
//       - NatIso.lean
//         - Prj.lean
//           - Utils.lean
//   - Stream
//     - Equiv.lean @rq:sme:stream:equiv
//       - PDefs.lean
//         - SDefs.lean @rq:sme:stream:impl
//   - ForMathlib
//     - Data
//       - PFunctor
//         - Multivariate
//           - Basic.lean
//           - M.lean
//       // - QPF
//       //   - Multivariate
//       //     - Basic.lean
//       //     - Constructions
//       //       - Cofix.lean
//       - TypeVec.lean
//       - ULift.lean
// ]
// ]

== Common

=== Transiteration

A family of functions,
that keep solving problems throughout this dissertation are what I call transliterations.
Given some parameter span $X$#footnote([This not necessarily a type, as lean does not have omega-types (Set$omega$ from Agda).]),
either in some $Type$,
or more commonly over some universe $cal(U)$.
We define a transliteration on $X$ as a family of functions $t_(a,b) : X a -> X b$,
such that they are closed under composition $t_(b,c) compose t_(a,b) = t_(a,c)$#footnote([
  This is very similar to saying it's an idempotent,
  but technically $t_(b,c)$ and $t_(a,b) $ arent the same function.
]),
and the self-path is identificaion $t_(a,a) = id$.

The trivial instantiation of a transliteration is a `cast`#footnote([
  Or if you read @cite:hottbook, this is called `transport`.
]),
here we pick $X$ as equal types,
obviously `cast aa = id` and `cast bc ∘ cast ab = cast (ab.trans bc)`.
One could even say that a transliteration is a function that behaves like `cast`.

An example we will keep defining is universe transliteration,
here we take $X = "ULift"_((-))$,
using this we define the transiteration as seen in @tr:ls:code.
This is the closest we get to having omega-types and cumilativity in lean;
as long as the function is applied at a usage of ULift it all just works.
We will use this function to define transliteration between universe-lifted polynomials,
we will see more of this in @sec:ulift_p.

#let f = takeL(read("../../sme/Sme/ForMathlib/Data/ULift.lean"), 2, 11)

#figure(
  raw(f, lang : "lean", block:true),
  caption: [Transliteration between universes of types]
)<tr:ls:code>

Another major usage of a transiteration was used when defining the eliminator for `ABI`,
I will discuss this more when we get to @sec:abi.
This was where I first discovered transliteration,
and made it possible to define a universe-polymorphic eliminator.

////////////////////////////////////////////////////////////////////////////////

=== Expanding the progressive approximation theory

#impl([], "sme/Sme/ForMathlib/{PFunctor/*,TypeVec.lean}")

During the feasability assesment I noticed that,
in the current formalised theory of polynomials,
the equivilence wouldn't even type-check.
This stemmed from a problem with the corecursive principle for the M type in the old implementation.
$"corec" : {alpha : "TypeVec".{cal(U)} n} arrow {beta : "Type" cal(U)} arrow (g : beta → P (alpha ::: beta)) arrow beta arrow M alpha$
#footnote(link("https://github.com/leanprover-community/mathlib4/blob/7a60b315c7441b56020c4948c4be7b54c222247b/Mathlib/Data/PFunctor/Multivariate/M.lean#L152-L154")) @cite:mathlib.
The problem here is that both $alpha$ and $beta$ have to both reside in $cal(U)$.
Solving this is done through the next two sections.

==== Universe lifting of polynomial functors.<sec:ulift_p>

The main problem caused here comes from the fact that lean isnt cummulative.
This means it is impossible to express a universe hetrogouns typevector.
In other words $alpha ::: beta$ is only typable if $alpha : "TypeVec".{cal(U)} n$ and $beta : "Type" cal(U)$.
The natural way of solving this is using the supremum in universe levels you get from
$"ULift" : "Type" cal(U) arrow "Type" (max cal(U) cal(V))$.
This means we can have $beta : "Type" cal(U)$ and $alpha : "Type" cal(V)$,
then ulift both of them to a common universe $"ULift" alpha ::: "ULift" beta : "TypeVec".{max cal(U) cal(V)} (n+1)$
#footnote[Note we overload ULift as a notation to refer to lifting TypeVecs as well].

Noticable the next hurdle we encounter is that PFunctors are restricted to a universe level.
Recall the definition from @sec:poly.
Observe how for a $"MvPfunctor".{cal(U)} n$,
we require that both the head and child reside in $cal(U)$.
This will also cause problems,
as looking back at the definition of the corecursor,
we will require $P$ to be able to accept $"ULift" alpha ::: "ULift" beta$.
If we do not add the ability to lift $P$,
the unifier will force $cal(U) = cal(V)$,
thereby invalidating all the work we did in the previous section.
Luckily lifting a PFunctor is relatively easy.
We define it as $"ULift" P eq.delta chevron.l "ULift" P.1, lambda x mapsto "ULift" (P.2 x."down") chevron.r$.
This works and now we can move on to generalizing the corecursor.
#footnote[
  TODO: Speak with JV / W to see if this might be done in the lit,
  Ex : Locally presentable and accessable categories Adameck roshiski
].

==== Generalizing the corecursor

#impl([], "[UPSTREAMED],sme/Sme/PFunctor/ForMathlib/M.lean")

Now with all the work in the previous section,
first we generalize a helper function#footnote([Done in TODO: PR NUMBER ]),
then we can define
$"corecU" : {alpha : "TypeVec".{cal(U)} n}
  arrow {beta : "Type" cal(V)}
  arrow (g : beta → "ULift" P ("ULift" alpha ::: "ULift" beta))
  arrow beta
  arrow M.{cal(U)} alpha$.
Notably we are able to fit the object into $cal(U)$
(this will not be the case for the SME).

`corecU` and `dest` satisfy an unfolding equation.
This is more complex than it used to be as we now need to lower before we continue with the mapping.

////////////////////////////////////////////////////////////////////////////////

== Stream implementation

#impl([@rq:sme:stream:impl, @rq:sme:stream:equiv], "sme/Sme/Stream/*")

As proving these equivleneces is challenging I decidede I would start by implementing it for the special case of streams.
Streams are the text-book coinductive datatype that most people know as mentioned in @sec:coind.
Therefore I expected this to be pedogodical to implement.

=== SME
#impl([@rq:sme:stream:impl], "sme/Sme/Stream/SDefs.lean")

First I set up a class (can't be a #Type as it varies through universe levels) of prestreams,
these correspond to the corecurisve principle holding their type.

I had to define hd and tl for streams here corresponding to the destructors of streams.
Care had to be taken to ensure that the definition would work under a quotient as well.

Then I defined a bisimilarity relation;
heads being equal and tails bisimilar as seen in @sec:bisim.
I proved this was an equivalence relation (reflexive, symmetric, transitive).
Using this I defined a setoid on PreStreams.

The definition of an SME Stream is then preobjects quotiented by this setoid.
Quotients are famously a pain to work with.
When lifting the destructors from PreStreams to Streams I have to go through the lifting function of Quotients.
When lifting to a quotient one has to provide the lifting function,
then a proof that the function is stable under quotienting.
Initially these proofs were in tactic-mode,
but were rewritten in term-mode for readability.
The corecursor was simpler to define,
it is just the constructor for PreStreams under a Quotient introduction.

The next step was defining a coinduction principle,
in the code this is called `bisim` to align to convention with @cite:mathlib.
The proof of this proceeds by Quotient soundness anc can be found in `SDefs.lean`.

Parts of this definition can be seen in @stream:fg:sme.

=== PA
#impl([], "sme/Sme/Stream/PDefs.lean")

To implement PA Streams,
I had to first implement the Stream's base functor,
this is quite easy for streams as they have one constructor (so a head of $1$),
and each of the families only hold one instance of the value (so child $lambda i (). 1$).
From here I defined the destructors of streams this is as simple as calling the child with the correct indicies.

For symetry I also defined a syntactically identical bisimilarity relation on PA Streams,
and for this I also prove a coinduction principle for PStreams of this relation.
This proof proceeded by using the coinduction principle on general polynomials,
which is a very tideous principle to work with as it requires unfolding the polynomial.
When it was done I cleaned it up and this can be seen in `PDefs.lean`.

The corecursor wasn't as simple as for the case of SME Streams either,
though all it required was doing a series of pattern-matches to get the right structure.
I will do something similar like this for ITrees and the NTMonad as well.

Parts of this definition can be seen in @stream:fg:pa.

=== Proving the equivalence
#impl([@rq:sme:stream:equiv], "sme/Sme/Stream/Equiv.lean")

The functions of this equivalence correspond to:
the corecursors parameterised by the destructors of the opposite type.
Proving that these are inverses was slightly involved,
I toyed around with a few different relations trying to make it work.
In the end I landed on the quite straight forward equality as seen in the @stream:fg:equiv.
This solved very nicely and made the entire proof quite small after cleaning.

Having done this I was ready to approach the case of the polynomial.
This turned out to be harder than I expected for 2 reasons.
1. Observant readers may notice the statement I proved is subtily the wrong statement.
  At the time I did not see this,
  but the equivalence should not be `SStream.{u, u} A ≃ PStream A`,
  but rather `SStream.{u, max u v} A ≃ PStream A`.
  This statement is actually dramatically harder to prove.
2. When you look at the proofs,
  in the bisimilarity there are `rfl`s,
  this is because the statements are *definitionaly* equal ($beta$,$eta$-equivalent).
  For general polynomials this will not be the case and also explode ever so slightly.

#let pdef = read("../../sme/Sme/Stream/PDefs.lean")
#let sdef = read("../../sme/Sme/Stream/SDefs.lean")
#let equiv = read("../../sme/Sme/Stream/Equiv.lean")

#pad(x: -1cm)[
#spg(
  figure(
    raw(takeL(pdef, 12, 33), block: true),
    caption: [PA Stream]
  ),
  <stream:fg:pa>,
  figure(
    raw(takeL(sdef, 53, 77), block: true),
    caption: [SME Stream]
  ),
  <stream:fg:sme>,
  figure(
    raw(takeL(equiv, 4, 18), block: true),
    caption: [Equivalence]
  ),
  <stream:fg:equiv>,
  columns: (1fr, 1fr, 1fr),
  caption: [Key code involved in Stream equivlance]
)
]

////////////////////////////////////////////////////////////////////////////////

== State machine encoding of M-Types

#impl([@rq:sme:stream:impl, @rq:sme:stream:equiv], "")

Noting the definition of corecU,
one might wonder if you could define M from first principles for this.
The problem one encounters is one of universes.
As seen in the definition above,
if one were to define a type whos construcor is directly the corecU definiton,
it would hold a $beta : "Type" cal(V)$.
This then forces the object to reside in
$"Type" max cal(U) (cal(V) + 1)$.
This is a problem as one loses most closure results as you will be lifting more and more.
The main beinifit from this is the performance aspect.
Going from reading to a depth $n$, to a depth $n+1$ is not $cal(O)(1)$ instead of $cal(O)(n)$.
This will be seen in @sec:smevpa.
We will henceforth refer to the datatype SME.PreM.

=== PreM

As we speak about in // TODO @pfunctofalg,
the M Type is the terminal object in the category of coalgebras.
We can see through reasoning (cumilatively) in this category that PreM is weakly terminal.
Looking at this category we want to force the incoming morphisms together.
This corresponds exactly to quotienting just as we saw for streams.

=== Writing for performance

#impl([@rq:sme:fast, @rq:sme:zc], "")

=== A coinduction principle on polynomials

#impl([@rq:sme:cind], "")

For an arbitrarry polynomial we can define bisimilarities for its cofix point.
Mathlib has a definition for this for the PA encoding @cite:mathlib.
This has the structure as seen in FIGURE.
I found this very challenging to work with;
Not only does this require using heterogeneous equalities,
it also requires synthesizing three elements.
These are the head and two children under the provided head.
After struggling with this,
I realize it can be solved using the universal property of the terminal object.
The exact structure of this can be seen in FIGURE.
An example of where this shines is as an alternative to conduction-up-to.
Instead of having the ability to extend the relation,
we get parts of the way there using automatic solving tactics like simp as seen in FIGURE.

== Proving the equivalence

#impl([@rq:sme:equiv], "")

Proving the equivalence on polynomials is much more challenging than proving it on streams.
We know at least from streams,
each of the directions will be given by each of their corecursors.
One might expect to follow the type signatures and mostly you do,
but Lean couldn’t help with this,
as it had to do higher order unification.
When Lean finally type checked one could see the functions are obvious as seen in FIGURE.
We now need to prove the expected diagrams commute.
When I was proving these equalities I was not very familiar with bisimilarities,
and tried tens of relations.
Finally I landed on simply forcing their equalities.
Once this was found I had to find the three required structures for bisimilarity.
I picked the head of the first type and was lucky that they both definitioaly was of the same type.
Then to prove the final equalities I proceeded by sigma-,
unction  extentiality,
finally proving the equalities.
The other direction followed analougesly.

This was the main deliverable of the project,
and would help make high performance low universe M types (HpLuM).
Sadly I could not use it directly but instead needed to also make a transliteration REFERENCE.
This transliteration helps justify the uniqueness of a low universe M type.
I hacked and used the Lean ABI stating this is a noop as mentioned in section REFERENCE TRANS.

I used this to instantiate the ABI type.
I then gave it a destructor,
a corecursor,
and a coinduction principal,
I proved the expected unfold lemass and gave it a functorial map.
For the rest of this dissipation I will be proving the results about this type.

== The ABI Type<sec:abi>

The problem the ABI type tries to tackle is one of abstracting the runtime datatype through functions.
Given an isomorphism $"eq" : alpha tilde.equiv beta$ for some types $alpha$ and $beta$,
my first try at solving this involved constructing an object $"ABI" alpha beta$,
making the following commute:

#figure(
  diagram(
    cell-size: 15mm,
    // Top row nodes
    node((-1, 1), $alpha$, name : <A1>),
    node((1, 3), $alpha$, name : <A2>),

    node((1, -1), $beta$, name : <B1>),
    node((3, 1), $beta$, name : <B2>),

    node((1, 1), $"ABI" alpha beta$, name : <S1>),
    node((2, 2), $"ABI" alpha beta$, name : <S2>),

    edge(<A1>, <B1>, $text("eq")$, "="),
    edge(<A2>, <B2>, $text("eq")$, "=", bend : -50deg),

    edge(<A1>, <S1>, $text("mkA")$, "->"),
    edge(<A2>, <S2>, $text("mkA")$, "->"),
    edge(<S1>, <A2>, $text("destA")$, "->"),
    edge(<A1>, <A2>, $bb(1)_alpha$, "->", label-side : right),

    edge(<B1>, <S1>, $text("mkB")$, "->"),
    edge(<B2>, <S2>, $text("mkB")$, "->"),
    edge(<S1>, <B2>, $text("destB")$, "->"),
    edge(<B1>, <B2>, $bb(1)_beta$, "->"),

    edge(<S1>, <S2>, $bb(1)_("ABI" alpha beta)$, "->"),
  ),
  caption:[Operations on ABI]
)<shrkops>

Additionally I had an elimination principle satisfying the two equations below.

```lean
def elim : {motive : ABI _ _ eq → Type w}
       → (hLog : (z : A) → motive (mkA z))
       → (hCheap : (z : B) → motive (mkB z))
       → (eqA : ∀ z, hLog z ≍ hCheap (eq z))
       → (eqB : ∀ z, hCheap z ≍ hLog (eq.symm z))
       → (v : ABI _ _ eq) → motive v := _

theorem elimLog : {motive : carry → Type w}
       → {hLog : (z : A) → motive (mkA z)}
       → {hCheap : (z : B) → motive (mkB z)}
       → {eqA : ∀ z, hLog z ≍ hCheap (eq z)}
       → {eqB : ∀ z, hCheap z ≍ hLog (eq.symm z)}
       → ∀ z, elim hLog hCheap eqA eqB (mkA z) = (hLog z) := _
theorem elimCheap : {motive : carry → Type w}
       → {hLog : (z : A) → motive (mkA z)}
       → {hCheap : (z : B) → motive (mkB z)}
       → {eqA : ∀ z, hLog z ≍ hCheap (eq z)}
       → {eqB : ∀ z, hCheap z ≍ hLog (eq.symm z)}
       → ∀ z : B, elim hLog hCheap eqA eqB (mkB z) = (hCheap z) := _
```

Through quite a bit of work
(which I call transliteration, as seen in the ABI file),
You can free a universe level and open for a more general usage of the function.

=== Weak univalence

// TODO: Talk about how this is kinda univalent.

#figure(
  diagram(
    cell-size: 15mm,
    // Top row nodes
    node((1, 0), $alpha$, name : <A1>),
    node((-1, 0), $beta$, name : <B1>),
    node((0, 1), $"ABI" alpha beta$, name : <S1>),

    edge(<A1>, <B1>, $text("eq")$, "="),

    edge(<A1>, <S1>, $text("mkA")$, "->"),

    edge(<B1>, <S1>, $text("mkB")$, "->"),
  ),
  caption:[Weak univalence up to shrink]
)<shrkops>

=== Relation to Shrink and further universe transforming types

// TODO: Shrink and ABI are related. "Universe altering type"
// TODO: Highlight the delta from the shrink type
TODO

////////////////////////////////////////////////////////////////////////////////

== NTMonad<sec:ntmonad>

== Interaction trees

TODO

=== Weak bisimilarity

TODO

=== A formally verified compiler

TODO

// Interaction trees (ITrees) are a coinductive datastructure detailed in @itrees_paper.

////////////////////////////////////////////////////////////////////////////////




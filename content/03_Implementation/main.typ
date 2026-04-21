#import "../utils.typ": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/colorful-boxes:1.4.3": slanted-colorbox as colorbox
#import "@preview/diagraph:0.3.6": render as grender
#import "@preview/tdtr:0.5.5" : tidy-tree-graph, tidy-tree-draws
#import "@preview/pintorita:0.1.4"
#import "@preview/subpar:0.2.2" as subpar: grid as spg
#show raw.where(lang: "pintora"): it => pintorita.render(it.text)

#let MT = [$M$-type]
#let MTs = [$M$-types]

#let ULift = $"ULift"$

#set raw(lang: "lean")

// TODO
#let impl(content, path) = align[Addressing: #content, Path: #raw(path)]

This chapter describes the implementation of each of the requirements stated in @sec:rq.
I will break it down into a common section,
then go by induvidual components.
I will also mention which parts are in process of being upstreamed and which parts are already in @cite:mathlib.

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
here we take $X = ULift_((-))$,
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
This stemmed from a problem with the corecursive principle for the #MT in the old implementation.
$"corec" : {alpha : "TypeVec".{cal(U)} n} arrow {beta : "Type" cal(U)} arrow (g : beta → P (alpha ::: beta)) arrow beta arrow M alpha$
#footnote(link("https://github.com/leanprover-community/mathlib4/blob/7a60b315c7441b56020c4948c4be7b54c222247b/Mathlib/Data/PFunctor/Multivariate/M.lean#L152-L154")) @cite:mathlib.
The problem here is that both $alpha$ and $beta$ have to both reside in $cal(U)$.
Solving this is done through the next two sections.

==== Universe lifting of polynomial functors.<sec:ulift_p>

The main problem caused here comes from the fact that lean isnt cummulative.
This means it is impossible to express a universe hetrogouns typevector.
In other words $alpha ::: beta$ is only typable if $alpha : "TypeVec".{cal(U)} n$ and $beta : "Type" cal(U)$.
The natural way of solving this is using the supremum in universe levels you get from
$ULift : "Type" cal(U) arrow "Type" (max cal(U) cal(V))$.
This means we can have $beta : "Type" cal(U)$ and $alpha : "Type" cal(V)$,
then ulift both of them to a common universe $ULift alpha ::: ULift beta : "TypeVec".{max cal(U) cal(V)} (n+1)$
#footnote[Note we overload ULift as a notation to refer to lifting TypeVecs as well].

Noticable the next hurdle we encounter is that PFunctors are restricted to a universe level.
Recall the definition from @sec:poly.
Observe how for a $"MvPfunctor".{cal(U)} n$,
we require that both the head and child reside in $cal(U)$.
This will also cause problems,
as looking back at the definition of the corecursor,
we will require $P$ to be able to accept $ULift alpha ::: ULift beta$.
If we do not add the ability to lift $P$,
the unifier will force $cal(U) = cal(V)$,
thereby invalidating all the work we did in the previous section.
Luckily lifting a PFunctor is relatively easy.
We define it as $ULift P eq.delta chevron.l ULift P.1, lambda x mapsto ULift (P.2 x."down") chevron.r$.
This works and now we can move on to generalizing the corecursor.
#footnote[
  TODO: Speak with JV / W to see if this might be done in the lit,
  Ex : Locally presentable and accessable categories Adameck roshiski
].
This defintion is also natural in the expected way.

==== Generalizing the corecursor

#impl([], "[UPSTREAMED],sme/Sme/PFunctor/ForMathlib/M.lean")

Now with all the work in the previous section,
first we generalize a helper function#footnote([Done in TODO: PR NUMBER ]),
then we can define
$"corecU" : {alpha : "TypeVec".{cal(U)} n}
  arrow {beta : Type cal(V)}
  arrow (g : beta → ULift P (ULift alpha ::: ULift beta))
  arrow beta
  arrow M.{cal(U)} alpha$.
Notably we are able to fit the object into $cal(U)$
(this will not be the case for the SME).

`corecU` and `dest` satisfy an unfolding equation.
This is more complex than it used to be as we now need to lower before we continue with the mapping.

////////////////////////////////////////////////////////////////////////////////

=== Polynomial equivalents
#impl([], "sme/Sme/PFunctor/EquivP.lean")

Often when people talk about polynomials, they actually mean structures that are equivalent to polynomials.
This is for example how @cite:keizer and other sources TODO FIND work.
I found it useful to work like this as well,
for this I made a type-class `EquivP` heavily inspired by how it was done in @cite:keizer @cite:mathlib.
I took the definition of curried type-functions (CTFs) from @cite:keizer and implemented coherences for these for the common polynomials.
I used this to make it cleaner to work with ITrees when I reached that point.
A key difference is that I implemented it using the output CTF as an outParam,
this means that I can synthesize the CTF from a given polynomials allowing for an easier user interface.
Type class synthesis works similar to a prolog engine and `outParam` corresponds to the prolog mode `?`.

=== Natural isomorphisms of MvFunctors
#impl([], "sme/Sme/PFunctor/NatIso.lean")

A problem I found when working with isomorphisms of Mv(P)Functors was that isomorphisms needed tons of coherences proven about them.
I observed that the coherences I was proving corresponded to naturality.
To then solve this I defined natural isomorphisms of multivariate functors.
To define this was relatively simple and can be seen in @natiso:ls:def.
Using what I learnt in category theory, it was easy enough to prove the symmetric direction of `nat'`.

#figure(
  raw(takeL(read("../../sme/Sme/PFunctor/NatIso.lean"), 6,10), block:true),
  caption: [Natural isomorphisms on MvFunctors]
)<natiso:ls:def>

== Stream implementation <sec:s>

#impl([@rq:sme:stream:impl, @rq:sme:stream:equiv], "sme/Sme/Stream/*")

As proving these equivleneces is challenging I decidede I would start by implementing it for the special case of streams.
Streams are the text-book coinductive datatype that most people know as mentioned in @sec:coind.
Therefore I expected this to be pedogodical to implement.

=== SME <sec:s:sme>
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

=== Proving the equivalence <sec:s:equiv>
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

#impl([@rq:sme:impl, @rq:sme:equiv], "sme/Sme/M/*")

Recalling back to @sec:m:sme,
we can seeing how we proceeded in @sec:s:sme,
we know how to proceed.
First make a class of preobjects,
then define a bisimilarity relation over these objects,
make the object by quotienting this relation.

== Rephrasing bisimilarity for #MTs <sec:bs>
#impl([@rq:sme:cind], "")

Coming into this dissertation,
I implemented almost all of it using the definition of bisimilarity given in @cite:mathlib as @bs:ls:mathlib.
This definition turned out to be very hard to work with.
Later in my dissertation I found an equivalent formulation using the universal property of the terminal object,
since bisimilarity requires all but the last family to be equal,
I simply equalize the objects last families.
This reduces the up-front cost of proving an #MT bisimilarity,
as previously one had to instantiate `a f f₁ f₂`,
finding these values was very difficult and time consuming as they usually required partially unfolding the definition.
The definition given in @bs:ls:my ended up being much easier to use.
One of the reasons for this is that all the proofs about mappings of polynomials can be applied in a simp to get the preliminatry proof.
This makes a lot of bisimilarity statements easier to work with.

// For an arbitrarry polynomial we can define bisimilarities for its cofix point.
// Mathlib has a definition for this for the PA encoding @cite:mathlib.
// This has the structure as seen in FIGURE.
// I found this very challenging to work with;
// Not only does this require using heterogeneous equalities,
// it also requires synthesizing three elements.
// These are the head and two children under the provided head.
// After struggling with this,
// I realize it can be solved using the universal property of the terminal object.
// The exact structure of this can be seen in FIGURE.
// An example of where this shines is as an alternative to conduction-up-to.
// Instead of having the ability to extend the relation,
// we get parts of the way there using automatic solving tactics like simp as seen in FIGURE.
//

#pad(x:-1cm)[
#spg(
  figure(
```
def MvPFunctor.M.bisim (R : P.M α → P.M α → Prop)
  (h :
    ∀ (x y : P.M α), R x y → ∃ a f f₁ f₂,
      M.dest P x = ⟨a, TypeVec.splitFun f f₁⟩ ∧
        M.dest P y = ⟨a, TypeVec.splitFun f f₂⟩ ∧ 
          ∀ (i : (P.B a).last), R (f₁ i) (f₂ i))
  (x y : P.M α) (r : R x y) : x = y := ...
```,
    caption: [@cite:mathlib definition]
  ),
  <bs:ls:mathlib>,
  figure(
```
def bisim_map (R : P.M α → P.M α → Prop)
  (x : R a b)
  (h : ∀ s t, R s t →
    ∃ (x : (TypeVec.id ::: Function.const _ PUnit.unit) <$$> s.dest
      = (TypeVec.id ::: Function.const _ PUnit.unit) <$$> t.dest),
      ∀ v, R (s.dest.snd .fz v) <| t.dest.snd .fz
        <| cast (congr (congr rfl (Sigma.ext_iff.mp x).1) rfl) v)
  : a = b := ...
```,
    caption: [New definition]
  ),
  <bs:ls:my>,
  columns: (auto, auto),
  caption: [Equivalent bisimilarity definitions]
)
]


=== PreM
#impl([@rq:sme:impl], "sme/Sme/M/PreM.lean")

To define PreM we do exactly as we did for Streams,
making sure to use the signature of `corecU` over `corec`.
For the case of streams,
we had two destructors `hd` and `tl`,
in this case we have only one `dest`.
Because of universe-level hell we cant define a nice signature like `dest : PreM P α → P (α ::: PreM P α)`,
as `PreM P α` resides in $Type max cal(U) cal((V + 1))$ for some $cal(V)$,
instead we get the signature `dest : PreM P α → ULift.{max u (v+1)} P (ULift α ::: PreM P α)`.
The definition of this requires transliterating the output of calling the generating function,
as the generating function produces a $ULift_(max cal(U) cal(V)) P$.

In addition to the two functions `corec` and `dest` we have defined for `PreM`,
I also need `ULift`ing of `PreM`s.
This is a function taking a `PreM.{u, v} P α` to a `PreM.{u, max v w} P α`.
This was defined in such a way to take as much care as possible to make it easy to work under quotients...
when we get to that section we can see to what extent I succeeded at this.

With all this plumbing done we can now move on to define bisimilarity.
It is quite hard to define bisimilarity of `PreM`s using the `coinductive` syntax I set up.
Instead, I use the relational lifting of multivariate functors.
Relational lifting lets me reason about the children of a polynomial functor when instantiated correctly.
The relational family I want to use for this is bisimilarity for the first argument,
and identity for all of the other children.
This is why I gave the first-principles definition of a coinductive predicate in @sec:coindp,
as we need to use this explicit cofixpoint construction to build the relation.

Proving this is an equivalence relation is much harder than for the case of streams.
The reason for this is the much more roundabound definition of bisimilarity.
Luckily mathlib has a lemma for working with liftR and PFunctors.
These proofs can be found in `PreM.lean`.
Once we have these we have that `PreM`s are setoids,
and can proceed to define the quotiented version.

== SM
#impl([@rq:sme:impl], "[UPSTREAMED],sme/Sme/{M/SM.lean,HEq.lean}")

I expected implementing the SME $M$-types to go as smoothly as implementing SME streams.
Defining the corecursor was as simple,
every other definition was much harder.

The destructor of SMs will be given by quotient lifting just as for streams.
The function is also very similar,
take the preobject destructor and equalize deeper occurances as to not leak the type.
The stability of this function is proven by soundness of quotients for the corecursive case,
and lifting the equality from bisimilarity for the other cases.

Proving the coinduction principle was dramatically harder.
The reason for this,
as with most things in this disertation,
is heterogeneous equalities.
Since hetrogenous equalities have very few congruences#footnote[
  An example is `(List A = List B) = (A = B)` is independent of lean.
],
often I need to solve them on a case-by-case basis.
As a consequence I ended up writing a few quite crucial lemmas,
these include `dcongr_heq` which I upstreamed,
along with `hfunext_iff` which I have an open PR with TODO UPSTREAM.
As a consequence, this proof has both forward and backward sections.
To save our sanity, I decided to rewrite it using @sec:bs,
after doing this the proof simply fell out.

The next proof I had to do was with regards to universe lifting of SME #MTs,
this involves lifting the state-machine state rather than any part of the polynomial.
This is the universe lifting function we defined for PreM types.
Universe lifting of this component is needed for proving the generalized equivalence we stated in @sec:s:equiv.

// Noting the definition of corecU,
// one might wonder if you could define M from first principles for this.
// The problem one encounters is one of universes.
// As seen in the definition above,
// if one were to define a type whos construcor is directly the corecU definiton,
// it would hold a $beta : "Type" cal(V)$.
// This then forces the object to reside in
// $"Type" max cal(U) (cal(V) + 1)$.
// This is a problem as one loses most closure results as you will be lifting more and more.
// The main beinifit from this is the performance aspect.
// Going from reading to a depth $n$, to a depth $n+1$ is not $cal(O)(1)$ instead of $cal(O)(n)$.
// This will be seen in @sec:smevpa.
// We will henceforth refer to the datatype SME.PreM.
//
// === PreM
//
// As we speak about in // TODO @pfunctofalg,
// the M Type is the terminal object in the category of coalgebras.
// We can see through reasoning (cumilatively) in this category that PreM is weakly terminal.
// Looking at this category we want to force the incoming morphisms together.
// This corresponds exactly to quotienting just as we saw for streams.

=== Writing for performance

#impl([@rq:sme:fast, @rq:sme:zc], "sme/Sme/M/SM.lean")

While conducting the evaluation for @rq:sme:fast,
I noticed that while calling a corecursor is zero-cost,
destructing one is not.
The problem for this seems to do with the interactions between inlining and partially applied functions.
I forked mathlib and added multiple inline directives to various functions.
TODO Continue this section

== Proving the equivalence

#impl([@rq:sme:equiv], "sme/Sme/M/Equiv.lean")

Proving the equivalence on polynomials is much more challenging than proving it on streams.
We know at least from streams,
each of the directions will be given by each of their corecursors.
One might expect to follow the type signatures and mostly you do,
but Lean couldn’t help with this,
as it had to do higher order unification.
When Lean finally type checked one could see the functions are obvious as seen in FIGURE.
We now need to prove that the two functions are inverses.
When I was proving these equalities I was not very familiar with bisimilarities,
and tried tens of invariants.
Finally I landed on simply forcing their equalities.
Once this was found, I had to prove it was a bisimilarity.
I picked the head of the first type and was lucky that they both definitioaly was of the same type.
This means the equality for the children is homogenous.
The other direction followed analougesly.

This was the main deliverable of the project,
and would help make high performance low universe #MTs (HpLuM)..

// Sadly I could not use it directly but instead needed to also make a transliteration REFERENCE.
// This transliteration helps justify the uniqueness of a low universe M type.
// I hacked and used the Lean ABI stating this is a noop as mentioned in section REFERENCE TRANS.
//
// I used this to instantiate the ABI type.
// I then gave it a destructor,
// a corecursor,
// and a coinduction principal,
// I proved the expected unfold lemass and gave it a functorial map.
// For the rest of this dissipation I will be proving the results about this type.

== The ABI Type<sec:abi>
#impl([@rq:abi:impl, @rq:abi:elim, @rq:abi:opt, @rq:abi:zc], "sme/Sme/ABI.lean")

// TODO:
// #show cite.where(<cite:mathlib>): [Mathlib @cite:mathlib]

@cite:mathlib has a type called `Shrink`.
This is a type which takes an equivalence between a `A : Type u` and a `B : Type v`,
and returns a `Type u`.
It has one constructor `B → Shrink A B`,
and one destructor `Shrink A B → B`,
which are inerses.
The definition given in @cite:mathlib is non-computable using choice,
this makes it useless for us.
Origionally I tried to make it computable by adding an `@[implemented_by]` to it,
which turned out not to work.
The reason this didnt work has to do with the fact that `Shrink` strangely satisfies the univalence axiom:
given `Shrink A` and `Shrink B` along with `A ≃ B`,
one can prove `Shrink A = Shrink B`.
This follows from propositional extentionality as seen in FIGURE.
Aaron Liu from the mathlib community used this in combination with quotients and trustCompiler to prove false.
From this I understood that I would have to make my own variation of the type.

From this I decided to make my own variant I called the ABI type.
Given an isomorphism $"eq" : alpha tilde.equiv beta$ for some types $alpha$ and $beta$,
I define the type $#raw("ABI") alpha beta "eq"$ to have two constructor,
eliminator pairs `mkA`, `mkB`, `destA` and `destB` satisfying the diagram seen in @abi:fg:ops.
Additionally I had an elimination principle satisfying expected $beta$-rules with the two constructors.
Through making the definition opaque I had quite a bit of problems with universe levels.
I ended up solving this using a transliteration.
This let me eliminate into any universe independent of $cal(U)$ and $cal(V)$.

// https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Cardinality.20model.20incompatible.20with.20Lean.20compiler/near/538013012

#spg(
  figure(
    text(size: 5pt)[
    #diagram(
      cell-size: 6em,
      // Top row nodes
      node((-1, 1), $alpha$, name : <A1>),
      node((1, 3), $alpha$, name : <A2>),

      node((1, -1), $beta$, name : <B1>),
      node((3, 1), $beta$, name : <B2>),

      node((1, 1), $#raw("ABI") alpha beta "eq"$, name : <S1>),
      node((2, 2), $#raw("ABI") alpha beta "eq"$, name : <S2>),

      edge(<A1>, <B1>, $"eq"$, "="),
      edge(<A2>, <B2>, $"eq"$, "=", bend : -50deg),

      edge(<A1>, <S1>, $#raw("mkA")$, "->"),
      edge(<A2>, <S2>, $#raw("mkA")$, "->"),
      edge(<S1>, <A2>, $#raw("destA")$, "->"),
      edge(<A1>, <A2>, $bb(1)_alpha$, "->", label-side : right),

      edge(<B1>, <S1>, $#raw("mkB")$, "->"),
      edge(<B2>, <S2>, $#raw("mkB")$, "->"),
      edge(<S1>, <B2>, $#raw("destB")$, "->"),
      edge(<B1>, <B2>, $bb(1)_beta$, "->"),

      edge(<S1>, <S2>, $bb(1)_("ABI" alpha beta)$, "->"),
    )],
    caption:[Operations on ABI]
  ),
  <abi:fg:ops>,
  figure(
    text(size: 5pt)[
    #diagram(
      cell-size: 6em,
      // Top row nodes

      node((1, -1), $beta$, name : <B1>),
      node((3, 1), $beta$, name : <B2>),

      node((1, 1), $#raw("Shrink") beta$, name : <S1>),
      node((2, 2), $#raw("Shrink") beta$, name : <S2>),

      edge(<B1>, <S1>, $#raw("mkB")$, "->"),
      edge(<B2>, <S2>, $#raw("mkB")$, "->"),
      edge(<S1>, <B2>, $#raw("destB")$, "->"),
      edge(<B1>, <B2>, $bb(1)_beta$, "->"),

      edge(<S1>, <S2>, $bb(1)_(#raw("Shrink") beta)$, "->"),
    )],
    caption:[Operations on Shrink]
  ),
  columns: (1fr, 1fr),
  caption: [Universe transforming types.]
)

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

== HpLuM<sec:hplum>
#impl([@rq:sme:abi], "sme/Sme/M/HpLuM.lean")

After implementing the `ABI` type, it is time to put it to use.
To do this, first I tried to simply use the equivalence,
what I found was this leaked the universe of the carrier.
I realised, I did not have to make a new equivlance for this,
but rather paste the previous equivalence with itself.
I called this equiv cross universe (`equivXU : SM.{u, max u v} P α ≃ SM.{u, max u w} P α`).
One can observe this equivalence forms a transliteration.
Additionally one might wonder, doesnt composing the equivalence with itself become a noop?
To which the answer is no, as we are parameterised in universe levels, so technically these are different functions.
This became a pain as the performance of this equivalence was $cal(O)(n^2)$.
To avoid this, I decided to mark this as `@[implemented_by, irreducible]`.
Once this was done I could start implementing the High performance Low universe M.

The HpLuM is the ABI type, parameterised by the equivalence given in the last section at universes $cal(U)$, $cal(U)$.
These universes prevent the carrier from being leaked.
From here we define the corecursor of the same signature as in the `SM`,
this uses a cocktail of universe changes, first one up using `SM.uLift`, then one down using `equivXU`,
finally being passed into a `mkB` constructor of the `ABI` type.
The next step is giving a `dest : HpLuM P α → P (α ::: HpLuM P α)`,
this is done using the eliminator for the `ABI`-type.
The reason I use this rather than just a `destB` (which is what `rec` compiles to),
using the eliminator lets me prove the coherence of the SME and PA inline.

Once this was done I started proving equations of these methods.
The first one was `dest_corec`, which has a nicer signature now.
Followed by a coinductive principle.
I also added an in-universe version of `corec` called `corec'`,
this has the exact behaviour of the old non generalized corecursor on PA M types.
In addition to this I added corecursor unrolling lemmas and mapping lemmas.
From here I then proved co-Lambek's.
Further that HpLuM actually is multifunctorial as the polynomial defintion,
along with destructor lemmas for map.

Further I added functionallity to reason about polynomials equivalents,
this is the reason I picked the CTF to be the outParam,
as it lets these functions synthesize the correct CTF without annotations.

I also found I needed a defintion of ulifting of HpLuMs.
Like everything to do with universe levels, this turned out to be a pain.
I also proved naturality conditions of these.

The next thing I had to prove, was transportation of natural isomorphisms.
This takes a natural isomorphisms between `P` and `P'`,
and lifts it to a natural isomorphisms between `HpLuM P` and `HpLuM P'`.
This will be used when we start working with futumorphic productivity.

When all of this was implemented, then I have a usable #MT library.

== NTMonad<sec:ntmonad>
#impl([@rq:ntm:impl], "sme/Sme/ITree/*")

The non-termination monad is a nice example of a coinductive datatype.
It has two constructors `tau : NTMonad A → NTMonad A` and `val : A → NTMonad A`.
The values of this type will always be either some value of `tau`s then a `val`,
or an a unique value `spin = tau spin`.
One can think of these as `coroutines`,
where they have a bind function that composes them.

I implemented them using by simply taking the cofixpoint of the Sum functor.
This was mainly just to test that I understood what was needed to implement ITrees,

TODO complete this section

== Interaction trees
#impl([@rq:it:impl, @rq:it:sbisim, @rq:it:kt, @rq:it:coind], "sme/Sme/ITree/*")

Interaction trees are the free-monad with non-termination as an effect @cite:itree.
In practice this means they can be used as a denotational object of imperative programs.
They have 3 constructors, returning a value (monoidal unit),
having a silent transition (for non-termination),
and having a visible effect.
This can be seen in @itree:ls:def.
The Lean defintion also includes a constructon of the polynomial equivalent.
When KTrees are mentioned in the ITree paper @cite:itree,
it is simply a function of the form `A -> ITree E B`,
for those familiar this is the object of the #strong[k]leisli category.

#set raw(syntaxes: "../Rocq.sublime-syntax")

#let itreestx = partL(read("../../sme/Sme/ITree/Defs.lean"), 8, 14, 63, 75, 106)

#let ostx = itreestx.at(1) + itreestx.at(3)

#spg(
  figure(
```Coq
CoInductive itree (E: Type -> Type) (R: Type): Type :=
| Ret (r: R)
| Tau (t: itree E R)
| Vis {A: Type} (e : E A) (k : A -> itree E R)
```,
    caption: [Rocq defintion from @cite:itree]
  ),
  figure(
    raw(ostx, block: true),
    caption: [Parts of the Lean defintion]
  ),
  columns: (auto,auto),
  caption: [Defintions of ITrees],
  label: <itree:ls:def>
)

ITrees have many operations and equations defined in the paper,
These can be seen in @itree:tb:fns,
here I have annotatted all of the functions I have implemented from the paper.
A notable difference is that in the Lean implementation strong bisimilarity implies equality,
this makes using some of the proofs easier.

#let gbox(title, rowspan : 1, colspan: 1, body) = grid.cell(rowspan : rowspan, colspan: colspan)[ #colorbox(title : title, color: (stroke : teal, fill : rgb("#0000")))[#body] ]

#pad(x: -1cm)[
#figure(
  grid(
    columns: (1fr, 1fr),
    gutter: 1em,
    gbox([Interaction Tree Operations], rowspan: 2)[
      - `ITree E A : Type` #super[LR]
      - `tau : ITree E A → ITree E A`#super[LR]
      - `ret : A → ITree E A`#super[LR]
      - `vis {R} : E R → (R → ITree E A) → ITree E A`#super[LR]
      - `bind : ITree E A → (A → ITree E B) → ITree E B`#super[LR]
      - `trigger : E A → ITree E A`#super[LR]
    ],
    gbox([Hetrogenous weak bisimilarity])[
      - `eutt (r : A → B → Prop) : ITree E A → ITree E B → Prop`#super[R]
    ],
    gbox([Strong and weak bisimilarity])[
      - `_ ≅ _ : ITree E A → ITree E B → Prop`#super[LR]
      - `_ ≈ _ : ITree E A → ITree E B → Prop`#super[LR]
    ],
    gbox([Events and subevents], rowspan: 2)[
      - `(e : E R)`#super[LR]                #h(1fr) `R` is the result of event `e`
      - `E +' F`#super[LR]                   #h(1fr) disjoint union of effects
      - `class E -< F`#super[LR]             #h(1fr) `E` is a subevent of `F`
      - `trigger [E -< F] : E ↝ ITree F` #super[R]
    ],
    gbox([Parametric functions])[
      `E ↝ F := ∀ X, E X → F X` #super[LR]
    ],
    gbox([Monadic interpretation])[
      `interp [Monad M] [MonadIter M] : (E ↝ M) → (ITreeE ↝ M)` #super[LR]
    ],
    gbox([Monad Laws])[
      - `bind (ret v) k = k v`
      - `bind t ret = t`
      - `bind t ret = t`
    ],
  ),
  kind: table,
  caption: [Functions implemented in (L)ean and (R)ocq]
)
<itree:tb:fns>
]

#show "->": it => sym.arrow

#pad(x: -1cm)[
#figure(
  grid(
    columns: (1.4fr, 1.1fr),
    gutter: 1em,
    gbox([Structural Laws])[
      - `tau t ≈ t` #super[LR]
      - `t ≈ spin` -> `t = spin` #super[L]
      - `bind (tau t) k = tau (bind t k)` #super[LR\*]
      - `bind (vis e k₁) k₂ = vis e λy. bind (k₁ y) k₂` #super[LR\*]
    ],
    gbox([Equivalence relation])[
      - `a ≈ a` #super[LR]
      - `a ≈ b` -> `b ≈ a` #super[LR]
      - `a ≈ b` -> `b ≈ c` -> `a ≈ c` #super[LR]
    ],
    gbox([Congruences])[
      - `t₁ ≈ t₂` -> `tau t₁ ≈ tau t₂` #super[LR]
      - `k₁ ≈ k₂` -> `vis e k₁ ≈ vis e k₂` #super[LR]
      - `t₁ ≈ t₂` -> `k₁ ≈ k₂` -> `bind t₁ k₂ ≈ bind t₂ k₂` #super[LR]
      - `k₁ ≈ k₂` -> `iter k₂ v ≈ iter k₂ v` #super[LR #sym.dagger]
    ],
    gbox([Monad Laws])[
      - `(ret v) >>= k = k v` #super[LR\*]
      - `t >>= ret = t` #super[LR\*]
      - `x >>= f >>= g = x >>= (f · >>= g)` #super[LR\*]
    ],
  ),
  kind: table,
  caption: [Equations implemented in (L)ean and (R)ocq#footnote[
    The annotations in the table are as follows:

    #h(1em) \* = strong bisimilarity rathe rthan equality in Rocq

    #h(1em) #sym.dagger = proven using coinduction-up-to in Rocq]]
)
<itree:tb:eqs>
]

=== The ITree Monad
#impl([@rq:it:mon, @rq:it:comb, @rq:it:lmon], "sme/Sme/ITree/Monad.lean")

ITrees form a monad, where the binding operation corresponds to whenever an itree returns,
calling the continuation.
The return constructor is the monads unit.
From this to ensure it is lawful there is a set of proof obligations,
these can be seen in @itree:tb:eqs.

=== Weak bisimilarity
#impl([@rq:it:wbisim], "sme/Sme/ITree/WBisim/*.lean")

Bisimilarity is often not sufficent for proving program equivalences.
This comes from the fact that sometimes we care about more than just equality.
For example the program `println 10` and `println (10 + 0)` are _equivalent_,
but not syntactically equal.
We can note that the effects produced by these programs are the same,
one simply takes more steps to get there.
This is where we rather consider the weak bisimilarity.
One can think of weak bisimilarity is an equivalence relation modulo silent steps;
two objects are observably the same effects but with a different tau count.
The rocq defintion #footnote[The syntax is slightly simplified for reading purposes here]
and my defintion differs quite a bit.
This is mainly because I decided to implement only hetrogenous weak bisimilarity,
and also that in rocq they have coinduction-up-to making proofs much easier,
in my defintion I need to 'bake in' as many principles as possible.
This is the reason for the `refl` constructor.
In the defintion I use `EStep` to mean some amount of taus,
and `Step` to mean a productive step to some non-tau value.
`EStep` forms a linear join-semilattice,
`Step` inherits some of this structure, but is slightly easier to work with.
One of the key pieces of structure helping this be closer to coinduction-up-to is the ability to skip taus in a proof,
this is done using the principle `skip : EStep a c → EStep b d → Invariant E A R c d → Invariant E A R a b`,
which operates directly on the invariant for the bisimilarity.
This solves problems similarity to how it is done in the paper,
it gives a principle where we can simply equations a lot by shifting them along the taus.
// This works very similarly to the main coinduction-up-to principle used in the paper,
// called ``


#spg(
  figure(
```coq
CoInductive euttF : itree E A → itree E B → Prop :=
| EqRet a b (REL: r a b) : euttF (Ret a) (Ret b)
| EqVis {R} (e : E R) k1 k2 (REL: ∀v, euttF (k1 v) (k2 v)) : euttF (Vis e k1) (Vis e k2)
| EqTau t1 t2 (REL: euttF t1 t2) : euttF (Tau t1) (Tau t2)
| EqTauL t1 ot2 (REL: euttF t1 ot2) : euttF (Tau t1) ot2
| EqTauR ot1 t2 (REL: euttF ot1 t2) : euttF ot1 (Tau t2).
```,
    caption : [Rocq definition]
  ),
  figure(
    raw(takeL(read("../../sme/Sme/ITree/WBisim/Defs.lean"), 14, 26), block: true),
    caption : [Lean definition]
  ),
  columns: (auto, auto),
  caption: [Weak-bisimilarity for ITrees]
)

In the ITree paper @cite:itree it is proven weak-bisimilarity is an equivalence relation,
a table of what is proven in each implementation can be found in @itree:tb:eqs.
Out of these the ones marked with #sym.dagger have been proven using coinduction-up-to.
These means they were particularly technical to prove and required defining helper predicates.
The main instance of this is `iter`-congruence,
for this I had to define two predicates `IterTrace` and `IterCotrace` for productive and spinning `iter`s respectively.
This is used to define that if one of the generators of the iteration is weakly bisimilarity to the other generator,
then if one is productive, the other is productive.
Further it can be used to show that when they are productive,
the values are related in the expected way.
This proof was highly indirect and required the creative step of coming up with the (co)trace abstraction.

=== A formally verified optimization
#impl([@rq:it:wbisim], "sme/Sme/ITree/WBisim/*.lean")

One of the main use cases of Interaction Trees is program verification.
To demonstrate this I implemented a simple imperative langauge IMP as seen in @itree:ls:istx,
I give it the denotational semantic as @itree:ls:isem,
then I define an optimization `simpl` @itree:ls:simpl on this.
All `simpl` does is simplifies constant expressions,
the proof of this respecting the semantics is provided in the code,
and is an example of how weak-bisimilarity can help prove an optimization correct.

#let i = partL(read("../../sme/Sme/ITree/Examples/Imp.lean"), 9, 25, 29, 72, 115)

#pad(x : -1cm)[
#spg(
  figure(raw(i.at(1), block: true), caption: [`Imp` syntax]),
  <itree:ls:istx>,
  figure(raw(i.at(3), block: true), caption: [`Imp` semantics]),
  <itree:ls:isem>,
  figure(raw(i.at(4), block: true), caption: [`simpl`]),
  <itree:ls:simpl>,
  columns: (auto, auto, auto),
  kind : raw,
  caption: [`Imp` and `simpl`],
  label: <itree:ls:imp>,
)
]


// Interaction trees (ITrees) are a coinductive datastructure detailed in @itrees_paper.

////////////////////////////////////////////////////////////////////////////////

== Futumorphic Productivity
#let FANTOMORPH = cite(<cite:fantomorph>, form: "prose")

// During my internship under AK and TG,
// I made a structure I then called `DeepThunk`s.
// I now refer to them as the induced productivity monad.
// They are the general way of constructing productive functions on cofixed points from terminating functions.
As mentioned in @sec:coind, every corecursive function has to be productive.
In the current library defintion,
this means we need to define the function using the corecursor
`corec {β α} : (β → P α β) → β → M P α`.
This can be quite cumbersome as one can only define one layer of the coinductive datatype at one,
#FANTOMORPH provides an alternative to this,


Given a polynomial $bold(P) accent(alpha, macron) beta$,
then the corecursor we get for $bold("M" P) accent(alpha, macron)$ is:

// $ "corec" : {beta} arrow.r (beta arrow.r bold(P) accent(alpha, macron) beta) arrow.r beta arrow.r bold("M" P) accent(alpha, macron) $

Often this is adequet,
but one has a few drawbacks that can be summarised as:
it has to emit exacly one 'layer' of the final structure.
The end goal would be to allow it to emit anything from layer 1 to the entire structure.
One can think of this as taking the most general choice of $beta$.
The structure that solves this is $bold("PT" P) accent(alpha, macron) beta eq.delta bold("M")_xi bold(P) accent(alpha, macron) (beta plus.o xi)$.
From here we construct two unique functions, inject and dtcorec:

$ "inject" : { beta } arrow.r bold("M" P) accent(alpha, macron) arrow.r bold("PT" P) accent(alpha, macron) beta 
colon.eq "corec"_(bold("PT" P)) ("map"_(bold("M" P)) (bb(1) ::: iota_r) compose "dest") $

$ "dtcorec" { beta } (g : beta arrow.r bold("PT" P) accent(alpha, macron) beta) : beta arrow.r bold("M" P) accent(alpha, macron)
colon.eq "corec"_(bold("M" P)) (("map"_(bold("M" P)) (bb(1) ::: [g, bb(1)]) ) compose "dest") compose g $




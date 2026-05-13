#import "../utils.typ": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge, shapes
#import "@preview/colorful-boxes:1.4.3": slanted-colorbox as colorbox
#import "@preview/diagraph:0.3.6": render as grender
#import "@preview/tdtr:0.5.5" : tidy-tree-graph, tidy-tree-draws
#import "@preview/subpar:0.2.2" as subpar: grid as spg

#set raw(lang: "lean")

#let impl(content, path) = [
  #set text(size: 10pt)

  #v(-8pt)

  #raw(path) #h(1fr) #content
]

// Feedback from Russell
// * Prefer first person
// * Mention each of requirements and say they are met. Put it in bold.

// Feedback from Jamie Vicary
// * The main thing examiners are looking for is: what is the challenge here? 
//   and how did you overcome it? Looking at Chapter 1, 
//   you give a nice intro to the mathematical aspects, 
//   but there is ample opportunity here for you to also comment on the level of challenge.
//   You could briefly summarize what was hard about your project,
//   and where did you really have to show ingenuity.
//   It's also OK to talk about this within the project,
//   e.g. "I tried to do X but encountered several problems, therefore instead I have done X' and everything works ok".
//   Examiners love to see things like this as it shows you've engaged with real-world problems.
// * You could also write in Chapter 1 (and also perhaps later in the dissertation) about the impact of your work. 
//   You write that you implement the SME with O(1) destructuring. 
//   Can you say more about what this buys you regarding the expressiveness of Lean -- for example, 
//   is there something that can be formalised using this infrastructure, 
//   which was not reasonably formalisable using previous methods.
//
// This chapter describes the implementation of each of the requirements stated in @sec:rq.
// I will break it down into a common section,
// then go by individual components.
// I will also mention which parts are in process of being upstreamed and which parts are already in Mathlib.
//
// The Lean component of this repository,
// and how they relate to each of the requirements can be seen in @impl:fg:overview.
// Additionally the project's import graph can be seen in @rep:fg:import.

#let fbox(boxc) = node.with(snap: -1, fill: boxc.lighten(90%), stroke: boxc)

#let sl = 2
#figure(
  [
  #set text(10pt)
  #diagram(
    cell-size: 4mm,
    fbox(MC)(enclose : (<slib>, <dt>)),

    node((1,1-sl), [PA Impl], name: <spa>),
    edge("->"),
    node((2,0-sl), [Equiv], name : <seq>),
    edge("<-"),
    node((2,1-sl), [SME Impl], name: <ssme>),
    fbox(MC)(align(top + left)[Stream (@sec:s)], enclose: (<spa>, <seq>, <ssme>, (0,-1)), snap: -1, name: <s>),

    node((1,1), [PreM], name: <prem>),
    edge("->"),
    node((2,1), [SM], name : <sm>),
    edge("->"),
    node((3,0), [#MT], name: <hplum>),
    edge("<-"),
    node((2,0), [Equiv], name: <peq>),
    edge(<sm>, <peq>, "->"),
    fbox(MC)(align(top+left)[Polynomial (@sec:impl-sm)], enclose: (<prem>,<sm>,<hplum>,<peq>, (0,1)),name : <slib>),

    edge(<hplum>, (3,2), <dtd>, "->"),

    node((2,2), [DT Defs], name: <dtd>),
    edge("->"),
    node((1,3), [DT Corec],name : <dtc>),
    edge(<dtd>,<dtf>,"->"),
    node((2,3), [DT Inject], name: <dtf>),
    fbox(MC)(align(top+left)[Deep thunks], enclose: (<dtf>,<dtd>,<dtc>, (0,2)), name: <dt>),

    edge(<hplum>, (3,3), <free>, "->"),
    edge(<free>, (2.7,4), (2,4), <clib>, "-"),
    fbox(MC)((2.7,3), [Free], name: <free>, ),

    edge(<hplum>, (3, 4), (2,4), <clib>, "->"),
    edge(<dtc>,   (1, 4), (2,4), <clib>, "->"),
    edge(<dtf>,   (2,4), <clib>, "-"),

    node((2,5), [Coinduction library], name: <clib>),

    // node(, [AltRepr], name: <abi>),
    edge(<abi>, <hplum>, "->"),
    fbox(MC)((3, -1), [AltRepr], name: (<abi>) ),

    edge(<abi>, (3.5, -1), <abil>, "->"),
    node((3.5,5), [AltRepr Type], name: <abil>),

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

    node((5,5), "ITree library", name:<itl>),
    edge(<iti>, (4,3), (5,3), <itl>, "-"),
    edge(<wbsi>, (5,3), <itl>, "->"),

    fbox(MC)(enclose: (<itd>, <wbsi>) ),
  )
  ],
  caption: [Birds-eye view of components of the project],
)
<impl:fg:overview>

The main component implemented in this dissertation is the State-machine encoding of the #MT `SM`.
Further showing the equivalence between the State-machine encoded #MT `SM.{𝓤, max 𝓤 𝓥} P α`, and the PA #MT `M.{𝓤} P α`.
This will be used to implement a performant #TM,
which has the efficiency of the `SM` encoding while being in the universe of the PA encoding.

== Stream implementation <sec:s>

#impl([@rq:sme:stream:impl, @rq:sme:stream:equiv], "sme/Sme/Stream/*")

#let pdef = flamboyant(read("../../sme/Sme/Stream/PDefs.lean"))
#let sdef = flamboyant(read("../../sme/Sme/Stream/SDefs.lean"))
#let equiv = flamboyant(read("../../sme/Sme/Stream/Equiv.lean"))

Proving the equivalence on #MTs was going to be hard,
for this reason I decided I would start by implementing it for the special case of streams.
Streams are the text-book coinductive data type that most people know as mentioned in @sec:coind.
Therefore I expected this to be pedagogical to implement.

=== State-Machine streams <sec:s:sme>
#impl([@rq:sme:stream:impl], "sme/Sme/Stream/SDefs.lean")

#let sds = partL(sdef, 7, 9, 11, 17, 27, 29, 43, 55, 64, 69, 78, 88, 99)

First setting up a class of prestreams,
these correspond to the corecursive principle holding their type.
Followed by the destructors `hd` and `tl` for streams.
Care had to be taken to ensure that the definition would work under a quotient as well.

#figure(raw(sds.at(1) + sds.at(3), block : true), caption: [PreStream and destructors])

Defining a bisimilarity relation;
heads being equal and tails bisimilar as seen in @sec:bisim.
Followed by proving this was an equivalence relation (reflexive, symmetric, transitive).
This would setup a setoid on `PreStream`s.

#spg(
  figure(raw(sds.at(4), block : true), caption: [Bisim definition], kind: raw),
  figure(raw(sds.at(6), block : true), caption: [Equivalence relation], kind: raw),
  columns: (auto, auto),
  caption: [`PreStream` setoid]
)

// TODO: check this uses `Stream` and Stream and stream consistenly.
The definition of a state-machine `Stream` is then preobjects quotiented by this setoid.
When lifting the destructors from `PreStream`s to `Stream`s,
I have to go through the lifting function of quotients.
When lifting to a quotient one has to provide the lifting function,
then a proof that the function is stable under the setoid.
The corecursor was defined using the constructor for `PreStream`s,
under the quotient constructor.

#spg(
  figure(raw(sds.at(8), block : true), caption: [Destructors for SStreams]),
  figure(raw(sds.at(9), block : true), caption: [`corec` for Streams]),
  columns: (auto,auto),
  caption: [`corec` and destructors for SStreams]
)

The next step was defining a coinduction principle;
that bisimilarity implies equality.
This is called `bisim` to align to convention with Mathlib.
The proof of this proceeds by quotient soundness and can be found in `SDefs.lean`.

#spg(
  figure(raw(sds.at(11), block : true), caption: [Bisim definition]),
  figure(raw(sds.at(12), block : true), caption: [Coinduction principle]),
  columns: (auto, auto),
  caption: [Coinduction principle for SStreams]
)

=== Progressive approximation streams
#impl([], "sme/Sme/Stream/PDefs.lean")

#let pds = partL(pdef, 8, 11, 13, 18, 20, 23, 34, 42, 52, 59)

I implement the stream's base functor.
Streams have one constructor (so a head of $1$),
and each of the families only hold one instance of the value (so child `λ i () ↦ 1`).

#spg(
  figure(raw(pds.at(1), block : true), caption: [Functor]),
  figure(raw(pds.at(2), block : true), caption: [PStream]),
  columns: (auto, auto),
  caption: [PStream definition]
)

I defined the destructors of streams by calling the child with the correct indicies.

#spg(
  figure(raw(pds.at(4), block : true), caption: [Head of a PStream]),
  figure(raw(pds.at(5), block : true), caption: [Tail of a PStream]),
  columns: (auto, auto),
  caption: [PStream destructors]
)

For symmetry, I defined a syntactically identical bisimilarity relation on PA streams,
and for this I prove a coinduction principle for PStreams of this relation.
This proof proceeded by using the coinduction principle on general polynomials.

#spg(
  figure(raw(pds.at(6), block : true), caption: [Bisimilarity of PStreams]),
  figure(raw(pds.at(8), block : true), caption: [Coinduction principle for PStreams]),
  columns: (auto, auto),
  caption: [Coinduction principle for PStreams]
)

The corecursor was lifted from the definition on #MTs.

#figure(raw(pds.at(9), block : true), caption: [`corec` for PStreams])

=== State-Machine Progressive approximation equivalence <sec:s:equiv>
#impl([@rq:sme:stream:equiv], "sme/Sme/Stream/Equiv.lean")

The functions of the equivalence between progressive approximation and state-machine Streams,
are corecursors parameterised by the destructors of the other encoding.
Proving that these are inverses was involved.
I toyed around with a few different relations trying to make it work.
In the end, I landed on the straightforward equality as seen in @stream:fg:equiv.
This solved and made the entire proof small after cleaning.

Having done this, I now can handle the case of a generic polynomial.
This turned out to be harder than I expected.
// TODO: Dont use the wrong statement here,
// it should be mentioned that it is only a problem for when it comes to instantiate the AltRepr type ...
Observant readers may notice the statement I proved is subtly different;
rather than proving the statement for a universe polymorphic carrier `SStream.{𝓤, max 𝓤 𝓥} A`,
here I prove it for a fixed universe `SStream.{𝓤, 𝓤} A`.
This is not a problem here, but when it comes to instantiate the `AltRepr` (@sec:abi) type,
the universe-polymorphic statement is required.

// but the equivalence should not be between state-machine Streams with a $cal(U)$ carrier `SStream.{𝓤, 𝓤} A` and PA Streams`PStream A`,
// but rather have the state-machine carrier be greater than or equal to $cal(U)$ `SStream.{𝓤, max 𝓤 𝓥} A`.
// This statement is harder to prove, and requires defining universe lifting of carriers.

#figure(
    raw(takeL(equiv, 4, 15), block: true),
    caption: [Equivalence between PA and state-machine streams]
) <stream:fg:equiv>

////////////////////////////////////////////////////////////////////////////////

== State-Machine encoding of #MTs<sec:impl-sm>

#impl([@rq:sme:impl, @rq:sme:equiv], "sme/Sme/M/*")

In this section, we will generalize from streams to the #MT.
We will proceed in the exact same steps,
First make a class of preobjects,
then define a bisimilarity relation,
finally making the state-machine #MT by quotienting bisimilarity.

As we are proving the universe-polymorphic equivalence,
a universe lifting function is also needed.

=== Rephrasing bisimilarity for #MTs <sec:bs>
#impl([@rq:sme:cind], "")

// TODO!: REPHRASE

// Mathlib has a definition of bisimilarity on #MTs as given in @bs:ls:mathlib.
// Writing proofs to satisfy this definition is parted into stages.
// First one has to discover witnesses by unfolding the definition until a head appears.
// At this point you instantiate `a` with the head,
// the prover then has to find witnesses for `f`, `f₁` and `f₂`.
// Usually one would pick `f` and `f₁` such that one of the proofs becomes trivial.
// This then requires massaging the equality for the `y` until it eventually fits the right definition.
// A lot of the unfolding is then removed to clean the proof.
// Next one has to prove that ``

I implemented this dissertation using the definition of bisimilarity as given in Mathlib (@bs:ls:mathlib).
This definition turned out to be hard to work with as it introduced hetrogenous equalities,
and required unfolding the definition.
Later in my dissertation I discovered an equivalent formulation,
using the universal property of the terminal object,
since bisimilarity requires all but the last family to be equal,
I equalize last families.
This reduces the up-front cost of proving an #MT bisimilarity,
as previously one had to instantiate a common head `a`,
a shared child-family in all but the last argument `f`
and two families in the last argument `f₁ f₂`.
Finding these values was difficult and time consuming as they usually required unfolding the definition.
The definition given in @bs:ls:my ended up being much easier to use.
One of the reasons for this is that all the proofs about mappings of polynomials can be applied in a `simp` call to get the preliminary proof.
This makes bisimilarity statements easier to work with.

// TODO!: nice because why,
// what makes this new definition nice,
// how can this definition be used.
// What is the difference that with the new statement.
// Use subjective language.

// TODO!: have a universe levels section.

// TODO!: Talk about difficulty after the case.
// Seperate difficulty from 

// For an arbitrarry polynomial we can define bisimilarities for its cofix point.
// Mathlib has a definition for this for the PA encoding Mathlib.
// This has the structure as seen in FIGURE.
// I found this challenging to work with;
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
    caption: [Mathlib definition]
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

=== PreM<sec:sme:prem>
#impl([@rq:sme:impl], "sme/Sme/M/PreM.lean")

#let premc = partL(flamboyant(read("../../sme/Sme/M/PreM.lean")), 12, 21, 24, 33, 43, 45, 53, 91, 94, 98, 101, 113, 128, 136, 143)

To define PreM, I proceed like I did for Streams.
We have to use the definition `corecU` over `corec`.

#figure(raw(premc.at(1), block:true), caption: [`PreM` definition])

For the case of streams,
I had two destructors `hd` and `tl`,
in this case I only have `dest`.
One would expect `dest` to have the signature `dest : PreM P α → P (α ::: PreM P α)`,
but this is in-fact not possible,
The reason this is `P : PFunctor.{𝓤} (n + 1)`,
expects the applied arguments to all be in universe #U.
As we can see in the definition above `PreM P α : Type max 𝓤 (𝓥 + 1)` for some #V,
consequently `dest` has the signature `dest : PreM P α → ULift.{max 𝓤 (𝓥+1)} P (ULift α ::: PreM P α)`.

#spg(
  figure(raw(premc.at(3), block:true), caption: [Destructor for `PreM`]),
  figure(raw(premc.at(4), block:true), caption: [Equation for destructoring a corec]),
  columns: (auto, auto),
  caption: [Destructor and $beta$-rule for `PreM`]
)

In addition to `corec` and `dest`, I also need `ULift`ing of `PreM`s.
This is a function taking a `PreM.{𝓤, 𝓥} P α` to a `PreM.{𝓤, max 𝓥 𝓦} P α`.
This will be used to state the full universe-polymorphic equivalence.

#figure(raw(premc.at(14), block:true), caption: [ULifting of `PreM`])

I can now move on to define bisimilarity.
I use the definition of bisimulation from @sec:bs.

#figure(raw(premc.at(6) + premc.at(8), block:true), caption: [Bisimilarity of `PreM` types])

I then prove that it is an equivalence relation.

#spg(
  figure(raw(premc.at(10), block:true),  caption: [Reflexivity]),
  grid.cell(rowspan:2)[#figure(raw(premc.at(12), block:true), caption: [Transitivity]) ],
  figure(raw(premc.at(11), block:true), caption: [Symmetry]),
  columns: (auto,auto),
  caption: [Equivalence relation for `PreM` bisimilarity.]
)

// This is why I gave the first-principles definition of a coinductive predicate in @sec:coindp,
// as we need to use this explicit cofixpoint construction to build the relation.

// Proving this is an equivalence relation is much harder than for the case of streams.
// The reason for this is the much more roundabound definition of bisimilarity.
// Mathlib has a lemma for working with liftR and PFunctors.
// These proofs can be found in `PreM.lean`.
This gives `PreM` a setoid structure to instantiate the quotient.

=== State-Machine #MT (SM) <sec:sme:impl>
#impl([@rq:sme:impl], "[UPSTREAMED],sme/Sme/{M/SM.lean,HEq.lean}")

#let fsm = partL(flamboyant(read("../../sme/Sme/M/SM.lean")), 110, 120, 163)

I expected implementing the state-machine $M$-types to go as smoothly as implementing state-machine streams.
Defining the corecursor was as simple.
Universe lifting and other defintions were not.

The destructor of `SM`s will be given by quotient lifting as for streams.
The function is also similar:
take the preobject destructor and equalize deeper occurances as to not leak the type.
The stability of this function is proven by soundness of quotients for the corecursive case,
and lifting the equality from bisimilarity for the other cases.

Proving the coinduction principle difficult.
The reason for this, is heterogeneous equalities.
Since Lean does not have injectivity of type constructors#footnote[
  An example is `(List A = List B) = (A = B)` is independent of Lean.
],
often I need to solve them on a case-by-case basis.
As a consequence I ended up writing a few crucial lemmas.
These include `dcongr_heq` which I upstreamed to Mathlib.
Therefore, this proof has both forward and backward sections.
To save our sanity, I decided to rewrite it using @sec:bs.
After doing this the proof fell out.

#figure(raw(fsm.at(1), block:true), caption: [Bisimilarity of `SM`-types])

The next proof I had to do was with regards to universe lifting of state-machine #MTs,
which involves lifting the carrier instead of any part of the polynomial.
This is the universe lifting function I defined for PreM types.
Universe lifting of this component is needed for proving the generalized equivalence I stated in @sec:s:equiv.

// === Writing for performance
//
// #impl([@rq:sme:fast, @rq:sme:zc], "sme/Sme/M/SM.lean")
//
// While conducting the evaluation for @rq:sme:fast,
// I noticed that while calling a corecursor is zero-cost,
// destructing one is not.
// The problem for this seems to do with the interactions between inlining and partially applied functions.
// I forked mathlib and added multiple inline directives to various functions.
// TODO Continue this section

=== State-Machine Progressive approximation equivalence <sec:sme:equiv>

#impl([@rq:sme:equiv], "sme/Sme/M/Equiv.lean")

Each of the directions will be given by each of their corecursors.
Further universe changes must also be handled.
Finding the functions that satisfied these universe changes was non-trivial,
as `map` can not change universe levels,
therefore I need new functions (`upMap`, `downMap` and `transliterateMap` @sec:transliteration).
The resulting functions are given in @sme:ls:fns,
here we can see the subtle universe changes both up and down.

#figure(
```lean
let msm := MvFunctor.map (TypeVec.id ::: ULift.up.{𝓤, max 𝓤 𝓥 + 1}) ∘ SM.dest
let mpa := liftAppend.{𝓤, max 𝓤 𝓥} ∘ M.dest P ∘ ULift.down.{max 𝓤 𝓥, 𝓤}
let toFun  := .corecU P msm,
let invFun := .corec mpa ∘ ULift.up,
```,
  caption: [Functions of the equivalence]
)<sme:ls:fns>


I now need to prove that the two functions are inverses.
I was not familiar with bisimilarities when proving these statements,
and tried many invariants.
Finally, I landed on forcing their equalities.
Once this was found, I had to prove it was a bisimilarity.
I picked the head of one of the applications,
and was lucky this was definitionally equal.
This means the equality for the children is homogenous.
The other direction followed analogously.

#figure(
  raw(takeL(flamboyant(read("../../sme/Sme/M/Equiv.lean")), 14, 56), block:true),
  caption: [Equivalence between state-machine and progressive approximation encoded #MTs `equivP`]
)

// This was the main deliverable of the project,
// and would make high performance low universe #MTs (M).

// Sadly I could not use it directly but instead needed to also make a transliteration REFERENCE.
// This transliteration helps justify the uniqueness of a low universe M type.
// I hacked and used the Lean AltRepr stating this is a noop as mentioned in section REFERENCE TRANS.
//
// I used this to instantiate the AltRepr type.
// I then gave it a destructor,
// a corecursor,
// and a coinduction principal,
// I proved the expected unfold lemass and gave it a functorial map.
// For the rest of this dissipation I will be proving the results about this type.

== The Alternative Representation (AltRepr) Type<sec:abi>
#impl([@rq:abi:impl, @rq:abi:elim, @rq:abi:opt], "sme/Sme/AltRepr.lean")

Mathlib has a type called `Shrink`.
This is a type which takes an equivalence between an `A : Type 𝓤` and a `B : Type 𝓥`,
and returns a `Type 𝓤`.
It has an equivalence `A ≃ Shrink A`.
`Shrink` is defined by extracting a type using choice.
Usage of `Classical.choose` can not be compiled.

#figure(
  ```lean
class Small (α : Type 𝓥) : Prop where equiv_small : ∃ S : Type 𝓦, Nonempty (α ≃ S)

def Shrink (α : Type 𝓥) [Small.{𝓦} α] : Type 𝓦 := Classical.choose (@Small.equiv_small α _)

@[no_expose]
noncomputable def equivShrink (α : Type 𝓥) [Small.{𝓦} α] : α ≃ Shrink α :=
  Nonempty.some (Classical.choose_spec (@Small.equiv_small α _))
  ```,
  caption: [Mathlib definition of `Shrink`]
)<abi:ls:shrink>

I tried to make it computable by adding an `@[implemented_by]` to it,
which turned out not to work as it made Lean unsound.
Shrink satisfies univalence; given `Shrink A` and `Shrink B` along with `A ≃ B`,
one can prove `Shrink A = Shrink B`.
Aaron Liu from the Mathlib community used this in combination with quotients and trustCompiler to prove false.
The proof Aaron Liu used can be found in @a:cm.

From this, I decided to make my own variant I called the `AltRepr` type,
as it gave a type an alternative representation.
Given an isomorphism `eq : α ≃ β` for some types `α : Type 𝓤` and `β : Type 𝓤`,
I define the type `AltRepr eq` to have two constructor-eliminator pairs `mkA`, `mkB`, `destA` and `destB`,
satisfying the diagram seen in @abi:fg:ops.
This has an elimination principle satisfying expected $beta$-rules with the two constructors.
Through making the definition opaque I had problems with universe levels.
I ended up solving this using a transliteration (@sec:transliteration).
This let me eliminate into any universe independent of $cal(U)$ and $cal(V)$.

// https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Cardinality.20model.20incompatible.20with.20Lean.20compiler/near/538013012

#let art = `AltRepr eq`

#spg(
  figure(
    text(size: 10pt)[
    #diagram(
      cell-size: 3em,
      spacing: (1cm, 1cm),
      // Top row nodes
      node((-1, 1), $alpha$, name : <A1>),
      node((1, 3), $alpha$, name : <A2>),

      node((1, -1), $beta$, name : <B1>),
      node((3, 1), $beta$, name : <B2>),

      node((1, 1), art, name : <S1>),
      node((2, 2), art, name : <S2>),

      edge(<A1>, <B1>, $e q$, "="),
      edge(<A2>, <B2>, $e q$, "=", bend : -50deg),

      edge(<A1>, <S1>, $#raw("mkA")$, "->"),
      edge(<A2>, <S2>, $#raw("mkA")$, "->"),
      edge(<S1>, <A2>, $#raw("destA")$, "->"),
      edge(<A1>, <A2>, $bb(1)_alpha$, "->", label-side : right),

      edge(<B1>, <S1>, $#raw("mkB")$, "->"),
      edge(<B2>, <S2>, $#raw("mkB")$, "->"),
      edge(<S1>, <B2>, $#raw("destB")$, "->"),
      edge(<B1>, <B2>, $bb(1)_beta$, "->"),

      edge(<S1>, <S2>, $bb(1)_#art$, "->"),
    )],
    caption:[Operations on AltRepr]
  ),
  <abi:fg:ops>,
  figure(
    text(size: 10pt)[
    #diagram(
      cell-size: 3em,
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
  columns: (auto, auto),
  caption: [Universe transforming types.]
)

// === Weak univalence
//
// // TODO: Talk about how this is kinda univalent.
//
// #figure(
//   diagram(
//     cell-size: 15mm,
//     // Top row nodes
//     node((1, 0), $alpha$, name : <A1>),
//     node((-1, 0), $beta$, name : <B1>),
//     node((0, 1), $"AltRepr" alpha beta$, name : <S1>),
//
//     edge(<A1>, <B1>, $text("eq")$, "="),
//
//     edge(<A1>, <S1>, $text("mkA")$, "->"),
//
//     edge(<B1>, <S1>, $text("mkB")$, "->"),
//   ),
//   caption:[Weak univalence up to shrink]
// )<shrkops>

// === Relation to Shrink and further universe transforming types
//
// TODO
// TODO: Shrink and AltRepr are related. "Universe altering type"
// TODO: Highlight the delta from the shrink type

////////////////////////////////////////////////////////////////////////////////

=== The #TM <sec:sme:abi>
#impl([@rq:sme:abi], "sme/Sme/M/HpLuM.lean")

After implementing the `AltRepr` type, it is time to put it to use.
To do this, first I tried to use the equivalence,
what I found was this leaked the universe of the carrier.
I realised, I did not have to make a new equivalence for this,
but paste the previous equivalence with itself.
I called this "equiv cross universe" (`equivXU : SM.{𝓤, max 𝓤 𝓥} P α ≃ SM.{𝓤, max 𝓤 𝓦} P α`).
One can observe this equivalence forms a transliteration (@sec:transliteration).
Additionally one might wonder, does composing the equivalence with itself become a no-op?
To which the answer is no, as we are parameterised in universe levels, so technically these are different functions.
The performance of this equivalence was $cal(O)(n^2)$.
To avoid this, I decided to mark this as `@[implemented_by]` with a cast.
Once this was done I could start implementing the #TM.

The #TM is the `AltRepr` type, parameterised by the equivalence given in the last section at universes `{𝓤 + 1, 𝓤}`.
These universes prevent the carrier from being leaked.
From here we define the corecursor of the same signature as in the `SM`,
this uses a cocktail of universe changes, first one up using `SM.uLift`, then one down using `equivXU`,
finally being passed into a `mkB` constructor of the `AltRepr` type.
I also defined `dest : M P α → P (α ::: M P α)`.
We observe this is a nicer signature than `SM.dest` and `PreM.dest`.

Next is proving the equations on the #TM.
The first one was `dest_corec`, which has the expected signature.
Followed by a coinductive principle.
I also added an in-universe version of `corec` called `corec'`.
This has the exact behaviour of the old non generalized corecursor on PA #MTs.
In addition to this I add a corecursor unrolling lemmas and mapping lemmas.
I then prove co-Lambek's theorem @cite:lambek and that the #TM is multifunctorial like the polynomial definition,
along with destructor lemmas for map.

I added functionality to reason about polynomial equivalents (@sec:polyeqs),
this is the reason I picked the curried type-functions to be the outParam,
as it lets these functions synthesize the correct curried type-functions without annotations.

I also found I needed a definition of ulifting of #TMs.
Like everything to do with universe levels, this turned out to be a challenge.
I also proved naturality conditions of these.

The next thing I have to prove is transportation of natural isomorphisms.
This takes a natural isomorphism between `P` and `P'`
and lifts it to a natural isomorphism between `M P` and `M P'`.
This will be used when we start working with futumorphic productivity.

With this completed, I have a usable #MT library.

== Non-Termination Monad (NTMonad)<sec:ntmonad>
#impl([@rq:ntm:impl], "sme/Sme/ITree/*")

The NTMonad is an example of a coinductive data type.
It has two constructors `tau : NTMonad A → NTMonad A` and `val : A → NTMonad A`.
The values of this type will always be either some value of `tau`s then a `val`,
or an a unique value `spin = tau spin`.
One can think of these as `coroutines`,
where interlacing destructing of taus,
is interlacing computation.

I implemented them by taking the cofixpoint of the Sum functor.
Mainly I ended up focusing on ITrees as they are a strict generalization of the NTMonad,
I still implemented the NTMonad as an exercise.
This is adequate as `NTMonad A = ITree EmptyE A`,
so it would be a waste to double up the implementation.

== Interaction Trees<sec:itree>
#impl([@rq:it:impl, @rq:it:sbisim, @rq:it:kt, @rq:it:coind], "sme/Sme/ITree/*")

To define ITrees in Lean, we implement the functor,
and prove results about polynomial equivalents on them.
When KTrees are mentioned in the ITree paper @cite:itree,
it is a function of the form `A -> ITree E B`,
for those familiar these are Kleisli morphisms @nlab:kleisli_category.

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
    caption: [Rocq definition from @cite:itree]
  ),
  figure(
    raw(ostx, block: true),
    caption: [Parts of the Lean definition]
  ),
  columns: (auto,auto),
  caption: [Defintions of ITrees],
  label: <itree:ls:def>
)

ITrees have many operations and equations defined in the paper @cite:itree.
These can be seen in @itree:tb:fns,
here I have annotated all of the functions I have implemented with superscript#super[L],
from the paper @cite:itree with#super[R],
and the other implementation of ITrees for lean by #MS with #super[M].
A boon of the Lean implementations over Rocq,
is that strong bisimilarity implies equality;
the coinduction principle is provable in Lean.
This fact is inherited from the #MT definition having a provable coinduction principle.
This makes using some of the proofs easier.

#let gfbox(title, rowspan : 1, colspan: 1, body) = grid.cell(rowspan : rowspan, colspan: colspan)[ #colorbox(title : title, color: (stroke : MC, fill : rgb("#0000")))[#body] ]

#figure(
  grid(
    columns: (auto, auto),
    gutter: 1em,
    gfbox([Interaction Tree Operations], rowspan: 2)[
      - `ITree E A : Type` #super[LRM]
      - `tau : ITree E A → ITree E A`#super[LRM]
      - `ret : A → ITree E A`#super[LRM]
      - `vis {R} : E R → (R → ITree E A) → ITree E A`#super[LRM]
      - `bind : ITree E A → (A → ITree E B) → ITree E B`#super[LRM]
      - `trigger : E A → ITree E A`#super[LRM]
    ],
    gfbox([Hetrogenous weak bisimilarity])[
      - `eutt (r : A → B → Prop) : ITree E A → ITree E B → Prop`#super[R]
    ],
    gfbox([Strong and weak bisimilarity])[
      - `_ ≅ _ : ITree E A → ITree E B → Prop`#super[LRM]
      - `_ ≈ _ : ITree E A → ITree E B → Prop`#super[LR]
      - `∀ a b. a ≅ b → a = b`#super[LM]
    ],
    gfbox([Events and subevents], rowspan: 2)[
      - `(e : E R)`#super[LRM]                #h(1fr) `R` is the result of event `e`
      - `E +' F`#super[LRM]                   #h(1fr) disjoint union of effects
      - `class E -< F`#super[LRM]             #h(1fr) `E` is a subevent of `F`
      - `trigger [E -< F] : E ↝ ITree F` #super[R]
    ],
    gfbox([Parametric functions])[
      `E ↝ F := ∀ X, E X → F X` #super[LR]
    ],
    gfbox([Monadic interpretation])[
      `interp [Monad M] [MonadIter M]
  : (E ↝ M) → (ITreeE ↝ M)` #super[LRM]
    ],
  ),
  kind: table,
  caption: [Functions implemented in the dissertaton (L)ean, in (R)ocq @cite:itree and (M). Sammler @cite:mslc]
)
<itree:tb:fns>

#show "->": it => sym.arrow

#[
#figure(
  grid(
    columns: (1fr, 1fr),
    gutter: 1em,
    gfbox([Structural Laws])[
      - `tau t ≈ t` #super[LR]
      - `t ≈ spin` -> `t = spin` #super[L]
      - `bind (tau t) k = tau (bind t k)` #super[LR\*M]
      - `bind (vis e k₁) k₂ 
  = vis e λy ↦ bind (k₁ y) k₂` #super[LR\*M]
    ],
    gfbox([Congruences])[
      - `t₁ ≈ t₂` -> `tau t₁ ≈ tau t₂` #super[LR]
      - `k₁ ≈ k₂` -> `vis e k₁ ≈ vis e k₂` #super[LR]
      - `t₁ ≈ t₂` -> `k₁ ≈ k₂
  ` -> `bind t₁ k₂ ≈ bind t₂ k₂` #super[LR]
      - `k₁ ≈ k₂` -> `iter k₂ v ≈ iter k₂ v` #super[LR #sym.dagger]
    ],
    gfbox([Equivalence relation])[
      - `a ≈ a` #super[LR]
      - `a ≈ b` -> `b ≈ a` #super[LR]
      - `a ≈ b` -> `b ≈ c` -> `a ≈ c` #super[LR]
    ],
    gfbox([Monad Laws])[
      - `(ret v) >>= k = k v` #super[LR\*M]
      - `t >>= ret = t` #super[LR\*M]
      - `x >>= f >>= g = x >>= (f · >>= g)` #super[LR\*M]
    ],
  ),
  kind: table,
  caption: [Equations implemented in the dissertaton (L)ean, in (R)ocq @cite:itree and (M). Sammler @cite:mslc
  #footnote[
    The annotations in the table are as follows:

    #h(1em) #super[L] = Implemented in this dissertation

    #h(1em) #super[R] = Implemented in @cite:itree

    #h(1em) #super[L] = Implemented in #MS

    #h(1em) \* = strong bisimilarity rather than equality in Rocq

    #h(1em) #sym.dagger = proven using coinduction-up-to in Rocq]]
)
<itree:tb:eqs>
]

#pagebreak()

=== The ITree Monad<sec:itree:mon>
#impl([@rq:it:mon, @rq:it:comb, @rq:it:lmon], "sme/Sme/ITree/Monad.lean")

ITrees form a monad, where the binding operation corresponds to pasting trees together,
as seen in @it:fg:bind;
`bind` iterates through the tree and calls the function on seeing a `ret`.
@it:fg:bind shows how biding $f(circle.small)=#[`vis e₂ <| ...`]$ over a tree `tau <| vis e₁ λ _ ↦ tau <| ret v`
The `ret` constructor is the monads unit.
To ensure it is lawful there is a set of proof obligations.
These can be seen in @itree:tb:eqs.

#figure(
  [
  #set text(size: 10pt)
  #diagram(
    cell-size: 4mm,
    node((-1,1.5), [`bind`]),

    node((0,0),`tau`),
    edge("->"),
    node((0,1),`vis e₁`),
    edge("-->"),
    node((0,2),`tau`),
    edge("->"),
    node((0,3),`ret v`),

    node((1,.5) ),
    edge("O-->"),
    node((1,1.5),`vis e₂`),
    edge("-->"),
    node((1,2.5),`...`),

    node((.4, 1.5), $f(circle.stroked.small)$),
    node(shape: shapes.paren.with(dir: left),enclose: ((1,.5), (1,2.5))),
    node(shape: shapes.paren.with(dir: right),enclose: ((1,.5), (1,2.5))),
    node((2,1.5), $=$),

    node((3,-.5),`tau`),
    edge("->"),
    node((3,0.5),`vis e₁`),
    edge("-->"),
    node((3,1.5),`tau`),
    edge("->"),
    node((3,2.5),`vis e₂`),
    edge("-->"),
    node((3,3.5),`...`),

    node(shape: shapes.paren.with(dir: left),enclose: ((3,2.5), (3,3.5)), inset:0pt),
    node(shape: shapes.paren.with(dir: right),enclose: ((3,2.5), (3,3.5)), inset:0pt),
    node((2.3, 2.9), $f(v)$),

    edge((-3,-.5), (-3,0), "->", label: "Constructor", label-side:left),
    edge((-3,.1), (-3,.6), "-->", label: "Function", label-side:left),
    node((5.5,0), " ")
  )
  ],
  caption: [Visual representation of `bind` on ITrees]
)<it:fg:bind>

=== Weak bisimilarity<sec:itree:wbisim>
#impl([@rq:it:wbisim], "sme/Sme/ITree/WBisim/*.lean")

Bisimilarity is often not sufficient for proving program equivalences.
This comes from the fact that sometimes we care about more than equality.
For example, the program `println 10` and `println (10 + 0)` are _equivalent_,
but not syntactically equal.
We can note that the events produced by these programs are the same,
yet one takes more steps to get there.
This is where we consider weak bisimilarity instead.
One can think of weak bisimilarity as an equivalence relation modulo silent steps;
two objects with the same observable events but with a different tau count.
The Rocq definition #footnote[The syntax is slightly simplified for reading purposes here]
and my definition differs.
This is mainly because I decided to implement only homogeneous weak bisimilarity,
and in Rocq they have coinduction-up-to.
Coinduction-up-to is a technique where the prover does not have to provide the full bisimulation,
but can rather use theorems to extend it @cite:paco @cite:coind-up-to.
In my definition, I need to 'bake in' as many principles as possible.
This is the reason for the `refl` constructor.
In the definition I use `EStep` to mean some amount of taus,
and `Step` to mean a productive step to some non-tau value.
`EStep` forms a linear join-semilattice,
`Step` inherits some of this structure, but is easier to work with.
One of the key pieces of structure helping this be closer to coinduction-up-to is the ability to skip taus in a proof,
this is done using the principle `skip : EStep a c → EStep b d → Invariant E A R c d → Invariant E A R a b`,
which operates directly on the invariant for the bisimilarity.
This solves problems similarly to how it is done in the paper,
it gives a principle where we can simplify equations by shifting them along the taus.
// This works similarly to the main coinduction-up-to principle used in the paper,
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

In the ITree paper @cite:itree, it is proven weak-bisimilarity is an equivalence relation.
Proven identities can be found in @itree:tb:eqs.
Out of these the ones marked with #sym.dagger have been proven using coinduction-up-to.
These were particularly technical to prove and required defining helper predicates.
The main instance of this is `iter`-congruence;
if two KTrees are weakly bisimilar,
the `iter` over them are equal.
For this I had to define two predicates `IterTrace` and `IterCotrace` for productive and spinning `iter`s respectively.
// This is used to define, if the two KTrees are weakly bisimilar,
// the generated ITrees have the same productivity behaviour.
This proof was indirect and required the creative step of coming up with the (co)trace abstraction.

=== A formally verified optimization
#impl([@rq:it:wbisim], "sme/Sme/ITree/WBisim/*.lean")

One of the main use cases of Interaction Trees is program verification.
I implement a simple imperative language IMP as seen in @itree:ls:istx.
I give it the denotational semantic as @itree:ls:isem,
then I define an optimization `simpl` @itree:ls:simpl on this.
All `simpl` does is simplify constant expressions,
the proof of this respecting the semantics is provided in the artifact,
and is an example of how weak-bisimilarity can help prove an optimization correct.

#let i = partL(read("../../sme/Sme/ITree/Examples/Imp.lean"), 9, 25, 28, 67, 114)

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

// Interaction trees (ITrees) are a coinductive datastructure detailed in @itrees_paper.

////////////////////////////////////////////////////////////////////////////////

== Free Monad<sec:futu>
#impl([], "")

#let trl = sym.triangle.stroked.l

// Putting these ideas together I created the structure #AK named 'DeepThunk' (`DT` for short).
Originally when considering the choice points for creating a variable layer polynomial,
I constructed it directly.
This structure became known as DeepThunks `DT P (α ::: β)`,
and was given as the cofix-point of `M ((P α -) ∘ (Sum β -)))`
(given in `sme/Sme/M/DT/Defs.lean`).
I define `dtcorec {β} : (β → DT P (α ::: β)) → β → M P α`,
an injector `inject β : M P α → DT P (α ::: β)`,
and a flattener `flatten : DT P (α ::: M P α) → M P α`.
These were extremely challenging to reason about,
but I successfully proved an unfolding lemma of the corecursor,
where it corresponds to doing a mapping operation then flattening.
As this seemed like an interesting structure,
I scoured the literature for similar objects.

Through this I found futumorphism.
These use the free monad to make a morphism `futu {β} : (β → P (α ::: Free P α β)) → M P α`.
The relationship betweem the `Free` monad and `DT` can be seen in @futu:fg:freedt.
This demonstrates that `P (α ::: Free α β)` is exactly `DT`.
A crucial difference is that `Free` has a well-defined notion of constructors and eliminator,
while `DT` has nothing equivalent.
As I wrote around 1700 lines for `DT`,
all this functionality fit into 700 lines for the futumorphism.
The implemented functions can be seen in @futu:tb:free.

#figure(
  $ underbracket((P α -) trl overbracket((beta plus.o -) trl (P α -) trl (beta plus.o -) trl ..., "Free monad"), "DeepThunk") $,
  caption: [Relationship between `Free` monad and `DT`#footnote[Here $trl$ is application as seen in OCaml.].],
)<futu:fg:freedt>

// TODO: Rewrite

The definition given for deep-thunks used the carrier as one of the mapped parameters to the polynomial.
I did not need to implement a dedicated map function,
this turned out to be a mistake.
The problem here is that any multivariate map can change the carrier.
For all equations involving the multivariate map,
had to be restricted to functions concatenated together.
This also meant that working with binds became a mess for universe levels.
Fundamentally we want to treat this as a different parameter so we can also use do notation.
Proving facts about binds also became extremely tedious.
We also did not have a monad unit as the structure of the base polynomial P can be arbitrary.
Another problem was DeepThunks across universes required applying a sequence of natural transformations.
These natural transformations had few equations other than naturality proven about them.

// TODO!!: MAJOR TODO, check alexs comments here.
When implementing the Free monad, I applied each of these learnings.
The definition used had the universe lifting built in,
meaning we only had to reason about switching universes once (`dest_corec`).
The carrier was also taken as a function parameter used to instantiate a constant.
This solved the problem of maps being able to change the carrier,
and at the same time allowed the free monad to satisfy the signature needed for the `Monad : (Type → Type) → Type` typeclass.
This was also made even simpler by implementing the corecursor and the destructor using the standard Lean `Sum`s.
With these design decisions,
implementing constructors (`recall` and `cont`) for the `Free` monad was just following the type signature.
I added a third constructor `cont'` which was in-universe allowing for some definitions to be simplified.
For both of these I added `cases` principles for the constructor sets.
I also set up the corecursor to operate on `Sum`s as well which made writing functions easy.
The coinductive principle for $M$-types could also be specalized to the Free monad using relational lifting on `Sum` types.
Building on the preexisting simp set for `Sum`s,
and marking the $beta$-rules as `@[simp]`,
many theorems became as clean as just invoking `simp`.
The best examples of these can be seen in the mapping equations on constructors.
These theorems were much harder to prove for DeepThunks.
Since we are no longer relying multivariate maps to change the carrier,
we now need a new map definition.

//
// #let rlap(content1, content2) = context {
// 	let w1 = measure(content1).width
// 	let w2 = measure(content2).width
// 	// content1
// 	repr(w1)
// 	repr(w2)
// 	// content2
// }
//
// $ underbracket(
//   rlap(
//     (P α -) trl (beta plus.o -) trl (P α -) trl (beta plus.o -) trl ...,
//     (P α -) trl (beta plus.o -) trl (P α -) trl (beta plus.o -) trl ...,
//     // (P α -) trl overbracket((beta plus.o -) trl (P α -) trl (beta plus.o -) trl ..., "Free monad"), 
// )
//   , "DeepThunk") $
//
// #let rlap(c1, ..cc) = context {
//     let cc = cc.pos()
// 	let w1 = measure(c1).width
//     let mx = cc.fold(w1, (acc, x) => measure(x).width)
// 	c1
// 	h(-w1)
//     for v in cc {
//       v
//       h(-measure(v).width)
//     }
// 	// content2
// 	h(mx)
// }
//
// #let mbox(v) = v
// $ underbracket(
//   rlap(
//     triangle.l,
//     // trl (beta plus.o -) trl (P α -) trl (beta plus.o -) trl ...,
//     triangle.l,
//     // trl (beta plus.o -) trl (P α -) trl (beta plus.o -) trl ...,
//     // (P α -) trl overbracket((beta plus.o -) trl (P α -) trl (beta plus.o -) trl ..., "Free monad"), 
// )
//   , "DeepThunk") $
//
//

#figure(
  grid(
    columns: (1fr, 1fr, 1fr),
    gutter: 1em,
    gfbox([Free Monad Operations], colspan: 2, rowspan: 2)[
      - `Free P α β : Type`
      - `recall : β → Free P α β`
      - `cont' : P (α ::: Free P α β) → Free P α β`\*
      - `dest' : Free P α β → β ⊕ P (α ::: Free P α β)`\*
      - `corec' : (γ → β ⊕ P (α ::: γ)) → γ → Free P α β`\*
      - `map : Free P α β → (β → γ) → Free P α γ`
      - `bind : Free P α β → (β → Free P α γ) → Free P α γ`
      - `inject β : M P α → Free P α β`
      - `flatten : Free P α (M P α) → M P α`
      - `futu' : (β → P (α ::: Free P α β)) → β → M P α`\*
    ],
    gfbox[Monad Laws][
      - `(recall v) >>= k = k v`
      - `t >>= recall = t`
      - `x >>= f >>= g` #linebreak() `= x >>= (f · >>= g)`
    ],
    gfbox[Functor Laws][
      - `id <$> x = x`
      - `(f ∘ g) <$> x`#linebreak()`= f <$> g <$> g`
    ],
  ),
  kind: table,
  caption: [Functions implemented for the Free monad#footnote[
    The annotations in the table are as follows:

    #h(1em) \* = Cross universe version also implemented.
  ]],
) <futu:tb:free>

== Machinery

Many large components of this project do not fit into any of the main components.
This section is dedicated to this exact kind of component.

=== Transliteration<sec:transliteration>

#definition[
  A *transliteration* over some parameter span#footnote[
    This is not necessarily a type, as Lean does not have omega-types (Set$omega$ from Agda) @cite:agda-univ.
  ]  $X$,
  either some $Type$ or more commonly over some universe $cal(U)$,
  is a family of functions $t_(a,b) : X_a -> X_b$.
  Such that
  + the functions are closed under composition $t_(b,c) compose t_(a,b) = t_(a,c)$#footnote([
    This is similar to saying it is an idempotent,
    but technically $t_(b,c)$ and $t_(a,b) $ are not the same function.
  ]),
  + the self-path is identificaion $t_(a,a) = id$.
]

A family of functions,
useful functions throughout this dissertation are what I call _transliterations_.

The trivial instantiation of a transliteration is a `cast`.
Here we pick $X$ as equal types.
Obviously `cast aa = id` and `cast bc ∘ cast ab = cast (ab.trans bc)`.
One could even say that a transliteration is a function that behaves like `cast`.

An example we will keep defining is universe transliteration,
here we take $X = ULift_((-))$,
using this we define the transliteration as seen in @tr:ls:code.
This is the closest we get to cumilativity in Lean;
through an application of the transliteration `transliterate : ULift.{v} α → ULift.{w} α`,
we can use a type as if it is in any higher universe.
We will define transliteration between universe-lifted polynomials,
we will see more of this in @sec:ulift_p.

#let f = takeL(read("../../sme/Sme/ForMathlib/Data/ULift.lean"), 2, 11)

#figure(
  raw(f, lang : "lean", block:true),
  caption: [Transliteration between universes of types]
)<tr:ls:code>

Another major usage of a transliteration was used when defining the eliminator for `AltRepr`,
I will discuss this more when we get to @sec:abi.
This was where I first found transliterations,
and made it possible to define a universe-polymorphic eliminator.

////////////////////////////////////////////////////////////////////////////////

=== Expanding the progressive approximation theory

#impl([], "[UPSTREAMED],sme/Sme/ForMathlib/{PFunctor/*,TypeVec.lean}")

During the feasability assesment, I noticed that in the current formalised theory of polynomials,
the equivalence would not even type-check.
This follows from the fact that the corecursor (@gp:fg:corec) requires that both $alpha$ and $beta$ reside in #U.
This would stop the corecursor having a state that is in a higher universe than the output.
Solving this is done through the next two sections.

#figure(
```lean
def corec : {α : TypeVec.{𝓤} n} → {β : Type 𝓤} → (g : β → P (α ::: β)) → β → M P α
```,
  caption: [`corec`#footnote(link("https://github.com/leanprover-community/mathlib4/blob/7a60b315c7441b56020c4948c4be7b54c222247b/Mathlib/Data/PFunctor/Multivariate/M.lean#L152-L154")) of PA #MTs given in Mathlib]
)<gp:fg:corec>

==== Universe lifting of polynomial functors<sec:ulift_p>

The main problem caused here comes from the fact that Lean is not cummulative.
This means it is impossible to express a universe heterogeneous typevector.
In other words `α ::: β` is only typable if `α : TypeVec.{𝓤} n` and `β : Type 𝓤`.
The natural way of solving this is using the supremum in universe levels you get from
`ULift : Type 𝓤 → Type max 𝓤 𝓥`.
This means we can have `β : Type 𝓤` and `α : Type 𝓥`,
then ulift both of them to a common universe `ULift α ::: ULift β : TypeVec.{max 𝓤 𝓥} (n+1)`
#footnote[Note we overload ULift as a notation to refer to lifting other structures as well.].

The next hurdle we encounter is that polynomials are restricted to a universe level.
Recall the definition from @sec:poly.
Observe how for a `MvPfunctor.{𝓤} n`,
we require that both the head and child reside in $cal(U)$.
This will also cause problems,
as looking back at the definition of the corecursor,
we will require $P$ to be able to accept `ULift α ::: ULift β`.
If we do not add the ability to lift $P$,
// TODO: verify this
the unifier will force $cal(U) = cal(V)$,
thereby invalidating all the work we did in the previous section.
We define it as `ULift P := ⟨ULift P.1, λ x ↦ ULift (P.2 x.down)⟩`.
This definition also satisfies naturality.
This works and now we can move on to generalizing the corecursor.
// #footnote[
//   TODO: Speak with JV / W to see if this might be done in the lit,
//   Ex : Locally presentable and accessable categories Adameck roshiski
// ].
// This definition is also natural in the expected way.

==== Generalizing the corecursor

#impl([], "[UPSTREAMED],sme/Sme/PFunctor/ForMathlib/M.lean")

Now with all the work in the previous section,
first we generalize a helper function#footnote[Done in PR #link("https://github.com/leanprover-community/mathlib4/pull/30400")[♯30400] to Mathlib ],
then we can define
`corecU : {α : TypeVec.{𝓤} n} → {β : Type 𝓥} → (g : β → ULift P (ULift α ::: ULift β)) → β → M.{𝓤} P α`.
Notably we are able to fit the object into $cal(U)$
(this will not be the case for the SME).

The functions `corecU` and `dest` satisfy an unfolding equation.
This is more complex than it used to be as we now need to lower the universe before we continue with the mapping.

////////////////////////////////////////////////////////////////////////////////

=== Polynomial equivalents<sec:polyeqs>
#impl([], "sme/Sme/PFunctor/EquivP.lean")

#let KEIZER = cite(<cite:keizer>, form: "prose")

// TODO: Prefer polynomial functor over polynomial
// TODO: Finish Keizer feedback.

Often when people talk about polynomial functors,
they are referring to structures that are equivalent
As in a `List` is not a pair of a head and child types,
but it is equivalent to a polynomial of this form.
For this I made a type-class `EquivP` (@peq:ls:peq) heavily inspired by how it was done in #KEIZER and Mathlib.
I took the definition of curried type-functions from QPFTypes @cite:keizer and implemented coherences for these for the common polynomials.
I used this to make it cleaner to work with ITrees when I reached that point.
A key difference is that I implemented it using the output curried type-functions as an outParam,
this means that I can synthesize the curried type-functions from a given polynomial allowing for an easier user interface.
Type class synthesis works similar to a prolog engine and `outParam` corresponds to the prolog mode `?`,
whereas the default mode is `+`.

#figure(
  raw(takeL(read("../../sme/Sme/PFunctor/EquivP.lean"), 89, 95), block: true),
  caption: [Type-class `EquivP` for polynomial equivalents]
)<peq:ls:peq>

=== Natural isomorphisms of MvFunctors
#impl([], "sme/Sme/PFunctor/NatIso.lean")

// A problem I found when working with isomorphisms of Mv(P)Functors was that isomorphisms need numerous coherences proven about them.
When working with isomorphic Mv(P)Functors,
it is often useful to require them to be natural.
Formally this means an isomorphism `iso` satisfies `f <$$> iso x = iso (f <$$> x)`.
To solve this I defined natural isomorphisms of multivariate functors @natiso:ls:def.
The naturality of the inverse of the isomorphism is provable.
// Using what I learnt in category theory, I proved the symmetric direction of `nat'`.

#figure(
  raw(takeL(read("../../sme/Sme/PFunctor/NatIso.lean"), 6,10), block:true),
  caption: [Natural isomorphisms on MvFunctors]
)<natiso:ls:def>



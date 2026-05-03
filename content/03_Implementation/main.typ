#import "../utils.typ": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge, shapes
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

// TODO: fix this
#let impl(content, path) = align[Addressing: #content, Path: #raw(path)]

This chapter describes the implementation of each of the requirements stated in @sec:rq.
I will break it down into a common section,
then go by individual components.
I will also mention which parts are in process of being upstreamed and which parts are already in #MATHLIB.

The Lean component of this repository,
and how they relate to each of the requirements can be seen in @impl:fg:overview.
Additionally the import graph can be seen in @rep:fg:import.


#let fbox(boxc) = node.with(snap: -1, fill: boxc.lighten(90%), stroke: boxc)

#let sl = 2
#figure(
  [
  #set text(10pt)
  #diagram(
    cell-size: 4mm,
    fbox(teal)(enclose : (<slib>, <dt>)),

    node((1,1-sl), [PA Impl], name: <spa>),
    edge("->"),
    node((2,0-sl), [Equiv], name : <seq>),
    edge("<-"),
    node((2,1-sl), [SME Impl], name: <ssme>),
    fbox(teal)(align(top + left)[Stream], enclose: (<spa>, <seq>, <ssme>, (0,-1)), snap: -1, name: <s>),

    node((1,1), [PreM], name: <prem>),
    edge("->"),
    node((2,1), [SM], name : <sm>),
    edge("->"),
    node((3,0), [HpLuM], name: <hplum>),
    edge("<-"),
    node((2,0), [Equiv], name: <peq>),
    edge(<sm>, <peq>, "->"),
    fbox(teal)(align(top+left)[Polynomial], enclose: (<prem>,<sm>,<hplum>,<peq>, (0,1)),name : <slib>),

    edge(<hplum>, (3,2), <dtd>, "->"),

    node((2,2), [DT Defs], name: <dtd>),
    edge("->"),
    node((1,3), [DT Corec],name : <dtc>),
    edge(<dtd>,<dtf>,"->"),
    node((2,3), [DT Inject], name: <dtf>),
    fbox(teal)(align(top+left)[Deep thunks], enclose: (<dtf>,<dtd>,<dtc>, (0,2)), name: <dt>),

    edge(<hplum>, (3,3), <free>, "->"),
    edge(<free>, (2.7,4), (2,4), <clib>, "-"),
    fbox(teal)((2.7,3), [Free], name: <free>, ),

    edge(<hplum>, (3, 4), (2,4), <clib>, "->"),
    edge(<dtc>,   (1, 4), (2,4), <clib>, "->"),
    edge(<dtf>,   (2,4), <clib>, "-"),

    node((2,5), [Coinduction library], name: <clib>),

    // node(, [ABI], name: <abi>),
    edge(<abi>, <hplum>, "->"),
    fbox(teal)((3, -1), [ABI], name: (<abi>) ),

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

    node((5,5), "ITree library", name:<itl>),
    edge(<iti>, (4,3), (5,3), <itl>, "-"),
    edge(<wbsi>, (5,3), <itl>, "->"),

    fbox(teal)(enclose: (<itd>, <wbsi>) ),
  )
  ],
  caption: [Birds-eye view of components of the project],
)
<impl:fg:overview>

== Common

Many large components of this project do not fit into any of main components.
This section is dedicated to this exact kind of component.


=== Transliteration

A family of functions,
that keep solving problems throughout this dissertation are what I call transliterations.
Given some parameter span#footnote[
  This is not necessarily a type, as Lean does not have omega-types (Set$omega$ from Agda) @cite:agda-univ.
]  $X$,
either in some $Type$,
or more commonly over some universe $cal(U)$.
We define a transliteration on $X$ as a family of functions $t_(a,b) : X a -> X b$,
such that they are closed under composition $t_(b,c) compose t_(a,b) = t_(a,c)$#footnote([
  This is similar to saying it is an idempotent,
  but technically $t_(b,c)$ and $t_(a,b) $ are not the same function.
]),
and the self-path is identificaion $t_(a,a) = id$.

The trivial instantiation of a transliteration is a `cast`#footnote([
  Or if you read the HoTTbook @cite:hottbook, this is called `transport`.
]),
here we pick $X$ as equal types,
obviously `cast aa = id` and `cast bc ∘ cast ab = cast (ab.trans bc)`.
One could even say that a transliteration is a function that behaves like `cast`.

An example we will keep defining is universe transliteration,
here we take $X = ULift_((-))$,
using this we define the transliteration as seen in @tr:ls:code.
This is the closest we get to having omega-types and cumilativity in Lean;
as long as the function is applied at a usage of ULift it all works.
We will use this function to define transliteration between universe-lifted polynomials,
we will see more of this in @sec:ulift_p.

#let f = takeL(read("../../sme/Sme/ForMathlib/Data/ULift.lean"), 2, 11)

#figure(
  raw(f, lang : "lean", block:true),
  caption: [Transliteration between universes of types]
)<tr:ls:code>

Another major usage of a transliteration was used when defining the eliminator for `ABI`,
I will discuss this more when we get to @sec:abi.
This was where I first discovered transliteration,
and made it possible to define a universe-polymorphic eliminator.

////////////////////////////////////////////////////////////////////////////////

=== Expanding the progressive approximation theory

#impl([], "sme/Sme/ForMathlib/{PFunctor/*,TypeVec.lean}")

During the feasability assesment I noticed that,
in the current formalised theory of polynomials,
the equivalence would not even type-check.
This stemmed from a problem with the corecursive principle for the #MT in the old implementation.
`corec : {α : TypeVec.{u} n} → {β : Type u} → (g : β → P (α ::: β)) → β → M P α`
#footnote(link("https://github.com/leanprover-community/mathlib4/blob/7a60b315c7441b56020c4948c4be7b54c222247b/Mathlib/Data/PFunctor/Multivariate/M.lean#L152-L154")) #MATHLIB.
The problem here is that both $alpha$ and $beta$ have to both reside in $cal(U)$.
Solving this is done through the next two sections.

==== Universe lifting of polynomial functors.<sec:ulift_p>

The main problem caused here comes from the fact that Lean is not cummulative.
This means it is impossible to express a universe heterogeneous typevector.
In other words $alpha ::: beta$ is only typable if $alpha : "TypeVec".{cal(U)} n$ and $beta : "Type" cal(U)$.
The natural way of solving this is using the supremum in universe levels you get from
$ULift : "Type" cal(U) arrow "Type" (max cal(U) cal(V))$.
This means we can have $beta : "Type" cal(U)$ and $alpha : "Type" cal(V)$,
then ulift both of them to a common universe $ULift alpha ::: ULift beta : "TypeVec".{max cal(U) cal(V)} (n+1)$
#footnote[Note we overload ULift as a notation to refer to lifting other structures as well.].

Noticable the next hurdle we encounter is that PFunctors are restricted to a universe level.
Recall the definition from @sec:poly.
Observe how for a $"MvPfunctor".{cal(U)} n$,
we require that both the head and child reside in $cal(U)$.
This will also cause problems,
as looking back at the definition of the corecursor,
we will require $P$ to be able to accept $ULift alpha ::: ULift beta$.
If we do not add the ability to lift $P$,
// TODO: verify this
the unifier will force $cal(U) = cal(V)$,
thereby invalidating all the work we did in the previous section.
Luckily lifting a PFunctor is relatively easy.
We define it as $ULift P eq.delta chevron.l ULift P.1, lambda x mapsto ULift (P.2 x."down") chevron.r$.
This works and now we can move on to generalizing the corecursor.
// #footnote[
//   TODO: Speak with JV / W to see if this might be done in the lit,
//   Ex : Locally presentable and accessable categories Adameck roshiski
// ].
This definition also satisfies naturality.
// This defintion is also natural in the expected way.

==== Generalizing the corecursor

#impl([], "[UPSTREAMED],sme/Sme/PFunctor/ForMathlib/M.lean")

Now with all the work in the previous section,
first we generalize a helper function#footnote[Done in PR #link("https://github.com/leanprover-community/mathlib4/pull/30400")[♯30400] to #MATHLIB ],
then we can define
`corecU : {α : TypeVec.{u} n} → {β : Type v} → (g : β → ULift P (ULift α ::: ULift β)) → β → M.{U} P α`.
Notably we are able to fit the object into $cal(U)$
(this will not be the case for the SME).

The functions `corecU` and `dest` satisfy an unfolding equation.
This is more complex than it used to be as we now need to lower the universe before we continue with the mapping.

////////////////////////////////////////////////////////////////////////////////

=== Polynomial equivalents<sec:polyeqs>
#impl([], "sme/Sme/PFunctor/EquivP.lean")

#let KEIZER = cite(<cite:keizer>, form: "prose")

Often when people talk about polynomials, they mean structures that are equivalent to polynomials.
This is for example how #KEIZER refers to polynomials.
I found it useful to work like this as well,
for this I made a type-class `EquivP` heavily inspired by how it was done in #KEIZER and #MATHLIB.
I took the definition of curried type-functions (CTFs) from @cite:keizer and implemented coherences for these for the common polynomials.
I used this to make it cleaner to work with ITrees when I reached that point.
A key difference is that I implemented it using the output CTF as an outParam,
this means that I can synthesize the CTF from a given polynomial allowing for an easier user interface.
Type class synthesis works similar to a prolog engine and `outParam` corresponds to the prolog mode `?`.

=== Natural isomorphisms of MvFunctors
#impl([], "sme/Sme/PFunctor/NatIso.lean")

A problem I found when working with isomorphisms of Mv(P)Functors was that isomorphisms need numerous coherences proven about them.
I observed that the coherences I was proving corresponded to naturality.
To solve this I defined natural isomorphisms of multivariate functors.
Defining this was relatively simple and can be seen in @natiso:ls:def.
Using what I learnt in category theory,
it was easy to prove the symmetric direction of `nat'`.

#figure(
  raw(takeL(read("../../sme/Sme/PFunctor/NatIso.lean"), 6,10), block:true),
  caption: [Natural isomorphisms on MvFunctors]
)<natiso:ls:def>

== Stream implementation <sec:s>

#impl([@rq:sme:stream:impl, @rq:sme:stream:equiv], "sme/Sme/Stream/*")

#let pdef = read("../../sme/Sme/Stream/PDefs.lean")
#let sdef = read("../../sme/Sme/Stream/SDefs.lean")
#let equiv = read("../../sme/Sme/Stream/Equiv.lean")

As proving these equivalences is challenging I decided I would start by implementing it for the special case of streams.
Streams are the text-book coinductive datatype that most people know as mentioned in @sec:coind.
Therefore I expected this to be pedagogical to implement.

=== State-machine streams <sec:s:sme>
#impl([@rq:sme:stream:impl], "sme/Sme/Stream/SDefs.lean")

#let sds = partL(sdef, 7, 9, 11, 17, 27, 29, 43, 55, 64, 69, 78, 88, 99)

First I set up a class of prestreams,
these correspond to the corecursive principle holding their type.
I had to define `hd` and `tl` for streams here corresponding to the destructors of streams.
Care had to be taken to ensure that the definition would work under a quotient as well.

#figure(raw(sds.at(1) + sds.at(3), block : true), caption: [PreStream and destructors])

Then I defined a bisimilarity relation;
heads being equal and tails bisimilar as seen in @sec:bisim.
I proved this was an equivalence relation (reflexive, symmetric, transitive).
Using this I defined a setoid on `PreStream`s.

#spg(
  figure(raw(sds.at(4), block : true), caption: [Bisim definition]),
  figure(raw(sds.at(6), block : true), caption: [Equivalence relation]),
  columns: (auto, auto),
  caption: [`PreStream` setoid]
)

// TODO: check this uses `Stream` and Stream and stream consistenly.
The definition of an SME `Stream` is then preobjects quotiented by this setoid.
Quotients are famously a difficult to work with#footnote[
  #link("https://proofassistants.stackexchange.com/questions/908/what-exactly-is-setoid-hell")
  #link("https://stackoverflow.com/questions/65493694/why-do-calculus-of-construction-based-languages-use-setoids-so-much/65509179")
].
When lifting the destructors from `PreStream`s to `Stream`s I have to go through the lifting function of quotients.
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

The next step was defining a coinduction principle,
in the code this is called `bisim` to align to convention with #MATHLIB.
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

To implement PA streams,
I had to first implement the stream's base functor,
this is easy for streams as they have one constructor (so a head of $1$),
and each of the families only hold one instance of the value (so child $lambda i (). 1$).

#spg(
  figure(raw(pds.at(1), block : true), caption: [Functor]),
  figure(raw(pds.at(2), block : true), caption: [PStream]),
  columns: (auto, auto),
  caption: [PStream definition]
)

From here I defined the destructors of streams this is as simple as calling the child with the correct indicies.

#spg(
  figure(raw(pds.at(4), block : true), caption: [Head of a PStream]),
  figure(raw(pds.at(5), block : true), caption: [Tail of a PStream]),
  columns: (auto, auto),
  caption: [PStream destructors]
)

For symmetry I defined a syntactically identical bisimilarity relation on PA streams,
and for this I prove a coinduction principle for PStreams of this relation.
This proof proceeded by using the coinduction principle on general polynomials.

#spg(
  figure(raw(pds.at(6), block : true), caption: [Bisimilarity of PStreams]),
  figure(raw(pds.at(8), block : true), caption: [Coinduction principle for PStreams]),
  columns: (auto, auto),
  caption: [Coinduction principle for PStreams]
)

The corecursor was directly lifted from the defintion on M-types,
all it required was doing a series of pattern-matches to get the right structure.
I will do something similar for ITrees and the NTMonad.

#figure(raw(pds.at(9), block : true), caption: [`corec` for PStreams])

=== Proving the equivalence <sec:s:equiv>
#impl([@rq:sme:stream:equiv], "sme/Sme/Stream/Equiv.lean")

The functions of this equivalence correspond to:
the corecursors parameterised by the destructors of the opposite type.
Proving that these are inverses was slightly involved,
I toyed around with a few different relations trying to make it work.
In the end I landed on the straightforward equality as seen in @stream:fg:equiv.
This solved and made the entire proof small after cleaning.

Having done this I was ready to approach the case of the polynomial.
This turned out to be harder than I expected.
Observant readers may notice the statement I proved is subtly the wrong statement.
At the time I did not see this,
but the equivalence should not be `SStream.{u, u} A ≃ PStream A`,
but `SStream.{u, max u v} A ≃ PStream A`.
This statement is harder to prove.

#spg(
  figure(
    raw(takeL(equiv, 4, 15), block: true),
    caption: [Equivalence]
  ),
  <stream:fg:equiv>,
  columns: (auto, auto, auto),
  caption: [Key code involved in Stream equivlance]
)

////////////////////////////////////////////////////////////////////////////////

== State-machine encoding of M-Types<sec:impl-sm>

#impl([@rq:sme:impl, @rq:sme:equiv], "sme/Sme/M/*")

Recalling the definition of the SME from @sec:m:sme,
and proceeding how we did in @sec:s:sme.
First make a class of preobjects,
then define a bisimilarity relation,
make the SME by quotienting this relation.

=== Rephrasing bisimilarity for #MTs <sec:bs>
#impl([@rq:sme:cind], "")

Coming into this dissertation,
I implemented almost all of it using the definition of bisimilarity as given in #MATHLIB as @bs:ls:mathlib.
This definition turned out to be hard to work with.
Later in my dissertation I found an equivalent formulation using the universal property of the terminal object,
since bisimilarity requires all but the last family to be equal,
I equalize last families.
This reduces the up-front cost of proving an #MT bisimilarity,
as previously one had to instantiate `a f f₁ f₂`,
finding these values was difficult and time consuming as they usually required partially unfolding the definition.
The definition given in @bs:ls:my ended up being much easier to use.
One of the reasons for this is that all the proofs about mappings of polynomials can be applied in a `simp` call to get the preliminary proof.
This makes bisimilarity statements easier to work with.

// For an arbitrarry polynomial we can define bisimilarities for its cofix point.
// Mathlib has a definition for this for the PA encoding #MATHLIB.
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
    caption: [#MATHLIB definition]
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

=== PreM
#impl([@rq:sme:impl], "sme/Sme/M/PreM.lean")

// TODO(DONE): remove fluff words: simply, nice, very, quite

To define PreM we do exactly as we did for Streams,
making sure to use the signature of `corecU` over `corec`.
For the case of streams,
we had two destructors `hd` and `tl`,
in this case we have only one `dest`.
Because of universe-levels we can not define a signature like `dest : PreM P α → P (α ::: PreM P α)`,
as `PreM P α` resides in $Type max cal(U) cal((V + 1))$ for some $cal(V)$,
instead we get the signature `dest : PreM P α → ULift.{max u (v+1)} P (ULift α ::: PreM P α)`.
The definition of this requires transliterating the output of calling the generating function,
as the generating function produces a $ULift_(max cal(U) cal(V)) P$.

In addition to the two functions `corec` and `dest` we have defined for `PreM`,
I also need `ULift`ing of `PreM`s.
This is a function taking a `PreM.{u, v} P α` to a `PreM.{u, max v w} P α`.
This was defined in such a way to take as much care as possible to make it easy to work under quotients.
// when we get to that section we can see to what extent I succeeded at this.

// TODO: update this to be using the new defintiion of bisim.
With all this plumbing done we can now move on to define bisimilarity.
It is impossible to define bisimilarity of `PreM`s using the `coinductive` syntax I set up.
Instead, I use the relational lifting of multivariate functors.
Relational lifting lets me reason about the children of a polynomial functor when instantiated correctly.
The relational family I want to use for this is bisimilarity for the first argument,
and identity for all of the other children.
This is done using an existential directly.

// This is why I gave the first-principles definition of a coinductive predicate in @sec:coindp,
// as we need to use this explicit cofixpoint construction to build the relation.

Proving this is an equivalence relation is much harder than for the case of streams.
The reason for this is the much more roundabound definition of bisimilarity.
Luckily #MATHLIB has a lemma for working with liftR and PFunctors.
These proofs can be found in `PreM.lean`.
This gives `PreM` a setoid structure and be used to instantiate the quotient.

=== SM <sec:sme:impl>
#impl([@rq:sme:impl], "[UPSTREAMED],sme/Sme/{M/SM.lean,HEq.lean}")

I expected implementing the SME $M$-types to go as smoothly as implementing SME streams.
Defining the corecursor was as simple,
every other definition was much harder.

The destructor of SMs will be given by quotient lifting as for streams.
The function is also similar,
take the preobject destructor and equalize deeper occurances as to not leak the type.
The stability of this function is proven by soundness of quotients for the corecursive case,
and lifting the equality from bisimilarity for the other cases.

Proving the coinduction principle difficult initially.
The reason for this,
as with most things in this dissertation,
is heterogeneous equalities.
Since hetrogenous equalities have few congruences#footnote[
  An example is `(List A = List B) = (A = B)` is independent of Lean.
],
often I need to solve them on a case-by-case basis.
As a consequence I ended up writing a few crucial lemmas,
these include `dcongr_heq` which I upstreamed.
// along with `hfunext_iff` which I have an open PR with TODO UPSTREAM.
Therefore, this proof has both forward and backward sections.
To save our sanity, I decided to rewrite it using @sec:bs,
after doing this the proof fell out.

The next proof I had to do was with regards to universe lifting of SME #MTs,
this involves lifting the carrier instead of any part of the polynomial.
This is the universe lifting function we defined for PreM types.
Universe lifting of this component is needed for proving the generalized equivalence we stated in @sec:s:equiv.

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

=== Proving the equivalence<sec:sme:equiv>

#impl([@rq:sme:equiv], "sme/Sme/M/Equiv.lean")

We know from streams,
each of the directions will be given by each of their corecursors,
additionally universe changes also must be handled.
Finding the functions that satisfied these universe chances was non-trivial,
as `map` can not change universe levels,
therefore we need new functions for this (`transliterateMap`).
The resulting functions are given in @sme:ls:fns,
here we can see the subtle universe changes both up and down.

#figure(
```lean
let msm := MvFunctor.map (TypeVec.id ::: ULift.up.{u, max u v + 1}) ∘ SM.dest
let mpa := liftAppend.{u, max u v} ∘ M.dest P ∘ ULift.down.{max u v, u}
let toFun  := .corecU P msm,
let invFun := .corec mpa ∘ ULift.up,
```,
  caption: [Functions of the equivalence]
)<sme:ls:fns>


We now need to prove that the two functions are inverses.
While proving these equalities I was not familiar with bisimilarities,
and tried many invariants.
Finally I landed on forcing their equalities.
Once this was found, I had to prove it was a bisimilarity.
I picked the head of one of the applications,
and was lucky this was definitionally equal.
This means the equality for the children is homogenous.
The other direction followed analogously.

#figure(
  raw(takeL(read("../../sme/Sme/M/Equiv.lean"), 14, 56), block:true),
  caption: [SME and PA equivlance `equivP`]
)

// This was the main deliverable of the project,
// and would make high performance low universe #MTs (HpLuM).

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
#impl([@rq:abi:impl, @rq:abi:elim, @rq:abi:opt], "sme/Sme/ABI.lean")

#MATHLIB has a type called `Shrink`.
This is a type which takes an equivalence between an `A : Type u` and a `B : Type v`,
and returns a `Type u`.
It has one constructor `B → Shrink A B`,
and one destructor `Shrink A B → B`,
which are inverses.
The definition given in #MATHLIB is non-computable using choice,
this makes it useless for code-generation.
Originally I tried to make it computable by adding an `@[implemented_by]` to it,
which turned out not to work.
The reason this did not work has to do with the fact that `Shrink` strangely satisfies the univalence axiom:
given `Shrink A` and `Shrink B` along with `A ≃ B`,
one can prove `Shrink A = Shrink B`.
Aaron Liu from the #MATHLIB community used this in combination with quotients and trustCompiler to prove false.
From this I understood that I would have to make my own variation of the type.
The proof Aaron Liu used can be found in @a:cm.

From this I decided to make my own variant I called the ABI type.
Given an isomorphism $e q : alpha tilde.equiv beta$ for some types $alpha$ and $beta$,
I define the type $#raw("ABI") alpha beta e q$ to have two constructor-eliminator pairs `mkA`, `mkB`, `destA` and `destB`,
satisfying the diagram seen in @abi:fg:ops.
Additionally I had an elimination principle satisfying expected $beta$-rules with the two constructors.
Through making the definition opaque I had problems with universe levels.
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

      node((1, 1), $#raw("ABI") alpha beta e q$, name : <S1>),
      node((2, 2), $#raw("ABI") alpha beta e q$, name : <S2>),

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
//     node((0, 1), $"ABI" alpha beta$, name : <S1>),
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
// TODO: Shrink and ABI are related. "Universe altering type"
// TODO: Highlight the delta from the shrink type

////////////////////////////////////////////////////////////////////////////////

=== High performance Low universe #MT (HpLuM) <sec:sme:abi>
#impl([@rq:sme:abi], "sme/Sme/M/HpLuM.lean")

After implementing the `ABI` type, it is time to put it to use.
To do this, first I tried to use the equivalence,
what I found was this leaked the universe of the carrier.
I realised, I did not have to make a new equivlance for this,
but paste the previous equivalence with itself.
I called this equiv cross universe (`equivXU : SM.{u, max u v} P α ≃ SM.{u, max u w} P α`).
One can observe this equivalence forms a transliteration.
Additionally one might wonder, does composing the equivalence with itself become a noop?
To which the answer is no, as we are parameterised in universe levels, so technically these are different functions.
This became a challange as the performance of this equivalence was $cal(O)(n^2)$.
To avoid this, I decided to mark this as `@[implemented_by, irreducible]` with a cast.
Once this was done I could start implementing the HpLuM.

The HpLuM is the ABI type, parameterised by the equivalence given in the last section at universes $cal(U)$, $cal(U)$.
These universes prevent the carrier from being leaked.
From here we define the corecursor of the same signature as in the `SM`,
this uses a cocktail of universe changes, first one up using `SM.uLift`, then one down using `equivXU`,
finally being passed into a `mkB` constructor of the `ABI` type.
The next step is giving a `dest : HpLuM P α → P (α ::: HpLuM P α)`,
this is done using the eliminator for the `ABI`-type.
The reason I use this instead of a `destB` (which is what `rec` compiles to),
using the eliminator lets me prove the coherence of the SME and PA inline.

Once this was done I started proving equations of these methods.
The first one was `dest_corec`, which has the expected signature.
Followed by a coinductive principle.
I also added an in-universe version of `corec` called `corec'`,
this has the exact behaviour of the old non generalized corecursor on PA #MTs.
In addition to this I added corecursor unrolling lemmas and mapping lemmas.
From here I then proved co-Lambek's theorem @cite:lambek.
Further I proved HpLuM is multifunctorial as the polynomial defintion,
along with destructor lemmas for map.

I added functionality to reason about polynomial equivalents (@sec:polyeqs),
this is the reason I picked the CTF to be the outParam,
as it lets these functions synthesize the correct CTF without annotations.

I also found I needed a defintion of ulifting of HpLuMs.
Like everything to do with universe levels, this turned out to be a challenge.
I also proved naturality conditions of these.

The next thing I had to prove, was transportation of natural isomorphisms.
This takes a natural isomorphism between `P` and `P'`,
and lifts it to a natural isomorphism between `HpLuM P` and `HpLuM P'`.
This will be used when we start working with futumorphic productivity.

With this completed, I have a usable #MT library.

== Non-Termination Monad (NTMonad)<sec:ntmonad>
#impl([@rq:ntm:impl], "sme/Sme/ITree/*")

The NTMonad is an example of a coinductive datatype.
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

To define ITrees in lean, we implement the functor,
and prove results about polynomial equivalents on them.
When KTrees are mentioned in the ITree paper @cite:itree,
it is a function of the form `A -> ITree E B`,
for those familiar these are kleisli morphisms @nlab:kleisli_category.

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

ITrees have many operations and equations defined in the paper @cite:itree.
These can be seen in @itree:tb:fns,
here I have annotated all of the functions I have implemented (as L) from the paper @cite:itree (as R),
and the other implementation of ITrees for lean by #MS.
A boon of the Lean implementations over Rocq,
is that strong bisimilarity implies equality.
This makes using some of the proofs easier.

#let gfbox(title, rowspan : 1, colspan: 1, body) = grid.cell(rowspan : rowspan, colspan: colspan)[ #colorbox(title : title, color: (stroke : teal, fill : rgb("#0000")))[#body] ]

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
      - `trigger : E A → ITree E A`#super[LR]
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
  = vis e λy. bind (k₁ y) k₂` #super[LR\*M]
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

    #h(1em) \* = strong bisimilarity rather than equality in Rocq

    #h(1em) #sym.dagger = proven using coinduction-up-to in Rocq]]
)
<itree:tb:eqs>
]

=== The ITree Monad<sec:itree:mon>
#impl([@rq:it:mon, @rq:it:comb, @rq:it:lmon], "sme/Sme/ITree/Monad.lean")

ITrees form a monad, where the binding operation corresponds to pasting trees together,
as seen in @it:fg:bind;
`bind` iterates through the tree and calls the function on seeing a `ret`.
The `ret` constructor is the monads unit.
To ensure it is lawful there is a set of proof obligations,
these can be seen in @itree:tb:eqs.

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
For example the program `println 10` and `println (10 + 0)` are _equivalent_,
but not syntactically equal.
We can note that the effects produced by these programs are the same,
yet one takes more steps to get there.
This is where we consider weak bisimilarity instead.
One can think of weak bisimilarity is an equivalence relation modulo silent steps;
two objects with the same observable effects but with a different tau count.
The rocq definition #footnote[The syntax is slightly simplified for reading purposes here]
and my definition differs.
This is mainly because I decided to implement only homogeneous weak bisimilarity,
and in rocq they have coinduction-up-to, making proofs much easier.
In my defintion I need to 'bake in' as many principles as possible.
This is the reason for the `refl` constructor.
In the defintion I use `EStep` to mean some amount of taus,
and `Step` to mean a productive step to some non-tau value.
`EStep` forms a linear join-semilattice,
`Step` inherits some of this structure, but is slightly easier to work with.
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

In the ITree paper @cite:itree it is proven weak-bisimilarity is an equivalence relation.
A table of what is proven in each implementation can be found in @itree:tb:eqs.
Out of these the ones marked with #sym.dagger have been proven using coinduction-up-to.
These were particularly technical to prove and required defining helper predicates.
The main instance of this is `iter`-congruence,
for this I had to define two predicates `IterTrace` and `IterCotrace` for productive and spinning `iter`s respectively.
This is used to define, if the two KTrees are weakly bisimilar,
the generated ITrees have the same productivity behaviour.
This proof was indirect and required the creative step of coming up with the (co)trace abstraction.

=== A formally verified optimization
#impl([@rq:it:wbisim], "sme/Sme/ITree/WBisim/*.lean")

One of the main use cases of Interaction Trees is program verification.
I implement a simple imperative language IMP as seen in @itree:ls:istx,
I give it the denotational semantic as @itree:ls:isem,
then I define an optimization `simpl` @itree:ls:simpl on this.
All `simpl` does is simplifies constant expressions,
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

== Futumorphic Productivity<sec:prod>

// During my internship under AK and TG,
// I made a structure I then called `DeepThunk`s.
// I now refer to them as the induced productivity monad.
// They are the general way of constructing productive functions on cofixed points from terminating functions.
As mentioned in @sec:coind, every corecursive function has to be productive.
In the current library defintion,
this means we need to define the function using the corecursor
`corec {β α} : (β → P (α ::: β)) → β → M P α`.
This can be cumbersome as one can only define one layer of the coinductive datatype at a time.
During my internship under #AK and #TG,
I had an idea of how to solve this,
unfortunately I did not have time to implement this completely during the internship.
The idea came from thinking about what choices I had when creating layers.
After the first layer (which is required for productivity),
we have a choice to either `recall` the corecursor from that point,
or `cont`inue a deeper structure.
We also observe that the argument we have to provide to `recall` would be the carrier.
A visualization of this structure can be seen in @futu:fg:cp.
Putting these ideas together I created the structure #AK named 'DeepThunk' (`DT` for short).
This structure, `DT P (α ::: β)`, was given as a cofix point of `μ ρ. (P α (Sum β ρ))`
(given in `sme/Sme/M/DT/Defs.lean`).
I then made a universe polynomial corecursor I called `dtcorec {β} : (β → DT P (α ::: β)) → β → M P α`,
an injector `inject β : M P α → DT P (α ::: β)`,
and a flattener `flatten : DT P (α ::: M P α) → M P α`.
These were extremely challenging to reason about,
but in the end I successfully proved an unfolding lemma of the corecursor,
where it corresponds to doing a mapping operation then flattening.

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

Seeing how much potential DeepThunks had,
I asked #AK whether he had seen a structure like this before,
and he pointed me to #FANTOMORPH.
This paper discusses different kinds of morphisms @cite:fantomorph.
Here I found futumorphisms,
which looked exactly like the structure I was looking for.
These use the free monad and make a morphism `futu {β} : (β → P (α ::: Free P α β)) → M P α` @cite:fantomorph @cite:futu @cite:urs.
The relationship betweem the `Free` monad and `DT` can be seen in @futu:fg:freedt#footnote[Here $trl$ is application as seen in OCaml.].
This demonstrates that `P (α ::: Free α β)` is exactly `DT`.
A crucial difference is that `Free` has a well-defined notion of constructor and eliminator,
while `DT` has nothing equivalent.
This means as I wrote around 1700 lines for `DT`,
almost all this functionallity fit into 700 lines for the futumorphism.
The implemented functions can be seen in @futu:tb:free.

#figure(
  $ underbracket((P α -) trl overbracket((beta plus.o -) trl (P α -) trl (beta plus.o -) trl ..., "Free monad"), "DeepThunk") $,
  caption: [Relationship between `Free` monad and `DT`],
)<futu:fg:freedt>


// !!!
//
// I ended up writing two implementations
// (excluding my earlier attempt during my internship).
// This is the DeepThunk and the Free monad implementations.
// Out of these the Free monad implementation is much more feature rich,
// this was only possible from the learning of DeepThunks,
// for which it deserves to be mentioned.

// Initially when trying to implement a structure to check productivity,
// I picked the simplest structure I could think of.
// This then developed into becoming what I have now included in my dissertation as DeepThunks.
// For this I developed the theory,
// including but not limited to an injector,
// and a corecursor.
The definition given for deep-thunks used the carrier as one of the mapped parameters to the polynomial.
Meaning I did not need to implement a dedicated map function,
this turned out to be a mistake.
The problem here is that any multivariate map can change the carrier.
This meant that for all equations involving the multivariate map,
had to be restricted to functions concatenated together.
This also meant that working with binds became a mess for universe levels.
Fundamentally we want to treat this as a different parameter so we can also use do notation.
Proving facts about binds also became extremely tedeous.
We also did not have a monad unit as the structure of the base polynomial P can be arbitrary.
Another problem was DeepThunks accross universes required applying a sequence of natural transformations.
These natural transformations had few equations other than naturality proven about them.
Additionally some proofs are unproven as they became too difficult.

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
proving many theorems became as simple as just invoking `simp`.
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
      - `inject β : HpLuM P α → Free P α β`
      - `flatten : Free P α (HpLuM P α) → HpLuM P α`
      - `futu' : (β → P (α ::: Free P α β)) → β → HpLuM P α`\*
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


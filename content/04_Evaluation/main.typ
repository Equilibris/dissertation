#import "@preview/subpar:0.2.2" as subpar: grid as spg
#import "../utils.typ": *

#set raw(lang: "lean")

// TODO: Talk about validation

This chapter will discuss and evaluate each of the components of the dissertation.
As mentioned in @sec:method,
I have been writing proofs verifying the correctness of my different components.
I refer to these throughout this chapter.
// TODO: Refer to these throughout the chapter
// Type signatures often are unable to encode performance (other than maybe something substructural),
Type signatures alone do not encode performance guarantees;
therefore, I write benchmarks and read LCNF to evaluate these features.
There will be a comparison of coinductive and ITree implementations,
and finally an assessment of the ergonomics of futumorphic and deep-thunk productivity.

An overview of all the requirements laid out can be viewed in @eval:tb:state.

#let rqtable(..args) = table(
  columns: 4,
  table.header[Req.][Met][Evidence][Path],
  ..args
)

#spg(
  grid.cell(
    rowspan: 2,
    figure(
      rqtable(
        [@rq:sme:stream:impl], [Y], [@sec:s], [`Stream/SDefs.lean`],
        [@rq:sme:stream:equiv], [Y], [@sec:s:equiv], [`Stream/Equiv.lean`],
        [@rq:sme:impl], [Y], [@sec:sme:impl], [`M/Defs.lean`],
        [@rq:sme:fast], [Y], [@sec:smevpa], [-],
        [@rq:sme:equiv], [Y], [@sec:sme:equiv], [`M/Equiv.lean`],
        [@rq:sme:ntm], [Y], [@sec:ntmonad], [`NTMonad/Defs.lean`],
        [@rq:sme:cind], [Y], [@sec:sme:abi], [`M/{HpLuM,SM}.lean`],
        [@rq:sme:abi], [Y], [@sec:sme:abi], [`M/HpLuM.lean`],
        [@rq:sme:itree], [Y], [@sec:itree], [`ITree/Defs.lean`],
        [@rq:sme:prod], [Y], [@sec:prod], [`M/{DT/*,Futu.lean}`],
        [@rq:sme:zc], [N], [@sec:smevpa], [-],
      ),
      caption: [State-machine encoding],
    )
  ),
  figure(
    rqtable(
      [@rq:ntm:impl], [Y],   [@sec:impl-sm], [`NTMonad/Defs.lean`],
      [@rq:ntm:mon],  [Y\*], [@sec:itnt],    [`ITree/Monad.lean`],
      [@rq:ntm:lfm],  [Y\*], [@sec:itnt],    [`ITree/Monad.lean`],
      [@rq:ntm:prod], [Y],   [TODO sec:futu:case], [`NTMonad/Defs.lean`],
    ),
    caption: [NT Monad],
  ),
  figure(
    rqtable(
      [@rq:abi:impl], [Y], [@sec:impl-sm], [`AltRepr.lean`],
      [@rq:abi:elim], [Y], [@sec:impl-sm], [`AltRepr.lean`],
      [@rq:abi:opt],  [Y], [@sec:eabi],    [`AltRepr.lean`],
      [@rq:abi:zc],   [Y], [@sec:eabi],    [`AltRepr.lean`],
    ),
    caption: [AltRepr Type],
  ),
  grid.cell(
    colspan: 2,
    figure(
      rqtable(
        [@rq:it:impl],   [Y], [@sec:itree], [ `ITree/Defs.lean` ],
        [@rq:it:sbisim], [Y], [@sec:itree], [ `ITree/Defs.lean` ],
        [@rq:it:mon],    [Y], [@sec:itree:mon], [ `ITree/Defs.lean` ],
        [@rq:it:kt],     [Y], [@sec:itree], [ `ITree/Defs.lean` ],
        [@rq:it:comb],   [Y], [@sec:itree], [ `ITree/Defs.lean` ],
        [@rq:it:coind],  [Y], [@sec:itree], [ `ITree/Defs.lean` ],
        [@rq:it:lmon],   [Y], [@sec:itree], [ `ITree/Defs.lean` ],
        [@rq:it:wbisim], [Y], [@sec:itree:wbisim], [ `ITree/Defs.lean` ],
        [@rq:it:moni],   [Y], [@sec:itree], [ `ITree/Defs.lean` ],
      ),
      caption: [ITrees],
    ),
  ),
  kind: table,
  columns: (1fr, 1fr),
  caption: [Requirements and completion],
  label: <eval:tb:state>
)


// As a main focus we will do an analysis of the asymptotics of the SM v PA encodings.

== State-machine encoding

For the state-machine encoding,
there are multiple aspects to evaluate.
For example performance, expressivity, and safety when compared to other implementations.
The implementations I will test are the PA encoding from #MATHLIB,
a mathematically optimal encoding,
and an implementation by #cite(<cite:mslc>, form: "prose") which was started during this project.
Notably this final implementation is built on domain theoretic methods,
meaning that instead of requiring productivity,
all it requires is monotonicity.
I will speak more about this when evaluating the futumorphic productivity.

=== Performance between SME and PA<sec:smevpa>

// TODO: Update this wording
After building the equivalence,
and instantiating `AltRepr`,
we now have the ability to compare the performance between 4 representations:
The HpLuM implementation,
the PA encoding,
and the PreM and quotiented representations SM as theoretical optima.
For @rq:sme:zc to be the case, the HpLuM would have to be within 1$sigma$ of the PreM encoding.
// The SME would be in the same ballpark for @rq:sme:zc to be the case.

I implemented streams for the different encodings,
then I measured, using a monotonic clock, how long it took to destructure $n$-layers of the stream of natural numbers,
I repeated this experiment 3 times.
For the PA, I swept $n in [0,200]$,
and for HpLuM and PreM, SM encodings $n in [0, 5000]$.
I fit polynomials for each of these implementations,
then I plot samples, along with the fit.
This generates the plot @ev:fg:perf.
As we can see, there is a discrepancy between the HpLuM and PreM encodings.
For an unknown reason the variance along each of these graphs pulsates,
this effect is relatively minor, but unexplainable.

Reviewing the output plot we can see that
the SME is $cal(O)(1)$ under destructuring,
as opposed to the PA encoding which is $cal(O)(n)$.
This is in line with the expected theoretical performance.

#figure(
  image("../../data/plot.png", width: 6in),
  caption: [Performance of PA, HpLuM, and SM #sym.amp PreM representation]
)<ev:fg:perf>

The SM and PreM implementations are drawn from the same distribution/* TODO: PROVE */.
On the other hand, the HpLuM is 1.5x slower/* TODO: Prove*/.
The issue causing this has to do with the destructor function needing to do a universe lowering.
This adds a fixed cost at each iteration,
compared to the PreM which calls the destructor function.

=== Comparison of corecursor implementations

In this section, I compare the different implementations of coinductives across several aspects:
performance, and ergonomics of object construction and usage.

#figure(
  table(
    columns: 4,
    table.header[][Diss.][#MATHLIB][#MS],
    [`dest` performance], $cal(O)(1)$, $cal(O)(n)$, $cal(O)(n)$,
    [Type Macro], [N], [Y#footnote[For Lean v4.25]], [N],
    [Function definitions], [`futu`], [`corec`], [`partial_fixpoint`],
  )
)

== AltRepr Type<sec:eabi>

When it comes to the AltRepr type,
we have it implemented @rq:abi:impl,
and we have an eliminator @rq:abi:elim.
We now have to assess whether or not it is zero cost @rq:abi:zc.
To do this, rather than testing the performance,
I inspect the generated code for each of the 5 functions.
The 3 functions we care about are `destB` @eabi:ls:destB,
`mkB` @eabi:ls:mkB, and `rec` @eabi:ls:rec.
// TODO: check each of these are, v each of these is
Additionally, each of these are marked with an `@[inline]` hint,
meaning that in compiled code they do not appear.
As we see in each of these,
the functions have become the identity.
For the case of `mkA` @eabi:ls:mkA and
`destA` @eabi:ls:destA,
they compile into the expected call to the equivalence.
This also lets us verify that we have the behaviour of the type `B` @rq:abi:opt.

This means all criteria for the AltRepr Type are met.

#spg(
  figure(
```lean
[Compiler.result] size: 0
def AltRepr.destB A B eq a.1 : lcAny :=
  return a.1
```,
    caption: [LCNF `AltRepr.destB`],
  ),
  <eabi:ls:destB>,
  figure(
```lean
[Compiler.result] size: 0
def AltRepr.mkB A B eq a.1 : lcAny :=
  return a.1
```,
    caption: [LCNF `AltRepr.mkB`],
  ),
  <eabi:ls:mkB>,
  grid.cell(rowspan : 2)[
    #box[
    #figure(
```lean
[Compiler.result] size: 1
def AltRepr.rec A B eq motive.1 hLog hCheap eqA eqB v : lcAny :=
  let _x.2 := hCheap v;
  return _x.2
```,
    caption: [LCNF `AltRepr.rec`],
  )
  <eabi:ls:rec> ]

    #"\n"
  ],
  figure(
```lean
[Compiler.result] size: 4
def AltRepr.destA A B eq a.1 : lcAny :=
  let _x.2 := Equiv.symm._redArg eq;
  cases _x.2 : lcAny
  | Equiv.mk toFun invFun left_inv right_inv =>
    let _x.3 := toFun a.1;
    return _x.3
```,
    caption: [LCNF `AltRepr.destA`],
  ),
  <eabi:ls:destA>,
  figure(
```lean
[Compiler.result] size: 3
def AltRepr.mkA A B eq a.1 : lcAny :=
  cases eq : lcAny
  | Equiv.mk toFun invFun left_inv right_inv =>
    let _x.2 := toFun a.1;
    return _x.2
```,
    caption: [LCNF `AltRepr.mkA`],
  ),
  <eabi:ls:mkA>,
  label: <eabi:ls:code>,
  kind: raw,
  columns: (2fr, 2fr, 1.3fr),
  caption: [LCNF for functions on the AltRepr Type],
)

== Interaction trees

// TODO: unjournalify

For evaluating interaction trees,
there are 3 main aspects to evaluate.
These are function coverage, proof coverage, and performance.
For performance, it is inherited directly from the performance of the $M$-Type,
so I will focus on function and proof coverage.

Function coverage can be found in @itree:tb:fns and proof coverage @itree:tb:eqs.
This is comparing against the ITree paper @cite:itree.
In private conversation with #NC,
he informed me of some of the additions to the interaction tree library for Rocq.
These include relations such as simulation up to taus (sutt),
and relation up to taus (rutt).
These relations turn out to be useful for compiler verification in for example compcert @cite:compcert.
One of the reasons for this has to do with undefined behaviour in C,
specifically non-termination.
In C, a non-terminating function is UB and therefore should be able to be related to any other function.
This is in line with the fact that the spinning ITree can be simulated by any other ITree.
This is as opposed to how the spinning ITree is unique up to weak bisimulation.

On the other hand,
Lean now has an ITree library,
something multiple groups have requested.
For this reason #TG has expressed interest in using the current implementation for his project VeIR @cite:veir.
All positive requirements are met
(@rq:it:impl @rq:it:sbisim @rq:it:mon @rq:it:kt @rq:it:comb @rq:it:coind @rq:it:lmon @rq:it:wbisim @rq:it:moni).

During the production of this dissertation,
#MS also started work on an interaction tree library.
This is done using his implementation of coinductives using domain theoretic means.
This also means that his definition of `iter` is not guaranteed to be productive,
but also has a nicer unfolding lemma.
The reason for this has to do with trying to avoid weak bisimilarity,
and therefore has no implementation of the relation.
The primary difference between this dissertation and #MS,
is he has a much greater focus on effects and interpretation.
This is something I explicitly avoided stated in @rq:it:eff.
From this regard both implementations have their merits.

== Non Termination Monad <sec:itnt>

// TODO: unjournalify

Once implementing the SME was done, I moved over to implementing the non-termination monad.
Here I focused on getting as ergonomic an experience as possible using `mkE` and `destE` for polynomial equivalents.
In doing this, I realised the expectation of ITrees being much harder was false.
I then stopped working on the NTMonad after just implementing @rq:ntm:impl,
as NTMonad is a special case of ITrees with the empty event.
I am counting @rq:ntm:lfm and @rq:ntm:mon as completed,
as the generalization encompasses it.

Later I came back to working on it for evaluating futumorphic productivity then completing @rq:ntm:prod.

== Futumorphic productivity

By inspecting the table @futu:tb:free,
we can see we have implemented @rq:ft:corec and @rq:ft:inject.
In the code one can also find the cross universe futumorphism solving @rq:ft:corecu.
We also have theorems about flattening, mapping and injection proven in the code,
these are all implemented to fill out a `simp`-set for futumorphism.
The result of this is that when an end-user uses a futumorphism,
all they have to provide is a mapping over constructor lemma,
and the rest will automatically solve.
The main theorems that make this possible,
is the unfolding of futumorphism lemmas.
For the case of `futu'`, the statement can be seen in @futu:ls:unf.
With this implemented we have @rq:ft:unfold.
Furthermore, I added theorems stating `inject` is an injection,
and `flatten` is `inject`'s left-inverse#footnote[These two are not equivalent statements.].

#figure(
  raw(takeL(read("../../sme/Sme/M/Futu.lean"), 737, 745), block: true),
  caption: [Futumorphic unfolding lemma]
)<futu:ls:unf>

=== Comparing function definitions

For evaluating the futumorphism, it is best to put practice over promise,
for this we can look at some functions written using the current 3 possible styles of writing functions.
These are directly using the corecursor and using a futumorphism.
I also tried to compare it to #MS,
but the fixpoint turned out to try to compute the entire definition in finite memory,
crashing my compiler,
this means these functions would not be useful to compute with.

The main use of a futumorphism,
is moving any recursive component of a corecursor out of the state domain,
and into an explicit function.
Doing this transformation lets the function be written exactly as one would expect to write a normal inductive function,
just inserting corecursive calls as `recall` constructors.
Three good examples of this can be seen in @futu:ls:ilc, @futu:ls:stutter and @futu:ls:rle.
This fact means that a productive function,
is exactly a function who's generating function to the futumorphism is terminating.

// A function where it is immediately noticeably from both a readability perspective,
// is interlacing with a constant @futu:ls:ilc and stuttering @futu:ls:stutter.

#let ffile = partL(read("../../sme/Sme/Examples/Futu.lean"), 14, 26, 36, 50, 60, 73)

#spg(
  figure(raw(ffile.at(1), block: true), caption: [Corec definition]),
  figure(raw(ffile.at(2), block: true), caption: [Futu definition]),
  columns: (auto,auto),
  caption: [Interlace constant],
  kind : raw,
  label: <futu:ls:ilc>
)

#spg(
  figure(raw(ffile.at(3), block: true), caption: [Corec definition]),
  figure(raw(ffile.at(4), block: true), caption: [Futu definition]),
  columns: (auto,auto),
  caption: [Stutter constant],
  kind : raw,
  label: <futu:ls:stutter>
)

#spg(
  figure(raw(ffile.at(5), block: true), caption: [Corec definition]),
  figure(raw(ffile.at(6), block: true), caption: [Futu definition]),
  columns: (auto,auto),
  caption: [Run-length encoding],
  kind : raw,
  label: <futu:ls:rle>
)


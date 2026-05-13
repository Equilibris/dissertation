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
  align: horizon,
  table.header[Req.][Met][Evidence][Path],
  ..args
)

#let Y = table.cell(fill: MC)[`Y`]
#let N = table.cell(fill: NC)[`N`]

#spg(
  grid.cell(
    rowspan: 2,
    figure(
      rqtable(
        [@rq:sme:stream:impl], Y, [@sec:s], [`Stream/SDefs.lean`],
        [@rq:sme:stream:equiv], Y, [@sec:s:equiv], [`Stream/Equiv.lean`],
        [@rq:sme:impl], Y, [@sec:sme:impl], [`M/Defs.lean`],
        [@rq:sme:fast], Y, [@sec:smevpa], [-],
        [@rq:sme:equiv], Y, [@sec:sme:equiv], [`M/Equiv.lean`],
        [@rq:sme:ntm], Y, [@sec:delay], [`NTMonad/Defs.lean`],
        [@rq:sme:cind], Y, [@sec:sme:abi], [`M/{HpLuM,SM}.lean`],
        [@rq:sme:abi], Y, [@sec:sme:abi], [`M/HpLuM.lean`],
        [@rq:sme:itree], Y, [@sec:itree], [`ITree/Defs.lean`],
        [@rq:sme:prod], Y, [@sec:futu], [`M/DT/*,M/Futu.lean`],
        // [@rq:sme:zc], N, [@sec:smevpa], [-],
      ),
      caption: [State-machine encoding],
    )
  ),
  figure(
    rqtable(
      [@rq:it:impl],   Y, [@sec:itree], [ `ITree/Defs.lean` ],
      [@rq:it:sbisim], Y, [@sec:itree], [ `ITree/Defs.lean` ],
      [@rq:it:mon],    Y, [@sec:itree:mon], [ `ITree/Defs.lean` ],
      [@rq:it:kt],     Y, [@sec:itree], [ `ITree/Defs.lean` ],
      [@rq:it:comb],   Y, [@sec:itree], [ `ITree/Defs.lean` ],
      [@rq:it:coind],  Y, [@sec:itree], [ `ITree/Defs.lean` ],
      [@rq:it:lmon],   Y, [@sec:itree], [ `ITree/Defs.lean` ],
      [@rq:it:wbisim], Y, [@sec:itree:wbisim], [ `ITree/Defs.lean` ],
      [@rq:it:moni],   Y, [@sec:itree], [ `ITree/Defs.lean` ],
    ),
    caption: [ITrees],
  ),
  figure(
    rqtable(
      [@rq:ntm:impl], Y, [@sec:impl-sm], [`NTMonad/Defs.lean`],
      [@rq:ntm:mon],  Y, [@sec:itnt],    [`ITree/Monad.lean`],
      [@rq:ntm:lfm],  Y, [@sec:itnt],    [`ITree/Monad.lean`],
    ),
    caption: [NT Monad],
  ),
  figure(
    rqtable(
      [@rq:abi:impl], Y, [@sec:impl-sm], [`AltRepr.lean`],
      [@rq:abi:elim], Y, [@sec:impl-sm], [`AltRepr.lean`],
      [@rq:abi:opt],  Y, [@sec:eabi],    [`AltRepr.lean`],
      [@rq:abi:zc],   Y, [@sec:eabi],    [`AltRepr.lean`],
    ),
    caption: [AltRepr Type],
  ),
  figure(
    rqtable(
      [@rq:ft:corec],   Y, [@sec:futu], `M/Free.lean`,
      [@rq:ft:inject],  Y, [@sec:futu], `M/Free.lean`,
      [@rq:ft:unfold],  Y, [@sec:futu], `M/Free.lean`,
      [@rq:ft:pinject], Y, [@sec:futu], `M/Free.lean`,
      [@rq:ft:corecu],  Y, [@sec:futu], `M/Free.lean`,
    ),
    caption: [Free],
  ),
  kind: table,
  columns: (1fr, 1fr),
  rows: (auto, auto, auto),
  caption: [Requirements and completion],
  label: <eval:tb:state>
)


// As a main focus we will do an analysis of the asymptotics of the SM v PA encodings.

== State-Machine encoding (core)

For the state-machine encoding,
there are multiple aspects to evaluate.
// TODO: 
For example performance, expressivity, and safety when compared to other implementations.
The implementations I will test are:
+ The #TM,
+ the `SM` (@sec:sme:impl) encodings as an encoding with the least possible overhead,
+ the progressive approximation encoding from Mathlib,
+ the implementation by #MS which was started during this project @cite:mslc.
Notably this final implementation is based on the progressive approximation encoding,
but functions are defined using domain theoretic methods.
A result of this is the ability to define diverging functions.

=== Performance between state-machine and progressive approximation encodings<sec:smevpa>

// TODO: Update this wording
// For @rq:sme:zc to be the case, the #TM would have to be within 1$sigma$ of the PreM encoding.
// The SME would be in the same ballpark for @rq:sme:zc to be the case.

I implemented streams for the different encodings.
Then I measured, using a monotonic clock, how long it took to destructure $n$-layers of the stream of natural numbers.
This means the $x$ axis of the graph will show the number of destructures,
in other words $n times cal(O)(f)$ if an encoding has a complexity $f$.
I repeated this experiment 5 times.
For the progressive approximation encoding and #MS's implementation, I swept $n in [0,200]$,
and for #TM and SM encodings $n in [0, 5000]$.
I fit polynomials for each of these implementations,
then I plot samples, along with the fit.
This generates @ev:fg:perf.

#figure(
  image("../../data/plot.png", width: 6in),
  caption: [Cumulative performance for stream destructing]
) <ev:fg:perf>

Reviewing the output plot we can see that the state-machine encoding is $cal(O)(1)$ under destructuring,
as opposed to the progressive approximation encoding which is $cal(O)(n)$.
This is in line with the expected theoretical performance.

// TODO!: state that
// TODO!: Mention pointer indirection.
// TODO!: In theory this could be addressed using unsafe cast,
// but i did nt want more potneital undoundess.

// The SM and PreM implementations are drawn from the same distribution/* TODO: PROVE */.
// On the other hand, the #TM is 1.5x slower/* TODO: Prove*/.
In addition to @ev:fg:perf,
which mainly shows the asymptotics of the different implementations,
I also computed a per-layer cost.
This was done by dividing the samples by the stream index we are testing (@ev:fg:layer).
The plot then shows the constant factor of the two implementations.

The difference between `SM` and the #TM types from the destructor function needing to do a universe lowering.
In practice this means the #TM adds two pointer indirections over the `SM` adding a fixed cost at each iteration,
compared to the `SM` which calls the destructor function directly.

#figure(
  image("../../data/stest.png", width: 6in),
  caption: [Per-layer performance for stream destructing]
) <ev:fg:layer>

#align(center)[*All success criteria for the SME type are met*.]

== AltRepr Type (extension)<sec:eabi>

// When it comes to the AltRepr type,
Going through the requirements of the AltRepr type,
I implemented it (@rq:abi:impl),
and added an eliminator (@rq:abi:elim).
We now have to assess whether usage zero cost (@rq:abi:zc).

It is not clear how one would test the performance of the AltRepr type.
So rather we can read the generated intermediate representation (LCNF) for the functions we care about.
Inspecting the performance of `mkB` @eabi:ls:mkB and `destB` @eabi:ls:destB,
we can see they have become the identity.
The eliminator `rec` has also compiled into simply calling the efficient implementation.
Additionally, each of these are marked with an `@[inline]` hint,
meaning that in compiled code they do not even appear.
This also lets us verify that we have the behaviour of the type `B` (@rq:abi:opt).

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
    figure(
```lean
[Compiler.result] size: 1
def AltRepr.rec A B eq motive.1 hLog hCheap eqA eqB v : lcAny :=
  let _x.2 := hCheap v;
  return _x.2
```,
    caption: [LCNF `AltRepr.rec`],
  ),
  <eabi:ls:rec>,

//   grid.cell(rowspan : 2)[
//     #box[
//     #figure(
// ```lean
// [Compiler.result] size: 1
// def AltRepr.rec A B eq motive.1 hLog hCheap eqA eqB v : lcAny :=
//   let _x.2 := hCheap v;
//   return _x.2
// ```,
//     caption: [LCNF `AltRepr.rec`],
//   )
//   <eabi:ls:rec> ]
//
//     #"\n"
//   ],
  // TODO: get rid of destA mkA
//   figure(
// ```lean
// [Compiler.result] size: 4
// def AltRepr.destA A B eq a.1 : lcAny :=
//   let _x.2 := Equiv.symm._redArg eq;
//   cases _x.2 : lcAny
//   | Equiv.mk toFun invFun left_inv right_inv =>
//     let _x.3 := toFun a.1;
//     return _x.3
// ```,
//     caption: [LCNF `AltRepr.destA`],
//   ),
//   <eabi:ls:destA>,
//   figure(
// ```lean
// [Compiler.result] size: 3
// def AltRepr.mkA A B eq a.1 : lcAny :=
//   cases eq : lcAny
//   | Equiv.mk toFun invFun left_inv right_inv =>
//     let _x.2 := toFun a.1;
//     return _x.2
// ```,
//     caption: [LCNF `AltRepr.mkA`],
//   ),
//   <eabi:ls:mkA>,
  label: <eabi:ls:code>,
  kind: raw,
  columns: (auto, auto, auto),
  caption: [LCNF for functions on the AltRepr Type],
)

#align(center)[*All success criteria for the AltRepr Type are met*.]

== Interaction Trees (extension)

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
// For instance sutt
For instance sutt turns out to be useful for compiler verification in for example compcert @cite:compcert.
In C, a non-terminating function is UB and therefore should be able to be related to any other function.
This is in line with the fact that the spinning ITree can be simulated by any other ITree.
This is as opposed to how the spinning ITree is unique up to weak bisimulation.

On the other hand,
Lean now has an ITree library,
something multiple groups have requested.
For this reason #TG has expressed interest in using the current implementation for his project VeIR @cite:veir.
// All positive requirements are met
// (@rq:it:impl @rq:it:sbisim @rq:it:mon @rq:it:kt @rq:it:comb @rq:it:coind @rq:it:lmon @rq:it:wbisim @rq:it:moni).

During the production of this dissertation,
#MS also started work on an interaction tree library.
This is done using his implementation of coinductive types using the progressive approximation encoding and domain theoretic means.
This also means that his definition of `iter` is not required to be productive.
The reason for this has to do with trying to avoid weak bisimilarity,
and therefore has no implementation of the relation.

The domain construction of the coinductive data types allow for very natural function definitions,
though unfortunately the definition is still slow.
From this regard both implementations have their merits.

#align(center)[*All success criteria for interaction trees are met*.]
// #align(center)[]

== The delay monad (core) <sec:itnt>

// TODO: unjournalify

The delay monad is a special case of interaction trees with no visible events.
As a consequence of this,
I will rather let the user implement the delay monad using interaction trees.
As stated above interaction trees form a lawful monad,
thereby through the generalization completing the requirements @rq:ntm:mon and @rq:ntm:lfm.

#align(center)[*All success criteria for the delay monad are completed by interaction trees*.]

// Once implementing the SME was done, I moved over to implementing the delay monad.
// Here I focused on getting as ergonomic an experience as possible using `mkE` and `destE` for polynomial equivalents.
// In doing this, I realised the expectation of ITrees being much harder was false.
// I then stopped working on the NTMonad after just implementing @rq:ntm:impl,
// as NTMonad is a special case of ITrees with the empty event.
// I am counting @rq:ntm:lfm and @rq:ntm:mon as completed,
// as the generalization encompasses it.

== Futumorphic productivity (extension)

By inspecting the @futu:tb:free,
we can see we have implemented a futumorphism (@rq:ft:corec) and an injection (@rq:ft:inject).
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
and `flatten` is `inject`'s left-inverse.

#figure(
  raw(takeL(read("../../sme/Sme/M/Futu.lean"), 737, 745), block: true),
  caption: [Futumorphic unfolding lemma]
)<futu:ls:unf>

=== Comparing function definitions

// TODO: Dont direclty use requirements.

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
  caption: [Run length decoding],
  kind : raw,
  label: <futu:ls:rle>
)

#align(center)[*All success criteria for the Free monad are met*.]


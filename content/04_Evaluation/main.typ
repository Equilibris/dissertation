#import "@preview/subpar:0.2.2" as subpar: grid as spg
#import "../utils.typ": *

This chapter will discuss and evaluate each of the components of the dissertation,
it will be split into distinct sections for each of the sections of the project.
As mentioned in @sec:method,
I have been writing proofs verifying the correctness of my different components.
I will refer to these throughout this chapter.
Type signatures often are unable to encode performance (other than maybe something substructural),
therefore for performance evaluations I simply write benchmarks as in any other programming language.
There will be a comparison of ITree implementations.
Finally an assessment of the ergonomics of futumorphic and deep-thunk productivy.

An overview of all the requirements laid out can be viewed @eval:tb:state.

#let rqtable(..args) = table(
  columns: 4,
  table.header[Req.][Met][Evidence][Path],
  ..args
)

#pad(x: -1cm)[
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
        [@rq:sme:zc], [Y], [@sec:smevpa], [-],
      ),
      caption: [State-machine encoding],
    )
  ),
  figure(
    rqtable(
      [@rq:ntm:impl], [Y],   [@sec:impl-sm], [`NTMonad/Defs.lean`],
      [@rq:ntm:mon],  [Y\*], [@sec:itnt],    [`ITree/Monad.lean`],
      [@rq:ntm:lfm],  [Y\*], [@sec:itnt],    [`ITree/Monad.lean`],
      [@rq:ntm:prod], [Y],   [@sec:futu:case], [`NTMonad/Defs.lean`],
    ),
    caption: [NT Monad],
  ),
  figure(
    rqtable(
      [@rq:abi:impl], [Y], [@sec:impl-sm], [`ABI.lean`],
      [@rq:abi:elim], [Y], [@sec:impl-sm], [`ABI.lean`],
      [@rq:abi:opt], [Y],  [@sec:impl-sm], [`ABI.lean`],
      [@rq:abi:zc], [Y],   [@sec:eabi],    [`ABI.lean`],
    ),
    caption: [ABI Type],
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
]

// As a main focus we will do an analysis of the asymptotics of the SM v PA encodings.

== State-machine encoding

For the state-machine encoding,
there are a few aspects to evaluate.
For example performance, expressivity, and safety when compared to other implementations.
The implementations I will test are the PA encoding from #MATHLIB,
a mathematically optimal encoding,
and an implementation by #cite(<cite:mslc>, form: "prose") which was started during this project.
Notably this final implementation is built on domain theoretic methods,
meaning that rather than requiring productivity,
all it requires is monatonicity.
I will speak more about this when evaluating the futumorphic productivity.

=== Performance between SME and PA<sec:smevpa>

After building the equivalence,
and instantiating shrink,
we now have the ability to compare the performance between 3 representations:
The SME encoding (high performance, hpRuns),
the PA encoding (slow, slRuns),
and a hand made big implementation (bigRuns).
The big implementation here serves as a theoretical optimum,
with no overheads of universe alterations and so on.
The big implementation is the underlying structure of the SM encoding,
but without quotienting and all that is needed to make that nice to use.
For @rq:sme:zc to bd the case the SME would have to be within 1$sigma$ of the big encoding.
// The SME would be in the same ballpark for @rq:sme:zc to be the case.

I implemented streams for the 3 different encodings,
then I measured, using a monotonic clock, how long it took to $m$-samples destructure $n$-layers of the stream of natural numbers.
For the PA I took $m=10$ and swept $n in [0,200]$,
and for SM and big encodings $m=3$ and $n in [0, 5000]$.
I fit polynomials for each of these implementations,
then I plot the average of the $m$ samples for each layer $n$ along with the fit.
This generates the plot @ev:fg:perf.
As we can see there is a discrepancy between the big and SM encodings.
For an unknown reason the variance along each of these graphs pulsates,
this effect is still relatively minor.

Reviewing the output graph we can see that
the SME is $cal(O)(1)$ under destructuring,
as opposed to the PA encoding which is $cal(O)(n)$.
This is in line with the expected theoretical reasoning.

#figure(
  image("../../data/plot.svg", width: 6in),
  caption: [Performance of SME, PA, and Big representation]
)<ev:fg:perf>

On the other hand, we can see that the big encoding is still around 4x faster.
The issue causing this has to do with the destructor function needing to do universe lifting.
This adds a fixed cost at each iteration,
this is compared to the destructor for the big representation,
which practically has to do nothing.

// ==== Big v HpLuM <sec:bhplum>
//
// There is a quite large discrepancy between the optimum and the HpLuM implementations.


== ABI Type<sec:eabi>



== Interaction trees

== Non Termination Monad

=== ITrees as the NTMonad<sec:itnt>

== Futumorphic productivity

=== Case studies<sec:futu:case>

NTMonad

Streams

// #figure(
//   ```lean
// def QStream.Base : MvPFunctor 2 := ⟨
//   Unit,
//   fun _ _ => Unit
// ⟩
//
// def QStreamSl α := M QStream.Base (fun _ => α)
// def QStreamHp α := HpLuM QStream.Base (fun _ => α)
//
// structure QStreamBig.{u} (α : Type _) where
//   corec ::
//     {t : Type u}
//     (functor : t → Nat × t)
//     (obj : t)
//
// def numsSl : QStreamSl Nat :=
//   .corec _ (fun n => ⟨.unit, fun | .fz, .unit => n.succ | .fs .fz, .unit => n⟩) Nat.zero
//
// def numsHp : QStreamHp Nat :=
//   .corec' (fun n => ⟨.unit, fun | .fz, .unit => n.succ | .fs .fz, .unit => n⟩) Nat.zero
//
// def numsBig : QStreamBig Nat :=
//   QStreamBig.corec (fun n => ⟨n, n + 1⟩) 0
//
// def QStreamBig.getNth (x : QStreamBig Nat) : Nat → Nat
//   | 0 => x.dest.fst
//   | n+1 => x.dest.snd.getNth n
//
// def QStreamSl.getNth (x : QStreamSl Nat) : Nat → Nat
//   | 0 => match x.dest with
//     | ⟨.unit, v⟩ => v (.fs .fz) .unit
//   | n+1 => match x.dest with
//     | ⟨.unit, v⟩ => QStreamSl.getNth (v .fz .unit) n
//
// def QStreamHp.getNth (x : QStreamHp Nat) : Nat → Nat
//   | 0 => match x.dest with
//     | ⟨.unit, v⟩ => v (.fs .fz) .unit
//   | n+1 => match x.dest with
//     | ⟨.unit, v⟩ => QStreamHp.getNth (v .fz .unit) n
//   ```
// )<perfcode>



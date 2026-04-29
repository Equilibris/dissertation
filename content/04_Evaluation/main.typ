#import "@preview/subpar:0.2.2" as subpar: grid as spg
#import "../utils.typ": *

This chapter will discuss and evaluate each of the components of the dissertation,
it will be split into distinct sections for each of the sections of the project.
As mentioned in @sec:method,
I have been writing proofs verifying the correctness of my different components.
I will refer to these throughout this chapter.
Type signatures often are unable to encode performance (other than maybe something substructural),
therefore for performance evaluations I write benchmarks as in any other programming language.
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
      [@rq:ntm:prod], [Y],   [@sec:futu:case], [`NTMonad/Defs.lean`],
    ),
    caption: [NT Monad],
  ),
  figure(
    rqtable(
      [@rq:abi:impl], [Y], [@sec:impl-sm], [`ABI.lean`],
      [@rq:abi:elim], [Y], [@sec:impl-sm], [`ABI.lean`],
      [@rq:abi:opt],  [Y], [@sec:eabi],    [`ABI.lean`],
      [@rq:abi:zc],   [Y], [@sec:eabi],    [`ABI.lean`],
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
meaning that instead of requiring productivity,
all it requires is monatonicity.
I will speak more about this when evaluating the futumorphic productivity.

=== Performance between SME and PA<sec:smevpa>

After building the equivalence,
and instantiating shrink,
we now have the ability to compare the performance between 4 representations:
The HpLuM implementation (high performance, hpRuns),
the PA encoding (slow, slRuns),
and the preobject and quotiented representations.
The PreM implementation is the underlying structure of the SM encoding,
but without quotienting and all that is needed to make that usable.
For @rq:sme:zc to be the case the HpLuM would have to be within 1$sigma$ of the PreM encoding.
// The SME would be in the same ballpark for @rq:sme:zc to be the case.

I implemented streams for the 3 different encodings,
then I measured, using a monotonic clock, how long it took to 3 samples destructure $n$-layers of the stream of natural numbers.
For the PA I swept $n in [0,200]$,
and for HpLuM and PreM, SM encodings $n in [0, 5000]$.
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
  caption: [Performance of PA, HpLuM, and, SM and PreM representation]
)<ev:fg:perf>

The SM and PreM implementations are drawn from the same distrubution TODO: PROVE.
On the other hand the HpLuM is 1.5x slower TODO: Prove.
The issue causing this has to do with the destructor function needing to do a universe lowering.
This adds a fixed cost at each iteration,
compared to the PreM which simply calls the function destructor function.

=== Comparison of ITree implementations

== ABI Type<sec:eabi>

When it comes to the ABI type,
we have it implemented @rq:abi:impl,
and we have an eliminator @rq:abi:elim.
We now simply have to assess weather or not it is zero cost @rq:abi:zc.
To do this, rather than testing the performance,
I inspect the generated code for each of the 5 functions.
The 3 functions we care about are `destB` @eabi:ls:destB,
`mkB` @eabi:ls:mkB, and `rec` @eabi:ls:rec.
Additionally each of these are marked with an `@[inline]` hint,
meaning that in compiled code they simply do not appear.
As we see in each of these,
the functions have simply become the identity.
For the case of `mkA` @eabi:ls:mkA and
`destA` @eabi:ls:destA,
they compile into the expected call to the equivalence.
This also lets us verify that we have the behaviour of the type `B` @rq:abi:opt.

This means all criteria for the ABI Type are met.

#spg(
  figure(
```lean
[Compiler.result] size: 0
def ABI.destB A B eq a.1 : lcAny :=
  return a.1
```,
    caption: [LCNF `ABI.destB`],
  ),
  <eabi:ls:destB>,
  figure(
```lean
[Compiler.result] size: 0
def ABI.mkB A B eq a.1 : lcAny :=
  return a.1
```,
    caption: [LCNF `ABI.mkB`],
  ),
  <eabi:ls:mkB>,
  grid.cell(rowspan : 2)[
    #box[
    #figure(
```lean
[Compiler.result] size: 1
def ABI.rec A B eq motive.1 hLog hCheap eqA eqB v : lcAny :=
  let _x.2 := hCheap v;
  return _x.2
```,
    caption: [LCNF `ABI.rec`],
  )
  <eabi:ls:rec> ]

    #"\n"
  ],
  figure(
```lean
[Compiler.result] size: 4
def ABI.destA A B eq a.1 : lcAny :=
  let _x.2 := Equiv.symm._redArg eq;
  cases _x.2 : lcAny
  | Equiv.mk toFun invFun left_inv right_inv =>
    let _x.3 := toFun a.1;
    return _x.3
```,
    caption: [LCNF `ABI.destA`],
  ),
  <eabi:ls:destA>,
  figure(
```lean
[Compiler.result] size: 3
def ABI.mkA A B eq a.1 : lcAny :=
  cases eq : lcAny
  | Equiv.mk toFun invFun left_inv right_inv =>
    let _x.2 := toFun a.1;
    return _x.2
```,
    caption: [LCNF `ABI.mkA`],
  ),
  <eabi:ls:mkA>,
  label: <eabi:ls:code>,
  kind: raw,
  columns: (2fr, 2fr, 1.3fr),
  caption: [LCNF for functions on the ABI Type],
)

== Interaction trees

For evaluating interaction trees,
there are 3 main aspects to evaluate interaction trees.
These are function coverage, proof coverage, and performance.
For performance it is inherited direcrly from the performance of the $M$-Type,
so I will focus on function and proof coverage.

Function coverage can be found in @itree:tb:fns and proof coverage @itree:tb:eqs.
This is when comparing against against the ITree paper @cite:itree.
While in private conversation with #NC,
he informed me of some of the additions to the interaction tree library for rocq.
These include relations such as simulation up to taus (sutt),
and relation up to taus (rutt).
These relations turn out to be useful for compiler verificaion in for example compcert TODO CITE.
One of the reasons for this has to do with undefined behaviour in C,
spesifically non-termination.
In C, a non-terminating function is UB and thereby should be able to be related to any other function.
This is in line with the fact that the spinning ITree can be simulated by any other ITree.
This is as opposed to how the spinning ITree is unique up to weak bisimulation.

On the other hand,
Lean now has an ITree library,
something multiple groups have wanted previously TODO PROVE.
For this reason #TG has expressed interest in using the current implementation for his project VeIR TODO CITE.
The requirements met by this implementation set are
@rq:it:impl @rq:it:sbisim @rq:it:mon @rq:it:kt @rq:it:comb @rq:it:coind @rq:it:lmon @rq:it:wbisim @rq:it:moni,
which are all of the positive requirements.

During the production of this artifact,
#MS also started work on an interaction tree library.
This is done using his implementation of coinductives using domain theoretic means.
This also means that his definition of `iter` is not guarangteed to be productive,
but also has a nicer unfolding lemma.
The primary difference between this dissertation and #MS,
is he has a much greater focus on effects and interpretation.
This is something I expclicitly avoided as form of @rq:it:eff.
From this regard both implementations have their merits,

== Non Termination Monad <sec:itnt>

Writing the project, #JV, #TG, #AK and I decided implementing interaction trees would be too ambitious.
For this we decided to make it an extention instead,
and rather reason about the simpler structure being the non-termination monad.
Once implementing the SME was done, I moved over to implementing the non-termination monad.
Here I focused on getting an as ergonimic experience as possible using `mkE` and `destE` for polynomial equialents.
In doing this I realised the assessment of ITrees being much harder was false.
For this reason I then stopped working on the NTMonad after just implementing @rq:ntm:impl.
The reason for this is the NTMonad is a special case of ITrees with the empty event.
For this reason I am counting @rq:ntm:lfm and @rq:ntm:mon as completed,
as the genrealization encompasses it.

Later I would come back to working on it for evaluating futumorphic productivity then completing @rq:ntm:prod.

== Futumorphic productivity

I ended up writing two functional implementations
(excluding my earlier attempt during my internship).
This is the DeepThunk implementation,
and the Free monad implementations.
Out of these the Free monad implementation is much more feature rich,
this was only possible from the learning of DeepThunks,
for which it deserves to be mentioned.

Initially when trying to implement a structure to check productivity,
I picked the simplest structure I could think of.
This then developed into becoming what I have now included in my dissertation as DeepThunks.
For this I developed the theory,
including but not limited to an injector,
and a corecursor.
The definition given for deep-thunks used the carrier as one of the mapped parametrs to the polynomial.
Meaning I did not need to implement a dedicated map function,
this turned out to be a mistake.
The problem here is that any multivariate map,
might also change the carrier.
This meant that for all equations involving the multivariate map,
had to be restricted to functions concatinated together.
This also meant that working with binds became a mess for universe levels.
Fundementally we want to treat this as a different parameter so we can also use do notation.
Proving facts about binds also became extremely tedeous.
We also did not have a monad unit as the structure of the base polynomial P can be arbitrary.
Another problem was DeepThunks accross universes required applying a sequence of natural transformations.
These natural transformations had few equations other than naturality proven about them.
Additionally some crutial proofs are unproven as they simply became too difficult.

// TODO: reorder this list.
When implementing the Free monad,
I applied each of these learnings.
The definition used had the universe lifting built in,
meaning we only had to reason about switching universes once (`dest_corec`).
The carrier was also taken as a function parameter used to instantiate a constant.
This solved the problem of maps being able to change the carrier,
and at the same time allowed the free monad to satisfy the signature needed for the `Monad : (Type → Type) → Type` typeclass.
This was also made even simpler by implementing the corecursor and the destructor using the standard Lean `Sum`s.
With these design descisions,
implementing constructors (`recall` and `cont`) for the `Free` monad was just following the type signature.
I added a third constructor `cont'` which was in-universe allowing for some definitions to be simplified.
For both of these I added `cases` principles for the constructor sets.
I also set up the corecursor to operate on `Sum`s as well which made writing functions very easy.
The coinductive principle for $M$-types could also be specalized to the Free monad using relational lifting on `Sum` types.
Building on the preexisting simp set for `Sum`s,
and marking the $beta$-rules as `@[simp]`,
proving many theorems became as simple as just invoking `simp`.
The best examples of these can be seen in the mapping equations on constructors.
These theorems were much harder to prove for DeepThunks.
Since we are no longer relying multivariate maps to change the carrier,
we now need a new map definition.

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



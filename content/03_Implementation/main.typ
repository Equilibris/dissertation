#import "../utils.typ": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

This chapter describes the implementation of the `Sme` constructs.

== Transiteration

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

#let f = read("../../sme/Sme/ForMathlib/Data/ULift.lean").split("\n").slice(2,11).join("\n")

#figure(
  raw(f, lang : "lean", block:true),
  caption: [Transliteration between universes of types]
)<tr:ls:code>

Another major usage of a transiteration was used when defining the eliminator for `ABI`,
I will discuss this more when we get to @sec:abi.
This was where I first discovered transliteration,
and made it possible to define a universe-polymorphic eliminator.

////////////////////////////////////////////////////////////////////////////////

== Stream implementation

As proving these equivleneces is extremely challenging I decidede I would start by implementing it for the special case of streams.
Streams are the text-book coinductive datatype that most people know as mentioned in @sec:coind.
Therefore I expected this to be an easy task to start with to test showing the equivilence.

First I set up a class of preobject:

////////////////////////////////////////////////////////////////////////////////

== Expanding the progressive approximation theory

During the pheasability assesment I noticed that,
in the current formalised theory of polynomials,
the statement wouldn't even type-check.
This stemmed from a problem with the corecursive principle for the M type in the old implementation.
$"corec" : {alpha : "TypeVec".{cal(U)} n} arrow {beta : "Type" cal(U)} arrow (g : beta → P (alpha ::: beta)) arrow beta arrow M alpha$
#footnote(link("https://github.com/leanprover-community/mathlib4/blob/7a60b315c7441b56020c4948c4be7b54c222247b/Mathlib/Data/PFunctor/Multivariate/M.lean#L152-L154")) @cite:mathlib.
The problem here is that both $alpha$ and $beta$ have to both reside in $cal(U)$.
Solving this is done through the next two sections.

=== Universe lifting of polynomial functors.<sec:ulift_p>

The main problem caused here comes from the fact that lean isnt cummulative.
This means it is impossible to express a universe hetrogouns typevector.
In other words $alpha ::: beta$ is only typable if $alpha : "TypeVec".{cal(U)} n$ and $beta : "Type" cal(U)$.
The natural way of solving this is using the supremum in universe levels you get from
$"ULift" : "Type" cal(U) arrow "Type" (max cal(U) cal(V))$.
This means we can have $beta : "Type" cal(U)$ and $alpha : "Type" cal(V)$,
then ulift both of them to a common universe $"ULift" alpha ::: "ULift" beta : "TypeVec".{max cal(U) cal(V)} (n+1)$
#footnote([Note we overload ULift as a notation to refer to lifting TypeVecs as well]).

Noticable the next hurdle we encounter is that PFunctors are restricted to a universe level.
Recall the definition from @pfunctorlean.
Observe how for a $"MvPfunctor".{cal(U)} n$,
we require that both the head and child reside in $cal(U)$.
This will also cause problems,
as looking back at the definition of the corecursor,
we will require $P$ to be able to accept $"ULift" alpha ::: "ULift" beta$.
If we do not add the ability to lift $P$,
the unifier will force $cal(U) = cal(V)$,
thereby invalidating all the work we did in the previous section.
Luckily lifting a PFunctor is relatively easy.
We define it as $"ULift" P eq.delta chevron.l "ULift" P.1, lambda x mapsto "ULift" (P.2 x) chevron.r$.
This works and now we can move on to our goal
#footnote([
  TODO: Speak with JV / W to see if this might be done in the lit,
  Ex : Locally presentable and accessable categories Adameck roshiski
]).

=== Generalizing the corecursor

Now with all the work in the previous section,
by generalizing $"corec'"$#footnote([Done in PR NUMBER ]),
we can define
$"corecU" : {alpha : "TypeVec".{cal(U)} n}
  arrow {beta : "Type" cal(V)}
  arrow (g : beta → "ULift" P ("ULift" alpha ::: "ULift" beta))
  arrow beta
  arrow M.{cal(U)} alpha$.
Notably we are able to fit the object into $cal(U)$
(as opposed to in the SME).

The expected diagram using corecU and dest commutes.

////////////////////////////////////////////////////////////////////////////////

== State machine encoding

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
This will be seen in @smevpa.
We will henceforth refer to the datatype SME.PreM.

=== PreM

As we speak about in @pfunctofalg,
the M Type is the terminal object in the category of coalgebras.
We can see through reasoning (cumilatively) in this category that PreM is weakly terminal.
Looking at this category we want to somehow force the incoming morphisms together.
This corresponds exactly to quotienting,
for this we will use Bisimilarity.

////////////////////////////////////////////////////////////////////////////////

== Interaction trees

Interaction trees (ITrees) are a coinductive datastructure detailed in @itrees_paper.

////////////////////////////////////////////////////////////////////////////////

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

////////////////////////////////////////////////////////////////////////////////


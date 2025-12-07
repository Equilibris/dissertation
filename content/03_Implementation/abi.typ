#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

== The ABI Type

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


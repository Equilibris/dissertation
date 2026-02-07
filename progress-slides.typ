#import "@preview/diatypst:0.9.1": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/codly:1.3.0": *
#import "@preview/codly-languages:0.1.8": *

#show: slides.with(
  title: "Efficient Coinductives through State-Machine Corecursors",
  subtitle: "Optimising the terminal F-coalgebra in Set\nfor computational behaviour in Lean4",
  date: "2025-02-23",
  authors: ("William Sørensen"),
  toc : false,
  // title-color: rgb("#DD3025") // Cambridge scarlet
  count: "dot-section"
)
#show raw: set text(font : "FiraCode Nerd Font")
#show: codly-init.with()
#codly(languages: codly-languages)
#set heading(numbering: (.., last) => "")

== Polynomials (background)

- A head $H$,
- child families $c_h$ in $h : H$.
- Morally, a collection of constructors $H$,
  and data at each constructor $c_h$.
- For now we will not consider "recursive" (inductive) data structures,
  rather I will have this be a variable we take the fix point in.
- Examples:
  - natural numbers `NatF(X) := 1 + X`,
  - lists `ListF(A, X) := 1 + A * X`,
  - streams `StreamF(A, X) := A * X`.

$ (h : H) times c_h arrow.r alpha eq.triple sum_(h : H) alpha^(c_h) $

#v(1fr)

See @nlab:polynomial_functor and @atfp

== Coinductives (background)

- Unbounded tree of data.
- Greatest cofixpoint of a polynomial.
- Morally, the process of putting the word "lazy" in front of a functor,
  - on lists it sends them to lazy lists.
- Have a corecursion principle rather than an recursion principle,
  - instead of `rec : (f a -> a) -> fix f -> a`,
  - we have `corec : (a -> f a) -> a -> cofix f`.
- On our examples and their correspondencens,
  - `cofix NatF`, natural numbers union infinity,
  - `cofix ListF(A)`, lists of `A`s with arbitrary length union streams of `A`,
  - `cofix StreamF(A)`, infinite streams of `A`s.

#v(1fr)

See @avigad_et_al

== Perfomance of coinductives (core)

- Previous work has demonstrated implementation of coinductives.
- Computational behaviour was not a concern.

#figure(
  image(
    "./data/plot.png",
    height: 160pt
  ),
  caption: "Perfomance of the old, new, and a perfect implementation"
)

== ABI Type (extention)

#columns(2)[
- Given $alpha:"Type"_cal(U)$, $beta:"Type"_cal(V)$ and $"eq" : alpha tilde.eq beta$.
- Univalence gives uniqueness.
- Adds a form of "weak-univalence".
- Allows for a zero cost universe transliteration.
- Symetric form of `Shrink`.

#v(1fr)

#figure(
  text(6pt)[
    #diagram(
      cell-size: 10mm,
      // Top row nodes
      node((-1, 1), $alpha$, name : <A1>),
      node((1, 3), $alpha$, name : <A2>),

      node((1, 1), $"Shrink" alpha beta$, name : <S1>),
      node((2, 2), $"Shrink" alpha beta$, name : <S2>),

      edge(<A1>, <S1>, $text("mk")$, "->"),
      edge(<A2>, <S2>, $text("mk")$, "->"),
      edge(<S1>, <A2>, $text("dest")$, "->"),
      edge(<A1>, <A2>, $bb(1)_alpha$, "->", label-side : right),

      edge(<S1>, <S2>, $bb(1)_("Shrink" alpha beta)$, "->"),
    )
  ],
  caption:[Operations on Shrink]
)<shrkops>

#colbreak()

#v(1fr)

#figure(
  text(6pt)[
    #diagram(
      cell-size: 10mm,
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
    )
  ],
  caption:[Operations on ABI]
)
]

== Interaction Trees (extention)

- Free monad with non-termination as an effect.

```lean
coinductive ITree
    (E : Type u -> Type u) (R : Type v) :=
  | tau : ITree E R -> ITree E R
  | ret : R -> ITree E R
  | vis {A : Type u} (e : E A) (k : A -> ITree E R)
```

- $"ITerm" E$ forms a monad,
  - With a method $"trigger" : E V → "ITree" E" "V$,
  - and $"iter" : (A -> "ITree" E (A + B)) -> A -> "ITree" E" "B$.
- And an equivelence relation $A approx B$,
  - satisfying $A approx B <-> #raw("tau") A approx B$.

== Project statistics

#no-codly[
#text(8pt)[```
❯ nix-shell -p cloc --run "cloc . --exclude-dir=.lake"
      95 text files.
      87 unique files.
      14 files ignored.

github.com/AlDanial/cloc v 2.06  T=0.09 s (925.5 files/s, 99584.0 lines/s)
-------------------------------------------------------------------------------
Language                     files          blank        comment           code
-------------------------------------------------------------------------------
Lean                            54           1174            232           5869
Typst                           20            304            119            994
SVG                              1              0              0            171
JSON                             3              0              0            125
TeX                              1              4              0             76
YAML                             3              8              7             69
Markdown                         2             27              0             68
Python                           2             22             18             57
Nix                              1              2              0             15
-------------------------------------------------------------------------------
SUM:                            87           1541            376           7444
-------------------------------------------------------------------------------
```]]

(excluding mathlib PRs)

== Bibliography

#bibliography("bib.bib", style : "apa")

= Further work

== Futumorphic productivity (extention)

- A futomorphism is a morphism `(c -> f (Free f c)) -> c -> cofix f`.
-

#v(1fr)

See @fantomorph

== CTree (extention)

CTree



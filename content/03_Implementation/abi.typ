#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#let shrink-ops-diagram(object, morphism, base-x: 0, base-y: 0) = (
  // Top row nodes
  node((base-x, base-y), object, name: label(morphism + "1")),
  node((base-x + 4, base-y), $"Shrink" alpha beta$, name: label("S" + morphism + "1")),

  // Bottom row nodes
  node((base-x + 4, base-y + 4), object, name: label(morphism + "2")),
  node((base-x + 6, base-y + 4), $"Shrink" alpha beta$, name: label("S" + morphism + "2")),

  // Edges
  edge(label(morphism + "1"), label("S" + morphism + "1"), $text(#str("mk" + morphism))$, "->"),
  edge(label(morphism + "1"), label(morphism + "2"), $bb(1)_#object$, "->"),
  edge(label("S" + morphism + "1"), label(morphism + "2"), $text(#str("dest" + morphism))$, "->"),
  edge(label("S" + morphism + "1"), label("S" + morphism + "2"), $bb(1)_("Shrink" alpha beta)$, "->"),
  edge(label(morphism + "2"), label("S" + morphism + "2"), $text(#str("mk" + morphism))$, "->"),
)

== The ABI Type

The problem the ABI type tries to tackle is one of abstracting the runtime datatype through functions.
My first try at solving this involved satisfying the following diagrams:
Given an isomorphism $"eq" : alpha tilde.equiv beta$ for some types $alpha$ and $beta$,


#figure(
  diagram(
    debug : 1,
    spacing: 10mm,
    ..shrink-ops-diagram($alpha$, "A", base-x: 1, base-y: 0),
    ..shrink-ops-diagram($beta$, "B", base-x: 0, base-y: 1),
  ),
  caption:[Operations on Shrink]
)<shrkops>



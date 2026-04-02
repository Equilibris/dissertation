#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "../../typ/pfunc.typ" as pfunc: show_map, show_obj, show_decl
#import "@preview/subpar:0.2.2" as subpar: grid as spg

#let mpf(a, b) = $chevron.l #a, #b chevron.r$
#let Type = $"Type"$

== Polynomial functors

A (multivariate) polynomial functor on set#footnote([
  For the readers familiar with category theory,
  simply think of categorical dependent products,
  and (co)limits when I use the set-theoretic language.
]) is:
a head-type,
along with a (collection of) child family(ies) parameterised by the head.
An object of a polynomial functor is a select head type,
and the functions form the corresponding child(ren) parameterised by the head as seen in @pfunc-math
#footnote([
  More can be read on the ncatlab article @nlab:polynomial_functor,
  we restrict ourselves to Set,
  so I recommend skipping to that section.
]).
// Equally this is the justification for why it is called a polynomial.
Moraly polynomial functors can be thought of as types generic in some set of arguments,
with a collection of constructors (the head type),
where the children correspond to how many of the polymorphic argument are wanted.

$ (h : H) times c_h arrow.r alpha eq.triple sum_(h : H) alpha^(c_h) $ <pfunc-math>

Polynomial functors have all finite products and coproducts.
Polynomial functors are also closed under (co)fixed points so I will write them using a notation a la inductives,
I will use notation provided in @cite:keizer.
For an explanation of the notation see @a:gpfunctors.

=== Common pfunctors

==== Constant

#spg(
  figure(
    text(size: 8pt)[
    ```lean
inductive Const
    (T : Type) (a_1 ... a_n : Type) where
  | mk (t : T)
    ```],
    caption: [Inductive Notation]
  ),
  figure(
    $ (T : Type) -> mpf(T, lambda i. lambda h. 0) $ ,
    caption: [Polynomial]
  ),
  columns: (1fr, 1fr),
  caption: [Constant pfunctor]
)

==== Prj

==== Sum

#spg(
  figure(
    text(size: 8pt)[
    ```lean
inductive Sum (A B : Type) where
  | inl : A -> Sum A B
  | inr : B -> Sum A B
    ```],
    caption: [Inductive Notation]
  ),
  figure(
    $ mpf(BB, lambda { 0, "true" 0 |-> 1, "false" 1 |-> 1, \_ " " \_ |-> 0 }) $ ,
    caption: [Polynomial]
  ),
  columns: (1fr, 1fr),
  caption: [Constant pfunctor]
)

==== Option

==== Functions from fixed types

==== W

==== M

// #figure(
//   diagram(
//     cell-size: 6mm,
//     // debug : 1,
//     show_decl("p1", (0,0), pfunc.prj),
//     show_decl("p2", (3,0), pfunc.sum),
//     show_decl("p3", (7,0), pfunc.list),
//
//     show_map("mp", (0,4), (($x$,),), (($alpha$,),), (($f$,),)),
//     show_obj("il", (2,4), pfunc.sum, "inl", (($excl.inv$, $bold(K)v$),), gap : 1, term : $"inl" v$),
//     show_obj("ir", (5,4), pfunc.sum, "inr", (($bold(K)v$, $excl.inv$),), gap : 1, term : $"inr" v$)
//   )
// )

=== Lean formalization <pfunctorlean>

#lorem(100)

=== F-(co)algebras<pfunctofalg>


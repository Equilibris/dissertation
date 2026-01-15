#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "../../typ/pfunc.typ" as pfunc: show_map, show_obj, show_decl

#pagebreak()

== Polynomial functors

A (multivariate) polynomial functor on set is:
a head-type,
along with a (collection of) child family(ies) parameterised by the head.
An object of a polynomial functor is a select head type,
and the corresponding child(ren) parameterised by the head as seen in @pfunc-math
(this shows only the monovariate version)
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

I find this notation a bit difficult to read,
so for a multivariate polynomial functor $P alpha_0 dots alpha_i$,
with head types as variants $h_0 dots h_j$,
and children $c_(i,h_j)$,
it would conventionally be written as @p-too-big,
I will display the $h$s and $c$s as in @p-reasonably-written.
I write an object of this functor, picked at $h_0$ with functions $f_i$,
as seen in @po-reasonably-written.
The justification of this notation will be seen @pfunctorlean.

$ (j' : "Fin" j) times (h : h_(j')) times (i' : "Fin" i) arrow.r c_(i',h) arrow.r alpha_(i') $<p-too-big>

#figure(
  diagram(
    cell-size: 6mm,
    show_decl("p1", (0,0), pfunc.genp)
  ),
  caption : [The head and child components of $P alpha_0 dots alpha_i$]
)<p-reasonably-written>

#figure(
  diagram(
    cell-size: 6mm,
    show_obj("p1", (0,0), pfunc.genp, "h0", (($f_0$,),($f_i$,),), params : $v$)
  ),
  caption : [An object of $P alpha_0 dots alpha_i$]
)<po-reasonably-written>

Mapping on MvPfunctors is done by composition of the arrows.
This can be seen in @po-mapping-defns.
By set forming a category,
mapping a composition is the same as mapping each one by one.

#figure(
  diagram(
    cell-size: 6mm,
    show_map("mp", (-2,0), (($beta_0$,), ($beta_i$,)), (($alpha_0$,), ($alpha_i$,)), (($g_0$,),($g_i$,))),
    show_obj("p1", (0,0), pfunc.genp, "h0", (($f_0$,),($f_i$,),), params : $v$),
    node((2,0), $eq.delta$),
    show_obj("p2", (3,0), pfunc.genp, "h0", (($g_0 compose f_0$,),($g_i compose f_i$,),), params : $v$, releg : (($beta_0$,), ($beta_i$,))),
  ),
  caption : [
    Definition of mapping of mvpfunctors,

    in this case specalised to
    $P alpha_0 dots alpha_i$]
)<po-mapping-defns>

=== Common pfunctors

==== Constant

A functor, fixed at a constant type $T$ and a arity $i$,
denoted $"const"_i T$,
shown in @p-const-schema.
It has one constructor $"mk"_alpha : T arrow.r "const"_i T alpha_0 dots alpha_i$,
with an inverse $"get"_alpha : "const"_i T alpha_0 dots alpha_i arrow.r T$.

#let P = pfunc.const($T$)

#figure(
  diagram(
    cell-size: 6mm,
    show_decl("p1", (0,0), P)
  ),
  caption : [Definition of $"const"_i T$]
)<p-const-schema>

#figure(
  diagram(
    cell-size: 6mm,
    show_map("mp", (-2,0), (($beta_0$,), ($beta_i$,)), (($alpha_0$,), ($alpha_i$,)), (($g_0$,),($g_i$,))),
    show_obj("p1", (0,0), P, "mk", (($excl.inv$,),($excl.inv$,),), params : $v$, term: $"mk"_alpha v$),
    node((2,0), $eq$),
    show_obj("p2", (3,0), P, "mk", (($excl.inv$,),($excl.inv$,),), params : $v$, releg : (($beta_0$,), ($beta_i$,)), term: $"mk"_beta v$),
  ),
  caption : [
    By initial hom uniqueness,

    the object is invariant under mapping. ]
)

==== Prj

Given a typevector $alpha_0 dots alpha_i$,
and a select index into the vector $(n : "Fin" i)$,
the projection functor holds a value of type $alpha_n$.
It is defined in @p-prj-schema.
It has one constructor $"mk"_alpha : alpha_n arrow.r "prj"_n alpha_0 dots alpha_i$,
with an inverse $"get"_alpha : "prj"_n alpha_0 dots alpha_i arrow.r alpha_n$.

#figure(
  diagram(
    cell-size: 6mm,
    show_decl("p1", (0,0), pfunc.prj)
  ),
  caption : [Definition of $"prj"_n$]
)<p-prj-schema>

#figure(
  diagram(
    cell-size: 6mm,
    show_map("mp", (-2,0), (($beta_0$,), ($beta_n$,), ($beta_i$,)), (($alpha_0$,), ($alpha_n$,), ($alpha_i$,)), (($g_0$,), ($g_n$,), ($g_i$,))),
    show_obj("p1", (0,0), pfunc.prj, "mk", (($excl.inv$,), ($bold(K)v$,) ,($excl.inv$,),), term: $"mk"_n v$),
    node((2,0), $eq$),
    show_obj("p2", (3,0), pfunc.prj, "mk", (($excl.inv$,), ($bold(K) (g_n v)$,) ,($excl.inv$,),), term: $"mk"_n (g_n v)$, releg : (($beta_0$,), ($beta_n$,), ($beta_i$,))),
    // show_obj("p2", (3,0), pfunc.prj, "mk", (($excl.inv$,),($excl.inv$,),), params : $v$, ),
  ),
  caption : [
    By initial hom uniqueness,

    mapping only changes the $n$th argument. ]
)

==== Sum

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

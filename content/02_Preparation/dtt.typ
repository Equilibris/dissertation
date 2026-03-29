#import "../utils.typ" : *
#import "@preview/curryst:0.6.0": rule, prooftree
#import "@preview/subpar:0.2.2" as subpar: grid as spg

== Dependent type theory
We can start by adding a type for Types,
giving us a higher order logic.
Recall back to discrete maths #footnote([TODO: Cite DM]),
how functions between sets $A, B : Type$ $,A -> B$ correspond with a form of arbitrary product,
$B^A eq.triple product_(x : A) B$.
We can generalize this by changing $B$ to be a function $B : A -> Type$,
then letting us write the #box[$Pi$-type]#footnote([
  Some call this a 'dependent product',
  or 'dependent function',
  but this sometimes confuses people so I will simply call it either a Pi,
  or a forall.
]) $product_(x : A) B(x)$.
We can also do the dual construction,
and get #box[$Sigma$-types].
The inference rules for these can be seen in @dtt:fg:psir.
These rules should be familiar as they are the analogous to the rules for $forall, exists$ in the 1st order sequent calculus,
their relationship can be seen in @dtt:eq:pt.
If you are unfamiliar with dependent types,
I recommend viewing them using this relationship.
For a more in depth at dependent type theory,
read @cite:hottbook.

#spg(
  figure(
    prooftree(
      rule(
        name : [$Pi$f],
        [$A : Type$],
        [$B : A -> Type$],
        [$product_(x : A) B(x)$]
      )
    ),
    caption: [$Pi$-forming rule]
  ),
  figure(
    prooftree(
      rule(
        name : [$Pi$i],
        [$Gamma, x : A tack.r v : B(x)$],
        [$Gamma tack.r lambda x. v : product_(x : A) B(x)$]
      )
    ),
    caption: [$Pi$-intro rule]
  ),
  figure(
    prooftree(
      rule(
        name : [$Pi$e],
        [$Gamma tack.r f : product_(x : A) B(x)$],
        [$Gamma tack.r v : A$],
        [$Gamma tack.r f v : B[x "/" v]$]
      )
    ),
    caption: [$Pi$-elimination rule]
  ),
  figure(
    prooftree(
      rule(
        name : [$Sigma$f],
        [$A : Type$],
        [$B : A -> Type$],
        [$sum_(x : A) B(x)$]
      )
    ),
    caption: [$Sigma$-forming rule]
  ),
  figure(
    prooftree(
      rule(
        name : [$Sigma$i],
        [$Gamma tack.r a : A$],
        [$Gamma tack.r b : B[x "/" a]$],
        [$Gamma tack.r chevron.l a, b, chevron.r : sum_(x : A) B(x)$]
      )
    ),
    caption: [$Sigma$-intro rule]
  ),
  figure(
    prooftree(
      rule(
        name : [$Sigma$e],
        [$Gamma tack.r v : sum_(a : A) B(a)$],
        [$Gamma tack.r a : A, b : B[x "/" b] tack.r x : C$],
        [$Gamma tack.r "let" chevron.l a, b chevron.r := v "in" x : C$]
      )
    ),
    caption: [$Sigma$-elimination rule#footnote([
      Technically this isn't the most general eliminator for Sigma's,
      as $C$ can depend on the content of the type.
      For symetry and simplicity I omit this.
    ])]
  ),
  columns: (auto,auto,auto),
  caption: [Inference rules for $Pi$ and $Sigma$ types],
  label: <dtt:fg:psir>
)
#let ch = footnote([
  Steve Awodey calls this 'categorification' @cite:cltt,
  as it is only one direction of Curry-Howard.
  I know @dtt:eq:pt is just a more verbose way of writing 'Curry-Howard',
  but I find it useful to be verbose here.
])
$ Pi, Sigma stretch(harpoons.rtlb)^("propositional truncation")_("Categorification"^ch) forall, exists $<dtt:eq:pt>

=== Categorically

Dependent type theory is an extention on the simply typed lambda calculus.
It is for locally cartesian closed categories,
what ST$lambda$C is for cartesian categories;
the semantics of a dependent calculus will be in terms of some LCCC.



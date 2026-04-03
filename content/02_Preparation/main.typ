#import "../utils.typ" : *
#import "../../typ/pfunc.typ" as pfunc: show_map, show_obj, show_decl
#import "@preview/curryst:0.6.0": rule, prooftree
#import "@preview/subpar:0.2.2" as subpar: grid as spg
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

////////////////////////////////////////////////////////////////////////////////

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

#let mpf(a, b) = $chevron.l #a, #b chevron.r$
#let Type = $"Type"$

////////////////////////////////////////////////////////////////////////////////

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

////////////////////////////////////////////////////////////////////////////////

== Recursion and Inductives<sec:coind>

We are all familiar with algebraic datatypes from OCaml.
These are structures freely generated from a set of constructurs.
The classic example is a list,
given as two constructors,
`cons : 'a -> 'a list -> 'a list` and `nil : 'a list`,
and a way to consume lists `fold : 'a -> ('b -> 'a -> 'a) -> 'b list -> 'a`.
We write this as seen in @cr:ls:list.
This is what is known as an inductive datatype.
Inductive datatypes are well-founded trees#footnote([
  OCaml is quite stupid and allows for non well-founded trees,
  an example is `let rec degen = Cons((), degen)`.
  This is because inductives and coinductives are 'coincident' in OCaml.
  We will come back to this in the next section.
]);
any function that terminates,
must by definition return at most a finite (but unbounded) amount of constructors.
This means fold is guarangteed to terminate too.
All (primitive) recursive functions can be compiled into a call to fold#footnote([TODO: Cite McBride's work]).

#figure(
```ocaml
type ('a, 'b) listF = Nil | Cons of 'a * 'b

type 'a list = Nil | Cons of 'a * 'a list
let nil = Nil
let cons h t = Cons(h,t)
let rec fold bh ih = function | Nil -> bh | Cons(h, t) -> ih h (fold bh ih t)
```,
  caption: [Definition of list in OCaml]
)<cr:ls:list>

=== Categorically

#let Set = $bold("Set")$

Given the family of endofunctors on $Set$.
Consider the polynomial given by $L_A = 1 plus.o (underline(A) times.o id)$,
or in its expanded form in @cr:m:list.
Now recall the definition of the category of #box[$L_A$-algebras]#footnote([TODO: Cite algebra definition]).
The lists we are used to are exactly the initial object in this category.
The initial map takes an algebra $f : L_A (B) -> B$ and yields a map $"fold" : mu L_A -> B$#footnote([TODO: Cite Neel]).
This is exactly what we want,
as expanding the definition or $L_A (B)$ and distrubuting this over the arrows we get the signature above.

$
L_A & (quad X quad &) &= & quad 1 quad        & plus.o quad & (& A       & times.o quad & X &) \
L_A & (quad f quad &) &= & (iota_l compose !) & plus.o_m    & (& bb(1)_A & times.o_m    & f &)
$<cr:m:list>

== Corecursion and coinductives

Coinductives are the duals of inductives,
they have an operation `unfold` which is the dual of the operation `fold`.

=== Morally

Morally,
if you have never seen `unfold`'s or coinductives,
simply view it as if a fix F yields an X,
then cofix F yields a lazy X#footnote([
  I. e. $"fix" L_A$ gives lists,
  then $"cofix" L_A$ gives lazy lists.
]).
We can think back to what we did in Foundations of Computer Science,
when we made lazy lists we also had to change recursive occurances to be thunked,
this thunking allows infinite structures to exist in finite memory.

=== In OCaml

#figure(
```ocaml
type 'a colist = Nil | Cons of 'a * (() -> 'a colist)
let nil = Nil
let cons h t = Cons(h,() -> t)
let rec fold bh ih = function | Nil -> bh | Cons(h, t) -> ih h (fold bh ih t)
```,
  caption: [Definition of list in OCaml]
)<cr:ls:colist>

=== Categorically

////////////////////////////////////////////////////////////////////////////////

== Tools used

== Requirement Analysis

To expand on the success critera given in the proposal,
I specified the project using MoSCoW.
Here the success critera have become MUSTs,
and improvements have become SHOULD.
I have done this for the core and each of the extentions of the project.

#let moscow(nm, m, s, c, x) = [
#let f(l) = (n) => box(width: 3em)[#strong(nm + l + [#n])]
#set enum(numbering: f("M"))
#m
#set enum(numbering: f("S"))
#s
#set enum(numbering: f("C"))
#c
#set enum(numbering: f("W"))
#x
]

=== State machine encoding (Core)

#columns(2)[
#moscow("S", [
1. The SME MUST be implemented.
2. The SME MUST be constant time under destructuring.
3. The SME MUST be able to express the NT monad, @pl:sec:ntm.
4. The equivelence between SME and PA MUST be implemented.
], [
1. The SME SHOULD have a coinduction principle.
], [
1. The SME COULD have a productivity transform @pl:sec:prod.
2. The SME COULD have an Interaction tree library @pl:sec:itree.
3. The SME COULD have a Choice Tree library @pl:sec:ctree.
], [
1. The SME WONT have a syntax macro a la @cite:keizer.
])

=== Non-termination-monad (Core)<pl:sec:ntm>

#moscow("N", [
1.
], [
1.
], [
1.
], [
1.
])

=== ABI Type (Extention)

=== Interaction Trees (Extention)<pl:sec:itree>

=== Futumorphic productivity (Extention)<pl:sec:prod>

=== Choice Trees (Extention)<pl:sec:ctree>
]



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


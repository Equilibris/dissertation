
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



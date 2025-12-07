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

// TODO


#include "abi.typ"

== Stream implementation

== Expanding the progressive approximation theory

During the pheasability assesment I noticed that,
in the current formalised theory of polynomials,
the statement wouldn't even type-check.
This stemmed from a problem with the corecursive principle for the M type in the old implementation.
$"corec" : {alpha : "TypeVec".{cal(U)} n} arrow {beta : "Type" cal(U)} arrow (g : beta → P (alpha ::: beta)) arrow beta arrow M alpha$
#footnote(link("https://github.com/leanprover-community/mathlib4/blob/7a60b315c7441b56020c4948c4be7b54c222247b/Mathlib/Data/PFunctor/Multivariate/M.lean#L152-L154")).
The problem here is that both $alpha$ and $beta$ have to both reside in $cal(U)$.
Solving this is done through the next two sections.

=== Universe lifting of polynomial functors.

The main problem caused here comes from the fact that lean isnt cummulative.
This means it is impossible to express a universe hetrogouns typevector.
In other words $alpha ::: beta$ is only typable if $alpha : "TypeVec".{cal(U)} n$ and $beta : "Type" cal(U)$.
The natural way of solving this is using the supremum in universe levels you get from
$"ULift" : "Type" cal(U) arrow "Type" (max cal(U) cal(V))$.
This means we can have $beta : "Type" cal(U)$ and $alpha : "Type" cal(V)$,
then ulift both of them to a common universe $"ULift" alpha ::: "ULift" beta : "TypeVec".{max cal(U) cal(V)} (n+1)$
#footnote([Note we overload ULift as a notation to refer to lifting TypeVecs as well]).

Noticable the next hurdle we encounter is that PFunctors are restricted to a universe level.
Recall the definition from @pfunctorlean.
Observe how for a $"MvPfunctor".{cal(U)} n$,
we require that both the head and child reside in $cal(U)$.
This will also cause problems,
as looking back at the definition of the corecursor,
we will require $P$ to be able to accept $"ULift" alpha ::: "ULift" beta$.
If we do not add the ability to lift $P$,
the unifier will force $cal(U) = cal(V)$,
thereby invalidating all the work we did in the previous section.
Luckily lifting a PFunctor is relatively easy.
We define it as $"ULift" P eq.delta angle.l "ULift" P.1, lambda x mapsto "ULift" (P.2 x) angle.r$.
This works and now we can move on to our goal
#footnote([
  TODO: Speak with JV / W to see if this might be done in the lit,
  Ex : Locally presentable and accessable categories Adameck roshiski
]).

=== Generalizing the corecursor

Now with all the work in the previous section,
by generalizing $"corec'"$#footnote([Done in PR NUMBER ]),
we can define
$"corecU" : {alpha : "TypeVec".{cal(U)} n}
  arrow {beta : "Type" cal(V)}
  arrow (g : beta → "ULift" P ("ULift" alpha ::: "ULift" beta))
  arrow beta
  arrow M.{cal(U)} alpha$.
Notably we are able to fit the object into $cal(U)$
(as opposed to in the SME).

The expected diagram using corecU and dest commutes.

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
The main beinifit from this is the performance aspect though.
This will be seen in @smevpa.
We will henceforth refer to the datatype SME.PreM.

== Proving the equvilence

== Cofix implementation


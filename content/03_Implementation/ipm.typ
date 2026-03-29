== Induced Productivity Transform

During my internship under AK and TG,
I made a structure I then called `DeepThunk`s.
I now refer to them as the induced productivity monad.
They are the general way of constructing productive functions on cofixed points from terminating functions.

Given a polynomial $bold(P) accent(alpha, macron) beta$,
then the corecursor we get for $bold("M" P) accent(alpha, macron)$ is:

$ "corec" : {beta} arrow.r (beta arrow.r bold(P) accent(alpha, macron) beta) arrow.r beta arrow.r bold("M" P) accent(alpha, macron) $

Often this is adequet,
but one has a few drawbacks that can be summarised as:
it has to emit exacly one 'layer' of the final structure.
The end goal would be to allow it to emit anything from layer 1 to the entire structure.
One can think of this as taking the most general choice of $beta$.
The structure that solves this is $bold("PT" P) accent(alpha, macron) beta eq.delta bold("M")_xi bold(P) accent(alpha, macron) (beta plus.o xi)$.
From here we construct two unique functions, inject and dtcorec:

$ "inject" : { beta } arrow.r bold("M" P) accent(alpha, macron) arrow.r bold("PT" P) accent(alpha, macron) beta 
colon.eq "corec"_(bold("PT" P)) ("map"_(bold("M" P)) (bb(1) ::: iota_r) compose "dest") $

$ "dtcorec" { beta } (g : beta arrow.r bold("PT" P) accent(alpha, macron) beta) : beta arrow.r bold("M" P) accent(alpha, macron)
colon.eq "corec"_(bold("M" P)) (("map"_(bold("M" P)) (bb(1) ::: [g, bb(1)]) ) compose "dest") compose g $


#import "../utils.typ": *

Coinductive datatypes are useful not only as a program verification tool,
but also in general purpose computation.
To this point Lean has only had implementations intended for theoretical reasoning,
from work such as #cite(<cite:qpf>, form: "prose") and #cite(<cite:keizer>, form: "prose").
There continues to be interest in this topic on the Lean Zulip,
and from other researchers with #cite(<cite:mslc>, form: "prose").
All prior work is slow, rendering it unusable for general purpose computation.

Lean now has a coinduction library with functions usable in general purpose computation.
This means that we can now write, and verify non-terminating programs,
and have the complexity we would like from the program.
To aid in writing these functions,
futumorphisms were implemented.
These allow for mixed corecursive-recursive definitions to be written in a more natural way.

On top of this, this dissertation includes a feature rich interaction tree library.
This has potential to be used directly in work that requires formally verified compilation or translation.
T. Grosser has expressed interest in using this on extending VeIR @cite:veir.
// In private conversation, M. Sammler is open to extentions to his ITree library for weak bisimilarity.

I have met all my success criteria,
along with universe changing type, an ITree implementation and a futumorphism implementation.

== Future work

On completion of this project,
there are now 3 coinduction libraries for lean.
The different abilities of the projects can be seen in @conc:tb:comp.
Each of the libraries now have their own contributions but currently are all incompatible.
The goal would be to make one library to unite all of these features.
This project would be more work than this dissertation.


#let gcv(body) = table.cell(body, fill: teal.lighten(50%))

#figure(
  table(
    columns: 4,
    table.header[][The project][#cite(<cite:keizer>, form: "prose")][#MS],
    [`dest` performance], gcv[$cal(O)(1)$], $cal(O)(n)$, $cal(O)(n)$,
    [Type Macro], [N], gcv[Y#footnote[For Lean v4.25]], [N],
    [Function definitions], [`futu`], [-], gcv[`partial_fixpoint`],
  )
)
<conc:tb:comp>

=== Syntax macro for types

#cite(<cite:keizer>, form: "prose") puts forward a macro for constructing QPFs @cite:qpf.
This is a required feature for any coinduction library,
for this reason it would be highly desirable to have this.
I have designed all the functions on the #TM to be drop in replacements for `M`.
This means it should be as simple as updating Alex's library to Lean 4.29,
and updating the relevant occurrences.

=== Derecursifier for corecursive function

A more ambitious goal is finding a way to write a derecursifier for corecursive functions.
This would be a macro taking a definition,
and transforming a function body into a corecursive function.
This would work similarly to `partial_fixpoint` but would need further work.
One of the main reasons the futumorphism was implemented,
was to serve as a middleground here,
but it might even be possible to use it in the derecursifier.

=== Extending the ITree library

The only component of the ITree paper missing is the collection of effects and heaplang compiler.
Implementing these would be a lot of work.

// The main component of the ITree paper missing is the zoo of events,



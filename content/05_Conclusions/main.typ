
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
In private conversation, M. Sammler is open to extentions to his ITree library for weak bisimilarity.

I have met all my success criteria,
along with universe changing type, an ITree implementation and a futumorphism implementation.

== Future work

=== Syntax macro for types

#cite(<cite:keizer>, form: "prose") puts forward a macro for constructing QPFs @cite:qpf.
This is a required feature for any coinduction library,
for this reason it would be highly desirable to have this.
I have designed all the functions on `HpLuM` to be drop in replacements for `M`.
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

The main component of the ITree paper missing is the zoo of events,
these would involve quite a bit of implementation.



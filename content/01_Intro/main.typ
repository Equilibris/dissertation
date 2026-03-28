
== Use cases

=== Infinite datastructures

Often,
a problem in programming requires leaving the finite.
In cases we want to maintain safety properties of the language.
For example:

- We cannot use termination as a critaria for infinite structures,
  so how do we maintain the totallity of the language.
- One would also want functions written for a language like this to have the expected runtime;
  we want a constant time to unfold.
- We want an interface that lets us unfold and reasona bout definition just how we would any other function.

A concreate example of a usecase for this would be reading from a UNIX file.
Since we can for example have a program `cat` which echos out all it is fed,
then what would the output of `yes | cat` be? // TODO: Make this no-break
This would have to be a stream.

=== Compiler semantics

Recalling L1#footnote[TODO: Add reference to sem of prog],
we gave it a big-step operational semantic.
We later tried to implement an interpreter for this semantic to execute L1 programs.
This required us to prove quite a few substantial coherences.
An alternative way we could have tried would be to write down an interpreter,
and simply use this as the semantic.
Most proof-assistants would not allow this though,
as they require function totallity.
So we would want:

- A way to write an interpreter of a partial language,
  and be able to use this interpreter as a semantic in formal software.
- We would also want the asymptotics of the interpreter to be the same as the source language.
- We want to be able to encode effects in the langauge in addition to just non-termination.

=== Safe webservers



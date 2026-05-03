
Lean @cite:lean is a pure and total functional language.
Meaning all functions must terminate.
Often, a problem in programming requires leaving the finite.
It would be nonsensical to require these to terminate.
For data like this we use something called a _coinductive_.
In general purpose programming, these appear all the time, for example Streams.
Researchers working on program verification are also interested in this,
they use structures called interaction trees as a denotational semantic @cite:itree.

Lean has an implementation of coinductives @cite:keizer @cite:qpf @cite:mathlib.
These are implemented as a series of progressive approximations.
We will refer to this as the PA encoding.
As a limitation of this encoding unfolding a layer of a coinductive,
takes time proportional to the depth of the layer.
A consequence of this is getting a stream to depth $n$ takes $cal(O)(n)$ time,
this gets dramatically worse as you map streams,
becoming intractable for most programs.
An alternative encoding stores a generating function,
parameterized by some carrier, and an initial state.
This is what I will refer to as the state-machine encoding.
By construction, destructuring will be $cal(O)(1)$.
The downside of this definition is that it is impredicative,
and therefore becomes harder to use and reason about.

This dissertation will implement the SME,
prove it is equivalent to the PA encoding,
and use this to construct an efficient coinduction library.
Additionally we will implement interaction trees,
with an equivalence relation that can be used to find contextually equivalent programs.

// This dissertation will prove these structures are equivalent,
// and use this 

// == Use cases
//
// === Infinite datastructures
//
// In cases we want to maintain safety properties of the language.
// For example:
//
// - We cannot use termination as a criteria for infinite structures,
//   so how do we maintain the totality of the language.
// - One would also want functions written for a language like this to have the expected runtime;
//   we want a constant time to unfold.
// - We want an interface that lets us unfold and reason about definition how we would any other function.
//
// A concrete example of a use case for this would be reading from a UNIX file.
// Since we can for example have a program `cat` which echos out all it is fed,
// then what would the output of #box[`yes | cat`] be?
// This would have to be a stream.
//
// // TODO: Write about the theoretical performance of the PA.
//
// === Compiler semantics
//
// Recalling L1#footnote[TODO: Add reference to sem of prog],
// we gave it a big-step operational semantics.
// We later tried to implement an interpreter for this semantics to execute L1 programs.
// This required us to prove many substantial coherences.
// An alternative way we could have tried would be to write down an interpreter,
// and use this as the semantics.
// Most proof assistants would not allow this though,
// as they require function totality.
// So we would want:
//
// - A way to write an interpreter of a partial language,
//   and be able to use this interpreter as a semantics in formal software.
// - We would also want the asymptotics of the interpreter to be the same as the source language.
// - We want to be able to encode effects in the language in addition to non-termination.
//
// === Safe webservers
//


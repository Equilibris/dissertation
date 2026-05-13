Lean @cite:lean is a pure and total functional language,
meaning all functions must terminate.
Problems such as program simulation
or production of streams of data
often require leaving the finite.
We refer to data like this as _coinductive_.
It does not make sense to require an infinite stream of data to terminate.
Researchers working on program verification are also interested in this,
they use structures called interaction trees as a denotational semantic @cite:itree.

Lean has two implementations of coinductive data types @cite:mathlib @cite:keizer @cite:qpf @cite:mslc.
These are implemented as a series of progressive approximations.
As a limitation of this encoding, unfolding a layer of a coinductive type,
takes time proportional to the depth of the layer.
A consequence of this is that getting a stream to depth $n$ takes $cal(O)(n)$ time.
This gets dramatically worse as you map streams,
becoming intractable for most programs.
An alternative encoding stores a generating function,
parameterised by some carrier, and an initial state.
This is what I will refer to as the state-machine encoding.
By construction, destructuring will be $cal(O)(1)$.
The downside of this definition is that it is impredicative,
and therefore becomes harder to use and reason about.

This dissertation is the final piece needed to complete state of coinductive data types in Lean.
We have macros for defining @cite:keizer and writing functions @cite:mslc on coinductive data types.
This dissertation is the first time anyone has decided to try and tackle the performance of library coinductive types.
As a result of this, the path is now set to make a usable coinduction library.
//
// It was no small undertaking building this project.
// Around every corner I had to wrangle universe levels and general polynomial functors.

I will implement the state-machine encoding of $M$-types,
prove it is equivalent to the progressive approximation encoding,
and use this to construct an efficient coinduction library.
Additionally, we will implement interaction trees,
with an equivalence relation that can be used to find contextually equivalent programs.

// TODO:
// Writing the project, #JV, #TG, #AK and I decided implementing interaction trees would be too ambitious.
// For this we decided to make it an extension instead,
// and rather reason about the simpler structure being the non-termination monad.

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


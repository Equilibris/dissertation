#import "../utils.typ": *

== Transiteration

A family of functions,
that keep solving problems throughout this dissertation are what I call transliterations.
Given some parameter span $X$#footnote([This not necessarily a type, as lean does not have omega-types (Set$omega$ from Agda).]),
either in some $Type$,
or more commonly over some universe $cal(U)$.
We define a transliteration on $X$ as a family of functions $t_(a,b) : X a -> X b$,
such that they are closed under composition $t_(b,c) compose t_(a,b) = t_(a,c)$#footnote([
  This is very similar to saying it's an idempotent,
  but technically $t_(b,c)$ and $t_(a,b) $ arent the same function.
]),
and the self-path is identificaion $t_(a,a) = id$.

The trivial instantiation of a transliteration is a `cast`#footnote([
  Or if you read @cite:hottbook, this is called `transport`.
]),
here we pick $X$ as equal types,
obviously `cast aa = id` and `cast bc ∘ cast ab = cast (ab.trans bc)`.
One could even say that a transliteration is a function that behaves like `cast`.

An example we will keep defining is universe transliteration,
here we take $X = "ULift"_((-))$,
using this we define the transiteration as seen in @tr:ls:code.
This is the closest we get to having omega-types and cumilativity in lean;
as long as the function is applied at a usage of ULift it all just works.
We will use this function to define transliteration between universe-lifted polynomials,
we will see more of this in @sec:ulift_p.

#let f = read("../../sme/Sme/ForMathlib/Data/ULift.lean").split("\n").slice(2,11).join("\n")

#figure(
  raw(f, lang : "lean", block:true),
  caption: [Transliteration between universes of types]
)<tr:ls:code>

Another major usage of a transiteration was used when defining the eliminator for `ABI`,
I will discuss this more when we get to @sec:abi.
This was where I first discovered transliteration,
and made it possible to define a universe-polymorphic eliminator.


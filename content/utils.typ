#import "@preview/ctheorems:1.1.3": *

#let Type = $bold("Type")$
#let MT = [$M$-type]
#let MTs = [$M$-types]

#let flamboyant(x) = x.replace("max v w", "max 𝓥 𝓦").replace("max u v", "max 𝓤 𝓥").replace("{u", "{𝓤").replace("v}", "𝓥}").replace("u}", "𝓤}").replace("{v", "{𝓥")
#let takeL(f, s, e) = f.split("\n").slice(s,e).join("\n")
#let partL(f, ..args) = {
  let args = (0,) + args.pos() + (none,)
  let f = f.split("\n")

  args.zip(args.slice(1)).map(((a,b)) => f.slice(a,b).join("\n"))
}

#let MATHLIB = [Mathlib @cite:mathlib]
#let FANTOMORPH = cite(<cite:fantomorph>, form: "prose")

#let JV = "Jamie Vicary"
#let AK = "Alex Keizer"
#let TG = "Tobias Grosser"
#let NC = "Nicolas Chappe"
#let MS = cite(<cite:mslc>, form:"prose")

#show: thmrules.with(qed-symbol: $square$)

#let theorem = thmbox("theorem", "Theorem", fill: rgb("#eeffee"))
#let corollary = thmplain(
  "corollary",
  "Corollary",
  base: "theorem",
  titlefmt: strong
)
#let definition = thmbox("definition", "Definition", inset: (x: 1.2em, top: 1em))

#let example = thmplain("example", "Example").with(numbering: none)

#let U = $cal(U)$
#let V = $cal(V)$

#let TM = [$cal(U)$-universe State-Machine #MT]
#let TMs = [$cal(U)$-universe State-Machine #MTs]

#let ULift = $"ULift"$



#import "template.typ": *
#import "@preview/wordometer:0.1.5": word-count, total-words

// Take a look at the file `template.typ` in the file panel
// to customize this template and discover how it works.

#set page(numbering: "i")

#show: project.with(
  title: "Efficient Coinductives through \nState-Machine Corecursors",
  college: none, // "Gonville & Caius College",
  author: BGN,
  // Insert your abstract after the colon, wrapped in brackets.
  // Example: `abstract: [This is my abstract...]`
  proforma: [
#table(
  strong[BGN], [ #BGN],
  [],[],
  strong[Title], table.cell(colspan:3)[ Efficient Coinductives through State-Machine Corecursors],
  strong[Word count], [ #total-words],
  // nix-shell -p cloc --run "cloc . --exclude-dir=.lake,ista-plv-coinductive,content,font --include-ext lean,py,typ"
  strong[Line count], [ #(9564 + 1755 + 388 + /* PR */150)],
  strong[Examination], [CST Part II],
  strong[Year], [ 2026],
  strong[Day-to-day #linebreak() supervisor ], [Alex Keizer#linebreak() Tobias Grosser],
  strong[Marking #linebreak() supervisor ], [ Jamie Vicary],
  strong[Project #linebreak()originator ], [ The candidate],
  [],[],
  strong[Ethics approval], [N/A],
  columns: (auto, auto, auto, auto),
  align: (right, left)
)

#set heading(outlined: false)

== Project Aims

Create the first high performance coinduction library outside of the kernel.
Construct simple coinductive types in this system.

// Optimise library coinductive data types in Lean and implement an example structure.

== Work completed

Implemented the first constant time coinduction library.
Constructed rich data structure for program verification and denotational semantics.
Improved ergonomics for coinductive function writing.

// Optimised library coinductive data types in Lean and implemented rich data types for program verification.

== Special difficulties

Alex Keizer had to take a break half way through the project,
Tobias Grosser took over supervision.

My grandfather /*Stein-Ulf Sørensen*/ passed away (2025-10-28),
my aunt /* Asbjørg Johanne Raanes*/ passed away (2025-12-19).
I missed term for both the funerals.
  ],
  acknowledgements: [
/ Alex Keizer : For supervising this dissertation and giving me the opportunity to explore coinductive types.
/ Tobias Grosser : For taking over supervision when Alex could not and pushing me to go further.
/ Jamie Vicary : For marking this project on short notice and providing insightful feedback.
/ Nicolas Chappe : For taking a genuine interest in the project and helping me with ITrees.
/ Wojciech Różowski : For helping with project specifics and technical parts of coinductives.
/ Russell Moore : For reviewing my dissertation and help me identify specialist language.
  ],
  date: "May 15, 2026",
  logo: "cst_logo.svg")

// #todo[Abtract]

#show: word-count.with(exclude: (
  "bibliography", "cite", "display", "equation", "h", "hide", "image", "line", "linebreak", "locate", "metadata", "pagebreak", "parbreak", "path", "polygon", "ref", "repeat", "smartquote", "space", "style", "update", "v",
  "figure",
  "caption",
  <aix>,
))

#set page(numbering: "1", number-align: center, )
#context counter(page).update(n => 1)

= Introduction

#include "content/01_Intro/main.typ"

= Preparation

#include "content/02_Preparation/main.typ"

= Implementation

#include "content/03_Implementation/main.typ"

= Evaluation

#include "content/04_Evaluation/main.typ"

= Conclusions

#include "content/05_Conclusions/main.typ"

#bibliography("bib.bib", style : "ieee")

#set heading(numbering: "1.A")

#[
= Appendicies

#[

// #context counter(figure).update(n => 1)
// #show: figure.with(numbering : "A")

#include "content/Appendix/pred.typ"
#include "content/Appendix/bench.typ"
#include "content/Appendix/cardmod.typ"
#include "content/Appendix/igraph.typ"

]

= Proposal

See proposal overleaf

#set page(numbering: none, margin: (top: 0cm, bottom:0cm, x:0cm, y:0cm))

#for i in range(1, 6) {
  image("./proposal.pdf", page: i)
}
]<aix>
// #include "./proposal.typ"


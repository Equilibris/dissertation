#import "template.typ": *
#import "typ/todo.typ": todo, show-todos
#import "@preview/wordometer:0.1.5": word-count, total-words

// Take a look at the file `template.typ` in the file panel
// to customize this template and discover how it works.

#set page(numbering: "i")

#show: project.with(
  title: "Efficient Coinductives through \nState-Machine Corecursors",
  author: "William Sørensen",
  // Insert your abstract after the colon, wrapped in brackets.
  // Example: `abstract: [This is my abstract...]`
  proforma: [
*Word count:* #total-words

  ],
  acknowledgements: lorem(59),
  date: "May 15, 2026",
  college: "Gonville & Caius College",
  logo: "cst_logo.svg")

// #todo[Abtract]

#show: word-count.with(exclude: (
  "bibliography", "cite", "display", "equation", "h", "hide", "image", "line", "linebreak", "locate", "metadata", "pagebreak", "parbreak", "path", "polygon", "ref", "repeat", "smartquote", "space", "style", "update", "v",
  "figure",
  "caption",
  <aix>,
))

#outline(
  title: [List of figures],
  target: figure
)

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

#lorem(1000)

// #include "content/Appendix/graph_pfunctor.typ"
#include "content/Appendix/igraph.typ"

= Proposal

See proposal overleaf

#set page(numbering: none, margin: (top: 0cm, bottom:0cm, x:0cm, y:0cm))

#for i in range(1, 6) {
  image("./proposal.pdf", page: i)
}
]<aix>
// #include "./proposal.typ"


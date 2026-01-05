#import "template.typ": *
#import "typ/todo.typ": todo, show-todos

// Take a look at the file `template.typ` in the file panel
// to customize this template and discover how it works.

#show: project.with(
  title: "Efficient Coinductives through \nState-Machine Corecursors",
  author: "William Sørensen",
  // Insert your abstract after the colon, wrapped in brackets.
  // Example: `abstract: [This is my abstract...]`
  abstract: lorem(59),
  acknowledgements: lorem(59),
  date: "May 22, 2025",
  college: "Gonville & Caius College",
  logo: "cst_logo.svg")

// #todo[Abtract]

#show-todos()

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

#bibliography("bib.bib", style : "apa")

= Appendicies


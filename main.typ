#import "template.typ": *
// Take a look at the file `template.typ` in the file panel
// to customize this template and discover how it works.
#show: project.with(
  title: "Coind",
  author: "William Sørensen",
  // Insert your abstract after the colon, wrapped in brackets.
  // Example: `abstract: [This is my abstract...]`
  abstract: lorem(59),
  acknowledgements: lorem(59),
  date: "April 29, 2023",
  college: "Gonville & Caius College",
  logo: "cst_logo.svg")

// We generated the example code below so you can see how
// your document will look. Go ahead and replace it with
// your own content!

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

= Appendicies


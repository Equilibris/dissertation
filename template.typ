#import "@preview/codly:1.3.0": *
#import "@preview/codly-languages:0.1.8": *


#let common(
  title: "My Dissertation",
  author: "<Insert name>",
  abstract: [],
  acknowledgements: [],
  date: none,
  logo: none,
  college: "<Insert college>",
  course: "Computer Science Tripos, Part III",
  body,
) = {
  set document(author: author, title: title)
  set page(numbering: "1", number-align: center)
  set text(font: "New Computer Modern", lang: "en")
  show math.equation: set text(weight: 400)
  set heading(numbering: "1.1")
  set par(justify: true)
  show: codly-init.with()
  codly(languages: codly-languages)

  body
}

// The project function defines how your document looks.
// It takes your content and some metadata and formats it.
// Go ahead and customize it to your liking!
#let project(
  title: "My Dissertation",
  author: "<Insert name>",
  abstract: [],
  acknowledgements: [],
  date: none,
  logo: none,
  college: "<Insert college>",
  course: "Computer Science Tripos, Part III",
  body,
) = {
  body = common(title: title, author: author, abstract: abstract, acknowledgements: acknowledgements, date : date, logo : logo, college : college, course : course, body)
  let chapternum = loc => {
    str(query(heading.where(level: 1, numbering: "1.1").before(loc), ).len())
  }

  show heading: it => {
    if it.level == 1 {
      pagebreak()
      v(4.5em)
      set text(size: 25pt)
      if it.numbering == "1.1" {
        "Chapter "; chapternum(it.location())
        v(0.5em)
        it.body
      }
      else {
        it
      }
      v(2em)
    }
    else if it.level < 4 {
      v(1em)
      it
      v(0.5em)
    }
    else {
      it
    }
  }

  // Title page.
  // The page can contain a logo if you pass one with `logo: "logo.png"`.
  set align(center)
  if logo != none {
    align(left, image(logo, width: 30%))
  }

  v(0.5fr)
  text(1.1em, date)
  v(1.2em, weak: true)
  text(2em, weight: 700, title)

  // Author information.
  pad(
    top: 0.7em,
    strong(author)
  )

  // College
  college

  v(1fr)
  par()[
    Submitted in partial fulfilment of the requirements for the\
    #course
  ]
  set align(left)

  // Declaration page.
  heading(
    outlined: false,
    numbering: none,
    "Declaration"
  )

  par()[
    I, #author of #college, being a candidate for the \course, hereby declare that this report and the work described in it are my own work, unaided except as may be specified below, and that the report does not contain material that has already been used to any substantial extent for a comparable purpose. \
    // #v(1em)
    *Signed*: #author \
    *Date*: #date
  ]

  // Abstract page.
  heading(
    outlined: false,
    numbering: none,
    "Abstract"
  )
  abstract

  // Acknowledgements page.
  heading(
    outlined: false,
    numbering: none,
    "Acknowledgements"
  )
  acknowledgements

  // Table of contents.
  outline(
    depth: 3,
    // indent: true,
    target: heading
  )

  // Main body.
  set par(justify: true)

  body
}

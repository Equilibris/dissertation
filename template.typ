// #import "@preview/codly:1.3.0": *
// #import "@preview/codly-languages:0.1.8": *
// #import "@preview/codelst:2.0.2": sourcecode
#import "@preview/itemize:0.2.0" as el
#import "@preview/ctheorems:1.1.3": *
#import "./content/utils.typ": BGN

#let common(
  title: "My Dissertation",
  author: "<Insert name>",
  proforma: [],
  acknowledgements: [],
  date: none,
  logo: none,
  college: "<Insert college>",
  course: "Computer Science Tripos, Part III",
  body,
) = {
  set document(author: BGN, title: title)
  set page(margin: 2cm)
  set text(font: "New Computer Modern", lang: "en")
  show math.equation: set text(weight: 400)
  set heading(numbering: "1.1")
  // set math.equation(numbering: "1.1")
  set par(justify: true)
  set raw(syntaxes: "./content/Rocq.sublime-syntax")
  show raw: set text(font : (name: "FiraCode Nerd Font"))
  show raw.where(block: true): set text(size: 6pt)
  show: el.default-enum-list
  show: el.config.ref
  show: thmrules.with(qed-symbol: $square$)
  // TODO: Fix codly
  // show: codly-init.with()
  // codly(languages: codly-languages, number-format : none, display-name: false, zebra-fill: none)
  // show raw: (code) => sourcecode(code)


  body
}

// The project function defines how your document looks.
// It takes your content and some metadata and formats it.
// Go ahead and customize it to your liking!
#let project(
  title: "My Dissertation",
  author: "<Insert name>",
  proforma: [],
  acknowledgements: [],
  date: none,
  logo: none,
  college: "<Insert college>",
  course: "Computer Science Tripos, Part II",
  body,
) = {
  set page(margin: 2cm, header: align(right + horizon)[#BGN #h(-2cm + 1em)])

  show table.header: strong
  set table( stroke: none, align: center)

  body = common(title: title, author: author, proforma: proforma, acknowledgements: acknowledgements, date : date, logo : logo, college : college, course : course, body)
  let chapternum = loc => {
    str(query(heading.where(level: 1, numbering: "1.1").before(loc), ).len())
  }

  show heading: it => {
    if it.level == 1 {
      pagebreak(weak: true)
      // v(4.5em)
      set text(size: 25pt)
      if it.numbering == "1.1" {
        "Chapter "; chapternum(it.location())
        [: ]
        it.body
        v(-.75em)
        line(length:100%)
        v(-.5em)
      }
      else {
        it
      }
      v(.5em)
    }
    else if it.level < 5 {
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
  grid(
    image("cst_logo.svg", height: 2cm),
    [],
    image("gnc.svg", height: 1.2cm),
    columns: (auto, 1fr, auto)
  )

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
    "Proforma"
  )
  proforma

  // Acknowledgements page.
  {
    show pagebreak: it => {}
    heading(
      outlined: false,
      numbering: none,
      "Acknowledgements"
    )
  }
  acknowledgements

  // Table of contents.
  pagebreak()
  {
  show pagebreak: it => {}

  show footnote: it => {}
  set footnote.entry(separator: none)

  show cite: it => {}
  show footnote.entry: it => {}
  columns(2,
    outline(
      depth: 3,
      // indent: true,
      target: heading
    )
  )
  pagebreak(weak:true)
  // columns(2,
    outline(
      title: [List of figures],
      target: figure
    )
  // )
  }

  // Main body.
  set par(justify: true)

  body
}

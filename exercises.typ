#set page(numbering: "1")
#set list(marker: ([•], [◦], [--]))
#let unipd-red = rgb(180, 27, 33)

#show heading.where(level: 1): it => {
  v(0.5em)
  set text(size: 20pt, fill: unipd-red)
  [#it.body]
  v(0.5pt)
}

#show outline.entry.where(
  level: 1
): it => {
  v(1em, weak: true)
  strong(it)
}

#let make_title(title: none, subtitle: none, author: none, date: none) = align(center, [
    #text(size: 30pt, weight: "bold", fill: unipd-red, smallcaps(title)) \
    #v(5pt)
    #text(size: 25pt, weight: "bold", fill: unipd-red, subtitle)

    #set text(size: 18pt)
    #author

    #date
  ]
)

#v(10em)
#figure(image("images/unipd-logo.png", width: 50%))
#v(3em)

#make_title(
  title:    [Languages for Concurrency and Distribution],
  subtitle: [Exercises],
  author:   [Alberto Lazari],
  date:     [II Semester A.Y. 2022-2023],
)
#pagebreak()

#outline(
  title: "Index",
  indent: 2em,
)
#pagebreak()

#include "exercises/ccs-vp.typ"

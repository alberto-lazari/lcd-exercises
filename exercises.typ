#import "@local/unipd-doc:0.0.1": *

#show: unipd-doc(
  title:    [Languages for Concurrency and Distribution],
  subtitle: [Exercises],
  author:   [Alberto Lazari],
  date:     [II Semester A.Y. 2022-2023],
)

#set heading(numbering: none)
#show heading: it => {
  set text(size: 1.3em)
  it
}

#set math.mat(delim: "[")

#show ref: it => {
  let eq = math.equation
  let el = it.element
  if el != none and el.func() == eq {
    // Override equation references.
    numbering(
      el.numbering,
      ..counter(eq).at(el.location())
    )
  } else {
    // Other references as usual.
    it
  }
}

#pagebreak()

#include "exercises/ccs-vp.typ"
#pagebreak()
#include "exercises/mu-calculus-operators.typ"

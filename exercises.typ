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
#pagebreak()

#include "exercises/ccs-vp.typ"
#pagebreak()
#include "exercises/mu-calculus-operators.typ"

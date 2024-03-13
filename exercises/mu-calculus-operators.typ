#import "/common.typ": *

#show heading.where(level: 3): it => {
  v(.5em)
  set text(size: .9em)
  box(inset: 1em, stroke: .5pt, it)
  v(.5em)
}
#show heading.where(level: 4): it => {
  $bullet space it$
  parbreak()
  v(.5em)
}

= Exercise G
// #include "invariant.typ"
// #pagebreak()

#include "until.typ"

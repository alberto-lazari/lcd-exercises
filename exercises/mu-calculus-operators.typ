#import "/common.typ": *

= Exercise G
== Inv
#box(stroke: 0.5pt, inset: 0.75em, width: 100%, [
  #lesson(13, page: 8)

  #underline(smallcaps("Exercise")) : #h(.2em) We defined

  #[
    #set par(first-line-indent: 5em)
    $inv()                &=    new() (phi and boxed() X) \ \
      "let" #h(6.8em) s1  &= [| new() (phi and boxed() X) |]$
  ]

  The set of processes for which $phi$ is invariant can be directly expressed as \
  $#h(13em) s2 = { P | forall P reaches P' quad P' satisfies phi }$

  Are they really the same?
  #[
    #set par(first-line-indent: 13em)
    $s1 =^? s2$

    $-> s1 subset.eq s2 : quad "show that if" P to(n) P' "then" P' satisfies phi \
      #h(6em) "by induction on the number" n "of"$

    $-> s1 subset.eq s2 : quad s2 "is a fixpoint of" f_phi$
  ]
])

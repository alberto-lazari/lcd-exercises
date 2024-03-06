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
== Invariant
#box(stroke: 0.5pt, inset: 0.75em, width: 100%, [
  #lesson(13, page: 8)

  #underline(smallcaps("Exercise")) : #h(.2em) We defined

  #[
    #set par(first-line-indent: 5em, hanging-indent: 5em)
    $"Inv"(phi)         &=          new(X) (phi and boxed(Act) X) \ \
    "let" #h(6.8em) s1  &= semantic(new(X) (phi and boxed(Act) X))$
  ]

  The set of processes for which $phi$ is invariant can be directly expressed as

  $#h(13em) s2 = { P | forall P reaches P' quad P' satisfies phi }$

  Are they really the same?
  #[
    #set par(first-line-indent: 13em, hanging-indent: 13em)
    $s1 =^? s2$

    $-> s1 subset.eq s2 : quad "show that if" P to(n) P' "then" P' satisfies phi$ \
    $#h(6.3em) "by induction on the number" n "of steps"$

    $-> s2 subset.eq s1 : quad s2 "is a fixpoint of" f_phi$
  ]
])

Let's introduce some definitions first:
- Let $f_phi (S) = semantic(phi and boxed(Act) X)_(eta [X -> S])$

- Let $eta(phi) = { P | P satisfies phi }$

- Let $boxed(Act) S = { P | forall alpha in Act st P to(alpha) P' ==> P' in S }$

- $s1 = semantic(new(X) (phi and boxed(Act) X)) = "Fix"(f_phi)$

=== $s1 subset.eq s2$
By induction on the number of steps $n$:
$ P in s1 ==> P to(n) P' ==> P' in s1 $

#line(length: 100%)
==== $n = 0$
$P to(0) P' ==> P' = P$

$P in s1 ==> P' in s1$

==== $n = k + 1$
*Assuming:*
#pi-enum[
+ $P in s1$

+ $P to(k + 1) P'' ==> P' to(1) P''$
]
By inductive hypothesis, $P in s1 ==> P to(k) P' ==> P' in s1$

*To prove:* $P' in s1 ==> P' to(1) P'' ==> P'' in s1$

$P' in s1 ==> P' in f_phi (s1) = semantic(phi and boxed(Act) X)_(eta [x -> s1]) = eta(phi) sect boxed(Act) s1 subset.eq boxed(Act) s1$ \
$==> P' in boxed(Act) s1$

$boxed(Act) s1 = { Q | forall alpha in Act st Q to(alpha) Q' ==> Q' in s1 }$

$P' to(1) P'' ==> exists alpha in Act st P' to(alpha) P''$

$
  cases(reverse: #true,
    P' in boxed(Act) s1,
    exists alpha in Act st P' to(alpha) P'',
  ) ==> P'' in s1
$

#line(length: 100%)

$P' in s1 ==> P' in eta(phi) sect boxed(Act) s1 subset.eq eta(phi)$ \
$==> P' satisfies phi$

$
  forall n st P to(n) P' ==> P' satisfies phi quad = quad forall P reaches P' st P' satisfies phi \
  ==> P in s2
$

hence the proved result
$ P in s1 ==> P to(n) P' ==> P' in s1 $
is equivalent to

$
  P in s1 ==> P in s2 \
  ==> s1 subset.eq s2
$
#align(right, $qed$)


=== $s2 subset.eq s1$
$s2 "is a fixpoint of" f_phi:$

$f_phi (s2) = semantic(phi and boxed(Act) X)_(eta [X -> s2]) = eta(phi) sect boxed(Act) s2$

$boxed(Act) s2 = { P | forall alpha in Act st P to(alpha) P' ==> P' in s2 }$

// TODO
...

$==> f_phi (s2) = s2$

$s2 "fixpoint of" f_phi ==> s2 subset.eq "Fix"(f_phi) = s1 ==> s2 subset.eq s1$
#align(right, $qed$)


#pagebreak()


== Until (strong)

// See CTr(P) (completed traces) lesson 6, page 4
- Let $complete(P) : "Proc" -> 2^"CC" quad$ be the set of all the complete computations of $P$ s.t. \
  $complete(P) = { c in "CC" | P = c_1 }$,
  where $"CC" = { mat(P_1, P_2, ..., P_n) | P_1 --> P_2 --> ... --> P_n stuck }
    subset.eq  display(union.big_(n in NN_0)) "Proc"^n$
  
- Let $"Even"(psi) = mu X st (psi or (diamond(Act) upright("T") and boxed(Act) X))$
- Let $semantic(#h(0em) "Even"(psi)) = { P | forall c in complete(P) st exists i in NN_0 st c_i satisfies phi }$

#let until-definition = $mu X st (psi or (phi and diamond(Act) upright("T") and boxed(Act) X))$
#box(stroke: 0.5pt, inset: 0.75em, width: 100%)[
  #underline(smallcaps("Exercise")) : #h(.2em) Let's define

  #par(first-line-indent: 5em)[
    $"Until"(phi, psi) = phi until psi = #until-definition$

    $"let" #h(2.6em) s1 = semantic(#until-definition)$
  ]

  The set of processes for which $phi until psi$ is satisfied can be directly expressed as

  #par(first-line-indent: 8.75em)[
    $s2 = { P |
      forall c in complete(P) st exists i in NN_0 st (
        c_i satisfies psi and
        forall j < i st c_j satisfies phi
      )
    }$
  ]

  Are they really the same?
  #par(first-line-indent: 8.75em)[
    $s1 =^? s2$

    $-> s1 subset.eq s2 : quad s2 "is a fixpoint of" f_phi$

    $-> s2 subset.eq s1 : quad$by induction on the number $n$ of steps
  ]
]

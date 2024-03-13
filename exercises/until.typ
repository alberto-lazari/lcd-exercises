#import "/common.typ": *

#let until-var = $psi or (phi and diamond(Act) upright("T") and boxed(Act) X)$
#let until-definition = $mu X st #until-var$
#let until-set = ${ P |
  forall c in complete(P) st exists i in NN_0 st (
    c_i satisfies psi and
    forall j < i st c_j satisfies phi
  )
}$
#let ups = $upsilon(phi, psi)$
#let func = $f_(ups)$
== Until (strong)

- Let $eta(phi) = semeta(phi) = semantic(phi) = { P | P satisfies phi }$

- Let $boxed(Act) S = { P | forall alpha in Act st P to(alpha) P' ==> P' in S }$

- Let $ups = #until-var$

#lesson(13, page: 6)
- Let $func(S) = semxs(ups)$

- Let $"CC" = { mat(P_1, P_2, ..., P_n) | P_1 --> P_2 --> ... --> P_n stuck }
    subset.eq  display(union.big_(i in NN_0)) "Proc"^i$ \
  be the set of all the complete computations of any process

#comment[See $"CTr"(P)$ (completed traces): lesson 6 -- page 4]
- Let $"CCmp" : "Proc" -> 2^"CC" space$ s.t. \
  $complete(P) = { c in "CC" | P = c_1 } space$ is the set of all the complete computations of $P$

#box(stroke: 0.5pt, inset: 0.75em, width: 100%)[
  #underline(smallcaps("Exercise")) : #h(.2em) Let's define

  #par(first-line-indent: 5em)[
    $"Until"(phi, psi) = phi until psi = mu X st ups = #until-definition$

    $"let" #h(2.6em) s1 = semantic(mu X st ups)$
  ]

  The set of processes for which $phi until psi$ is satisfied can be directly expressed as

  #par(first-line-indent: 8.75em)[
    $s2 = #until-set$
  ]

  Are they really the same?
  #par(first-line-indent: 8.75em)[
    $s1 =^? s2$

    $-> s1 subset.eq s2 : quad s2 "is a fixpoint of" func$

    $-> s2 subset.eq s1 : quad$by induction on the number $n$ of steps
  ]
]

$s1 = semeta(mu X st ups) = "fix"(func)$

=== $s1 subset.eq s2$
*To prove:* #h(.5em) $semeta(mu X st ups) subset.eq #until-set$

$s1 = "fix"(func)$

#comment[$s1$ is the lfp $==>$ it is a subset of every fixed point of $func$]
$==> forall S subset.eq "Proc" st ( func(S) = S ==> s1 subset.eq S )$

In particular, this holds for $s2$:
#math.equation(block: true, numbering: "(1)",
  $func(s2) = s2 ==> s1 subset.eq s2$
) <lfp>

#comment[Remember, $func(S) = semxs(#until-var)$]

$s2$ is a fixed point of $func$, in fact:

$s2 &= #until-set =$

#comment[$P satisfies psi$, otherwise it has to be that $P satisfies phi$ and it does at least a step]
#comment[All the complete computations of the next steps respect the same property]
$= { P | & P satisfies psi or (
  P satisfies phi and
  exists P' in "Proc" st P --> P' and
  forall P --> P' st \
    & forall c in complete(P') st exists i in NN_0 st (
      c_i satisfies psi and
      forall j < i st c_j satisfies phi
    )
)}$

Note that $space forall c in complete(P') st exists i in NN_0 st (
  c_i satisfies psi and
  forall j < i st c_j satisfies phi
)
space <==> space
P' in s2$

$==>
s2 &= { P | P satisfies psi or (
  P satisfies phi and
  exists P' in "Proc" st P --> P' and
  forall P --> P' st P' in s2
)} = \

&= semeta(psi) union (
  semeta(phi) sect
  semeta(diamond(Act) T) sect
  semxs2(boxed(Act) X)
) = \

&= semxs2(psi or (phi and diamond(Act) T and boxed(Act) X)) = func(s2)
$

Which is equivalent to
#math.equation(block: true, numbering: "(1)",
  $func(s2) = s2$
) <fixpoint>

From @lfp:
#math.equation(block: true)[
  @fixpoint $==> s1 subset.eq s2$
]

#align(right, $qed$)
#line(length: 100%)


=== $s1 supset.eq s2$
*To prove:* #h(.5em) $semeta(mu X st ups) supset.eq #until-set$

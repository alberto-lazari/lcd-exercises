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

#let until-var = $psi or (phi and diamond(Act) upright("T") and boxed(Act) X)$
#let until-definition = $mu X st #until-var$
#let until-set = ${ P |
  forall c in complete(P) st exists i in NN st (
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
    subset.eq  display(union.big_(i in NN)) Proc^i$ \
  be the set of all the complete computations of any process

#comment[See $"CTr"(P)$ (completed traces): lesson 6 -- page 4]
- Let $"CCmp" : Proc -> 2^"CC" space$ s.t. \
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

    $-> s2 subset.eq s1 : quad$by induction on $n$ in $f_ups^n (empty)$
  ]
]

#lesson(13, page: 6)
By the definition of the semantics of $semeta(mu X. phi)$
#numeq($s1 = semeta(mu X st ups) = "fix"(func)$) <mu-sem>

=== $s1 subset.eq s2$
*To prove:* #h(.5em) $semeta(mu X st ups) subset.eq #until-set$

#comment[$s1$ is the lfp $==>$ it is a subset of every fixed point of $func$]
@mu-sem $space ==> space
forall S subset.eq Proc st ( func(S) = S quad ==> quad s1 subset.eq S )$

In particular, this holds for $s2$:
#numeq($func(s2) = s2 quad ==> quad s1 subset.eq s2$) <lfp>

#comment[Remember, $func(S) = semxs(#until-var)$]

$s2$ is a fixed point of $func$, in fact:

$s2 = #until-set =$

#par(first-line-indent: 1.40em)[
  #comment[$P satisfies psi$, otherwise it has to be that $P satisfies phi$ and it does at least a step]
  #comment[All the complete computations of the next steps respect the same property]
  $= { P | & P satisfies psi or (
    P satisfies phi and
    exists P' in Proc st P --> P' and
    forall P --> P' st \
      & forall c in complete(P') st exists i in NN st (
        c_i satisfies psi and
        forall j < i st c_j satisfies phi
      )
  )}$
]

Note that
$ forall c in complete(P') st exists i in NN st (
  c_i satisfies psi and
  forall j < i st c_j satisfies phi
)
quad <==> quad
P' in s2 $

$==>
s2 &= { P | P satisfies psi or (
  P satisfies phi and
  exists P' in Proc st P --> P' and
  forall P --> P' st P' in s2
)} = \

&= semeta(psi) union (
  semeta(phi) sect
  semeta(diamond(Act) upright("T")) sect
  semxs2(boxed(Act) X)
) = \

&= semxs2(psi or (phi and diamond(Act) upright("T") and boxed(Act) X)) = func(s2)
$

Which is equivalent to
#numeq($func(s2) = s2$) <fixpoint>

From @lfp:
#math.equation(block: true)[
  @fixpoint $quad ==> quad s1 subset.eq s2$
]

#align(right, $qed$)
#line(length: 100%)


=== $s1 supset.eq s2$
*To prove:* #h(.5em) $semeta(mu X st ups) supset.eq #until-set$

#lesson(13, page: 6)
For finite state processes it holds that
#numeq($forall n in N st f_ups^n (empty) subset.eq "fix"(func) = s1$) <func-fix>

Let $R_n = { P | forall c in complete(P) st
  exists i lt.eq.slant n st (
    c_i satisfies psi and
    forall j < i st c_j satisfies phi
  )
}$ s.t.
$space display(lim_(n -> infinity)) R_n = s2$

Assuming
#numeq($forall n in NN st R_n subset.eq f_ups^n (empty)$) <R-fix>

By @func-fix and @R-fix
$ space forall n in NN st R_n subset.eq f_ups^n (empty) subset.eq s1
quad ==> quad

forall n in NN st R_n subset.eq s1
quad ==> quad
s2 subset.eq s1
$

Let's prove @R-fix by induction on $n in NN$:

// Break the page
#v(3em)

==== Case $n = 1$
Let's prove
$space R_1 subset.eq f_ups (empty)$

$R_1 &= { P | forall c in complete(P) st
  exists i lt.eq.slant 1 st (
    c_i satisfies psi and
    forall j < i st c_j satisfies phi
  )
} = \

&= { P | forall c in complete(P) st
  c_1 satisfies psi and
  forall j < 1 st c_j satisfies phi
} = \

&= { P | forall c in complete(P) st c_1 satisfies psi } =
{ P | P satisfies psi } =
semeta(psi)
$

$f_ups (empty) &= semantic(ups)_(eta [X -> empty]) =
semantic(#until-var)_(eta [X -> empty]) = \

&= semeta(psi) union semantic(
  phi and diamond(Act) upright("T") and boxed(Act) X
)_(eta [X -> empty])
space supset.eq space
semeta(psi) = R_1
$

==== Case $n ==> n + 1$
Assuming
#pi-enum[
+ $R_n subset.eq f_ups^n (empty)$
]

Let's prove
$space R_(n + 1) subset.eq f_ups^(n + 1) (empty)$

$R_(n + 1) &= { P | & forall c in complete(P) st
  exists i lt.eq.slant n + 1 st (
    c_i satisfies psi and
    forall j < i st c_j satisfies phi
  )
} = \

&= { P | & P satisfies psi or (
  P satisfies phi and
  exists P' in Proc st P --> P' and
  forall P --> P' st
    forall c in complete(P') st exists i lt.eq.slant n st ( \
      && c_i satisfies psi and
      forall j < i st c_j satisfies phi
    )
)}
$

Note that
$ forall c in complete(P') st exists i lt.eq.slant n st (
  c_i satisfies psi and
  forall j < i st c_j satisfies phi
)
quad <==> quad
P' in R_n $

$==> R_(n + 1) &= { P | P satisfies psi or (
  P satisfies phi and
  exists P' in Proc st P --> P' and
  forall P --> P' st P' in R_n
)} = \

&= semeta(psi) union (
  semeta(phi) sect
  semeta(diamond(Act) upright("T")) sect
  semantic(boxed(Act) X)_(eta [X -> R_n])
) = \

&= semantic(psi or (phi and diamond(Act) upright("T") and boxed(Act) X))_(eta [X -> R_n]) = f_ups (R_n)
$

Because $f_ups$ is monotone, by $pi_1$ (inductive hypothesis)
$ R_n subset.eq f_ups^n (empty)
space ==> space
f_ups (R_n) subset.eq f_ups (f_ups^n (empty)) = f_ups^(n + 1) (empty)
$

$ ==> R_(n + 1) subset.eq f_ups^(n + 1) (empty) $

#align(right, $qed$)

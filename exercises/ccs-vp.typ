#import "/common.typ": *

#show heading.where(level: 2): it => {
  v(0.5em)
  set text(size: 13pt)
  box(inset: 1em, stroke: 0.5pt, it.body)
  v(0.5pt)
}

= Exercise C
#box(stroke: 0.5pt, inset: 0.75em, width: 100%, [
  #lesson(5, page: 7)

  #underline[*Theorem*] : $space.quad$ Let $ccs() : "CCS-VP" to() "CCS"$ as above.

  Then for all CCS-VP programs $P$
  #align(center, box[
    #set align(left)
    #grid(
    columns: (2em, auto, auto, auto),
    gutter: (1.5em, 3em),
    [(i)],
    [$P to(alpha) P'$],
    [$==>$],
    [$ccs(P) to(ahat) ccs(P')$],

    [(ii)],
    [$ccs(P) to(ahat) Q$],
    [$==>$],
    [$exists space P' st P to(alpha) P' and ccs(P') = Q$],
  )])

  where
  $
    ahat = cases(
      an  &"if" alpha = a(n),
      oan &"if" alpha = oa(n),
      tau &"if" alpha = tau
    )
  $
])

_*Proof by structural induction on $P$*_

Let's first introduce the rule "ind-(i)", which is derived by the consequence (i) of the inductive hypothesis of the theorem.
#prooftree(
    axiom($P to(alpha) P'$),
  rule(label: "ind-(i)", $ccs(P) to(ahat) ccs(P')$)
)

#let P    = $a(x). P$
#let P1   = $P{sub(n, x)}$
#let ccsP = $display(sum_(i in NN)) a_i. ccs(#P1)$
#let Q    = $ccs(#P1)$
== Case #P
#inum[
+ Assuming:
  #pi-enum[
  + $#P to(a(n)) #P1$

  + $ccs(#P) = ccsP$
  ]
  $==> ccs(#P) to(an) ccs(#P1)$, because: #prooftree(
    rule(label: "ACT", n: 0, $an. ccs(#P1) to(an) ccs(#P1)$),
    rule(
      label: (left: "SUM", right: $n in NN$),
      $ccsP to(an) ccs(#P1)$
    ),
  )

+ Assuming:
  #pi-enum[
  + $ccs(#P) to(an) #Q$

  + Let $Q = #Q$
  ]
  Let $P' = #P1$

  $==> ccs(P') = Q$ by $pi_2$ and $#P to(a(n)) P'$, because:
  #prooftree(
    rule(label: (left: "input", right: $n in NN$), n: 0, $#P to(a(n)) #P1$),
  )
]

#let P    = $oa(e). P$
#let P1   = $P$
#let ccsP = $oan. ccs(#P1)$
#let Q    = $ccs(#P1)$
== Case #P
#inum[
+ Assuming:
  #pi-enum[
  + $e$ evaluates to $n$

  + $#P to(oa(n)) #P1$

  + $ccs(#P) = ccsP$
  ]
  $==> ccs(#P) to(oan) ccs(#P1)$, because:
  #prooftree(
    rule(label: "ACT", n: 0, $ccsP to(oan) ccs(#P1)$),
  )

+ Assuming:
  #pi-enum[
  + $e$ evaluates to $n$

  + $ccs(#P) to(oan) #Q$

  + Let $Q = #Q$
  ]
  Let $P' = #P1$

  $==> ccs(P') = Q$ by $pi_2$ and $#P to(oa(n)) P'$, because:
  #prooftree(
    rule(
      label: (left: "output", right: $pi_1$), n: 0,
      $#P to(oa(n)) #P1$
    ),
  )
]

#let P    = $tau. P$
#let P1   = $P$
#let ccsP = $tau. ccs(#P1)$
#let Q    = $ccs(#P1)$
== Case #P
#inum[
+ Assuming:
  #pi-enum[
  + $#P to(tau) #P1$

  + $ccs(#P) = ccsP$
  ]
  $==> ccs(#P) to(tau) ccs(#P1)$, because:
  #prooftree(
    rule(label: "ACT", n: 0, $ccsP to(tau) ccs(#P1)$),
  )

+ Assuming:
  #pi-enum[
  + $ccs(#P) to(tau) #Q$

  + Let $Q = #Q$
  ]
  Let $P' = #P1$

  $==> ccs(P') = Q$ by $pi_2$ and $#P to(tau) P'$, because:
  #prooftree(
    rule(label: "silent", n: 0, $#P to(tau) #P1$),
  )
]

#let P    = $display(sum_(i in I)) space.hair P_i$
#let P1   = $P_j^'$
#let ccsP = $display(sum_(i in I)) space.hair ccs(P_i)$
#let Q    = $ccs(#P1)$
== Case #P
#inum[
+ Assuming:
  #pi-enum[
  + $#P to(alpha) #P1$

  + $ccs(#P) = ccsP$
  ]
  $==> ccs(#P) to(ahat) ccs(#P1)$, because:
  #prooftree(
    axiom(label: $pi_3$, $P_j to(alpha) #P1$),
    rule(label: "ind-(i)", $ccs(P_j) to(ahat) ccs(#P1)$),
    rule(label: (left: "SUM", right: $j in I$), $ccsP to(ahat) ccs(#P1)$),
  )

  Where $pi_3$ is deduced from the fact that the assumption $pi_1$ can only be derived by the following tree:
  #prooftree(
    axiom($P_j to(alpha) #P1$),
    rule(label: (left: "SUM", right: $j in I$), $#P to(alpha) #P1$),
  )

+ Assuming:
  #pi-enum[
  + $ccs(#P) to(ahat) #Q$

  + Let $Q = #Q$

  + $ccs(#P) = ccsP$
  ]
  $==> ccs(P_j) to(ahat) ccs(#P1)$ is derivable, because $pi_1$ can only be derived by the following tree:
  #prooftree(
    axiom($ccs(P_j) to(ahat) ccs(#P1)$),
    rule(label: (left: "SUM", right: $j in I$), $ccsP to(ahat) ccs(#P1)$),
  )

  Then, by inductive hypothesis, $exists Pind st P_j to(alpha) Pind and Pind = ccs(P_j^')$

  - Let $Pind = #P1 st P_j to(alpha) #P1$
  - Let $P' = #P1$

  $==> ccs(P') = Q "by" pi_2 "and" #P to(alpha) P'$, because:
  #prooftree(
    axiom($P_j to(alpha) #P1$),
    rule(label: (left: "SUM", right: $j in I$), $#P to(alpha) #P1$),
  )
]


#let P    = $P_1 | P_2$
#let ccsP = $ccs(P_1) | ccs(P_2)$
== Case #P
For this case there are more sub-cases to consider.

#let P1    = $P_1^' | P_2$
#let ccsP1 = $ccs(P_1^') | ccs(P_2)$
#let Q     = $ccs(#P1)$
=== Sub-case $#P to(alpha) #P1$
#inum[
+ Assuming:
  #pi-enum[
  + $#P to(alpha) #P1$

  + $ccs(#P) = ccsP$

  + $ccs(#P1) = ccsP1$
  ]
  $==> ccs(#P) to(ahat) ccs(#P1)$, because:
  #prooftree(
    axiom(label: $pi_4$, $P_1 to(alpha) P_1^'$),
    rule(label: "ind-(i)", $ccs(P_1) to(ahat) ccs(P_1^')$),
    rule(label: "parallel", $ccsP to(ahat) ccsP1$),
  )

  Where $pi_4$ is derivable, because $pi_1$ can only be derived by the following tree:
  #prooftree(
    axiom($P_1 to(alpha) P_1^'$),
    rule(label: "parallel", $#P to(alpha) #P1$),
  )

+ Assuming:
  #pi-enum[
  + $ccs(#P) to(ahat) #Q$

  + Let $Q = #Q$

  + $ccs(#P) = ccsP$

  + $ccs(#P1) = ccsP1$
  ]
  $==> ccs(P_1) to(ahat) ccs(P_1^')$ is derivable, because $pi_1$ can only be derived by the following tree:
  #prooftree(
    axiom($ccs(P_1) to(ahat) ccs(P_1^')$),
    rule(label: "parallel", $ccsP to(ahat) ccsP1$),
  )

  Then, by inductive hypothesis, $exists Pind st P_1 to(alpha) Pind and ccs(Pind) = ccs(P_1^')$

  - Let $Pind = P_1^' st P_1 to(alpha) P_1^'$
  - Let $P' = #P1$

  $==> ccs(P') = Q "by" pi_2 "and" #P to(alpha) P'$, because:
  #prooftree(
    axiom($P_1 to(alpha) P_1^'$),
    rule(label: "parallel", $#P to(alpha) #P1$),
  )
]

#let P1    = $P_1 | P_2^'$
#let ccsP1 = $ccs(P_1) | ccs(P_2^')$
#let Q     = $ccs(#P1)$
=== Sub-case $#P to(alpha) #P1$
#inum[
+ Assuming:
  #pi-enum[
  + $#P to(alpha) #P1$

  + $ccs(#P) = ccsP$

  + $ccs(#P1) = ccsP1$
  ]
  $==> ccs(#P) to(ahat) ccs(#P1)$, because:
  #prooftree(
    axiom(label: $pi_4$, $P_2 to(alpha) P_2^'$),
    rule(label: "ind-(i)", $ccs(P_2) to(ahat) ccs(P_2^')$),
    rule(label: "parallel", $ccsP to(ahat) ccsP1$),
  )

  Where $pi_4$ is derivable, because $pi_1$ can only be derived by the following tree:
  #prooftree(
    axiom($P_2 to(alpha) P_2^'$),
    rule(label: "parallel", $#P to(alpha) #P1$),
  )

+ Assuming:
  #pi-enum[
  + $ccs(#P) to(ahat) #Q$

  + Let $Q = #Q$

  + $ccs(#P) = ccsP$

  + $ccs(#P1) = ccsP1$
  ]
  $==> ccs(P_2) to(ahat) ccs(P_2^')$ is derivable, because $pi_1$ can only be derived by the following tree:
  #prooftree(
    axiom($ccs(P_2) to(ahat) ccs(P_2^')$),
    rule(label: "parallel", $ccsP to(ahat) ccsP1$),
  )

  Then, by inductive hypothesis, $exists Pind st P_2 to(alpha) Pind and ccs(Pind) = ccs(P_2^')$

  - Let $Pind = P_2^' st P_2 to(alpha) P_2^'$
  - Let $P' = #P1$

  $==> ccs(P') = Q "by" pi_2 "and" #P to(alpha) P'$, because:
  #prooftree(
    axiom($P_2 to(alpha) P_2^'$),
    rule(label: "parallel", $#P to(alpha) #P1$),
  )
]

#let P1    = $P_1^' | P_2^'$
#let ccsP1 = $ccs(P_1^') | ccs(P_2^')$
#let Q     = $ccs(#P1)$
=== Sub-case $#P to(tau) #P1$
#inum[
+ Assuming:
  #pi-enum[
  + $#P to(tau) #P1$

  + $ccs(#P) = ccsP$

  + $ccs(#P1) = ccsP1$
  ]
  $==> ccs(#P) to(tau) ccs(#P1)$, because:
  // TODO: find out if it's ok to leave the in + out + subst part implicit
  #prooftree(
        axiom(label: $pi_4$, $P_1 to(alpha) P_1^'$),
      rule(label: "ind-(i)", $ccs(P_1) to(ahat) ccs(P_1^')$),
        axiom(label: $pi_5$, $P_2 to(out(alpha)) P_2^'$),
      rule(label: "ind-(i)", $ccs(P_2) to(oahat) ccs(P_2^')$),
    rule(label: "parallel", n: 2, $ccsP to(tau) ccsP1$),
  )

  Where $pi_4$ and $pi_5$ are derivable, because $pi_1$ can only be derived by the following tree:
  #prooftree(
      axiom(label: $pi_4$, $P_1 to(alpha) P_1^'$),
      axiom(label: $pi_5$, $P_2 to(out(alpha)) P_2^'$),
    rule(label: "parallel", n: 2, $#P to(tau) #P1$),
  )

+ Assuming:
  #pi-enum[
  + $ccs(#P) to(tau) #Q$

  + Let $Q = #Q$

  + $ccs(#P) = ccsP$

  + $ccs(#P1) = ccsP1$
  ]
  $==> ccs(P_1) to(tau) ccs(P_1^') "and" ccs(P_2) to(tau) ccs(P_2^')$ are derivable, because $pi_1$ can only be derived by the following tree:
  #prooftree(
      axiom($ccs(P_1) to(ahat) ccs(P_1^')$),
      axiom($ccs(P_2) to(oahat) ccs(P_2^')$),
    rule(label: "parallel", n: 2, $ccsP to(tau) ccsP1$),
  )

  Then, by inductive hypothesis follows:
  #set enum(numbering: "1)")
  + $exists Pind_1 st P_1 to(alpha) Pind_1 and ccs(Pind_1) = ccs(P_1^')$

  + $exists Pind_2 st P_2 to(out(alpha)) Pind_2 and ccs(Pind_2) = ccs(P_2^')$

  Using 1) and 2):
  - Let $Pind_1 = P_1^' st P_1 to(alpha) P_1^'$

  - Let $Pind_2 = P_2^' st P_2 to(out(alpha)) P_2^'$

  - Let $P' = #P1$

  $==> ccs(P') = Q "by" pi_2 "and" #P to(alpha) P'$, because:
  #prooftree(
      axiom($P_1 to(alpha) P_1^'$),
      axiom($P_2 to(out(alpha)) P_2^'$),
    rule(label: "parallel", n: 2, $#P to(tau) #P1$),
  )
]


#let P     = $P without L$
#let P1    = $P' without L$
#let ccsP  = $ccs(P) without L'$
#let ccsP1 = $ccs(P') without L'$
#let Q     = $ccs(#P1)$
== Case #P
#inum[
+ Assuming:
  #pi-enum[
  + $#P to(alpha) #P1$

  + $ccs(#P) = ccsP$, where $L' = { an | a in L, n in NN }$

  + $ccs(#P1) = ccsP1$
  ]
  $==> ccs(#P) to(ahat) ccs(#P1)$, because:
  #prooftree(
    axiom(label: $pi_4$, $P to(alpha) P'$),
    rule(label: "ind-(i)", $ccs(P) to(ahat) ccs(P')$),
    rule(label: (left: "RES", right: $ahat, oahat in.not L'$), $ccsP to(ahat) ccsP1$),
  )

  Where $pi_4$ is derivable and $alpha, out(alpha) in.not L$, because $pi_1$ can only be derived by the following tree:
  #prooftree(
    axiom($P to(alpha) P'$),
    rule(label: (left: "RES", right: $alpha, out(alpha) in.not L$), $#P to(alpha) #P1$),
  )

  Note that $ahat, oahat in.not L'$ by construction of $L'$, because $alpha, out(alpha) in.not L$.

+ Assuming:
  #pi-enum[
  + $ccs(#P) to(ahat) #Q$

  + Let $Q = #Q$

  + $ccs(#P) = ccsP$, where $L' = { an | a in L, n in NN }$

  + $ccs(#P1) = ccsP1$
  ]
  $==> ccs(P) to(ahat) ccs(P')$ is derivable and $ahat, oahat in.not L'$, because $pi_1$ can only be derived by the following tree:
  #prooftree(
    axiom($ccs(P) to(ahat) ccs(P')$),
    rule(label: (left: "RES", right: $ahat, oahat in.not L'$), $ccsP to(ahat) ccsP1$),
  )
  Note that $alpha, out(alpha) in.not L$ by construction of $L'$, because $ahat, oahat in.not L'$.

  Then, by inductive hypothesis, $exists Pind st P to(alpha) Pind and ccs(Pind) = ccs(P')$

  - Let $Pind = P' st P to(alpha) P'$
  - Let $P_("th")^' = #P1$

  $==> ccs(P_("th")^') = Q "by" pi_2 "and" #P to(alpha) P_("th")^'$, because:
  #prooftree(
    axiom($P to(alpha) P'$),
    rule(label: (left: "RES", right: $alpha, out(alpha) in.not L$), $#P to(alpha) #P1$),
  )
]


#let P     = $P red(f)$
#let P1    = $P' red(f)$
#let ccsP  = $ccs(P) red(f')$
#let ccsP1 = $ccs(P') red(f')$
#let Q     = $ccs(P' red(f))$
== Case #P
#inum[
+ Assuming:
  #pi-enum[
  + $#P to(f(alpha)) #P1$

  + $ccs(#P) = ccsP$, where $f' = lambda an. f(a)_n, n in NN$

  + $ccs(#P1) = ccsP1$
  ]
  // TODO: find out if this is safe to assume
  For simplicity, let's assume that $f(a(n)) = f(a)$.
  This allows for a more concise definition of $f'$:
  $ f' = lambda ahat. hat(f(alpha)) $

  $==> ccs(#P) to(hat(f(alpha))) ccs(#P1)$, because:
  #prooftree(
    axiom(label: $pi_4$, $P to(alpha) P'$),
    rule(label: "ind-(i)", $ccs(P) to(ahat) ccs(P')$),
    rule(label: "Redirection", $ccsP to(f'(ahat)) ccsP1$),
  )

  Where $pi_4$ is derivable, because $pi_1$ can only be derived by the following tree:
  #prooftree(
    axiom($P to(alpha) P'$),
    rule(label: "Redirection", $#P to(f(alpha)) #P1$),
  )

+ Assuming:
  #pi-enum[
  + $ccs(#P) to(hat(f(alpha))) #Q$

  + Let $Q = #Q$

  + $ccs(#P) = ccsP$, where $f' = lambda an. f(a)_n, n in NN$

  + $ccs(#P1) = ccsP1$
  ]
  // TODO: find out if this is safe to assume
  For simplicity, let's assume that $f(a(n)) = f(a)$.
  This allows for a more concise definition of $f'$:
  $ f' = lambda ahat. hat(f(alpha)) $

  $==> ccs(P) to(ahat) ccs(P')$ is derivable, because $pi_1$ can only be derived by the following tree:
  #prooftree(
    axiom($ccs(P) to(ahat) ccs(P')$),
    rule(label: "Redirection", $ccsP to(f'(ahat)) ccsP1$),
  )
  Then, by inductive hypothesis, $exists Pind st P to(alpha) Pind and ccs(Pind) = ccs(P')$

  - Let $Pind = P' st P to(alpha) P'$
  - Let $P_("th")^' = #P1$

  $==> ccs(P_("th")^') = Q "by" pi_2 "and" #P to(alpha) P_("th")^'$, because:
  #prooftree(
    axiom($P to(alpha) P'$),
    rule(label: "Redirection", $#P to(f(alpha)) #P1$),
  )
]


#let P     = $"if" b "then" P$
== Case #P
// TODO: consider avoiding the false case
For this case there are two sub-cases to consider.

#let P1    = $P'$
#let ccsP  = $ccs(P)$
#let ccsP1 = $ccs(P')$
#let Q     = $ccsP1$
=== Sub-case $b = tt$
#inum[
+ Assuming:
  #pi-enum[
  + $b = tt$

  + $#P to(alpha) #P1$

  + $ccs(#P) = ccsP$
  ]
  $==> ccs(#P) to(ahat) ccs(#P1)$, because:
  #prooftree(
    axiom(label: $pi_4$, $P to(alpha) P'$),
    rule(label: "ind-(i)", $ccs(P) to(ahat) ccs(P')$),
  )

  Where $pi_4$ is derivable, because $pi_2$ can only be derived by the following tree:
  #prooftree(
    axiom($P to(alpha) P'$),
    rule(label: (left: "conditionals", right: $pi_1$), $#P to(alpha) #P1$),
  )

+ Assuming:
  #pi-enum[
  + $b = tt$

  + $ccs(#P) to(ahat) #Q$

  + Let $Q = #Q$

  + $ccs(#P) = ccsP$
  ]
  $==> ccs(P) to(ahat) ccs(P')$ is derivable, by $pi_2$ and $pi_4$.

  Then, by inductive hypothesis, $exists Pind st P to(alpha) Pind and ccs(Pind) = ccs(P')$

  - Let $Pind = P' st P to(alpha) P'$
  - Let $P_("th")^' = #P1$

  $==> ccs(P_("th")^') = Q "by" pi_3 "and" #P to(alpha) P_("th")^'$, because:
  #prooftree(
    axiom($P to(alpha) P'$),
    rule(label: (left: "conditionals", right: $pi_1$), $#P to(alpha) #P1$),
  )
]

#let P1    = $P'$
#let ccsP  = $deadlock$
=== Sub-case $b = ff$
Assuming:
#pi-enum[
+ $b = ff$

+ $ccs(#P) = ccsP$
]
$==> #P stuck$, because there's no rule to derive it and $ccs(#P) stuck$, by $pi_2$

$==>$ vacuously true

#let P    = $K(e1, ..., en)$
#let P1   = $P'$
#let ccsP = $K_(k1, ..., kn)$
#let Q    = $ccs(#P1)$
== Case #P
#inum[
+ Assuming:
  #pi-enum[
  + #ei evaluates to #ki, $forall i in {1..n}$

  + $K(x1, ..., xn) eq.def P$

  + $#P to(alpha) #P1$

  + $ccsP eq.def ccs(P{sub(k1, x1), ..., sub(kn, xn)})$

  + $ccs(#P) = ccsP$
  ]
  $==> ccs(#P) to(ahat) ccs(#P1)$, because:
  #prooftree(
    axiom(label: $pi_6$, $P{sub(k1, x1), ..., sub(kn, xn)} to(alpha) P'$),
    rule(label: "ind-(i)", $ccs(P{sub(k1, x1), ..., sub(kn, xn)}) to(ahat) ccs(P')$),
    rule(label: (left: "Constant", right: $pi_4$), $ccsP to(ahat) ccs(#P1)$),
  )

  Where $pi_6$ is derivable, because $pi_3$ can only be derived by the following tree:
  #prooftree(
    axiom($P{sub(k1, x1), ..., sub(kn, xn)} to(alpha) P'$),
    rule(label: (left: "constant", right: $pi_1, pi_2$), $#P to(alpha) #P1$),
  )

+ Assuming:
  #pi-enum[
  + #ei evaluates to #ki, $forall i in {1..n}$

  + $K(x1, ..., xn) eq.def P$

  + $ccs(#P) to(ahat) #Q$

  + $ccsP eq.def ccs(P{sub(k1, x1), ..., sub(kn, xn)})$

  + Let $Q = #Q$

  + $ccs(#P) = ccsP$
  ]
  $==> ccs(P{sub(k1, x1), ..., sub(kn, xn)}) to(ahat) ccs(P')$ is derivable, because $pi_3$ can only be derived by the following tree:
  #prooftree(
    axiom($ccs(P{sub(k1, x1), ..., sub(kn, xn)}) to(ahat) ccs(P')$),
    rule(label: (left: "Constant", right: $pi_4$), $ccsP to(ahat) ccs(#P1)$),
  )
  Then, by inductive hypothesis, $exists Pind st P{sub(k1, x1), ..., sub(kn, xn)} to(alpha) Pind and ccs(Pind) = ccs(P')$

  - Let $Pind = P' st P{sub(k1, x1), ..., sub(kn, xn)} to(alpha) P'$
  - Let $P_("th")^' = #P1$

  $==> ccs(P_("th")^') = Q "by" pi_5 "and" #P to(alpha) P_("th")^'$, because:
  #prooftree(
    axiom($P{sub(k1, x1), ..., sub(kn, xn)} to(alpha) P'$),
    rule(label: (left: "constant", right: $pi_1, pi_2$), $#P to(alpha) #P1$),
  )
]

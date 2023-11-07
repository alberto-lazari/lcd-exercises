#import "typst-prooftree/prooftree.typ": rule, axiom
#let prooftree(size: 1em, spacing: (vertical: 0.8em), ..rules) = {
  import "/typst-prooftree/prooftree.typ": *
  set text(size)
  box(width: 100%, inset: 0.5em, [$ #prooftree(label: (padding: 1em), spacing: spacing, ..rules) $])
}

// Comment-style lesson number annotation (# Lesson n – page m)
#let lesson(page: none, number) = {
  set text(gray)
  [\# Lesson #number -- page #page]
}

// CCS stuff
#let ccs(..elements) = {
  let exp = $space$

  if elements.pos().len() > 0 {
    exp = elements.pos().join[,]
  }

  $[| space.punct exp space.punct |]$
}
#let sub(val, var) = [$attach(#line(start: (0pt, 8pt), angle: -45deg, length: 10pt, stroke: 0.5pt), tl: val, br: var)$]
#let red(..elements) = {
  let exp = $space$

  if elements.pos().len() > 0 {
    exp = elements.pos().join[,]
  }

  $space.punct [ #h(0.2em) exp #h(0.2em) ]$
}
#let inum(list) = {
  set enum(numbering: "(i)")
  list
}
#let pi-enum(list) = {
  set enum(numbering: (..nums) => {
    let num = nums.pos()
                  .map(str)
                  .join()
    $pi_#num)$
  })
  list
}

#let to(..label) = {
  $limits(-->)^#label.pos().join[,]$
}
#let stuck = $--> #line(start: (-1.3em, 0.7em), angle: -60deg, length: 9pt, stroke: 0.5pt)$
#let hat(var) = $limits(var)^#text(size: 10pt, $caret$)$
#let out(var) = $overline(var)$
#let st = $"s.t."$
#let ahat = $hat(alpha)$
#let oahat = $hat(out(alpha))$
#let oa = $overline(a)$
#let an = $a_n$
#let oan = $oa_n$
#let x1 = $x_1$
#let xn = $x_n$
#let xi = $x_i$
#let k1 = $k_1$
#let kn = $k_n$
#let ki = $k_i$
#let e1 = $e_1$
#let en = $e_n$
#let ei = $e_i$
#let Pind = $P_("ind")^'$
#let tt = $sans("true")$
#let ff = $sans("false")$
#let deadlock = $Ø$


// Mu-calculus stuff
#let boxed(exp) = $[exp] space$
#let diamond(exp) = $angle.l exp angle.r space$
#let new(var) = $nu var. space$
#let reaches = $to(wide *)$
#let semantic(..elements) = ccs(..elements)

#let satisfies = $tack.r.double$
#let until = $space cal(U) space$

#let s1 = $S_1$
#let s2 = $S_2$
#let Act = $"Act"$

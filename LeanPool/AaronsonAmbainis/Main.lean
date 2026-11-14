/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import LeanPool.AaronsonAmbainis.Bridge.Capstone

/-!
# The Aaronson–Ambainis conjecture: the final theorems

The statements proved here are the propositions of `LeanPool/AaronsonAmbainis/Conjecture.lean`.
That file imports only Mathlib and uses no definition of this project, so it is enough to read
it in order to know what has been proved.

* `aaronson_ambainis` — the conjecture of Aaronson and Ambainis (Conjecture 6 of arXiv:0911.0996v3;
  Conjecture 1.7 of the journal version) with the exponent `7` in place of `O(1)`: a polynomial
  `p` of degree at most `d` with `0 ≤ p ≤ 1` on `{0,1}^N` and variance at least `ε > 0` has a
  variable of influence at least `(ε/d)^7`.
* `aaronson_ambainis_explicit` — the same with the lower bound
  `(8 √15 / (125 π^4)) ε^{5/2} / d^6`.
* `aaronson_ambainis_pm` — Theorem 1.1 of the upstream paper
  on the cube `{-1,1}^n` (the bit `true` is `1`, the bit
  `false` is `-1`), for polynomials with values in `[-1,1]`, with the lower bound
  `(√15 / (500 π^4)) ε^{5/2} / d^6`.
* `aaronson_ambainis_of_fbsDegreeBound` — the lower bound `(32 √15 / (125 π^4)) ε^{5/2} / d^6`,
  under the hypothesis `FbsDegreeBound`, which is Theorem 1.7 of Agarwal and Ben-David
  (arXiv:2410.19062) as printed.

The first three theorems have no hypothesis. The proofs are assembled in `Chain.lean` (the chain
of the links, from the determinant inequality to the main theorem on the cube) and in
`Bridge/Capstone.lean` (the passage from the definitions of the project to the statements of
`Conjecture.lean`).
-/

@[expose] public section

namespace AaronsonAmbainis

/-- **The Aaronson–Ambainis conjecture**, as printed, with the exponent `7` for `O(1)`. -/
theorem aaronson_ambainis : PrintedConjecture :=
  Bridge.printedConjecture

/-- The Aaronson–Ambainis conjecture with the explicit lower bound
`(8 √15 / (125 π^4)) ε^{5/2} / d^6`. -/
theorem aaronson_ambainis_explicit : ExplicitBound :=
  Bridge.explicitBound

/-- Theorem 1.1 of the upstream paper on the cube
`{-1,1}^n`, with the explicit lower bound `(√15 / (500 π^4)) ε^{5/2} / d^6`. -/
theorem aaronson_ambainis_pm : ExplicitBoundPM :=
  Bridge.explicitBoundPM

/-- The explicit lower bound `(32 √15 / (125 π^4)) ε^{5/2} / d^6`, from Theorem 1.7 of
arXiv:2410.19062, which is a hypothesis here. -/
theorem aaronson_ambainis_of_fbsDegreeBound : FbsDegreeBound → ExplicitBoundImproved :=
  Bridge.explicitBoundImproved_of_fbsDegreeBound

end AaronsonAmbainis

/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Aaronson–Ambainis conjecture: the statements, written with nothing but Mathlib

This file imports only Mathlib and uses no definition, instance or notation of this project, so
the meaning of the statements below depends on Mathlib alone: `MvPolynomial.eval`,
`MvPolynomial.totalDegree`, finite sums over `Fin N → Bool`, `Finset.filter`, `Function.update`,
`Real.pi`, `Real.sqrt`, real powers `x ^ (y : ℝ)`, the absolute value, and the field operations of
`ℝ`.

It contains statements only (`def … : Prop`); nothing is proved here. The theorems are in
`LeanPool/AaronsonAmbainis/Main.lean`. To know what has been proved it is enough to read this file.

The first definition, `PrintedConjecture`, is the conjecture as printed, in the normalisation of
Aaronson and Ambainis, with the number `7` for `O(1)`. `PrintedConjecture` is the statement of
the theorem `aaronson_ambainis` of `Main.lean`, so to check that the statement proved is the
conjecture, a reader needs to read only `PrintedConjecture`. Like `PrintedConjecture`,
`ExplicitBound` and `ExplicitBoundImproved` are stated on the cube `{0,1}^N` in the normalisation
of Aaronson and Ambainis; `FbsDegreeBound` is stated on the cube `{0,1}^n`. The last definition,
`ExplicitBoundPM`, is the main theorem (Theorem 1.1) of the upstream paper,
on the cube `{-1,1}^n`, in the form with a lower bound `ε`
for the variance; a reader who checks `PrintedConjecture` does not need `ExplicitBoundPM`.

## Encoding

A point of either cube is `X : Fin N → Bool`, and the bit `true` is the number `1`. On the cube
`{0,1}^N` the bit `false` is the number `0`; on the cube `{-1,1}^n` of `ExplicitBoundPM` the bit
`false` is the number `-1`. The point `X^i` (the point `X` with the `i`-th bit flipped) is
`Function.update X i (!X i)`. The expectation over either cube is `(∑ X, …) / 2 ^ N`, with `N`
the number of variables (`n` in `ExplicitBoundPM`). The power
`ε^{5/2}` is the real power `ε ^ ((5 : ℝ) / 2)`.

## Sources

* S. Aaronson and A. Ambainis, *The need for structure in quantum speedups*, arXiv:0911.0996v3,
  Conjecture 6 (Conjecture 1.7 of the journal version, Theory of Computing 10 (2014), 133–166):
  "Let p : R^N → R be a polynomial of degree d. Suppose that 0 ≤ p(X) ≤ 1 for all X ∈ {0,1}^N,
  and E_{X∈{0,1}^N}[(p(X) − E[p])²] ≥ ε. Then there exists an i such that
  Inf_i[p] ≥ (ε/d)^{O(1)}", where "Inf_i[p] := E_{X∈{0,1}^N}[(p(X) − p(X^i))²]".
* A. Agarwal and S. Ben-David, *Oracle separations for the quantum-classical polynomial
  hierarchy*, arXiv:2410.19062 (version 2), Theorem 1.7: "Let f : {0,1}^n → [0,1] be a
  real-valued function which can be expressed as a polynomial of degree at most d. Then there is
  an assignment of weights {c_{x,i}}_{x∈{0,1}^n, i∈[n]} to inputs x and positions i ∈ [n] such
  that for all x, y ∈ {0,1}^n, we have  Σ_{i : x_i ≠ y_i} c_{x,i} ≥ |f(x) − f(y)|,
  Σ_{i=1}^n c_{x,i} ≤ (π²/4) d²."
-/

@[expose] public section

namespace AaronsonAmbainis

/-- The conjecture of Aaronson and Ambainis as printed (Conjecture 6 of arXiv:0911.0996v3, quoted
above), in the normalisation of Aaronson and Ambainis, with the absolute constant `7` for `O(1)`:
`Inf_i[p] ≥ (ε/d)^7`. "A polynomial of degree `d`" is read as a polynomial of total degree at
most `d`; the statement for total degree at most `d` is equivalent to the statement for degree
exactly `d`, because `(ε/d)^7` decreases in `d` and a polynomial of degree `0` has variance `0`.
The condition `ε > 0` is written out. -/
def PrintedConjecture : Prop :=
  ∀ (N d : ℕ) (p : MvPolynomial (Fin N) ℝ), p.totalDegree ≤ d →
    (∀ X : Fin N → Bool,
      0 ≤ MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p ∧
        MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p ≤ 1) →
    ∀ ε : ℝ, 0 < ε →
      (∑ X : Fin N → Bool,
          (MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p
            - (∑ Y : Fin N → Bool, MvPolynomial.eval (fun i => if Y i then (1 : ℝ) else 0) p)
                / 2 ^ N) ^ 2) / 2 ^ N ≥ ε →
      ∃ i : Fin N,
        (∑ X : Fin N → Bool,
          (MvPolynomial.eval (fun k => if X k then (1 : ℝ) else 0) p
            - MvPolynomial.eval
                (fun k => if Function.update X i (!X i) k then (1 : ℝ) else 0) p) ^ 2) / 2 ^ N
          ≥ (ε / (d : ℝ)) ^ 7

/-- `PrintedConjecture` with the explicit lower bound `(8 √15 / (125 π^4)) ε^{5/2} / d^6` in place
of `(ε/d)^7`. -/
def ExplicitBound : Prop :=
  ∀ (N d : ℕ) (p : MvPolynomial (Fin N) ℝ), p.totalDegree ≤ d →
    (∀ X : Fin N → Bool,
      0 ≤ MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p ∧
        MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p ≤ 1) →
    ∀ ε : ℝ, 0 < ε →
      (∑ X : Fin N → Bool,
          (MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p
            - (∑ Y : Fin N → Bool, MvPolynomial.eval (fun i => if Y i then (1 : ℝ) else 0) p)
                / 2 ^ N) ^ 2) / 2 ^ N ≥ ε →
      ∃ i : Fin N,
        (∑ X : Fin N → Bool,
          (MvPolynomial.eval (fun k => if X k then (1 : ℝ) else 0) p
            - MvPolynomial.eval
                (fun k => if Function.update X i (!X i) k then (1 : ℝ) else 0) p) ^ 2) / 2 ^ N
          ≥ 8 * Real.sqrt 15 / (125 * Real.pi ^ 4) * ε ^ ((5 : ℝ) / 2) / (d : ℝ) ^ 6

/-- Theorem 1.7 of arXiv:2410.19062 as printed (for `n ≥ 1` and `d ≥ 1`), as a proposition. It
is used only as the hypothesis of `aaronson_ambainis_of_fbsDegreeBound`: this project does not
prove it with the constant `π²/4`. (The unconditional theorems use a bound of the same kind with
a constant twice as large, which is proved in the directories `Row`, `Pack` and `Dual`.) -/
def FbsDegreeBound : Prop :=
  ∀ (n d : ℕ), 1 ≤ n → 1 ≤ d → ∀ f : (Fin n → Bool) → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
    (∃ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ d ∧
      ∀ x, f x = MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p) →
    ∃ c : (Fin n → Bool) → Fin n → ℝ,
      (∀ x y, ∑ i ∈ Finset.univ.filter (fun i => x i ≠ y i), c x i ≥ |f x - f y|) ∧
      (∀ x, ∑ i, c x i ≤ Real.pi ^ 2 / 4 * (d : ℝ) ^ 2)

/-- The conjecture of Aaronson and Ambainis with the explicit lower bound
`(32 √15 / (125 π^4)) ε^{5/2} / d^6`: the conclusion of `aaronson_ambainis_of_fbsDegreeBound`,
whose hypothesis is `FbsDegreeBound`. -/
def ExplicitBoundImproved : Prop :=
  ∀ (N d : ℕ) (p : MvPolynomial (Fin N) ℝ), p.totalDegree ≤ d →
    (∀ X : Fin N → Bool,
      0 ≤ MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p ∧
        MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p ≤ 1) →
    ∀ ε : ℝ, 0 < ε →
      (∑ X : Fin N → Bool,
          (MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p
            - (∑ Y : Fin N → Bool, MvPolynomial.eval (fun i => if Y i then (1 : ℝ) else 0) p)
                / 2 ^ N) ^ 2) / 2 ^ N ≥ ε →
      ∃ i : Fin N,
        (∑ X : Fin N → Bool,
          (MvPolynomial.eval (fun k => if X k then (1 : ℝ) else 0) p
            - MvPolynomial.eval
                (fun k => if Function.update X i (!X i) k then (1 : ℝ) else 0) p) ^ 2) / 2 ^ N
          ≥ 32 * Real.sqrt 15 / (125 * Real.pi ^ 4) * ε ^ ((5 : ℝ) / 2) / (d : ℝ) ^ 6

/-- The main theorem (Theorem 1.1) of the upstream paper, on the cube `{-1,1}^n`, in the
form with a lower bound `ε` for the variance (Theorem 1.1 with `Var(p) > 0` is the case
`ε = Var(p)`): range `[-1,1]`, influence `Inf_i(p) = E[((p(x) − p(x^i))/2)²]`, explicit lower
bound `(√15 / (500 π^4)) ε^{5/2} / d^6`. The bit `true` is the number `1`, and the bit `false` is
the number `-1`. -/
def ExplicitBoundPM : Prop :=
  ∀ (n d : ℕ) (p : MvPolynomial (Fin n) ℝ), p.totalDegree ≤ d →
    (∀ X : Fin n → Bool, |MvPolynomial.eval (fun i => if X i then (1 : ℝ) else -1) p| ≤ 1) →
    ∀ ε : ℝ, 0 < ε →
      (∑ X : Fin n → Bool,
          (MvPolynomial.eval (fun i => if X i then (1 : ℝ) else -1) p
            - (∑ Y : Fin n → Bool, MvPolynomial.eval (fun i => if Y i then (1 : ℝ) else -1) p)
                / 2 ^ n) ^ 2) / 2 ^ n ≥ ε →
      ∃ i : Fin n,
        (∑ X : Fin n → Bool,
          ((MvPolynomial.eval (fun k => if X k then (1 : ℝ) else -1) p
            - MvPolynomial.eval
                (fun k => if Function.update X i (!X i) k then (1 : ℝ) else -1) p) / 2) ^ 2)
            / 2 ^ n
          ≥ Real.sqrt 15 / (500 * Real.pi ^ 4) * ε ^ ((5 : ℝ) / 2) / (d : ℝ) ^ 6

end AaronsonAmbainis

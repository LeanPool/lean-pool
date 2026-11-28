/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.SVI.SignFormula

/-! # Reading the degree by sign queries

Part of the SVI polynomial-sign certificate (#174).

A sign program that finds the degree and leading sign of the numerator polynomial from the signs
of its coefficients, as polynomials in the parameters (`degreeProgram_eval`).

## Main definitions

* `degreeProgram`: a sign program that scans the coefficients of `universalPolynomial` from index
  `n` down and returns the first nonzero index with its sign.

## Main results

* `universalCoefficient_eval`: evaluating the `r`-th coefficient of `universalPolynomial` at the
  parameters `p` gives `(polynomial p).coeff r`.
* `degreeProgram_eval`: if `(polynomial p).natDegree ≤ n`, then `degreeProgram n` evaluates at `p`
  to the degree and the sign of the leading coefficient of `polynomial p`.

## Tags

sign program, polynomial degree, leading coefficient sign, SVI, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI
open Polynomial

/-- A sign program reading off, from the top coefficient down, the first index `≤ n` whose
coefficient of the universal polynomial is nonzero, with its sign; `(0, s)` with the sign of the
constant coefficient if none is. -/
noncomputable def degreeProgram : ℕ → SignProgram (ℕ × SignType)
  | 0 => (signQuery (universalPolynomial.coeff 0)).bind fun s ↦ .pure (0,s)
  | n+1 => .query (universalPolynomial.coeff (n+1))
      (.pure (n+1,.neg)) (degreeProgram n) (.pure (n+1,.pos))

theorem universalCoefficient_eval (p : Params) (r : ℕ) :
    parameterEval p (universalPolynomial.coeff r) = (polynomial p).coeff r := by
  rw [← coeff_map, universalPolynomial_eval]

theorem degreeProgram_eval (p : Params) (n : ℕ) (hn : (polynomial p).natDegree ≤ n) :
    (degreeProgram n).eval p =
      ((polynomial p).natDegree, SignType.sign (polynomial p).leadingCoeff) := by
  induction n with
  | zero =>
    have hd : (polynomial p).natDegree = 0 := Nat.eq_zero_of_le_zero hn
    simp [degreeProgram, SignProgram.eval_bind, SignProgram.eval,
      universalCoefficient_eval, leadingCoeff, hd]
  | succ n ih =>
    simp only [degreeProgram, SignProgram.eval, universalCoefficient_eval]
    cases hs : SignType.sign ((polynomial p).coeff (n+1)) with
    | zero =>
      have hz : (polynomial p).coeff (n+1) = 0 := sign_eq_zero_iff.mp hs
      have hd : (polynomial p).natDegree ≤ n := by
        by_contra h
        have he : (polynomial p).natDegree = n+1 := by omega
        have hne : polynomial p ≠ 0 := by intro h; simp [h] at he
        have hc : (polynomial p).coeff (n+1) ≠ 0 := by
          rw [← he, coeff_natDegree]
          exact leadingCoeff_ne_zero.mpr hne
        exact hc hz
      exact ih hd
    | neg =>
      have hneg : (polynomial p).coeff (n+1) < 0 := sign_eq_neg_one_iff.mp hs
      have hd := natDegree_eq_of_le_of_coeff_ne_zero hn (ne_of_lt hneg)
      simp only [leadingCoeff, hd, hs]
    | pos =>
      have hpos : 0 < (polynomial p).coeff (n+1) := sign_eq_one_iff.mp hs
      have hd := natDegree_eq_of_le_of_coeff_ne_zero hn (ne_of_gt hpos)
      simp only [leadingCoeff, hd, hs]

end SVI
end MathFin

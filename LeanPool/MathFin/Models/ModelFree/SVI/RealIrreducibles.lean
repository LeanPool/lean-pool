/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.SVI.QuadraticRootSignature
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Monic irreducible real polynomials

Part of the SVI polynomial-sign certificate (#174).

A monic irreducible real polynomial is linear or a positive quadratic `(X − a)² + b²`.

## Main results

* `monic_real_irreducible_cases`: a monic irreducible `p : ℝ[X]` is either `X - C c` or
  `positiveQuadratic a b` with `b ≠ 0`.

## Tags

irreducible real polynomials, fundamental theorem of algebra, linear or quadratic factors, SVI,
MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI
open Polynomial

/-- Every monic irreducible real polynomial is linear or a strictly positive
completed-square quadratic. -/
theorem monic_real_irreducible_cases (p : ℝ[X]) (hm : p.Monic) (hi : Irreducible p) :
    (∃ c : ℝ, p = X - C c) ∨
      ∃ a b : ℝ, b ≠ 0 ∧ p = positiveQuadratic a b := by
  have hlo := hi.natDegree_pos
  have hhi := hi.natDegree_le_two
  have hd : p.natDegree = 1 ∨ p.natDegree = 2 := by omega
  rcases hd with hd | hd
  · left
    exact ⟨-p.coeff 0, by simpa using hm.eq_X_add_C hd⟩
  · right
    have hp : p = X^2 + C (p.coeff 1)*X + C (p.coeff 0) := by
      have h := p.as_sum_range_C_mul_X_pow
      have h2 : p.coeff 2 = 1 := by simpa [hd] using hm.coeff_natDegree
      simpa [hd, Finset.sum_range_succ, h2, add_comm, add_left_comm, add_assoc] using h
    let a := -p.coeff 1 / 2
    let s := p.coeff 0 - (p.coeff 1)^2 / 4
    have hs : 0 < s := by
      by_contra hn
      have hsn : 0 ≤ -s := by linarith
      have hsq := Real.sq_sqrt hsn
      have hroot : p.IsRoot (a + Real.sqrt (-s)) := by
        rw [IsRoot, hp]
        simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C]
        dsimp [a, s] at *
        nlinarith
      exact hi.not_isRoot_of_natDegree_ne_one (by omega) hroot
    refine ⟨a, Real.sqrt s, ne_of_gt (Real.sqrt_pos.2 hs), ?_⟩
    rw [hp, positiveQuadratic, Real.sq_sqrt hs.le]
    have haC := congrArg (C : ℝ → ℝ[X]) (show -2*a = p.coeff 1 by dsimp [a]; ring)
    have hsC := congrArg (C : ℝ → ℝ[X]) (show a^2+s = p.coeff 0 by dsimp [a, s]; ring)
    simp only [map_mul, map_neg, map_ofNat] at haC
    simp only [map_add, map_pow] at hsC
    linear_combination -X * haC - hsC

end SVI
end MathFin

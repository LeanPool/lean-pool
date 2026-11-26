/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4LinearCrossCoordinates
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Distinct crossing lines have independent directions

For the local crossing discs in XII (4.5), page 253, the two
supporting lines through a meeting are distinct. Their nonzero
directions have nonzero determinant. If the determinant vanished,
one direction would be a real multiple of the other, making the
lines equal. The coordinate equivalence then sends the axes to
the two directions.
-/

public section

namespace GraphMinor.GM12

private theorem exists_scalar_of_cross_det_zero {u v : ℂ} (hu : u ≠ 0)
    (hdet : u.re * v.im - u.im * v.re = 0) : ∃ r : ℝ, r • u = v := by
  classical
  by_cases hur : u.re = 0
  · have hui : u.im ≠ 0 := fun h => hu (Complex.ext hur h)
    rw [hur, zero_mul, zero_sub, neg_eq_zero] at hdet
    have hvr : v.re = 0 := (mul_eq_zero.mp hdet).resolve_left hui
    refine ⟨v.im / u.im, Complex.ext ?_ ?_⟩
    · simp only [Complex.smul_re, smul_eq_mul, hur, mul_zero, hvr]
    · rw [Complex.smul_im, smul_eq_mul]
      exact div_mul_cancel₀ _ hui
  · refine ⟨v.re / u.re, Complex.ext ?_ ?_⟩
    · rw [Complex.smul_re, smul_eq_mul]
      exact div_mul_cancel₀ _ hur
    · rw [Complex.smul_im, smul_eq_mul]
      field_simp [hur]
      linear_combination -hdet

/-- Distinct lines through a common point have nonzero real
cross determinant, for any nonzero vectors defining them. -/
theorem cross_det_ne_of_distinct_lines {x u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0)
    (hne : line[ℝ, x, x + u] ≠ line[ℝ, x, x + v]) :
    u.re * v.im - u.im * v.re ≠ 0 := by
  intro hdet
  obtain ⟨r, hr⟩ := exists_scalar_of_cross_det_zero hu hdet
  have hxv : x + v ∈ line[ℝ, x, x + u] := by
    apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
    refine ⟨r, ?_⟩
    rw [AffineMap.lineMap_apply]
    change r • ((x + u) - x) + x = x + v
    rw [add_sub_cancel_left, hr, add_comm]
  have hxxv : x ≠ x + v := by
    intro h
    have hvzero : (0 : ℂ) = v := add_left_cancel (show x + 0 = x + v by simpa only [add_zero] using
      h)
    exact hv hvzero.symm
  have heq := affineSpan_pair_eq_of_mem_of_mem_of_ne (left_mem_affineSpan_pair ℝ x (x + u)) hxv hxxv
  exact hne heq.symm

/-- A common meeting of two distinct lines has continuous linear
coordinates carrying the axes to their directions, as used in
XII (4.5)'s crossing discs, page 253. -/
theorem exists_cross_coordinates_of_distinct_lines {x u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0)
    (hne : line[ℝ, x, x + u] ≠ line[ℝ, x, x + v]) :
    ∃ A : ℂ ≃L[ℝ] ℂ, A 1 = u ∧ A Complex.I = v :=
  exists_linear_cross_coordinates (cross_det_ne_of_distinct_lines hu hv hne)

end GraphMinor.GM12

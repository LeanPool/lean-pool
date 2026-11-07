/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.ThinAnnulus
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Three equidistant neighbors in a thin planar annulus contain a close pair

The coordinates are in an orthonormal frame with the apex `(a,0)`.
The inputs and output are exact squared Euclidean distances. The limit proof
in `docs/results/annulus-atomic-limit-2026-10-13.md` uses this finite lemma
before counting perpendicular-bisector witnesses. No limit theorem is asserted
in this module.
-/

@[expose] public section

namespace Esgk

/-- Two equidistant neighbors on the same transverse side of the apex axis
are close, provided their squared radii lie in `[1-x,1]` and `a≥1/2`. -/
lemma annular_same_side_sqDist_le {a x u v U V : ℝ}
    (ha : 1 / 2 ≤ a) (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (hlo : 1 - x ≤ u ^ 2 + v ^ 2) (hhi : u ^ 2 + v ^ 2 ≤ 1)
    (hLo : 1 - x ≤ U ^ 2 + V ^ 2) (hHi : U ^ 2 + V ^ 2 ≤ 1)
    (heq : (a - u) ^ 2 + v ^ 2 = (a - U) ^ 2 + V ^ 2)
    (hside : 0 ≤ v * V) :
    (u - U) ^ 2 + (v - V) ^ 2 ≤ 4 * x := by
  have hrow : 2 * a * (u - U) = (u ^ 2 + v ^ 2) - (U ^ 2 + V ^ 2) := by
    nlinarith [heq]
  have hcoeff : 0 ≤ 2 * a - 1 := by linarith
  have hdu : u - U ≤ x := by
    by_cases hd : 0 ≤ u - U
    · nlinarith [mul_nonneg hcoeff hd]
    · linarith
  have hdl : -x ≤ u - U := by
    by_cases hd : 0 ≤ U - u
    · nlinarith [mul_nonneg hcoeff hd]
    · linarith
  have hdabs : |u - U| ≤ x := abs_le.mpr ⟨hdl, hdu⟩
  have hu : |u| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg v]
  have hU : |U| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg V]
  have hsabs : |u + U| ≤ 2 := (abs_add_le u U).trans (by linarith)
  have husq : |u ^ 2 - U ^ 2| ≤ 2 * x := by
    calc
      |u ^ 2 - U ^ 2| = |u - U| * |u + U| := by
        rw [← abs_mul]
        congr 1
        ring
      _ ≤ x * 2 := mul_le_mul hdabs hsabs (abs_nonneg _) hx
      _ = 2 * x := by ring
  obtain ⟨husql, husqu⟩ := abs_le.mp husq
  have hvsq : |v ^ 2 - V ^ 2| ≤ 3 * x := by
    rw [abs_le]
    constructor <;> nlinarith
  have habs : |v - V| ≤ |v + V| := by
    have hm := sq_abs (v - V)
    have hp := sq_abs (v + V)
    have hn := abs_nonneg (v - V)
    have hN := abs_nonneg (v + V)
    nlinarith
  have hvclose : (v - V) ^ 2 ≤ |v ^ 2 - V ^ 2| := by
    calc
      (v - V) ^ 2 = |v - V| * |v - V| := by rw [← pow_two, sq_abs]
      _ ≤ |v - V| * |v + V| := mul_le_mul_of_nonneg_left habs (abs_nonneg _)
      _ = |v ^ 2 - V ^ 2| := by
        rw [← abs_mul]
        congr 1
        ring
  have hdclose : (u - U) ^ 2 ≤ x ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ x - (u - U))
      (by linarith : 0 ≤ x + (u - U))]
  nlinarith [mul_nonneg hx (by linarith : 0 ≤ 1 - x)]

/-- Among three real transverse coordinates, two lie on the same weak side
of zero. -/
lemma three_has_same_transverse_side (v : Fin 3 → ℝ) :
    ∃ i j : Fin 3, i ≠ j ∧ 0 ≤ v i * v j := by
  by_cases h0 : 0 ≤ v 0 <;> by_cases h1 : 0 ≤ v 1 <;> by_cases h2 : 0 ≤ v 2
  · exact ⟨0, 1, by decide, mul_nonneg h0 h1⟩
  · exact ⟨0, 1, by decide, mul_nonneg h0 h1⟩
  · exact ⟨0, 2, by decide, mul_nonneg h0 h2⟩
  · exact ⟨1, 2, by decide, mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)⟩
  · exact ⟨1, 2, by decide, mul_nonneg h1 h2⟩
  · exact ⟨0, 2, by decide, mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)⟩
  · exact ⟨0, 1, by decide, mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)⟩
  · exact ⟨0, 1, by decide, mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)⟩

/-- In an orthonormal frame with apex `(a,0)`, three points with equal
distance to the apex and squared radii in `[1-x,1]` contain a pair of squared
distance at most `4*x`. In the annulus application `x≤3/4` guarantees `a≥1/2`.
The stronger coordinate statement only needs `x≤1` once the apex bound is given. -/
theorem annular_three_equidistant_has_close_pair (u v : Fin 3 → ℝ) {a x : ℝ}
    (ha : 1 / 2 ≤ a) (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (hlo : ∀ i, 1 - x ≤ u i ^ 2 + v i ^ 2)
    (hhi : ∀ i, u i ^ 2 + v i ^ 2 ≤ 1)
    (heq : ∀ i j, (a - u i) ^ 2 + v i ^ 2 = (a - u j) ^ 2 + v j ^ 2) :
    ∃ i j : Fin 3, i ≠ j ∧ (u i - u j) ^ 2 + (v i - v j) ^ 2 ≤ 4 * x := by
  obtain ⟨i, j, hij, hside⟩ := three_has_same_transverse_side v
  exact ⟨i, j, hij, annular_same_side_sqDist_le ha hx hx1
    (hlo i) (hhi i) (hlo j) (hhi j) (heq i j) hside⟩

end Esgk

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUECenterGeometry.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUESymmetricInequalities
/-!
# Correspondence GUE center geometry

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueCenterCoordinate_eq`, `gueRawDensity_center_factorization`.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- The vector of `EuclideanSpace ℝ (Fin n)` with all coordinates `(√n)⁻¹`, a unit vector when
`0 < n`. -/
def gueCenterUnit (n : ℕ) : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun _ => (Real.sqrt n)⁻¹)
/-- The center coordinate `⟪gueCenterUnit n, x⟫` of `x`. -/
def gueCenterCoordinate (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ := inner ℝ (gueCenterUnit n) x

theorem gueCenterUnit_norm {n : ℕ} (hn : 0 < n) : ‖gueCenterUnit n‖=1 := by
  have hs : Real.sqrt n≠0 := ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  have hsq : ‖gueCenterUnit n‖^2=1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [gueCenterUnit, PiLp.toLp_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    field_simp
  nlinarith [norm_nonneg (gueCenterUnit n)]

theorem gueCenterCoordinate_eq (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    gueCenterCoordinate n x=(Real.sqrt n)⁻¹*∑i, x i := by
  unfold gueCenterCoordinate
  rw [PiLp.inner_apply]
  simp only [gueCenterUnit, PiLp.toLp_apply, RCLike.inner_apply, starRingEnd_apply, star_trivial]
  rw [← Finset.sum_mul, mul_comm]

theorem gueRawDensity_center_factorization {n : ℕ} (hn : 0 < n) (t : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) (hy : inner ℝ (gueCenterUnit n) y = 0) :
    gueRawDensity n (t • gueCenterUnit n+y)=Real.exp (-(n : ℝ)/2*t^2)*gueRawDensity n y := by
  have hs : ‖t • gueCenterUnit n+y‖^2=t^2+‖y‖^2 := by
    rw [norm_add_sq_real, real_inner_smul_left, hy, mul_zero, mul_zero, add_zero, norm_smul,
      gueCenterUnit_norm hn, Real.norm_eq_abs, mul_one, sq_abs]
  have he (x : EuclideanSpace ℝ (Fin n)) :
      gueRawDensity n x=Real.exp (-(n : ℝ)/2*‖x‖^2)*∏p∈guePairs n, (x p.2-x p.1)^2 := by
    unfold gueRawDensity
    rw [EuclideanSpace.real_norm_sq_eq]
  rw [he, he, hs]
  have hd (p : Fin n×Fin n) :
      (t • gueCenterUnit n+y) p.2-(t • gueCenterUnit n+y) p.1=y p.2-y p.1 := by
    simp only [PiLp.add_apply, PiLp.smul_apply, gueCenterUnit, smul_eq_mul]
    ring
  simp_rw [hd]
  rw [mul_add, Real.exp_add]
  ring

end
end GinibrePoincare

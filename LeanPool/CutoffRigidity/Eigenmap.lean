/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Tactic

/-!
# The Euclidean linear algebra of normalized multi-eigenmaps

These results formalize the orthogonal-row argument in the proof of
`th:maineucl` in `cutcur-lean.tex`. The spectral and probabilistic inputs
are separate obligations; here the rows are explicitly scaled orthonormal
vectors in the genuine Euclidean inner product space.
-/

public section

namespace CutoffRigidity

open scoped InnerProductSpace

/-- The linear part of a normalized eigenmap, written using its row vectors. -/
@[expose] noncomputable def eigenmapLinear {d k : ℕ}
    (v : Fin k → EuclideanSpace ℝ (Fin d)) (rate : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun i => Real.sqrt rate * inner ℝ (v i) x)

/-- Bessel's inequality gives the squared norm bound for the eigenmap. -/
theorem eigenmapLinear_norm_sq_le {d k : ℕ}
    {v : Fin k → EuclideanSpace ℝ (Fin d)} (hv : Orthonormal ℝ v)
    {rate : ℝ} (hr : 0 ≤ rate) (x : EuclideanSpace ℝ (Fin d)) :
    ‖eigenmapLinear v rate x‖ ^ 2 ≤ rate * ‖x‖ ^ 2 := by
  have hb := hv.sum_inner_products_le (s := Finset.univ) x
  simp only [Real.norm_eq_abs, sq_abs] at hb
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ i, (Real.sqrt rate * inner ℝ (v i) x) ^ 2) ≤ _
  simp only [mul_pow, Real.sq_sqrt hr]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hb hr

/-- The norm estimate in the paper, before passing to Wasserstein distances. -/
theorem eigenmapLinear_norm_le {d k : ℕ}
    {v : Fin k → EuclideanSpace ℝ (Fin d)} (hv : Orthonormal ℝ v)
    {rate : ℝ} (hr : 0 ≤ rate) (x : EuclideanSpace ℝ (Fin d)) :
    ‖eigenmapLinear v rate x‖ ≤ Real.sqrt rate * ‖x‖ := by
  have h := eigenmapLinear_norm_sq_le hv hr x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  simpa only [mul_pow, Real.sq_sqrt hr] using h

/-- Subtracting inputs subtracts the linear parts of the eigenmap. -/
theorem eigenmapLinear_sub {d k : ℕ}
    (v : Fin k → EuclideanSpace ℝ (Fin d)) (rate : ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    eigenmapLinear v rate (x - y) = eigenmapLinear v rate x - eigenmapLinear v rate y := by
  ext i
  change Real.sqrt rate * inner ℝ (v i) (x - y) =
    Real.sqrt rate * inner ℝ (v i) x - Real.sqrt rate * inner ℝ (v i) y
  rw [inner_sub_right, mul_sub]

/-- Orthogonal normalized rows give the Lipschitz constant used in the paper. -/
theorem eigenmapLinear_lipschitz {d k : ℕ}
    {v : Fin k → EuclideanSpace ℝ (Fin d)} (hv : Orthonormal ℝ v)
    {rate : ℝ} (hr : 0 ≤ rate) :
    LipschitzWith ⟨Real.sqrt rate, Real.sqrt_nonneg rate⟩ (eigenmapLinear v rate) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (eigenmapLinear v rate x) (eigenmapLinear v rate y) ≤ Real.sqrt rate * dist x y
  simpa only [dist_eq_norm, ← eigenmapLinear_sub] using eigenmapLinear_norm_le hv hr (x - y)

/-- Adding the affine constant preserves the same Lipschitz bound. -/
theorem eigenmapAffine_lipschitz {d k : ℕ}
    {v : Fin k → EuclideanSpace ℝ (Fin d)} (hv : Orthonormal ℝ v)
    {rate : ℝ} (hr : 0 ≤ rate) (b : EuclideanSpace ℝ (Fin k)) :
    LipschitzWith ⟨Real.sqrt rate, Real.sqrt_nonneg rate⟩
      (fun x => eigenmapLinear v rate x + b) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_add_right] using (eigenmapLinear_lipschitz hv hr).dist_le_mul x y

/-- The norm bound is attained in any row direction. -/
theorem eigenmapLinear_norm_sq_smul_row {d k : ℕ}
    {v : Fin k → EuclideanSpace ℝ (Fin d)} (hv : Orthonormal ℝ v)
    {rate : ℝ} (hr : 0 ≤ rate) (R : ℝ) (j : Fin k) :
    ‖eigenmapLinear v rate (R • v j)‖ ^ 2 = rate * R ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ i, (Real.sqrt rate * inner ℝ (v i) (R • v j)) ^ 2) = _
  simp [inner_smul_right, orthonormal_iff_ite.mp hv, mul_pow, Real.sq_sqrt hr]

/-- The squared norm has the exact maximum `rate * R²` on the closed ball.
A row index supplies the nontriviality of the first eigenspace. -/
theorem eigenmapLinear_ball_isGreatest {d k : ℕ}
    {v : Fin k → EuclideanSpace ℝ (Fin d)} (hv : Orthonormal ℝ v)
    {rate R : ℝ} (hr : 0 ≤ rate) (hR : 0 ≤ R) (j : Fin k) :
    IsGreatest ((fun x => ‖eigenmapLinear v rate x‖ ^ 2) '' Metric.closedBall 0 R)
      (rate * R ^ 2) := by
  constructor
  · refine ⟨R • v j, ?_, eigenmapLinear_norm_sq_smul_row hv hr R j⟩
    simp [Metric.mem_closedBall, dist_zero_right, norm_smul, hv.norm_eq_one, abs_of_nonneg hR]
  · rintro _ ⟨x, hx, rfl⟩
    have hxR : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    calc
      ‖eigenmapLinear v rate x‖ ^ 2 ≤ rate * ‖x‖ ^ 2 := eigenmapLinear_norm_sq_le hv hr x
      _ ≤ rate * R ^ 2 := mul_le_mul_of_nonneg_left (sq_le_sq₀ (norm_nonneg x) hR |>.mpr hxR) hr

/-- The exact supremum of the squared eigenmap norm on a closed ball. -/
theorem eigenmapLinear_ball_sup {d k : ℕ}
    {v : Fin k → EuclideanSpace ℝ (Fin d)} (hv : Orthonormal ℝ v)
    {rate R : ℝ} (hr : 0 ≤ rate) (hR : 0 ≤ R) (j : Fin k) :
    sSup ((fun x => ‖eigenmapLinear v rate x‖ ^ 2) '' Metric.closedBall 0 R) =
      rate * R ^ 2 :=
  (eigenmapLinear_ball_isGreatest hv hr hR j).csSup_eq

end CutoffRigidity

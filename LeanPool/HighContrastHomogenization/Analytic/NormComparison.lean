/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.AnalyticCarriers
public import LeanPool.HighContrastHomogenization.Analytic.EuclideanAmbient
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# High-contrast homogenization: Analytic.NormComparison

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The ambient norm against the Euclidean quantities

`Vec d = Fin d → ℝ` carries the supremum norm, while every Euclidean quantity in
the volume-normalized spaces of `s.introduction` is written through
`vecNormSq`.  The two are comparable, with the dimensional loss appearing only
in one direction:

`‖z‖ ≤ |z|` and `|z|² ≤ d ‖z‖²`.

Both are needed by the finiteness statements for the normalized norms: the first
turns a Euclidean distance in a Gagliardo denominator into an ambient one, and
the second turns an ambient bound on a test field into a Euclidean one.

The module also collects the elementary consequences of smoothness and compact
support that those statements consume — a uniform bound on the field, a uniform
bound on its derivative, the resulting global Lipschitz bound for the ambient
norm — and the volume of an ambient ball, which is a product of intervals and
therefore has an explicit value independent of the centre.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Comparison of the ambient (sup) norm with the Euclidean quantities -/

theorem norm_le_sqrt_vecNormSq (z : Vec d) : ‖z‖ ≤ Real.sqrt (vecNormSq z) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
  have h1 : z i ^ 2 ≤ vecNormSq z := sq_apply_le_vecNormSq z i
  have h2 : Real.sqrt (z i ^ 2) ≤ Real.sqrt (vecNormSq z) := Real.sqrt_le_sqrt h1
  rw [Real.norm_eq_abs]
  rwa [Real.sqrt_sq_eq_abs] at h2

theorem vecNormSq_le_dim_mul_norm_sq (z : Vec d) : vecNormSq z ≤ (d : ℝ) * ‖z‖ ^ 2 := by
  have hb : ∀ i : Fin d, z i ^ 2 ≤ ‖z‖ ^ 2 := by
    intro i
    have h := norm_le_pi_norm z i
    rw [Real.norm_eq_abs] at h
    have h0 : (0 : ℝ) ≤ |z i| := abs_nonneg _
    calc z i ^ 2 = |z i| * |z i| := by rw [← sq_abs, pow_two]
      _ ≤ ‖z‖ * ‖z‖ := mul_self_le_mul_self h0 h
      _ = ‖z‖ ^ 2 := (pow_two _).symm
  have hconst : ∑ _i : Fin d, ‖z‖ ^ 2 = (d : ℝ) * ‖z‖ ^ 2 := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [vecNormSq_eq_sum_sq]
  calc ∑ i, z i ^ 2 ≤ ∑ _i : Fin d, ‖z‖ ^ 2 := Finset.sum_le_sum fun i _ => hb i
    _ = (d : ℝ) * ‖z‖ ^ 2 := hconst

theorem norm_basisVec_le_one (i : Fin d) : ‖(basisVec i : Vec d)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
  rw [Real.norm_eq_abs, basisVec_apply]
  split <;> norm_num

/-! ## Smooth compactly supported maps are bounded and Lipschitz -/

theorem exists_norm_bound_of_hasCompactSupport {ψ : Vec d → Vec d}
    (hcont : Continuous ψ) (hcs : HasCompactSupport ψ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖ψ x‖ ≤ M := by
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hcont
  exact ⟨C, le_trans (norm_nonneg _) (hC 0), hC⟩

theorem exists_fderiv_bound_of_hasCompactSupport {ψ : Vec d → Vec d}
    (hsm : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcs : HasCompactSupport ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖fderiv ℝ ψ x‖ ≤ C := by
  have hone : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  obtain ⟨C, hC⟩ :=
    (hcs.fderiv ℝ).exists_bound_of_continuous (hsm.continuous_fderiv hone)
  exact ⟨C, le_trans (norm_nonneg _) (hC 0), hC⟩

/-- A smooth compactly supported field is globally Lipschitz for the ambient
(sup) norm. -/
theorem exists_lipschitz_of_hasCompactSupport {ψ : Vec d → Vec d}
    (hsm : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcs : HasCompactSupport ψ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y, ‖ψ x - ψ y‖ ≤ L * ‖x - y‖ := by
  have hone : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  obtain ⟨C, hC0, hC⟩ := exists_fderiv_bound_of_hasCompactSupport hsm hcs
  have hlip : LipschitzWith C.toNNReal ψ := by
    refine lipschitzWith_of_nnnorm_fderiv_le (hsm.differentiable hone) fun x => ?_
    exact (Real.le_toNNReal_iff_coe_le hC0).mpr (by simpa using hC x)
  refine ⟨C, hC0, fun x y => ?_⟩
  have h := hlip.dist_le_mul x y
  rwa [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal C hC0] at h

/-! ## The volume of an ambient ball -/

theorem volume_ball_eq (x : Vec d) {r : ℝ} (hr : 0 < r) :
    volume (Metric.ball x r) = ENNReal.ofReal ((2 * r) ^ d) := by
  rw [Real.volume_pi_ball x hr, Fintype.card_fin]

end

end HighContrast
end HCPolySupport

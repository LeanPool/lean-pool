/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.SwirlBound

/-!
# Swirl Bound Cutoff Decay

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- Reduction of `eq:aniso:closure:w`'s swirl bound to the single-power decay shape
`W t ≤ C_η (−t)^{−η}` consumed by the Grönwall step of `lem:aniso:closure`.

The raw bound from `CIV.swirl_bound_ball` reads
`(−t)^η |swirlCoeffAt u (x,t)| ≤ (−t_η)^η max(M_b, M_i) + (−t_η)^η M_f (t − t_η)`.
Since `t − t_η < −t_η` for every `t < 0` and `M_f ≥ 0` (forced by `hMf`), the
accumulated-source term is bounded by its value at `t = 0⁻`, yielding a single
constant
`C_η := (−t_η)^η max(M_b, M_i) + (−t_η)^{η+1} M_f`
for which dividing the raw bound by `(−t)^η` lands exactly on `C_η (−t)^{−η}`. -/
theorem swirlCoeffAt_le_of_swirl_bound_ball
    (u : ParabolicPoint → Vec3) (pr : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u pr f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hfaxi : IsAxisymmetricOn f unitCylinder)
    (Mf : ℝ) (hMf : ∀ z ∈ unitCylinder, |f z 1| ≤ Mf)
    (Rstar : ℝ) (hR : 0 < Rstar ∧ Rstar < 1) (tη η : ℝ) (htη : tη ∈ Ioo (-1 : ℝ) 0)
    (hη : 0 < η)
    (hG : ∀ t ∈ Ioo tη (0 : ℝ), ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) Rstar →
        |radialQuotient u (meridional x₁ x₃, t)| ≤ η / (-t))
    (Mb : ℝ)
    (hbdry : ∀ x : Vec3, vec3EuclideanNorm x = Rstar → ∀ t ∈ Ioo tη (0 : ℝ), |u (x, t) 1| ≤ Mb)
    (Mi : ℝ) (hinit : ∀ x ∈ vec3Ball (0 : Vec3) Rstar, |u (x, tη) 1| ≤ Mi) :
    ∃ Cη : ℝ, 0 ≤ Cη ∧ ∀ t ∈ Ioo tη (0 : ℝ), ∀ x ∈ vec3Ball (0 : Vec3) Rstar,
      (x 0 ≠ 0 ∨ x 1 ≠ 0) → |swirlCoeffAt u (x, t)| ≤ Cη * (-t) ^ (-η) := by
  have h_tη_pos : 0 < -tη := by linarith only [htη.2]
  have h_tη_nonneg : 0 ≤ -tη := by linarith only [htη.2]
  have h_rpow_tη_nonneg : 0 ≤ (-tη) ^ η := Real.rpow_nonneg h_tη_nonneg η
  have h_Mf_nonneg : 0 ≤ Mf := by
    have hzero : ((0 : Vec3), tη) ∈ unitCylinder := by
      refine ⟨by
        rw [mem_vec3Ball, sub_zero, vec3EuclideanNorm_zero]
        exact hR.1.trans hR.2, htη⟩
    exact le_trans (abs_nonneg (f ((0 : Vec3), tη) 1)) (hMf ((0 : Vec3), tη) hzero)
  have h_Mi_nonneg : 0 ≤ Mi := by
    have hzero_mem : (0 : Vec3) ∈ vec3Ball (0 : Vec3) Rstar := by
      rw [mem_vec3Ball, sub_zero, vec3EuclideanNorm_zero]
      exact hR.1
    have h := hinit 0 hzero_mem
    exact le_trans (abs_nonneg _) h
  have h_Mb_nonneg : 0 ≤ Mb := by
    have hnorm : vec3EuclideanNorm (meridional Rstar 0) = Rstar := by
      rw [vec3EuclideanNorm_meridional]
      simp [hR.1.le]
    have ht_mem : tη / 2 ∈ Ioo tη (0 : ℝ) := by
      constructor <;> linarith only [htη.1, htη.2]
    have h := hbdry (meridional Rstar 0) hnorm (tη / 2) ht_mem
    exact le_trans (abs_nonneg _) h
  have h_max_nonneg : 0 ≤ max Mb Mi := by
    exact le_max_iff.mpr (Or.inl h_Mb_nonneg)
  have hCη_nonneg : 0 ≤ (-tη) ^ η * max Mb Mi + (-tη) ^ (η + 1) * Mf := by
    positivity
  set Cη := (-tη) ^ η * max Mb Mi + (-tη) ^ (η + 1) * Mf with hCη_def
  refine ⟨Cη, hCη_nonneg, ?_⟩
  intro t ht x hx hoff
  have ht_neg : t < 0 := ht.2
  have h_t_pos : 0 < -t := by linarith only [ht.2]
  have h_t_nonneg : 0 ≤ -t := by linarith only [ht.2]
  have h_rpow_t_nonneg : 0 ≤ (-t) ^ η := Real.rpow_nonneg h_t_nonneg η
  have h_rpow_t_pos : 0 < (-t) ^ η := Real.rpow_pos_of_pos h_t_pos η
  have hbound := swirl_bound_ball u pr f hsol haxi hfaxi Mf hMf Rstar hR tη η htη hη hG Mb hbdry
    Mi hinit t ht x hx hoff
  have h_tsub_le : t - tη ≤ -tη := by linarith only [ht_neg]
  have h_term_le : (-tη) ^ η * Mf * (t - tη) ≤ (-tη) ^ (η + 1) * Mf := by
    have h_nonneg_prod : 0 ≤ (-tη) ^ η * Mf := mul_nonneg h_rpow_tη_nonneg h_Mf_nonneg
    have h1 : (-tη) ^ η * Mf * (t - tη) ≤ (-tη) ^ η * Mf * (-tη) :=
      mul_le_mul_of_nonneg_left h_tsub_le h_nonneg_prod
    have h2 : (-tη) ^ η * Mf * (-tη) = (-tη) ^ (η + 1) * Mf := by
      calc
        (-tη) ^ η * Mf * (-tη) = (-tη) ^ η * (-tη) * Mf := by ring
        _ = (-tη) ^ η * ((-tη) ^ (1 : ℝ)) * Mf := by rw [Real.rpow_one]
        _ = (-tη) ^ (η + 1) * Mf := by rw [← Real.rpow_add h_tη_pos η 1]
    linarith only [h1, h2]
  have h_total : (-t) ^ η * |swirlCoeffAt u (x, t)| ≤ Cη := by
    rw [hCη_def]
    linarith only [hbound, h_term_le]
  have h_div : |swirlCoeffAt u (x, t)| ≤ Cη / (-t) ^ η :=
    (le_div_iff₀ h_rpow_t_pos).mpr (by
      rw [mul_comm]; exact h_total)
  have h_rewrite : Cη / (-t) ^ η = Cη * (-t) ^ (-η) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg h_t_nonneg η]
  rw [h_rewrite] at h_div
  exact h_div

end CIV

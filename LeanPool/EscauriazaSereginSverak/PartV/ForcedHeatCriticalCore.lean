/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatEnergyIdentity
public import LeanPool.EscauriazaSereginSverak.PartV.HeatEntropyTime

/-!
# The regularized `|Z| Z` test for the forced heat response

Testing the forced heat equation with the regularized critical test
`heatRegTest η Z` absorbs half of the forcing into the dissipation and leaves
`|Z| |g|²`:

`∫ E_η(Z(t₁)) + ½ ∫₀^{t₁} ∑_j D_j ≤ ∫₀^{t₁} ∫ |Z| |g|²`,

where `D_j = ∑_i ∂_j[T_i(Z)] ∂_j Z_i` is the entropy dissipation. This is the
critical energy inequality in the proof of `lem:pv-stokes`.
-/

public section

open CKN

open MeasureTheory Set Filter
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The components of the derivative of the regularized critical test. -/
theorem heatRegTest_fderiv_apply_component {η : ℝ} (hη : 0 < η) (v a : Vec3) (i : Fin 3) :
    fderiv ℝ (heatRegTest η) v a i =
      (heatRegSq η v ^ (1 / 2 : ℝ) - η) * a i +
        heatRegSq η v ^ (-(1 / 2 : ℝ)) * heatRegDot v a * v i := by
  have hdiff : DifferentiableAt ℝ (heatRegTest η) v :=
    ((heatRegTest_contDiff hη).differentiable (by simp)) v
  rw [← heatRegTest_fderiv hη v a i, fderiv_apply hdiff i]
  rfl

/-- The pointwise absorption of the forcing: for the regularized critical
test, `-(∑_i (T'(v) a)_i (a_i + G_i)) ≤ -½ ∑_i (T'(v) a)_i a_i + |v| |G|²`. -/
theorem heatRegTest_forcing_absorb {η : ℝ} (hη : 0 < η) (v a G : Vec3) :
    -(∑ i : Fin 3, fderiv ℝ (heatRegTest η) v a i * (a i + G i)) ≤
      -(1 / 2 : ℝ) * (∑ i : Fin 3, fderiv ℝ (heatRegTest η) v a i * a i) +
        vec3EuclideanNorm v * ∑ i : Fin 3, G i ^ 2 := by
  set r : ℝ := heatRegSq η v ^ (1 / 2 : ℝ) with hr
  set ρ : ℝ := heatRegSq η v ^ (-(1 / 2 : ℝ)) with hρ
  set n : ℝ := vec3EuclideanNorm v with hn
  set d : ℝ := heatRegDot v a with hd
  set e : ℝ := heatRegDot v G with he
  set Sa : ℝ := ∑ i : Fin 3, a i ^ 2 with hSa
  set SG : ℝ := ∑ i : Fin 3, G i ^ 2 with hSG
  set aG : ℝ := ∑ i : Fin 3, a i * G i with haG
  have hα : 0 ≤ r - η := sub_nonneg.mpr (heatReg_root_ge_eta hη v)
  have hαn : r - η ≤ n := heatReg_root_sub_eta_le_norm hη v
  have hrpos : 0 < r := Real.rpow_pos_of_pos (heatRegSq_pos hη v) _
  have hρr : ρ = r⁻¹ := heatReg_inv_rpow_half hη v
  have hρ0 : 0 ≤ ρ := by rw [hρr]; exact inv_nonneg.mpr hrpos.le
  have hn0 : 0 ≤ n := vec3EuclideanNorm_nonneg v
  have hn2 : n ^ 2 = ∑ i : Fin 3, v i ^ 2 := vec3EuclideanNorm_sq v
  have hr2 : r ^ 2 = n ^ 2 + η ^ 2 := by
    rw [hr, ← Real.sqrt_eq_rpow, Real.sq_sqrt (heatRegSq_pos hη v).le, hn2]
    rfl
  have hnr : n ≤ r := by nlinarith only [hr2, hrpos, hn0, sq_nonneg η]
  have hρn : ρ * n ^ 2 ≤ n := by
    rw [hρr, inv_mul_le_iff₀ hrpos]
    nlinarith only [hnr, hn0]
  have he2 : e ^ 2 ≤ n ^ 2 * SG := by
    rw [hn2, he]
    simpa [heatRegDot] using
      (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3)) (fun i => v i)
        (fun i => G i))
  have haG2 : -aG ≤ (1 / 2 : ℝ) * Sa + (1 / 2 : ℝ) * SG := by
    have h0 : 0 ≤ ∑ i : Fin 3, (a i + G i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hexp : ∑ i : Fin 3, (a i + G i) ^ 2 = Sa + 2 * aG + SG := by
      simp only [hSa, hSG, haG, add_sq, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    linarith only [h0, hexp]
  have hcomp (i : Fin 3) : fderiv ℝ (heatRegTest η) v a i = (r - η) * a i + ρ * d * v i :=
    heatRegTest_fderiv_apply_component hη v a i
  have hsum1 : ∑ i : Fin 3, fderiv ℝ (heatRegTest η) v a i * (a i + G i) =
      (r - η) * Sa + (r - η) * aG + ρ * d * d + ρ * d * e := by
    simp only [hcomp, hSa, haG, hd, he, heatRegDot]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsum2 : ∑ i : Fin 3, fderiv ℝ (heatRegTest η) v a i * a i =
      (r - η) * Sa + ρ * d * d := by
    simp only [hcomp, hSa, hd, heatRegDot]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum1, hsum2]
  have hde : -(d * e) ≤ (1 / 2 : ℝ) * d ^ 2 + (1 / 2 : ℝ) * e ^ 2 := by
    nlinarith only [sq_nonneg (d + e)]
  have hSG0 : 0 ≤ SG := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h1 : -((r - η) * aG) ≤ (r - η) * ((1 / 2 : ℝ) * Sa + (1 / 2 : ℝ) * SG) := by
    nlinarith only [mul_le_mul_of_nonneg_left haG2 hα]
  have h2 : -(ρ * d * e) ≤ ρ * ((1 / 2 : ℝ) * d ^ 2 + (1 / 2 : ℝ) * e ^ 2) := by
    nlinarith only [mul_le_mul_of_nonneg_left hde hρ0]
  have h3 : (r - η) * SG ≤ n * SG := mul_le_mul_of_nonneg_right hαn hSG0
  have h4 : ρ * e ^ 2 ≤ n * SG := by
    calc
      ρ * e ^ 2 ≤ ρ * (n ^ 2 * SG) := mul_le_mul_of_nonneg_left he2 hρ0
      _ = (ρ * n ^ 2) * SG := by ring
      _ ≤ n * SG := mul_le_mul_of_nonneg_right hρn hSG0
  nlinarith only [h1, h2, h3, h4]

/-- Pointwise `(1 + |x|)^{-3}` bounds for the response, its spatial gradient,
the tensor, and a `C¹` test vanishing at the origin together with its
derivative along the gradient. -/
theorem response_atom_bounds {g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hg : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (g i j)) (hgc : ∀ i j, HasCompactSupport (g i j))
    {T : Vec3 → Vec3} (hT : ContDiff ℝ 1 T) (hT0 : T 0 = 0) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (p : Vec3 × ℝ) (i j : Fin 3),
      |responseVec g p i| ≤ A / (1 + vec3EuclideanNorm p.1) ^ 3 ∧
      |responseGrad g j p i| ≤ A / (1 + vec3EuclideanNorm p.1) ^ 3 ∧
      |g i j p| ≤ A / (1 + vec3EuclideanNorm p.1) ^ 3 ∧
      |T (responseVec g p) i| ≤ A / (1 + vec3EuclideanNorm p.1) ^ 3 ∧
      |fderiv ℝ T (responseVec g p) (responseGrad g j p) i| ≤
        A / (1 + vec3EuclideanNorm p.1) ^ 3 := by
  obtain ⟨M, hM, hdec⟩ := vecTimeDiv_response_decay hg hgc
  obtain ⟨L, hL, hLb⟩ := exists_linear_bound_of_contDiff hT hT0 M
  refine ⟨L * M + M, by positivity, fun p i j => ?_⟩
  set w : ℝ := (1 + vec3EuclideanNorm p.1) ^ 3
  have hw : 1 ≤ w := one_le_pow₀ (by
    have := vec3EuclideanNorm_nonneg p.1
    linarith only [this])
  have hwpos : 0 < w := lt_of_lt_of_le zero_lt_one hw
  have hMA : M / w ≤ (L * M + M) / w :=
    div_le_div_of_nonneg_right (by nlinarith only [hL, hM]) hwpos.le
  have hLA : L * (M / w) ≤ (L * M + M) / w := by
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (by nlinarith only [hL, hM]) hwpos.le
  have hZnorm : ‖responseVec g p‖ ≤ M / w :=
    (pi_norm_le_iff_of_nonneg (div_nonneg hM hwpos.le)).2 fun k => by
      rw [Real.norm_eq_abs]
      exact (hdec k k k p).1
  have hZle : ‖responseVec g p‖ ≤ M := hZnorm.trans (div_le_self hM hw)
  have hGnorm : ‖responseGrad g j p‖ ≤ M / w :=
    (pi_norm_le_iff_of_nonneg (div_nonneg hM hwpos.le)).2 fun k => by
      rw [Real.norm_eq_abs]
      exact (hdec k j j p).2.1
  refine ⟨(hdec i i i p).1.trans hMA, (hdec i j j p).2.1.trans hMA,
    (hdec i j j p).2.2.2.2.1.trans hMA, ?_, ?_⟩
  · rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm _ i).trans ((hLb _ hZle).1.trans
      ((mul_le_mul_of_nonneg_left hZnorm hL).trans hLA))
  · rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm _ i).trans ((ContinuousLinearMap.le_opNorm _ _).trans
      ((mul_le_mul (hLb _ hZle).2 hGnorm (norm_nonneg _) hL).trans hLA))

/-- Continuity of the response, its gradient, and the derivative of a `C¹` test
along the gradient. -/
theorem response_continuity {g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hg : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (g i j)) (hgc : ∀ i j, HasCompactSupport (g i j))
    {T : Vec3 → Vec3} (hT : ContDiff ℝ 1 T) :
    Continuous (responseVec g) ∧ (∀ j, Continuous (responseGrad g j)) ∧
      ∀ j, Continuous (fun p => fderiv ℝ T (responseVec g p) (responseGrad g j p)) := by
  have hU (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (causalHeatConv (vecTimeDiv g i)) :=
    causalHeatConv_contDiff (vecTimeDiv_contDiff hg i) (vecTimeDiv_hasCompactSupport hgc i)
  have hZ : Continuous (responseVec g) := continuous_pi fun k => (hU k).continuous
  have hGr (j : Fin 3) : Continuous (responseGrad g j) := continuous_pi fun k =>
    ((hU k).continuous_fderiv (by simp)).clm_apply continuous_const
  exact ⟨hZ, hGr, fun j => ((hT.continuous_fderiv one_ne_zero).comp hZ).clm_apply (hGr j)⟩

end ESS

end

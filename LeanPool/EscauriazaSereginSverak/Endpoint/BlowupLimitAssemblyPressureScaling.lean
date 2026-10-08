/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceBasic
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Spatial rescaling of the pressure Poisson identity

The distributional identity -Δ P = ∂_i ∂_j F_ij is invariant under the
spatial rescaling P ↦ r² P(x₀ + r ·), F ↦ r² F(x₀ + r ·). This is the
scaling identity p₁^k = P[v^k ⊗ v^k] used in `prop:blowup-limit`.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Change of variables along a positive spatial dilation and translation. -/
theorem blowupLimitAssemblyPressure_integral_comp_affine
    (g : Vec3 → ℝ) (x₀ : Vec3) {r : ℝ} (hr : 0 < r) :
    ∫ x : Vec3, g (x₀ + r • x) = (r ^ 3)⁻¹ * ∫ y : Vec3, g y := by
  have h := Measure.integral_comp_smul (μ := (volume : Measure Vec3))
    (fun y : Vec3 => g (x₀ + y)) r
  rw [Module.finrank_fin_fun, integral_add_left_eq_self] at h
  rw [h, smul_eq_mul, abs_of_pos (by positivity)]

/-- First coordinate derivatives along the inverse affine map. -/
theorem blowupLimitAssemblyPressure_spatialDeriv_affine
    (g : Vec3 → ℝ) (hg : Differentiable ℝ g) (x₀ : Vec3) (r : ℝ)
    (j : Fin 3) (y : Vec3) :
    CKN.spatialDeriv (fun y => g (r⁻¹ • (y - x₀))) j y =
      r⁻¹ * CKN.spatialDeriv g j (r⁻¹ • (y - x₀)) := by
  have hA : HasFDerivAt (fun y : Vec3 => r⁻¹ • (y - x₀))
      (r⁻¹ • ContinuousLinearMap.id ℝ Vec3) y := by
    simpa using ((hasFDerivAt_id (𝕜 := ℝ) y).sub_const x₀).const_smul r⁻¹
  have hcomp := ((hg (r⁻¹ • (y - x₀))).hasFDerivAt.comp y hA).fderiv
  unfold CKN.spatialDeriv
  change (fderiv ℝ (g ∘ fun y : Vec3 => r⁻¹ • (y - x₀)) y) (basisVec j) = _
  rw [hcomp]
  simp

/-- A constant factor passes through a coordinate derivative. -/
theorem blowupLimitAssemblyPressure_spatialDeriv_const_mul
    (G : Vec3 → ℝ) {y : Vec3} (hG : DifferentiableAt ℝ G y) (c : ℝ) (i : Fin 3) :
    CKN.spatialDeriv (fun y => c * G y) i y = c * CKN.spatialDeriv G i y := by
  unfold CKN.spatialDeriv
  rw [fderiv_const_mul hG]
  simp

/-- Second coordinate derivatives along the inverse affine map. -/
theorem blowupLimitAssemblyPressure_mixedSecond_affine
    (g : Vec3 → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x₀ : Vec3) (r : ℝ)
    (i j : Fin 3) (y : Vec3) :
    CKN.mixedSecond (fun y => g (r⁻¹ • (y - x₀))) i j y =
      r⁻¹ ^ 2 * CKN.mixedSecond g i j (r⁻¹ • (y - x₀)) := by
  have hdiff : Differentiable ℝ g := hg.differentiable (by simp)
  have hgj : ContDiff ℝ (⊤ : ℕ∞) (CKN.spatialDeriv g j) :=
    CKN.contDiff_spatialDeriv_smooth hg j
  have hgjd : Differentiable ℝ (CKN.spatialDeriv g j) := hgj.differentiable (by simp)
  have hfirst : CKN.spatialDeriv (fun y => g (r⁻¹ • (y - x₀))) j =
      fun y => r⁻¹ * CKN.spatialDeriv g j (r⁻¹ • (y - x₀)) := by
    funext y
    exact blowupLimitAssemblyPressure_spatialDeriv_affine g hdiff x₀ r j y
  have hAd : Differentiable ℝ (fun y : Vec3 => r⁻¹ • (y - x₀)) :=
    (differentiable_id.sub_const x₀).const_smul r⁻¹
  have hinner : DifferentiableAt ℝ
      (fun y => CKN.spatialDeriv g j (r⁻¹ • (y - x₀))) y :=
    (hgjd.comp hAd) y
  unfold CKN.mixedSecond
  rw [hfirst, blowupLimitAssemblyPressure_spatialDeriv_const_mul _ hinner,
    blowupLimitAssemblyPressure_spatialDeriv_affine (CKN.spatialDeriv g j) hgjd x₀ r i y]
  ring

/-- The spatial Laplacian along the inverse affine map. -/
theorem blowupLimitAssemblyPressure_laplacian_affine
    (g : Vec3 → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x₀ : Vec3) (r : ℝ)
    (y : Vec3) :
    CKN.spatialLaplacian (fun y => g (r⁻¹ • (y - x₀))) y =
      r⁻¹ ^ 2 * CKN.spatialLaplacian g (r⁻¹ • (y - x₀)) := by
  unfold CKN.spatialLaplacian
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact blowupLimitAssemblyPressure_mixedSecond_affine g hg x₀ r i i y

/-- The pressure Poisson identity on a time slice is invariant under the
spatial parabolic rescaling. -/
theorem blowupLimitAssemblyPressure_poisson_rescale
    {P : Vec3 → ℝ} {F : Fin 3 → Fin 3 → Vec3 → ℝ}
    (h : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, P x * (-CKN.spatialLaplacian ψ x) =
        ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, F i j x * CKN.mixedSecond ψ i j x)
    (x₀ : Vec3) {r : ℝ} (hr : 0 < r) :
    ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, r ^ 2 * P (x₀ + r • x) * (-CKN.spatialLaplacian ψ x) =
        ∑ i : Fin 3, ∑ j : Fin 3,
          ∫ x, r ^ 2 * F i j (x₀ + r • x) * CKN.mixedSecond ψ i j x := by
  intro ψ hψ hψc
  have hr0 : r ≠ 0 := hr.ne'
  let A : Vec3 ≃ₜ Vec3 := (Homeomorph.subRight x₀).trans
    (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr0))
  have hAeq : ⇑A = fun y : Vec3 => r⁻¹ • (y - x₀) := by
    funext y
    rfl
  let ψ' : Vec3 → ℝ := fun y => ψ (r⁻¹ • (y - x₀))
  have hψ'eq : ψ' = ψ ∘ A := by rw [hAeq]; rfl
  have hψ' : ContDiff ℝ (⊤ : ℕ∞) ψ' := by
    rw [hψ'eq]
    exact hψ.comp (by rw [hAeq]; fun_prop)
  have hψ'c : HasCompactSupport ψ' := by
    rw [hψ'eq]
    exact hψc.comp_homeomorph A
  have hkey : ∀ x : Vec3, r⁻¹ • ((x₀ + r • x) - x₀) = x := by
    intro x
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr0, one_smul]
  have hmain := h ψ' hψ' hψ'c
  have hr3 : (r ^ 3)⁻¹ * r ^ 4 = r := by
    field_simp
  have hLHS : ∫ x, r ^ 2 * P (x₀ + r • x) * (-CKN.spatialLaplacian ψ x) =
      r * ∫ y, P y * (-CKN.spatialLaplacian ψ' y) := by
    let G : Vec3 → ℝ := fun y => P y * (-CKN.spatialLaplacian ψ' y)
    have hpt : ∀ x : Vec3, r ^ 2 * P (x₀ + r • x) * (-CKN.spatialLaplacian ψ x) =
        r ^ 4 * G (x₀ + r • x) := by
      intro x
      simp only [G, ψ']
      rw [blowupLimitAssemblyPressure_laplacian_affine ψ hψ x₀ r, hkey]
      field_simp
    have hcv := blowupLimitAssemblyPressure_integral_comp_affine G x₀ hr
    calc
      ∫ x, r ^ 2 * P (x₀ + r • x) * (-CKN.spatialLaplacian ψ x) =
          ∫ x, r ^ 4 * G (x₀ + r • x) := by
        congr 1
        funext x
        exact hpt x
      _ = r ^ 4 * ∫ x, G (x₀ + r • x) := integral_const_mul _ _
      _ = r * ∫ y, G y := by rw [hcv, ← mul_assoc, mul_comm (r ^ 4), hr3]
  have hRHS : ∀ i j : Fin 3,
      ∫ x, r ^ 2 * F i j (x₀ + r • x) * CKN.mixedSecond ψ i j x =
        r * ∫ y, F i j y * CKN.mixedSecond ψ' i j y := by
    intro i j
    let G : Vec3 → ℝ := fun y => F i j y * CKN.mixedSecond ψ' i j y
    have hpt : ∀ x : Vec3, r ^ 2 * F i j (x₀ + r • x) * CKN.mixedSecond ψ i j x =
        r ^ 4 * G (x₀ + r • x) := by
      intro x
      simp only [G, ψ']
      rw [blowupLimitAssemblyPressure_mixedSecond_affine ψ hψ x₀ r, hkey]
      field_simp
    have hcv := blowupLimitAssemblyPressure_integral_comp_affine G x₀ hr
    calc
      ∫ x, r ^ 2 * F i j (x₀ + r • x) * CKN.mixedSecond ψ i j x =
          ∫ x, r ^ 4 * G (x₀ + r • x) := by
        congr 1
        funext x
        exact hpt x
      _ = r ^ 4 * ∫ x, G (x₀ + r • x) := integral_const_mul _ _
      _ = r * ∫ y, G y := by rw [hcv, ← mul_assoc, mul_comm (r ^ 4), hr3]
  rw [hLHS, hmain, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hRHS i j]

end ESS

end

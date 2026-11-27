/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.CutoffFourierIntegrability
public import LeanPool.VacuumBellSeparation.FreeField.IteratedDerivativeIntegral

/-!
# Identification of the actual cutoff Fourier integral

Dominated differentiation identifies every weighted-derivative coordinate of
the Banach integral with the corresponding coordinate of `cutoffSchwartzFourier χ ψ`. The
actual Banach factorization of a tempered distribution then justifies moving
that distribution through the integral. This is an identity for the existing
Schwartz Fourier transform and the existing distribution, not a new model.
-/

@[expose] public section

open MeasureTheory Filter
open scoped SchwartzMap FourierTransform BoundedContinuousFunction


noncomputable section

namespace VacuumBellSeparation

/-- The canonical `ContinuousENorm (∀ i, E i)` instance used in the construction. -/
abbrev cutoffIntegralFinitePiContinuousENorm
    {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] :
    ContinuousENorm (∀ i, E i) := inferInstance

/-- Continuity of the extended norm in the space used to integrate the derivatives. -/
local instance cutoffDerivativeContinuousENorm (s : Finset (ℕ × ℕ)) :
    ContinuousENorm (SchwartzDerivativeBanach s) :=
  cutoffIntegralFinitePiContinuousENorm (ι := s)
    (E := fun i : s => EuclideanSpace ℝ (Fin 3) →ᵇ
      ContinuousMultilinearMap ℝ (fun _ : Fin i.val.2 => EuclideanSpace ℝ (Fin 3)) ℂ)

/-- The canonical `NormedSpace ℂ (∀ i, E i)` instance used in the construction. -/
abbrev cutoffIntegralFinitePiNormedSpace
    {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)] :
    NormedSpace ℂ (∀ i, E i) := inferInstance

/-- Complex normed-space structure used by the derivative-valued Fourier integral. -/
local instance cutoffDerivativeComplexNormedSpace (s : Finset (ℕ × ℕ)) :
    NormedSpace ℂ (SchwartzDerivativeBanach s) :=
  cutoffIntegralFinitePiNormedSpace (ι := s)
    (E := fun i : s => EuclideanSpace ℝ (Fin 3) →ᵇ
      ContinuousMultilinearMap ℝ (fun _ : Fin i.val.2 => EuclideanSpace ℝ (Fin 3)) ℂ)


/-- The actual Schwartz product of the cutoff with the Fourier transform. -/
noncomputable def cutoffSchwartzFourier
    (χ ψ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ :=
  SchwartzMap.smulLeftCLM ℂ χ (𝓕 ψ)

@[simp] theorem cutoffSchwartzFourier_apply
    (χ ψ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    cutoffSchwartzFourier χ ψ x = χ x * (𝓕 ψ) x :=
  SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth (𝓕 ψ) x

theorem continuous_iteratedFDeriv_cutoffFourierKernel
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (hχ : HasCompactSupport χ)
    (j : ℕ) (x : EuclideanSpace ℝ (Fin 3)) :
    Continuous (fun p => iteratedFDeriv ℝ j (cutoffFourierKernel χ p) x) := by
  have h := (BoundedContinuousFunction.evalCLM ℂ x).continuous.comp
    (continuous_cutoffFourierKernel_weightedDerivative χ hχ 0 j)
  simpa only [Function.comp_def, BoundedContinuousFunction.evalCLM_apply,
    schwartzWeightedDerivative_apply,
    pow_zero, one_smul] using h

theorem integral_cutoffFourierKernel_apply
    (ψ χ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    (∫ p, ψ p • cutoffFourierKernel χ p x) = (cutoffSchwartzFourier χ ψ) x := by
  rw [cutoffSchwartzFourier_apply]
  change (∫ p, ψ p * cutoffFourierKernel χ p x) = χ x * (𝓕 ψ) x
  rw [SchwartzMap.fourier_coe, Real.fourier_eq, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by
    simp only [cutoffFourierKernel_apply, spatialFourierCharacter, Circle.smul_def, smul_eq_mul]
    ring

/-- Actual differentiation under the cutoff Fourier integral at every order. -/
theorem iteratedFDeriv_cutoffFourier_integral
    (ψ χ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (hχ : HasCompactSupport χ)
    (j : ℕ) (x : EuclideanSpace ℝ (Fin 3)) :
    iteratedFDeriv ℝ j (cutoffSchwartzFourier χ ψ) x =
      ∫ p, ψ p • iteratedFDeriv ℝ j (cutoffFourierKernel χ p) x := by
  let f := fun p y : EuclideanSpace ℝ (Fin 3) => ψ p • cutoffFourierKernel χ p y
  have hf (p : EuclideanSpace ℝ (Fin 3)) : ContDiff ℝ (⊤ : ℕ∞) (f p) :=
    (cutoffFourierKernel χ p).smooth ⊤ |>.const_smul (ψ p)
  have hfd (p y : EuclideanSpace ℝ (Fin 3)) (n : ℕ) :
      iteratedFDeriv ℝ n (f p) y = ψ p • iteratedFDeriv ℝ n (cutoffFourierKernel χ p) y :=
    iteratedFDeriv_const_smul_apply' ((cutoffFourierKernel χ p).smooth n).contDiffAt
  have hmeas (n : ℕ) (y : EuclideanSpace ℝ (Fin 3)) :
      AEStronglyMeasurable (fun p => iteratedFDeriv ℝ n (f p) y) volume := by
    simp_rw [hfd]
    exact (ψ.continuous.smul (continuous_iteratedFDeriv_cutoffFourierKernel χ hχ n
      y)).aestronglyMeasurable
  let b := fun n p => ‖ψ p‖ * cutoffFourierSeminormBound χ 0 n p
  have hb (n : ℕ) (p y : EuclideanSpace ℝ (Fin 3)) :
      ‖iteratedFDeriv ℝ n (f p) y‖ ≤ b n p := by
    rw [hfd, norm_smul]
    exact mul_le_mul_of_nonneg_left
      (((cutoffFourierKernel χ p).norm_iteratedFDeriv_le_seminorm ℂ n y).trans
        (seminorm_cutoffFourierKernel_le χ p 0 n)) (norm_nonneg _)
  have h := iteratedFDeriv_integral_of_global_bounds volume f hf hmeas b hb
    (fun n => integrable_norm_mul_cutoffFourierSeminormBound ψ χ 0 n) j x
  have heq : (fun y => ∫ p, f p y) = (cutoffSchwartzFourier χ ψ) :=
    funext (integral_cutoffFourierKernel_apply ψ χ)
  simpa only [heq, hfd] using h

/-- The genuine Banach integral equals the weighted derivatives of the actual
Schwartz cutoff Fourier transform. -/
theorem integral_schwartzDerivativeMap_cutoffFourierKernel
    (s : Finset (ℕ × ℕ))
    (ψ χ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (hχ : HasCompactSupport χ) :
    (∫ p, ψ p • schwartzDerivativeMap s (cutoffFourierKernel χ p)) =
      schwartzDerivativeMap s (cutoffSchwartzFourier χ ψ) := by
  have hint : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ψ p • schwartzDerivativeMap s (cutoffFourierKernel χ p)) volume :=
    integrable_schwartzDerivativeMap_cutoffFourierKernel s ψ χ hχ
  funext i
  apply BoundedContinuousFunction.ext
  intro x
  let E : SchwartzDerivativeBanach s →L[ℂ]
      ContinuousMultilinearMap ℝ (fun _ : Fin i.val.2 => EuclideanSpace ℝ (Fin 3)) ℂ :=
    (BoundedContinuousFunction.evalCLM ℂ x).comp
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun a : s =>
      BoundedContinuousFunction (EuclideanSpace ℝ (Fin 3)) (ContinuousMultilinearMap ℝ
        (fun _ : Fin a.val.2 => EuclideanSpace ℝ (Fin 3)) ℂ)) i)
  have h := ContinuousLinearMap.integral_comp_comm (μ := volume)
    (E := SchwartzDerivativeBanach s)
    (φ := fun p : EuclideanSpace ℝ (Fin 3) =>
      ψ p • schwartzDerivativeMap s (cutoffFourierKernel χ p)) E hint
  calc
    _ = ∫ p, ‖x‖ ^ i.val.1 •
        (ψ p • iteratedFDeriv ℝ i.val.2 (cutoffFourierKernel χ p) x) := by
      change E (∫ p, ψ p • schwartzDerivativeMap s (cutoffFourierKernel χ p)) = _
      rw [← h]
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by
        change E (ψ p • schwartzDerivativeMap s (cutoffFourierKernel χ p)) =
          ‖x‖ ^ i.val.1 • (ψ p • iteratedFDeriv ℝ i.val.2 (cutoffFourierKernel χ p) x)
        rw [map_smul]
        change ψ p • (‖x‖ ^ i.val.1 •
          iteratedFDeriv ℝ i.val.2 (cutoffFourierKernel χ p) x) = _
        exact smul_comm _ _ _
    _ = ‖x‖ ^ i.val.1 •
        (∫ p, ψ p • iteratedFDeriv ℝ i.val.2 (cutoffFourierKernel χ p) x) := integral_smul _ _
    _ = _ := by
      rw [← iteratedFDeriv_cutoffFourier_integral ψ χ hχ]
      rfl

/-- Actual distribution/Fourier interchange through the proved Banach integral identity. -/
theorem distribution_cutoffFourier_integral
    (T : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ)
    (ψ χ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (hχ : HasCompactSupport χ) :
    T (cutoffSchwartzFourier χ ψ) = ∫ p, ψ p * T (cutoffFourierKernel χ p) := by
  obtain ⟨s, L, hL⟩ := temperedDistribution_banach_factorization T
  have hint : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ψ p • schwartzDerivativeMap s (cutoffFourierKernel χ p)) volume :=
    integrable_schwartzDerivativeMap_cutoffFourierKernel s ψ χ hχ
  calc
    _ = L (schwartzDerivativeMap s (cutoffSchwartzFourier χ ψ)) := (hL _).symm
    _ = L (∫ p, ψ p • schwartzDerivativeMap s (cutoffFourierKernel χ p)) := by
      rw [integral_schwartzDerivativeMap_cutoffFourierKernel s ψ χ hχ]
    _ = ∫ p, L (ψ p • schwartzDerivativeMap s (cutoffFourierKernel χ p)) :=
      (ContinuousLinearMap.integral_comp_comm (μ := volume)
        (E := SchwartzDerivativeBanach s)
        (φ := fun p : EuclideanSpace ℝ (Fin 3) =>
          ψ p • schwartzDerivativeMap s (cutoffFourierKernel χ p)) L hint).symm
    _ = _ := integral_congr_ae (Eventually.of_forall fun p => by
      change L (ψ p • schwartzDerivativeMap s (cutoffFourierKernel χ p)) =
        ψ p * T (cutoffFourierKernel χ p)
      rw [map_smul, hL, smul_eq_mul])

end VacuumBellSeparation

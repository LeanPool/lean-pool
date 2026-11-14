/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.OUBackwardDerivative

/-!
# The time-dependent OU interpolation derivative

The outer backward-time generator cancels the spatial generator of the inner
observable. Bounds here are ordinary space-time regularity bounds; all
Gaussian integrability and generator identities are proved.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open EhrhardGaussian.Gaussian (coordinateDerivative standardGaussianMeasure)
open scoped Topology

namespace EhrhardGaussian.Ehrhard

/-- A space–time directional derivative splits into its time and spatial parts. -/
theorem fderiv_spaceTime_split {n : ℕ} {F : ℝ × (Fin n → ℝ) → ℝ}
    {t : ℝ} {y : Fin n → ℝ} (hF : DifferentiableAt ℝ F (t, y)) (v : Fin n → ℝ) :
    fderiv ℝ F (t, y) (1, v) = fderiv ℝ F (t, y) (1, 0) +
      fderiv ℝ (fun z => F (t, z)) y v := by
  have h := hF.hasFDerivAt.comp y (hasFDerivAt_prodMk_right t y)
  dsimp only [Function.comp_def] at h
  rw [h.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    ← map_add]
  congr 1
  ext <;> simp only [Prod.fst_add, Prod.snd_add, zero_add, add_zero]

/-- The time derivative is the full derivative evaluated in the unit time direction. -/
theorem deriv_spaceTime_left {n : ℕ} {F : ℝ × (Fin n → ℝ) → ℝ}
    {t : ℝ} {y : Fin n → ℝ} (hF : DifferentiableAt ℝ F (t, y)) :
    deriv (fun s => F (s, y)) t = fderiv ℝ F (t, y) (1, 0) := by
  have h := hF.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id' t).prodMk (hasDerivAt_const t y))
  exact h.deriv

/-- The sufficient local regularity form of the time-dependent OU derivative:
`d_s P_(T-s) F_s = P_(T-s) (∂_s F_s - L F_s)`. -/
theorem hasDerivAt_ouSpaceTimeAverage_generator {n : ℕ} {U : Set ℝ} (hU : IsOpen U)
    {t T : ℝ} (ht : t ∈ U) (hT : ∀ s ∈ U, s < T)
    {F : ℝ × (Fin n → ℝ) → ℝ} (hF : ContDiffOn ℝ 1 F (U ×ˢ univ))
    (hsection : HasPolynomiallyBoundedSecondCoordinateDerivatives (fun y => F (t, y)))
    {C : ℝ} (hC : 0 ≤ C) {N : ℕ}
    (hbound : ∀ s ∈ U, ∀ y : Fin n → ℝ,
      |F (s, y)| + ‖fderiv ℝ F (s, y)‖ ≤ C * (1 + ‖y‖) ^ N)
    (x : Fin n → ℝ) :
    HasDerivAt (ouSpaceTimeAverage F T x)
      (ouAverage (fun y => fderiv ℝ F (t, y) (1, 0) -
        ouGenerator (fun z => F (t, z)) y) x (T - t)) t := by
  let e := Real.exp (t - T)
  let r := Real.exp (2 * (t - T))
  let b := Real.sqrt (1 - r)
  let w : (Fin n → ℝ) → (Fin n → ℝ) := fun z => e • x + b • z
  let G : (Fin n → ℝ) → ℝ := fun y => F (t, y)
  let P : (Fin n → ℝ) → ℝ := fun y => fderiv ℝ F (t, y) (1, 0)
  have htime : 0 < T - t := sub_pos.mpr (hT t ht)
  have he : -(T - t) = t - T := by ring
  have hr : -2 * (T - t) = 2 * (t - T) := by ring
  have hopen : IsOpen (U ×ˢ (univ : Set (Fin n → ℝ))) := hU.prod isOpen_univ
  have hdiff (y : Fin n → ℝ) : DifferentiableAt ℝ F (t, y) :=
    (hF.contDiffAt (hopen.mem_nhds ⟨ht, mem_univ _⟩)).differentiableAt_one
  have hPcont : Continuous P :=
    ((hF.continuousOn_fderiv_of_isOpen hopen le_rfl).comp_continuous
      (by fun_prop : Continuous (fun y : Fin n → ℝ => (t, y)))
      (fun _ => ⟨ht, mem_univ _⟩)).clm_apply continuous_const
  have hPbound (y : Fin n → ℝ) : |P y| ≤ C * (1 + ‖y‖) ^ N := by
    calc
      |P y| ≤ ‖fderiv ℝ F (t, y)‖ * ‖((1 : ℝ), (0 : Fin n → ℝ))‖ :=
        (fderiv ℝ F (t, y)).le_opNorm _
      _ = ‖fderiv ℝ F (t, y)‖ := by rw [Prod.norm_mk, norm_one, norm_zero, max_eq_left zero_le_one,
        mul_one]
      _ ≤ C * (1 + ‖y‖) ^ N :=
        (le_add_of_nonneg_left (abs_nonneg _)).trans (hbound t ht y)
  have hPint := integrable_shift_of_polynomial_bound hPcont.measurable hC hPbound (e • x) b
  have hgenint := integrable_shift_ouGenerator hsection (e • x) b
  have hxint := integrable_shift_fderiv_fixed hsection (e • x) x b
  have hzint := integrable_shift_fderiv_id hsection (e • x) b
  have hQint : Integrable (fun z => fderiv ℝ G (w z) (-e • x + (r / b) • z))
      (standardGaussianMeasure n) := by
    apply ((hxint.const_mul (-e)).add (hzint.const_mul (r / b))).congr
    exact ae_of_all _ fun z => by
      change (-e) * fderiv ℝ G (w z) x + (r / b) * fderiv ℝ G (w z) z = _
      dsimp only
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hG₁ := hasPolynomiallyBoundedCoordinateDerivatives_of_second hsection
  have hgen : ouAverage (ouGenerator G) x (T - t) =
      ∫ z, fderiv ℝ G (w z) (-e • x + (r / b) • z) ∂standardGaussianMeasure n := by
    have h := (hasDerivAt_ouAverage_generator hsection x htime).unique
      (hasDerivAt_ouAverage hG₁ x htime)
    simpa only [he, hr] using h
  have h := hasDerivAt_ouSpaceTimeAverage hU ht hT hF hC hbound x
  convert h using 1
  rw [ouAverage, he, hr]
  change (∫ z, P (w z) - ouGenerator G (w z) ∂standardGaussianMeasure n) =
    ∫ z, fderiv ℝ F (t, w z) (1, e • x + (-r / b) • z) ∂standardGaussianMeasure n
  have hsplit (z : Fin n → ℝ) : fderiv ℝ F (t, w z) (1, e • x + (-r / b) • z) =
      P (w z) - fderiv ℝ G (w z) (-e • x + (r / b) • z) := by
    rw [fderiv_spaceTime_split (hdiff (w z))]
    change P (w z) + fderiv ℝ G (w z) (e • x + (-r / b) • z) = _
    have hv : e • x + (-r / b) • z = -(-e • x + (r / b) • z) := by
      simp only [neg_add, neg_smul, neg_neg, neg_div]
    rw [hv, map_neg, sub_eq_add_neg]
  simp_rw [hsplit]
  rw [integral_sub hPint hgenint, integral_sub hPint hQint]
  congr 1
  simpa only [ouAverage, he, hr] using hgen

end EhrhardGaussian.Ehrhard

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.OUInitialContinuity
public import LeanPool.EhrhardGaussian.Ehrhard.CompactQuantileBounds

/-! # Preserving a strict quantile gap under small initial smoothing -/

@[expose] public noncomputable section

open Set

namespace EhrhardGaussian.Ehrhard

/-- A strict quantile gap persists for a positive Ornstein–Uhlenbeck averaging time under a
generator bound. -/
theorem exists_ou_quantile_gap {n k : ℕ} {f : Fin k → (Fin n → ℝ) → ℝ}
    (hf : ∀ i, HasPolynomiallyBoundedSecondCoordinateDerivatives (f i))
    {a b M η : ℝ} (ha : 0 < a) (hb : b < 1) (hM : 0 ≤ M) (hη : 0 < η)
    (hbound : ∀ i y, f i y ∈ Icc a b) (hgen : ∀ i y, |ouGenerator (f i) y| ≤ M)
    (θ : Fin k → ℝ) (hgap : ∀ y, quantileLinear θ (fun i => f i y) ≤ -η) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y, quantileLinear θ (ouFamily f (ε, y)) ≤ -η / 2 := by
  obtain ⟨L, hL, hLip⟩ := exists_quantileLinear_lipschitz θ ha hb
  let ε := η / (2 * (L * M + 1))
  have hden : 0 < 2 * (L * M + 1) := by positivity
  have hε : 0 < ε := div_pos hη hden
  have heq : 2 * (L * M + 1) * ε = η := by
    dsimp only [ε]
    field_simp
  have hcoeff : L * (M * ε) ≤ η / 2 := by nlinarith only [heq, hε]
  refine ⟨ε, hε, ?_⟩
  intro y
  have hnorm : ‖ouFamily f (ε, y) - (fun i => f i y)‖ ≤ M * ε := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hM hε.le)).mpr
    intro i
    simpa only [ouFamily, Pi.sub_apply, Real.norm_eq_abs] using
      abs_ouAverage_sub_le_generator_bound (hf i)
        (fun z => abs_le_max_abs_abs (hbound i z).1 (hbound i z).2) (hgen i) y hε.le
  have hf₁ := fun i => hasPolynomiallyBoundedCoordinateDerivatives_of_second (hf i)
  have h := hLip (ouFamily f (ε, y)) (fun i => f i y)
    (ouFamily_mem_Icc hf₁ hbound y ε) (fun i => hbound i y)
  have hdiff := (le_abs_self (quantileLinear θ (ouFamily f (ε, y)) - quantileLinear θ (fun i => f i
    y))).trans
    (h.trans (mul_le_mul_of_nonneg_left hnorm hL))
  linarith only [hdiff, hcoeff, hgap y]

end EhrhardGaussian.Ehrhard

end

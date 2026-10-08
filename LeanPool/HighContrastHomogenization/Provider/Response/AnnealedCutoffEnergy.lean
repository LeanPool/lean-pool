/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ResponseCongruence

/-!
# High-contrast homogenization: Provider.Response.AnnealedCutoffEnergy

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The annealed cutoff-energy estimate

The samplewise cutoff-energy estimate keeps the cutoff-weighted child responses
inside the absolute value, because for a single coefficient sample they do not
vanish.  Averaging over a translation invariant law removes them, and what is
left is an estimate for the expectation of the cutoff-weighted energy defect
alone.

This module performs that average.  The expectation of the correction is zero
by the annealed vanishing; the remaining composition is a mean-zero correction
combinator, so the only additional inputs are integrability hypotheses and one
equality saying that the reference coefficient family represents the sample.
The right-hand side is then reduced to expectations of the response, the
partition defect, and the difference energy by an integral form of the
Cauchy-Schwarz inequality.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

noncomputable section

open MeasureTheory Book.Ch05.Section53.JUpperBoundWeakNorms

variable {d : ℕ}

/-! ## Cauchy-Schwarz for the roots of two nonnegative observables -/

/-- **Cauchy-Schwarz for square roots.**  The expectation of a product of square
roots of nonnegative integrable observables is at most the product of the roots
of their expectations. -/
theorem integral_sqrt_mul_sqrt_le_sqrt_mul_sqrt {α : Type*}
    [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfnn : 0 ≤ᵐ[μ] f) (hgnn : 0 ≤ᵐ[μ] g) :
    ∫ x, Real.sqrt (f x) * Real.sqrt (g x) ∂μ ≤
      Real.sqrt (∫ x, f x ∂μ) * Real.sqrt (∫ x, g x ∂μ) := by
  have hpow : ∀ y : ℝ, y ^ (2 : ℝ) = y ^ (2 : ℕ) := by
    intro y
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hfm : AEStronglyMeasurable (fun x => Real.sqrt (f x)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable
  have hgm : AEStronglyMeasurable (fun x => Real.sqrt (g x)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hg.aestronglyMeasurable
  have hfsq : (fun x => Real.sqrt (f x) ^ (2 : ℕ)) =ᵐ[μ] f := by
    filter_upwards [hfnn] with x hx
    exact Real.sq_sqrt hx
  have hgsq : (fun x => Real.sqrt (g x) ^ (2 : ℕ)) =ᵐ[μ] g := by
    filter_upwards [hgnn] with x hx
    exact Real.sq_sqrt hx
  have hfL2 : MemLp (fun x => Real.sqrt (f x)) 2 μ :=
    (memLp_two_iff_integrable_sq hfm).2 (hf.congr hfsq.symm)
  have hgL2 : MemLp (fun x => Real.sqrt (g x)) 2 μ :=
    (memLp_two_iff_integrable_sq hgm).2 (hg.congr hgsq.symm)
  have htwo : ENNReal.ofReal (2 : ℝ) = 2 := by
    simp
  have hpq : Real.HolderConjugate 2 2 :=
    Real.holderConjugate_iff.2 ⟨by norm_num, by norm_num⟩
  have hmain :=
    integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2) hpq
      (f := fun x => Real.sqrt (f x)) (g := fun x => Real.sqrt (g x))
      (Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _)
      (Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _)
      (by rw [htwo]; exact hfL2) (by rw [htwo]; exact hgL2)
  have hfint : ∫ x, Real.sqrt (f x) ^ (2 : ℝ) ∂μ = ∫ x, f x ∂μ := by
    simp only [hpow]
    exact integral_congr_ae hfsq
  have hgint : ∫ x, Real.sqrt (g x) ^ (2 : ℝ) ∂μ = ∫ x, g x ∂μ := by
    simp only [hpow]
    exact integral_congr_ae hgsq
  rw [hfint, hgint] at hmain
  rw [Real.sqrt_eq_rpow (∫ x, f x ∂μ), Real.sqrt_eq_rpow (∫ x, g x ∂μ)]
  simpa using hmain

/-! ## The annealed cutoff-energy estimate -/

end

end Response
end HighContrast
end HCPolySupport

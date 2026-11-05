/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.TailMoments
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.AESummability

/-!
# TailProbability

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The two upper-tail conditions hold almost surely

Both conditions of `TailGauge.lean` are countable statements whose terms have
summable first moments, so Tonelli's theorem gives them almost surely.

* The ascending gradient series on one cube `y + □_n` is summable almost surely
  because its terms have `Γ₂` tails at geometric amplitudes; this is the
  probabilistic content of `(J2)` after the exact scaling law of the shells.
* The quantitative two-leg condition is the same statement for the doubly
  indexed family weighted by `3^{-ℓ}` on the descending leg and `3^{ℓ}` on the
  ascending leg, whose first moments are of order `(3^{γ-1})^{ℓ}` times a
  summable profile in `r`.  Finiteness of the double sum gives one sample
  constant valid at every scale, which is what the growth bound of the field
  needs.

## Main results

* `ae_upperGradBounded` — the ascending series on `y + □_n` is bounded.

## References

* ABK26, `(J2)`, `e.jk.O`, `e.nabla.jk.O`.
-/

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 2. The geometric ascending amplitude -/

private theorem ascendingScale_eq (M : ABKModel d) (n : ℤ) (r : ℕ) :
    (3 : ℝ) ^ (-n) * Real.rpow 3 ((M.gamma - 1) * ((n + (r : ℤ) : ℤ) : ℝ)) =
      ((3 : ℝ) ^ (-n) * Real.rpow 3 ((M.gamma - 1) * (n : ℝ))) *
        Real.rpow 3 (M.gamma - 1) ^ r := by
  have hcast : ((n + (r : ℤ) : ℤ) : ℝ) = (n : ℝ) + (r : ℝ) := by push_cast; ring
  rw [hcast, mul_add, Section4.Provider.BoundsEaL.rpow3_add,
    Section4.Provider.BoundsEaL.rpow3_mul_natCast, mul_assoc]

private theorem rpow3_gamma_sub_one_nonneg (M : ABKModel d) :
    (0 : ℝ) ≤ Real.rpow 3 (M.gamma - 1) :=
  Real.rpow_nonneg (by norm_num) _

private theorem summable_geometric_gamma (M : ABKModel d) :
    Summable fun r : ℕ => Real.rpow 3 (M.gamma - 1) ^ r :=
  summable_geometric_of_lt_one (rpow3_gamma_sub_one_nonneg M)
    (Section4.Provider.BoundsEaL.rpow_gamma_sub_one_lt_one M)

/-! ## 3. The ascending condition on one cube -/

/-- **The ascending gradient series on `y + □_n` has bounded partial sums almost
surely.**  This is `(J2)` read through the exact shell scaling: the `r`-th term
has a `Γ₂` tail at the geometric amplitude `3^{-n} 3^{(γ-1)(n+r)}`. -/
theorem ae_upperGradBounded (M : ABKModel d) (n : ℤ) (y : Vec d) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure, UpperGradBounded n y omega := by
  have hApos : (0 : ℝ) < (3 : ℝ) ^ (-n) * Real.rpow 3 ((M.gamma - 1) * (n : ℝ)) :=
    shellW1InfGradAmplitude_pos M n n
  have hrpos : (0 : ℝ) < Real.rpow 3 (M.gamma - 1) := Real.rpow_pos_of_pos (by norm_num) _
  have hae := Provider.Orlicz.ae_summable_of_isBigOWith_gammaSigma
    (mu := (cutoffSampleLaw M).toMeasure) (sigma := 2)
    (X := fun (r : ℕ) (omega : CutoffSample d) =>
      Section4.Support.shellW1InfGradNorm n
        (ShellField.translate y (omega.1 (n + (r : ℤ)))))
    (a := fun r : ℕ =>
      ((3 : ℝ) ^ (-n) * Real.rpow 3 ((M.gamma - 1) * (n : ℝ))) *
        Real.rpow 3 (M.gamma - 1) ^ r)
    (by norm_num) (fun _ _ => Section4.Support.shellW1InfGradNorm_nonneg _ _)
    (fun r => (measurable_shellW1InfGradNorm_translate_comp n (n + (r : ℤ)) y).aemeasurable)
    (fun r => mul_pos hApos (pow_pos hrpos r))
    ((summable_geometric_gamma M).mul_left _)
    (fun r => by
      have h := Section4.Provider.BoundsEaL.isBigOWith_gammaSigma_shellW1InfGradNorm_translate
        M (by omega : n ≤ n + (r : ℤ)) y
      rwa [ascendingScale_eq M n r] at h)
  filter_upwards [hae] with omega hsum
  obtain ⟨C, hC⟩ := exists_nat_ge (∑' r : ℕ,
    Section4.Support.shellW1InfGradNorm n (ShellField.translate y (omega.1 (n + (r : ℤ)))))
  refine ⟨C, fun q => ?_⟩
  refine le_trans ?_ hC
  exact hsum.sum_le_tsum (Finset.range q)
    (fun r _ => Section4.Support.shellW1InfGradNorm_nonneg _ _)

/-! ## 4. The quantitative two-leg condition -/

/-- `Real.rpow` written with the power notation, so that the `Real.rpow_*`
lemmas apply to the explicit spelling used by the shell displays. -/
private theorem rpow_eq_hpow (a b : ℝ) : Real.rpow a b = a ^ b := rfl

end

end Algsuperdiff.Section5.Field

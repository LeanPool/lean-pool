/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Comparison.SliceBounds
public import LeanPool.CIVAxisymmetric.Statements.IsLocallyBoundedOn
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# ELp Norm Bridge

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory Set
open scoped ENNReal
open CKN


noncomputable section

namespace CIV

/-- The `L^∞` bridge in the comparison monotonicity argument: if, for almost every reference
time `τ₀` and almost every later time `τ`, every real number dominating the earlier slice
`x ↦ q (x, τ₀)` almost everywhere also dominates the later slice `x ↦ q (x, τ)` almost
everywhere, then the essential supremum of the later slice is bounded by the essential supremum
of the earlier one. The earlier slice's essential supremum may itself be infinite, in which case
the bound holds trivially; when it is finite, its own value serves as the dominating real number,
so the hypothesis transfers it directly to the later slice. -/
theorem comparison_eLpNorm_top_of_ae_dominance {m : ℕ} {I : Set ℝ} {q : Vec m × ℝ → ℝ}
    (hq : IsLocallyBoundedOn m I q)
    (hstep : ∀ᵐ τ₀ ∂(volume.restrict I), ∀ᵐ τ ∂(volume.restrict I), τ₀ < τ →
      ∀ M : ℝ, (∀ᵐ x : Vec m, |q (x, τ₀)| ≤ M) → ∀ᵐ x : Vec m, |q (x, τ)| ≤ M) :
    ∀ᵐ τ₀ ∂(volume.restrict I), ∀ᵐ τ ∂(volume.restrict I), τ₀ < τ →
      eLpNorm (fun x => q (x, τ)) ⊤ volume ≤ eLpNorm (fun x => q (x, τ₀)) ⊤ volume := by
  have hmeas := hq.ae_slice_measurable
  filter_upwards [hstep, hmeas] with τ₀ hτ0 hMτ0
  filter_upwards [hτ0, hmeas] with τ hτ hMτ
  intro hlt
  by_cases hRtop : eLpNorm (fun x : Vec m => q (x, τ₀)) ⊤ volume = ⊤
  · rw [hRtop]
    exact le_top
  · have hCess : eLpNormEssSup (fun x : Vec m => q (x, τ₀)) volume
        = eLpNorm (fun x : Vec m => q (x, τ₀)) ⊤ volume :=
      (eLpNorm_exponent_top hMτ0).symm
    have hbound0 : ∀ᵐ x : Vec m,
        |q (x, τ₀)| ≤ (eLpNorm (fun x : Vec m => q (x, τ₀)) ⊤ volume).toReal := by
      have h1 : ∀ᵐ x : Vec m,
          ‖q (x, τ₀)‖ₑ ≤ eLpNormEssSup (fun x : Vec m => q (x, τ₀)) volume :=
        ae_le_eLpNormEssSup
      rw [hCess] at h1
      filter_upwards [h1] with x hx
      have hxreal : ‖q (x, τ₀)‖ₑ.toReal
          ≤ (eLpNorm (fun x : Vec m => q (x, τ₀)) ⊤ volume).toReal :=
        ENNReal.toReal_mono hRtop hx
      rwa [toReal_enorm, Real.norm_eq_abs] at hxreal
    have hbound : ∀ᵐ x : Vec m,
        |q (x, τ)| ≤ (eLpNorm (fun x : Vec m => q (x, τ₀)) ⊤ volume).toReal :=
      hτ hlt _ hbound0
    have hEssτ : eLpNormEssSup (fun x : Vec m => q (x, τ)) volume
        ≤ ENNReal.ofReal (eLpNorm (fun x : Vec m => q (x, τ₀)) ⊤ volume).toReal :=
      eLpNormEssSup_le_of_ae_bound hbound
    rw [ENNReal.ofReal_toReal hRtop] at hEssτ
    rw [eLpNorm_exponent_top hMτ]
    exact hEssτ

end CIV

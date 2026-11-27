/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.LpMultiplication

/-!
# Unitary multiplication by an actual measurable unit-modulus function

This works on arbitrary measures. The inverse is literal conjugate
multiplication, and the norm identity is proved on AE representatives.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped ComplexConjugate ENNReal

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (w : α → ℂ) (hw : Measurable w) (hu : ∀ x, ‖w x‖ = 1)

include hw hu in
theorem memLp_unitModulus : MemLp w ⊤ μ :=
  memLp_top_of_bound hw.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => (hu x).le)

theorem norm_lpMultiplication_unitModulus (v : Lp ℂ 2 μ) :
    ‖lpMultiplication μ w (memLp_unitModulus μ w hw hu) v‖ = ‖v‖ := by
  have hae := lpMultiplication_ae μ w (memLp_unitModulus μ w hw hu) v
  apply le_antisymm
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hae] with x hx
    simp only [hx, norm_mul, hu x, one_mul, le_refl]
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hae] with x hx
    simp only [hx, norm_mul, hu x, one_mul, le_refl]

/-- Linear isometry equivalence for the ℓᵖ unit modulus, of type `Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ`. -/
noncomputable def lpUnitModulus : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ := by
  let A := lpMultiplication μ w (memLp_unitModulus μ w hw hu)
  have hwc : Measurable (fun x => conj (w x)) := Complex.continuous_conj.measurable.comp hw
  have huc : ∀ x, ‖conj (w x)‖ = 1 := fun x => by rw [Complex.norm_conj, hu x]
  let B := lpMultiplication μ (fun x => conj (w x))
    (memLp_unitModulus μ _ hwc huc)
  have hBA (v : Lp ℂ 2 μ) : B (A v) = v := by
    apply Lp.ext
    filter_upwards [lpMultiplication_ae μ _ (memLp_unitModulus μ _ hwc huc) (A v),
      lpMultiplication_ae μ w (memLp_unitModulus μ w hw hu) v] with x hB hA
    change B (A v) x = v x
    rw [hB, hA, ← mul_assoc, Complex.conj_mul', hu x]
    simp
  have hAB (v : Lp ℂ 2 μ) : A (B v) = v := by
    apply Lp.ext
    filter_upwards [lpMultiplication_ae μ w (memLp_unitModulus μ w hw hu) (B v),
      lpMultiplication_ae μ _ (memLp_unitModulus μ _ hwc huc) v] with x hA hB
    change A (B v) x = v x
    rw [hA, hB, ← mul_assoc, Complex.mul_conj', hu x]
    simp
  exact
    { toLinearEquiv :=
        { A.toLinearMap with
          invFun := B
          left_inv := hBA
          right_inv := hAB }
      norm_map' := norm_lpMultiplication_unitModulus μ w hw hu }

theorem lpUnitModulus_ae (v : Lp ℂ 2 μ) :
    lpUnitModulus μ w hw hu v =ᵐ[μ] fun x => w x * v x :=
  lpMultiplication_ae μ w (memLp_unitModulus μ w hw hu) v

end VacuumBellSeparation

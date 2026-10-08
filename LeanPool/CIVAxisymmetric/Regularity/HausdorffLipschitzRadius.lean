/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Identities.Vorticity
public import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Hausdorff measure, Lipschitz maps, and null sets

When a subset of `ℝ³` has vanishing one-dimensional Hausdorff measure, its Lipschitz
image has vanishing Lebesgue measure (`volume_image_eq_zero_of_hausdorffMeasure_one_eq_zero`),
and consequently almost every radius `r` avoids the image
(`ae_notMem_image_of_hausdorffMeasure_one_eq_zero`).
The classical fact that a null set cannot contain a whole sphere for almost every radius,
used in the proof of `lem:aniso:annulus`, is `ae_forall_norm_ne_of_hausdorffMeasure_one_eq_zero`:
for a null set `S`, almost every `r` has `∂B(r) ∩ S = ∅`.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-! ### Lipschitz bounds for the Hausdorff measure -/

/-- A Lipschitz map `f : Vec3 → ℝ` cannot increase the one-dimensional Hausdorff measure
by more than the Lipschitz constant: `μH¹(f '' S) ≤ K · μH¹(S)`. -/
theorem hausdorffMeasure_image_le_of_lipschitzWith {f : Vec3 → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (S : Set Vec3) :
    μH[(1 : ℝ)] (f '' S) ≤ K * μH[(1 : ℝ)] S := by
  calc
    μH[(1 : ℝ)] (f '' S) ≤ (K : ℝ≥0∞) ^ (1 : ℝ) * μH[(1 : ℝ)] S :=
      hf.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1) S
    _ = K * μH[(1 : ℝ)] S := by simp

/-- If `S` has vanishing one-dimensional Hausdorff measure, its Lipschitz image has vanishing
Lebesgue measure in `ℝ`. -/
theorem volume_image_eq_zero_of_hausdorffMeasure_one_eq_zero {f : Vec3 → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {S : Set Vec3} (hS : μH[(1 : ℝ)] S = 0) :
    (volume : Measure ℝ) (f '' S) = 0 := by
  have hzero : μH[(1 : ℝ)] (f '' S) = 0 := by
    refine le_antisymm ?_ (by positivity)
    calc
      μH[(1 : ℝ)] (f '' S) ≤ K * μH[(1 : ℝ)] S := hausdorffMeasure_image_le_of_lipschitzWith hf S
      _ = K * 0 := by rw [hS]
      _ = 0 := by simp
  rw [← hausdorffMeasure_real]
  exact hzero

/-- If `S` has vanishing one-dimensional Hausdorff measure, almost every real number `r`
lies outside the Lipschitz image `f '' S`. -/
theorem ae_notMem_image_of_hausdorffMeasure_one_eq_zero {f : Vec3 → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {S : Set Vec3} (hS : μH[(1 : ℝ)] S = 0) :
    ∀ᵐ r : ℝ, r ∉ f '' S := by
  have hvol : (volume : Measure ℝ) (f '' S) = 0 :=
    volume_image_eq_zero_of_hausdorffMeasure_one_eq_zero hf hS
  rwa [measure_eq_zero_iff_ae_notMem] at hvol

/-! ### Spheres avoiding a null set -/

/-- For a subset `S` of `ℝ³` with vanishing one-dimensional Hausdorff measure, almost every
radius `r` has the property that no point of `S` lies on the sphere `‖x‖ = r`. This is the
classical fact behind the choice of a radius `R` with `∂B(R)` disjoint from the singular set
`S₀` in the proof of `lem:aniso:annulus`. -/
theorem ae_forall_norm_ne_of_hausdorffMeasure_one_eq_zero {S : Set Vec3} (hS : μH[(1 : ℝ)] S = 0) :
    ∀ᵐ r : ℝ, ∀ x ∈ S, ‖x‖ ≠ r := by
  have h := ae_notMem_image_of_hausdorffMeasure_one_eq_zero lipschitzWith_one_norm hS
  filter_upwards [h] with r hr x hx
  intro heq
  apply hr
  exact ⟨x, hx, heq⟩

end CIV

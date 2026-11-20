/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceCollisionVolume.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceCollisionCoordinates

/-!
# Correspondence collision volume

Part of the weak Sobolev domains and collision capacity development of the
Ginibre Poincaré formalization.

Main results: `correspondenceCollision_compact_tube_volume`.
-/

@[expose] public section
namespace GinibrePoincare
noncomputable section
open MeasureTheory
open scoped ENNReal

/-- A compact collision tube has quadratic Lebesgue volume, uniformly in its width. -/
theorem correspondenceCollision_compact_tube_volume {n : ℕ} (j k : Fin n) (hjk : k ≠ j)
    (K : Set (Configuration n)) (hK : IsCompact K) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ r : ℝ,
      volume {z : Configuration n | z ∈ K ∧ ‖z j - z k‖ ≤ r} ≤
        C * ENNReal.ofReal r ^ 2 := by
  classical
  let L : Set ({i : Fin n // i ≠ j} → ℂ) :=
    (fun z : Configuration n => fun i : {i : Fin n // i ≠ j} => z i.val) '' K
  have hL : IsCompact L := hK.image (by fun_prop)
  refine ⟨volume L * NNReal.pi, ENNReal.mul_ne_top hL.measure_ne_top (by simp), ?_⟩
  intro r
  let B : Set (ℂ × ({i : Fin n // i ≠ j} → ℂ)) :=
    {p | p.2 ∈ L ∧ ‖p.1 - p.2 ⟨k, hjk⟩‖ ≤ r}
  have hc : Continuous (fun p : ℂ × ({i : Fin n // i ≠ j} → ℂ) =>
      ‖p.1 - p.2 ⟨k, hjk⟩‖) := by fun_prop
  have hB : MeasurableSet B := (hL.measurableSet.preimage measurable_snd).inter
    (isClosed_le hc continuous_const).measurableSet
  have hsub : {z : Configuration n | z ∈ K ∧ ‖z j - z k‖ ≤ r} ⊆
      correspondenceCollisionSplit j ⁻¹' B := by
    intro z hz
    rw [Set.mem_preimage, correspondenceCollisionSplit_apply]
    exact ⟨⟨z, hz.1, rfl⟩, hz.2⟩
  calc
    _ ≤ volume (correspondenceCollisionSplit j ⁻¹' B) := measure_mono hsub
    _ = volume B := (correspondenceCollisionSplit_volume j).measure_preimage hB.nullMeasurableSet
    _ = (volume L * NNReal.pi) * ENNReal.ofReal r ^ 2 := by
      rw [Measure.volume_eq_prod, Measure.prod_apply_symm hB]
      have hfib (y : {i : Fin n // i ≠ j} → ℂ) :
          ((fun x : ℂ => (x, y)) ⁻¹' B) =
          if y ∈ L then Metric.closedBall (y ⟨k, hjk⟩) r else ∅ := by
        ext x
        by_cases hy : y ∈ L <;> simp [B, hy, Metric.mem_closedBall, dist_eq_norm]
      simp_rw [hfib]
      simp only [apply_ite volume, Complex.volume_closedBall, measure_empty]
      change (∫⁻ y, L.indicator (fun _ => ENNReal.ofReal r ^ 2 * NNReal.pi) y) = _
      rw [lintegral_indicator hL.measurableSet, lintegral_const]
      rw [Measure.restrict_apply_univ]
      ring

end
end GinibrePoincare


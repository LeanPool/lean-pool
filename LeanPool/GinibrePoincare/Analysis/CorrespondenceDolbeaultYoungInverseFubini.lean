/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceDolbeaultYoungInverseFubini.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceDolbeaultYoungInverseSlice

/-!
# Correspondence Dolbeault Young inverse Fubini

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `dolbeaultOrdinaryL2_integrable_compact`,
`dolbeaultCoordinateConvolution_test_fubini`.
-/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

theorem dolbeaultOrdinaryL2_integrable_compact {n : ℕ} (u : dolbeaultOrdinaryL2 n)
    (M : ℝ) (hu : ∀ᵐ z : Configuration n ∂volume, z ∉ Metric.closedBall 0 M → u z = 0) :
    Integrable (u : Configuration n → ℂ) volume := by
  let K : Set (Configuration n) := Metric.closedBall 0 M
  let : IsFiniteMeasure (volume.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (isCompact_closedBall (0 : Configuration n) M).measure_lt_top⟩
  have hi : IntegrableOn (u : Configuration n → ℂ) K volume :=
    ((Lp.memLp u).restrict K).integrable (by norm_num)
  have hI := (integrable_indicator_iff (show MeasurableSet K from measurableSet_closedBall)).mpr hi
  apply hI.congr
  filter_upwards [hu] with z hz
  by_cases h : z∈K
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h, hz h]

theorem dolbeaultCoordinateConvolution_test_fubini {n : ℕ} (j : Fin n)
    (k : ℂ → ℂ) (hk : Integrable k volume) (u : dolbeaultOrdinaryL2 n)
    (hu : Integrable (u : Configuration n → ℂ) volume)
    (ψ : Configuration n → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    (∫ z : Configuration n, ψ z*(dolbeaultCoordinateConvolution j k u) z) =
      ∫ w : Configuration n, (∫ y : ℂ, k y*ψ (w+Pi.single j y))*u w := by
  have hψj : Continuous (fun p : ℂ × Configuration n => ψ (p.2+Pi.single j p.1)) := by
    apply hψ.comp
    apply continuous_snd.add
    apply continuous_pi
    intro l
    by_cases hl : l=j
    · subst l
      simpa using continuous_fst
    · simpa [Pi.single_eq_of_ne hl] using (continuous_const : Continuous (fun _ : ℂ × Configuration
        n => (0 : ℂ)))
  obtain ⟨C, hC⟩ := (hc.isCompact_range hψ).isBounded.exists_norm_le
  have hj : Integrable (fun p : ℂ × Configuration n =>
      k p.1*ψ (p.2+Pi.single j p.1)*u p.2) (volume.prod volume) := by
    have hm := (hk.aestronglyMeasurable.comp_fst.mul hψj.aestronglyMeasurable).mul
      hu.aestronglyMeasurable.comp_snd
    apply ((hk.norm.mul_prod hu.norm).const_mul C).mono' hm
    exact ae_of_all _ (fun p => by
      change ‖k p.1*ψ (p.2+Pi.single j p.1)*u p.2‖ ≤ _
      rw [norm_mul, norm_mul]
      have hb := hC (ψ (p.2+Pi.single j p.1)) ⟨_, rfl⟩
      calc
        _ ≤ ‖k p.1‖*C*‖u p.2‖ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hb (norm_nonneg _)) (norm_nonneg _)
        _ = C*(‖k p.1‖*‖u p.2‖) := by ring)
  rw [dolbeaultCoordinateConvolution_compact_test j k hk u ψ hψ hc]
  have hs (y : ℂ) : (∫ z : Configuration n, ψ z*u (z-Pi.single j y)) =
      ∫ w : Configuration n, ψ (w+Pi.single j y)*u w := by
    have h := integral_add_right_eq_self (μ := (volume : Measure (Configuration n)))
      (fun z => ψ z*u (z-Pi.single j y)) (Pi.single j y)
    simpa only [add_sub_cancel_right] using h.symm
  have he (y : ℂ) : k y*(∫ w : Configuration n, ψ (w+Pi.single j y)*u w) =
      ∫ w : Configuration n, k y*ψ (w+Pi.single j y)*u w := by
    rw [← integral_const_mul]
    congr 1
    funext w
    ring
  simp_rw [hs, he]
  rw [integral_integral_swap hj]
  simp_rw [integral_mul_const]

end
end GinibrePoincare

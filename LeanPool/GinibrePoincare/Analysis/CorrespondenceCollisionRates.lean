/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceCollisionRates.lean.
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

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceCollisionCutoff

/-!
# Correspondence collision rates

Part of the weak Sobolev domains and collision capacity development of the
Ginibre Poincaré formalization.

Main results: `correspondenceCollisionCutoff_compact_rates`.
-/

@[expose] public section
namespace GinibrePoincare
noncomputable section
open MeasureTheory
open scoped ENNReal

private theorem compact_tube_integral_bound {n : ℕ} (hn : 0 < n)
    (j k : Fin n) (K : Set (Configuration n)) (hK : IsCompact K)
    (r A : ℝ) (_ : 0 ≤ A) (F : Configuration n → ℝ)
    (hF : IntegrableOn F K (ginibreMeasure n)) (hb : ∀ z, F z ≤ A)
    (hz : ∀ z, r < ‖z j - z k‖ → F z = 0) :
    (∫ z in K, F z ∂ginibreMeasure n) ≤
      A * (ginibreMeasure n {z | z ∈ K ∧ ‖z j-z k‖ ≤ r}).toReal := by
  let := ginibreMeasure_isProbabilityMeasure hn
  let S : Set (Configuration n) := {z | z ∈ K ∧ ‖z j-z k‖ ≤ r}
  have hc : Continuous (fun z : Configuration n => ‖z j-z k‖) := by fun_prop
  have hS : MeasurableSet S := hK.measurableSet.inter
    (isClosed_le hc continuous_const).measurableSet
  have hi : Integrable (S.indicator (fun _ => A)) ((ginibreMeasure n).restrict K) :=
    (integrable_const A).indicator hS
  have hp : ∀ᵐ z ∂(ginibreMeasure n).restrict K, F z ≤ S.indicator (fun _ => A) z := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hzK
    by_cases hzS : z ∈ S
    · simpa [Set.indicator_of_mem hzS] using hb z
    · have hzr : r < ‖z j-z k‖ := lt_of_not_ge (by simpa [S, hzK] using hzS)
      simp [Set.indicator_of_notMem hzS, hz z hzr]
  have h := integral_mono_ae hF hi hp
  rw [integral_indicator hS, integral_const] at h
  have hsub : S ⊆ K := fun z hz => hz.1
  simpa [measureReal_def, Measure.restrict_apply hS, Measure.restrict_apply_univ,
    Set.inter_eq_left.mpr hsub, smul_eq_mul, mul_comm] using h

/-- Exact Appendix A orders for the smooth single-collision cutoff:
fourth-order squared-value error and second-order ordinary gradient energy. -/
theorem correspondenceCollisionCutoff_compact_rates {n : ℕ} (hn : 0 < n)
    (p : VandermondePair n) (K : Set (Configuration n)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε →
      (∫ z in K, |1-correspondenceCollisionCutoff p.val.1 p.val.2 ε z|^2
        ∂ginibreMeasure n) ≤ C*ε^4 ∧
      (∫ z in K, ‖ginibreEuclideanGradient
          (correspondenceCollisionCutoff p.val.1 p.val.2 ε) z‖^2
        ∂ginibreMeasure n) ≤ C*ε^2 := by
  let := ginibreMeasure_isProbabilityMeasure hn
  obtain ⟨D, hD, hm⟩ := correspondenceCollision_compact_tube_mass hn p K hK
  obtain ⟨G, hG0, hG⟩ := correspondenceCollisionCutoff_gradient_bound n
  have hr (r : ℝ) (hr : 0 ≤ r) :
      (ginibreMeasure n {z | z ∈ K ∧ ‖z p.val.1-z p.val.2‖ ≤ r}).toReal ≤ D.toReal*r^4 := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hD (by simp)) (hm r hr)
    simpa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr] using h
  refine ⟨16*D.toReal*(G+1), by positivity, ?_⟩
  intro ε hε
  have hc := correspondenceCollisionCutoff_smooth p.val.1 p.val.2 ε
  have hm2 := hr (2*ε) (by positivity)
  have hbval (z : Configuration n) : |1-correspondenceCollisionCutoff p.val.1 p.val.2 ε z|^2 ≤ 1 :=
      by
    obtain ⟨h0, h1⟩ := correspondenceCollisionCutoff_mem_unit p.val.1 p.val.2 ε z
    rw [sq_abs]
    nlinarith
  have hiv : IntegrableOn (fun z => |1-correspondenceCollisionCutoff p.val.1 p.val.2 ε z|^2)
      K (ginibreMeasure n) :=
    ((continuous_const.sub hc.continuous).abs.pow 2).continuousOn.integrableOn_compact hK
  have hig : IntegrableOn (fun z => ‖ginibreEuclideanGradient
      (correspondenceCollisionCutoff p.val.1 p.val.2 ε) z‖^2) K (ginibreMeasure n) :=
    ((continuous_ginibreEuclideanGradient _ hc).norm.pow 2).continuousOn.integrableOn_compact hK
  have hv := compact_tube_integral_bound hn p.val.1 p.val.2 K hK (2*ε) 1 (by norm_num)
    _ hiv hbval (by
      intro z hz
      have h := correspondenceCollisionCutoff_one_gradient_zero p.val.1 p.val.2 hε z hz.le
      simp [h.1])
  have hg := compact_tube_integral_bound hn p.val.1 p.val.2 K hK (2*ε) (G/ε^2)
    (by positivity) _ hig (hG p.val.1 p.val.2 ε hε) (by
      intro z hz
      have h := correspondenceCollisionCutoff_one_gradient_zero p.val.1 p.val.2 hε z hz.le
      simp [h.2])
  constructor
  · have hv' := hv.trans (by simpa using hm2)
    have hD0 := ENNReal.toReal_nonneg (a := D)
    nlinarith [mul_nonneg hD0 hG0, pow_nonneg hε.le 4]
  · have hg' := hg.trans (mul_le_mul_of_nonneg_left hm2 (by positivity : 0 ≤ G/ε^2))
    have he : ε ≠ 0 := hε.ne'
    have heq : G/ε^2*(D.toReal*(2*ε)^4) = 16*D.toReal*G*ε^2 := by field_simp; ring
    rw [heq] at hg'
    have hD0 := ENNReal.toReal_nonneg (a := D)
    nlinarith [mul_nonneg hD0 (sq_nonneg ε)]

end
end GinibrePoincare


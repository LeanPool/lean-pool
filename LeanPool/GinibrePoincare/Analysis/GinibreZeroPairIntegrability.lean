/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreZeroPairIntegrability.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibrePhaseRegularSobolev
public import LeanPool.GinibrePoincare.Analysis.GinibreDensityBound
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Integral.Pi

/-! # Local inverse-radius control at simultaneous coordinate zeroes

For distinct complex coordinates the reciprocal of their combined squared radius
is locally Lebesgue integrable. This is the concrete domination needed for cutoff
energy at the remaining exceptional set of the radial weak-domain argument.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology BigOperators
namespace GinibrePoincare
noncomputable section

/-- The planar inverse norm is locally integrable at the origin as well as away from it. -/
theorem complex_norm_inv_locallyIntegrable :
    LocallyIntegrable (fun z : ℂ => ‖z‖⁻¹) volume := by
  apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1)
    (by simp [Complex.finrank_real_complex]) (by norm_num [Complex.finrank_real_complex])
  · apply ae_of_all
    intro z
    simp only [Real.rpow_neg_one, one_mul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z)), le_refl]
  · exact ((continuous_norm : Continuous (fun z : ℂ => ‖z‖)).measurable.inv).aestronglyMeasurable

/-- Products of inverse norms of two distinct coordinates are integrable on
compact configuration sets; distinctness prevents a planar inverse-square singularity. -/
theorem configuration_two_norm_inv_integrableOn_compact (n : ℕ) (i j : Fin n)
    (hij : i ≠ j) (K : Set (Configuration n)) (hK : IsCompact K) :
    IntegrableOn (fun z => ‖z i‖⁻¹ * ‖z j‖⁻¹) K volume := by
  classical
  obtain ⟨R, hR0, hR⟩ := hK.isBounded.exists_pos_norm_lt
  let B := Set.univ.pi (fun _ : Fin n => Metric.closedBall (0 : ℂ) R)
  have hKB : K ⊆ B := by
    intro z hz k _
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_pi_norm z k).trans (hR z hz).le
  let : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : ℂ) R)) :=
    ⟨by simpa using (isCompact_closedBall (0 : ℂ) R).measure_lt_top (μ := volume)⟩
  let f (k : Fin n) (z : ℂ) : ℝ :=
    if k = i then ‖z‖⁻¹ else if k = j then ‖z‖⁻¹ else 1
  have hf (k : Fin n) : Integrable (f k) (volume.restrict (Metric.closedBall (0 : ℂ) R)) := by
    by_cases hi : k = i
    · simpa [f, hi, IntegrableOn] using complex_norm_inv_locallyIntegrable.integrableOn_isCompact
        (isCompact_closedBall (0 : ℂ) R)
    · by_cases hj : k = j
      · simpa [f, hi, hj, IntegrableOn] using
          complex_norm_inv_locallyIntegrable.integrableOn_isCompact
          (isCompact_closedBall (0 : ℂ) R)
      · simp only [f, hi, hj, ↓reduceIte]
        exact integrable_const 1
  have he (z : Configuration n) : (∏ k, f k (z k)) = ‖z i‖⁻¹ * ‖z j‖⁻¹ := by
    have he' (k : Fin n) : f k (z k) =
        (if k = i then ‖z k‖⁻¹ else 1) * (if k = j then ‖z k‖⁻¹ else 1) := by
      by_cases hi : k = i
      · subst k; simp [f, hij]
      · by_cases hj : k = j
        · subst k; simp [f, hij.symm]
        · simp [f, hi, hj]
    simp_rw [he']
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hp := Integrable.fintype_prod hf
  simp_rw [he] at hp
  have hb : IntegrableOn (fun z : Configuration n => ‖z i‖⁻¹ * ‖z j‖⁻¹) B volume := by
    unfold IntegrableOn B
    rw [volume_pi, Measure.restrict_pi_pi]
    exact hp
  exact hb.mono_set hKB

/-- The inverse combined squared radius is integrable on every compact set. -/
theorem configuration_pair_radius_inv_integrableOn_compact (n : ℕ) (i j : Fin n)
    (hij : i ≠ j) (K : Set (Configuration n)) (hK : IsCompact K) :
    IntegrableOn (fun z => (Complex.normSq (z i) + Complex.normSq (z j))⁻¹) K volume := by
  have hi := configuration_two_norm_inv_integrableOn_compact n i j hij K hK
  have hzi : ∀ᵐ z ∂(volume : Measure (Configuration n)), z i ≠ 0 := by
    rw [volume_pi]
    exact Measure.ae_eval_ne (fun _ : Fin n => (volume : Measure ℂ)) i 0
  have hzj : ∀ᵐ z ∂(volume : Measure (Configuration n)), z j ≠ 0 := by
    rw [volume_pi]
    exact Measure.ae_eval_ne (fun _ : Fin n => (volume : Measure ℂ)) j 0
  apply hi.mono' (by fun_prop)
  filter_upwards [ae_restrict_of_ae hzi, ae_restrict_of_ae hzj] with z hzi hzj
  have hai : 0 < ‖z i‖ := norm_pos_iff.mpr hzi
  have haj : 0 < ‖z j‖ := norm_pos_iff.mpr hzj
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    Real.norm_eq_abs, abs_of_nonneg (by positivity), ← mul_inv]
  apply (inv_le_inv₀ (by positivity) (mul_pos hai haj)).mpr
  nlinarith [sq_nonneg (‖z i‖ - ‖z j‖)]

/-- The concrete Ginibre density bound transfers the inverse pair-radius
integrability to the weighted measure on every compact set. -/
theorem ginibre_pair_radius_inv_integrableOn_compact (n : ℕ) (hn : 0 < n)
    (i j : Fin n) (hij : i ≠ j) (K : Set (Configuration n)) (hK : IsCompact K) :
    IntegrableOn (fun z => (Complex.normSq (z i) + Complex.normSq (z j))⁻¹)
      K (ginibreMeasure n) := by
  obtain ⟨c, hc, hm⟩ := ginibreMeasure_le_finite_smul_volume n hn
  have hi := (configuration_pair_radius_inv_integrableOn_compact n i j hij K hK).smul_measure hc
  have he : (ginibreMeasure n).restrict K ≤ c • (volume : Measure (Configuration n)).restrict K :=
      by
    rw [← Measure.restrict_smul]
    exact Measure.restrict_mono (Set.Subset.refl K) hm
  exact hi.mono_measure he

end
end GinibrePoincare

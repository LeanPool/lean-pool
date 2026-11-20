/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/StrongConvexRadialSymmetrizedLaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.StrongConvexRadialEntropyTransfer
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-!
# Strong convex radial symmetrized law

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `potential_magnitude_map_eq_symmetrizedRadiusProduct`,
`potentialSymmetrizedRadiusProduct_integral_symmetric`.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal
namespace GinibrePoincare
noncomputable section

/-- Actual random uniform labels for the independent Kostlan radii. -/
def potentialSymmetrizedRadiusProduct (n : ℕ) (V : Potential) : Measure (Fin n → ℝ) :=
  (Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞)⁻¹ •
    ∑ e : Equiv.Perm (Fin n), (potentialRadiusProduct n V).map (fun r => r ∘ e)

/-- The actual magnitude pushforward of the interacting gas is exchangeable. -/
theorem potential_magnitude_pushforward_relabel (n : ℕ) {V : Potential}
    (hV : Continuous V) (e : Equiv.Perm (Fin n)) :
    ((potentialMeasure n V).map magnitudeVector).map (fun r => r ∘ e) =
      (potentialMeasure n V).map magnitudeVector := by
  have hm : Measurable (magnitudeVector : Configuration n → Fin n → ℝ) := by
    unfold magnitudeVector
    fun_prop
  rw [Measure.map_map (by fun_prop) hm]
  have he : (fun r : Fin n → ℝ => r ∘ e) ∘ magnitudeVector = magnitudeVector ∘ permute e := rfl
  rw [he, ← Measure.map_map hm (measurePreserving_permute_potentialMeasure n hV e).measurable,
    (measurePreserving_permute_potentialMeasure n hV e).map_eq]

/-- The symmetrisation of `F`: the average `(1 / n!) ∑ e, F (r ∘ e)` over all permutations `e` of
the coordinates of `r`. -/
def radiusPermutationAverage (n : ℕ) (F : (Fin n → ℝ) → ℝ) (r : Fin n → ℝ) : ℝ :=
  (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ * ∑ e : Equiv.Perm (Fin n), F (r ∘ e)

theorem radiusPermutationAverage_symmetric (n : ℕ) (F : (Fin n → ℝ) → ℝ) :
    IsSymmetricRadiusTest n (radiusPermutationAverage n F) := by
  classical
  intro p r
  unfold radiusPermutationAverage
  congr 1
  have h := Equiv.sum_comp (Equiv.mulLeft p) (fun e : Equiv.Perm (Fin n) => F (r ∘ e))
  change (∑ e : Equiv.Perm (Fin n), F (r ∘ (p * e : Equiv.Perm (Fin n)))) = (∑ e : Equiv.Perm (Fin
      n), F (r ∘ e)) at h
  simpa only [Function.comp_def, Equiv.Perm.mul_apply] using h

theorem radiusPermutationAverage_continuous (n : ℕ) (F : (Fin n → ℝ) → ℝ)
    (hF : Continuous F) : Continuous (radiusPermutationAverage n F) := by
  classical
  unfold radiusPermutationAverage
  apply Continuous.const_mul
  exact continuous_finsetSum _ fun e _ => hF.comp (by fun_prop)

theorem radiusPermutationAverage_bound (n : ℕ) (F : (Fin n → ℝ) → ℝ)
    (C : ℝ) (hC : ∀ r, ‖F r‖ ≤ C) (r : Fin n → ℝ) :
    ‖radiusPermutationAverage n F r‖ ≤ C := by
  classical
  have hcard : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin n)) := by exact_mod_cast Fintype.card_pos
  unfold radiusPermutationAverage
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcard)]
  calc
    _ ≤ (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ * ∑ e : Equiv.Perm (Fin n), ‖F (r ∘ e)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hcard.le)
    _ ≤ (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ * ∑ _e : Equiv.Perm (Fin n), C :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun e _ => hC _)) (inv_nonneg.mpr hcard.le)
    _ = C := by simp [hcard.ne']

theorem radiusPermutationAverage_integral (n : ℕ) (μ : Measure (Fin n → ℝ))
    [IsFiniteMeasure μ] (F : BoundedContinuousFunction (Fin n → ℝ) ℝ) :
    (∫ r, radiusPermutationAverage n F r ∂μ) =
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ *
        ∑ e : Equiv.Perm (Fin n), ∫ r, F (r ∘ e) ∂μ := by
  classical
  unfold radiusPermutationAverage
  rw [integral_const_mul, integral_finsetSum]
  intro e he
  apply (integrable_const ‖F‖).mono'
  · exact (F.continuous.comp (by fun_prop)).aestronglyMeasurable
  · exact .of_forall (fun r => F.norm_coe_le_norm _)

theorem potentialSymmetrizedRadiusProduct_integral (n : ℕ) (V : Potential)
    [IsFiniteMeasure (potentialRadiusProduct n V)] (F : BoundedContinuousFunction (Fin n → ℝ) ℝ) :
    (∫ r, F r ∂potentialSymmetrizedRadiusProduct n V) =
      ∫ r, radiusPermutationAverage n F r ∂potentialRadiusProduct n V := by
  classical
  unfold potentialSymmetrizedRadiusProduct
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
    rw [radiusPermutationAverage_integral]
    congr 1
    apply Finset.sum_congr rfl
    intro e he
    exact integral_map (Measurable.of_eval (fun i => measurable_pi_apply (e i))).aemeasurable
        F.continuous.aestronglyMeasurable
  · intro e he
    exact F.integrable _

instance potentialSymmetrizedRadiusProduct_isProbability (n : ℕ) (V : Potential)
    [IsProbabilityMeasure (potentialRadiusProduct n V)] :
    IsProbabilityMeasure (potentialSymmetrizedRadiusProduct n V) := by
  classical
  constructor
  rw [potentialSymmetrizedRadiusProduct, smul_apply, _root_.sum_apply]
  have hu (e : Equiv.Perm (Fin n)) :
      ((potentialRadiusProduct n V).map (fun r => r ∘ e)) univ = 1 := by
    have hp : Measurable (fun r : Fin n → ℝ => r ∘ e) :=
      Measurable.of_eval (fun i => measurable_pi_apply (e i))
    rw [Measure.map_apply hp MeasurableSet.univ]
    simp
  simp only [hu, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel
    (by exact_mod_cast (Fintype.card_ne_zero (α := Equiv.Perm (Fin n)))) (ENNReal.natCast_ne_top _)

/-- Full measurable Kostlan radius law, with genuine uniform random labels. -/
theorem potential_magnitude_map_eq_symmetrizedRadiusProduct (n : ℕ) (hn : 0 < n)
    {V : Potential} (hV : Continuous V) (hrot : IsRotationalPotential V)
    (hfin : potentialPartition n V < ⊤) :
    (potentialMeasure n V).map magnitudeVector = potentialSymmetrizedRadiusProduct n V := by
  classical
  let := potentialMeasure_isProbabilityMeasure n hn hV hfin
  let (i : Fin n) := potentialSquaredRadiusLaw_isProbabilityMeasure n hn hV hrot hfin i
  let (i : Fin n) : IsProbabilityMeasure ((potentialSquaredRadiusLaw n i.val V).map Real.sqrt) :=
    (by infer_instance)
  let : IsProbabilityMeasure (potentialRadiusProduct n V) := by unfold potentialRadiusProduct;
                                                                  infer_instance
  have hm : Measurable (magnitudeVector : Configuration n → Fin n → ℝ) := by
    unfold magnitudeVector
    fun_prop
  let : IsProbabilityMeasure ((potentialMeasure n V).map magnitudeVector) :=
    (by infer_instance)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  rw [potentialSymmetrizedRadiusProduct_integral]
  have he := potential_magnitude_expectation_eq_radiusProduct n hn hV hrot hfin
    (radiusPermutationAverage n F) (radiusPermutationAverage_continuous n F F.continuous)
    (radiusPermutationAverage_symmetric n F) ‖F‖
    (radiusPermutationAverage_bound n F ‖F‖ F.norm_coe_le_norm)
  rw [← integral_map hm.aemeasurable
    (radiusPermutationAverage_continuous n F F.continuous).aestronglyMeasurable] at he
  rw [radiusPermutationAverage_integral] at he
  have hi (e : Equiv.Perm (Fin n)) :
      (∫ r, F (r ∘ e) ∂(potentialMeasure n V).map magnitudeVector) =
        ∫ r, F r ∂(potentialMeasure n V).map magnitudeVector := by
    have hp : Measurable (fun r : Fin n → ℝ => r ∘ e) :=
      Measurable.of_eval (fun i => measurable_pi_apply (e i))
    have hh := integral_map (μ := (potentialMeasure n V).map magnitudeVector)
      (f := fun r : Fin n → ℝ => F r) hp.aemeasurable F.continuous.aestronglyMeasurable
    rw [potential_magnitude_pushforward_relabel n hV e] at hh
    exact hh.symm
  simp_rw [hi] at he
  simpa [Fintype.card_ne_zero] using he

theorem potentialSymmetrizedRadiusProduct_integral_symmetric (n : ℕ) (V : Potential)
    [IsFiniteMeasure (potentialRadiusProduct n V)] (G : (Fin n → ℝ) → ℝ)
    (hG : Measurable G) (hs : IsSymmetricRadiusTest n G) (C : ℝ)
    (hb : ∀ r, ‖G r‖ ≤ C) :
    (∫ r, G r ∂potentialSymmetrizedRadiusProduct n V) = ∫ r, G r ∂potentialRadiusProduct n V := by
  classical
  have hi (e : Equiv.Perm (Fin n)) : Integrable G
      ((potentialRadiusProduct n V).map (fun r => r ∘ e)) :=
    (integrable_const C).mono' hG.aestronglyMeasurable (.of_forall hb)
  have he (e : Equiv.Perm (Fin n)) :
      (∫ r, G r ∂(potentialRadiusProduct n V).map (fun r => r ∘ e)) =
        ∫ r, G r ∂potentialRadiusProduct n V := by
    have hp : Measurable (fun r : Fin n → ℝ => r ∘ e) :=
      Measurable.of_eval (fun i => measurable_pi_apply (e i))
    rw [integral_map hp.aemeasurable hG.aestronglyMeasurable]
    exact integral_congr_ae (.of_forall (fun r => hs e r))
  unfold potentialSymmetrizedRadiusProduct
  rw [integral_smul_measure, integral_finsetSum_measure (fun e _ => hi e)]
  simp only [he, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

end
end GinibrePoincare

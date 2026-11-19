/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalRegularityCoordinateLp.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityCoordinates
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Ginibre transition analytic local regularity coordinate lp

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalRegularity_coordinate_restricted_memLp`,
`ginibreLocalRegularity_coordinate_pullback_memLp`.
-/

@[expose] public section
open MeasureTheory Measure
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreLocalRegularity_coordinate_restricted_memLp
    (n : ℕ) (K : Set (Configuration n)) (u : Configuration n → ℂ)
    (hu : MemLp u 2 ((volume : Measure (Configuration n)).restrict K)) :
    MemLp (fun x => u ((configurationEuclideanEquiv n).symm x)) 2
      ((volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))).restrict
        ((configurationEuclideanEquiv n) '' K)) := by
  let e := (configurationEuclideanEquiv n).toHomeomorph.toMeasurableEquiv
  let q := fun x => u (e.symm x)
  have hm : MemLp q 2 (((volume : Measure (Configuration n)).restrict K).map e) := by
    apply e.memLp_map_measure_iff.mpr
    simpa only [q, Function.comp_def, MeasurableEquiv.symm_apply_apply] using hu
  obtain ⟨c, hc, he⟩ := ginibreLocalRegularity_coordinate_volume n
  have hmap : (((volume : Measure (Configuration n)).restrict K).map e) =
      (c : ℝ≥0∞) • ((volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))).restrict (e '' K)) := by
    have hr := e.restrict_map (volume : Measure (Configuration n)) (e '' K)
    rw [Set.preimage_image_eq _ e.injective] at hr
    change ((volume : Measure (Configuration n)).map (configurationEuclideanEquiv n)).restrict (e ''
        K) = _ at hr
    rw [he, Measure.restrict_smul] at hr
    exact hr.symm
  rw [hmap] at hm
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
  have hmi := hm.smul_measure (c := (c : ℝ≥0∞)⁻¹) (ENNReal.inv_ne_top.mpr hc0)
  rw [smul_smul, ENNReal.inv_mul_cancel hc0 ENNReal.coe_ne_top, one_smul] at hmi
  exact hmi

theorem ginibreLocalRegularity_coordinate_pullback_memLp
    {V : Type*} [NormedAddCommGroup V] (n : ℕ)
    (g : EuclideanSpace ℝ (Fin n × Fin 2) → V)
    (hg : MemLp g 2 (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))) :
    MemLp (g ∘ configurationEuclideanEquiv n) 2 (volume : Measure (Configuration n)) := by
  obtain ⟨c, hc, he⟩ := ginibreLocalRegularity_coordinate_volume n
  have hi := hg.smul_measure (c := (c : ℝ≥0∞)) ENNReal.coe_ne_top
  change MemLp g 2 (c • (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))) at hi
  rw [← he] at hi
  exact hi.comp_of_map (configurationEuclideanEquiv n).continuous.measurable.aemeasurable

end
end GinibrePoincare

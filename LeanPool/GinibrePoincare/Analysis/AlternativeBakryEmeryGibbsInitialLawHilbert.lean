/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryGibbsInitialLawHilbert.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsInitialLawMass
public import LeanPool.GinibrePoincare.Analysis.GaussianFourierCoordinates
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianInitialMeasureIdentification
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique
/-!
# Alternative Bakry Emery Gibbs initial law Hilbert

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmeryConfiguration_normalizedGibbs_map`,
`bakryEmeryConfiguration_gibbs_probability`.
-/

@[expose] public section
open Set MeasureTheory Measure
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem bakryEmeryConfiguration_volume_map (n : ℕ) :
    ∃ c : ℝ≥0, 0 < c ∧ (volume : Measure (Configuration n)).map (configurationEuclideanEquiv n) =
      c • (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) := by
  let e := configurationEuclideanEquiv n
  let μ := (volume : Measure (Configuration n)).map e
  let : IsAddHaarMeasure μ := e.isAddHaarMeasure_map volume
  exact ⟨addHaarScalarFactor μ volume, addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume,
    isAddLeftInvariant_eq_smul μ volume⟩

theorem bakryEmeryConfiguration_normalizedGibbs_map (n : ℕ) (W : Configuration n → ℝ)
    (hW : Continuous W) :
    (bakryEmeryNormalizedGibbs volume W).map (configurationEuclideanEquiv n) =
      bakryEmeryNormalizedGibbs volume (W ∘ (configurationEuclideanEquiv n).symm) := by
  let e := configurationEuclideanEquiv n
  let U := W ∘ e.symm
  obtain ⟨c, hc, he⟩ := bakryEmeryConfiguration_volume_map n
  have hmass : (∫ z : Configuration n, Real.exp (-W z)) =
      (c : ℝ)*(∫ x : EuclideanSpace ℝ (Fin n × Fin 2), Real.exp (-U x)) := by
    have hh := integral_map_equiv (μ := (volume : Measure (Configuration n)))
      e.toHomeomorph.toMeasurableEquiv (fun x => Real.exp (-U x))
    change (∫ x, Real.exp (-U x) ∂(volume : Measure (Configuration n)).map e) = _ at hh
    rw [he, integral_smul_nnreal_measure] at hh
    simpa [U, Function.comp_def, NNReal.smul_def, smul_eq_mul] using hh.symm
  have hraw : ((volume : Measure (Configuration n)).withDensity (fun z => ENNReal.ofReal (Real.exp
      (-W z)))).map e =
      (c : ENNReal) • (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))).withDensity
        (fun x => ENNReal.ofReal (Real.exp (-U x))) := by
    have hm := ginibre_map_density_composition (volume : Measure (Configuration n)) e
        e.continuous.measurable
      (fun x => ENNReal.ofReal (Real.exp (-U x))) (by fun_prop)
    rw [he] at hm
    change _ = ((c : ENNReal) • volume).withDensity _ at hm
    rw [withDensity_smul_measure] at hm
    simpa [U, Function.comp_def] using hm
  unfold bakryEmeryNormalizedGibbs
  rw [Measure.map_smul _ e.continuous.measurable.aemeasurable, hraw, hmass, ENNReal.ofReal_mul
      c.coe_nonneg, smul_smul]
  congr 1
  rw [ENNReal.mul_inv (Or.inl (by rw [ENNReal.ofReal_coe_nnreal]; exact_mod_cast hc.ne'))
    (Or.inl ENNReal.ofReal_ne_top)]
  calc
    (ENNReal.ofReal (c : ℝ))⁻¹ * (ENNReal.ofReal (∫ x, Real.exp (-U x)))⁻¹ * (c : ENNReal) =
      ((c : ENNReal)⁻¹*(c : ENNReal))*(ENNReal.ofReal (∫ x, Real.exp (-U x)))⁻¹ := by
        rw [ENNReal.ofReal_coe_nnreal]; ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel (by exact_mod_cast hc.ne') ENNReal.coe_ne_top, one_mul]

theorem bakryEmeryConfiguration_density_integrable (n : ℕ) (W : Configuration n → ℝ)
    (κ : ℝ) (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2)) :
    Integrable (fun z => Real.exp (-W z)) volume := by
  let e := configurationEuclideanEquiv n
  let U := W ∘ e.symm
  have hU : ContDiff ℝ 2 U := hW.comp e.symm.contDiff
  have hi := bakryEmeryStrongConvex_density_integrable U κ hκ hU hc
  obtain ⟨c, _, he⟩ := bakryEmeryConfiguration_volume_map n
  have him : Integrable (fun x => Real.exp (-U x)) ((volume : Measure (Configuration n)).map e) :=
      by
    rw [he]
    exact hi.smul_measure_nnreal
  have hh := (integrable_map_equiv e.toHomeomorph.toMeasurableEquiv (fun x => Real.exp (-U x))).mp
      him
  simpa [U, Function.comp_def] using hh

theorem bakryEmeryConfiguration_gibbs_probability (n : ℕ) (W : Configuration n → ℝ)
    (κ : ℝ) (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2)) :
    IsProbabilityMeasure (bakryEmeryNormalizedGibbs volume W) :=
  bakryEmeryNormalizedGibbs_probability volume W hW.continuous
    (bakryEmeryConfiguration_density_integrable n W κ hκ hW hc)
end
end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/EquilibriumProbability.lean.
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

public import LeanPool.GinibrePoincare.Analysis.EquilibriumFactorization
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Probability.Independence.Basic

/-!
# Probabilistic equilibrium factorization

The actual joint law of the coordinate sum `S` and zero-sum component `W`
is the product of the standard complex Gaussian and the recentered Ginibre
marginal. Haar uniqueness supplies the positive constant Jacobian; the
pointwise density identity supplies the product density. The recentered
marginal's normalization follows from the already proved Ginibre probability
normalization. The Gamma law of `n |W|²` is not part of this module.
-/


@[expose] public section


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GinibrePoincare

noncomputable section

/-- The standard complex Gaussian, with density `π⁻¹ exp (-|s|²)`. -/
def standardComplexGaussianMeasure : Measure ℂ :=
  complexCoordinateGaussianProbability 1

instance : IsProbabilityMeasure standardComplexGaussianMeasure := by
  unfold standardComplexGaussianMeasure
  infer_instance

/-- The equilibrium coordinate change as a Borel measurable equivalence. -/
def equilibriumMeasurableCoordinates (n : ℕ) (hn : 0 < n) :
    Configuration n ≃ᵐ ℂ × zeroSumHyperplane n :=
  (equilibriumCoordinates n hn).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

/-- A Haar (Lebesgue) measure on the zero-sum hyperplane. Its arbitrary constant
normalization will be absorbed into the recentered probability density. -/
def recenteredVolume (n : ℕ) : Measure (zeroSumHyperplane n) := Measure.addHaar

instance (n : ℕ) : Measure.IsAddHaarMeasure (recenteredVolume n) := by
  unfold recenteredVolume
  infer_instance

instance (n : ℕ) : SigmaFinite (recenteredVolume n) := by
  unfold recenteredVolume
  infer_instance

/-- Linearity gives a constant Jacobian with respect to product Haar measure. -/
theorem equilibriumCoordinates_map_volume (n : ℕ) (hn : 0 < n) :
    ∃ c : ℝ≥0, 0 < c ∧
      (configurationVolume n).map (equilibriumMeasurableCoordinates n hn) =
        (c : ℝ≥0∞) • (volume : Measure ℂ).prod (recenteredVolume n) := by
  let e := equilibriumCoordinates n hn
  have : Measure.IsAddHaarMeasure (configurationVolume n) := by
    unfold configurationVolume
    infer_instance
  have : Measure.IsAddHaarMeasure ((configurationVolume n).map e) := inferInstance
  let ν := (volume : Measure ℂ).prod (recenteredVolume n)
  refine ⟨Measure.addHaarScalarFactor ((configurationVolume n).map e) ν, ?_, ?_⟩
  · exact Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  · change (configurationVolume n).map e = _
    exact Measure.isAddLeftInvariant_eq_smul _ _

@[simp]
theorem equilibriumMeasurableCoordinates_apply (n : ℕ) (hn : 0 < n)
    (z : Configuration n) :
    equilibriumMeasurableCoordinates n hn z =
      (coordinateSum z, ⟨recenteredConfiguration n z, coordinateSum_recentered n z⟩) := rfl

/-- Density of the recentered component before fixing its total mass. -/
def recenteredEquilibriumDensity (n : ℕ) (w : zeroSumHyperplane n) : ℝ≥0∞ :=
  ENNReal.ofReal (equilibriumGinibreDensity n w.val)

theorem measurable_equilibriumGinibreDensity (n : ℕ) :
    Measurable (equilibriumGinibreDensity n) := by
  exact measurable_const.mul (measurable_rawGinibreDensity n)

theorem measurable_recenteredEquilibriumDensity (n : ℕ) :
    Measurable (recenteredEquilibriumDensity n) :=
  ENNReal.measurable_ofReal.comp
    ((measurable_equilibriumGinibreDensity n).comp measurable_subtype_coe)

theorem standardComplexGaussianMeasure_eq_withDensity :
    standardComplexGaussianMeasure = (volume : Measure ℂ).withDensity
      (complexCoordinateGaussianDensity 1) :=
  complexCoordinateGaussianMeasure_eq_withDensity (by decide : 0 < 1)

/-- Explicit standard-complex-Gaussian density, making the variance convention
independent of the name of the measure. -/
theorem standardComplexGaussianMeasure_eq_exp_density :
    standardComplexGaussianMeasure = (volume : Measure ℂ).withDensity
      (fun s => ENNReal.ofReal (Real.pi⁻¹ * Real.exp (-Complex.normSq s))) := by
  rw [standardComplexGaussianMeasure_eq_withDensity]
  congr 1
  funext s
  simp [complexCoordinateGaussianDensity]

private theorem exp_normSq_eq_pi_mul_gaussianDensity (s : ℂ) :
    ENNReal.ofReal (Real.exp (-Complex.normSq s)) =
      ENNReal.ofReal Real.pi * complexCoordinateGaussianDensity 1 s := by
  unfold complexCoordinateGaussianDensity
  rw [← ENNReal.ofReal_mul Real.pi_pos.le]
  congr 1
  simp only [Nat.cast_one, neg_mul, one_mul, one_div]
  field_simp

private theorem equilibrium_density_in_coordinates (n : ℕ) (hn : 0 < n)
    (p : ℂ × zeroSumHyperplane n) :
    ENNReal.ofReal (equilibriumGinibreDensity n
      ((equilibriumMeasurableCoordinates n hn).symm p)) =
      ENNReal.ofReal Real.pi * complexCoordinateGaussianDensity 1 p.1 *
        recenteredEquilibriumDensity n p.2 := by
  let e := equilibriumMeasurableCoordinates n hn
  have hs : coordinateSum (e.symm p) = p.1 :=
    congrArg Prod.fst (e.apply_symm_apply p)
  have hw : recenteredConfiguration n (e.symm p) = p.2.val :=
    congrArg (fun q : ℂ × zeroSumHyperplane n => q.2.val) (e.apply_symm_apply p)
  rw [normalized_equilibrium_factorization n hn, centerOfMassSqNorm,
    hs, hw, ENNReal.ofReal_mul (Real.exp_pos _).le,
    exp_normSq_eq_pi_mul_gaussianDensity]
  rfl

/-- The joint law factors as a standard complex Gaussian and a probability
measure on the zero-sum hyperplane. No independence or marginal-law hypothesis
is assumed. -/
theorem equilibrium_jointLaw_exists (n : ℕ) (hn : 0 < n) :
    ∃ ν : Measure (zeroSumHyperplane n), IsProbabilityMeasure ν ∧
      (ginibreMeasure n).map (equilibriumMeasurableCoordinates n hn) =
        standardComplexGaussianMeasure.prod ν ∧
      ∃ c : ℝ≥0, 0 < c ∧ ν = ((c : ℝ≥0∞) * ENNReal.ofReal Real.pi) •
        (recenteredVolume n).withDensity (recenteredEquilibriumDensity n) := by
  let e := equilibriumMeasurableCoordinates n hn
  obtain ⟨c, hc, hvol⟩ := equilibriumCoordinates_map_volume n hn
  let ρ := (recenteredVolume n).withDensity (recenteredEquilibriumDensity n)
  let ν := ((c : ℝ≥0∞) * ENNReal.ofReal Real.pi) • ρ
  have hf : Measurable (fun p => ENNReal.ofReal (equilibriumGinibreDensity n (e.symm p))) :=
    ENNReal.measurable_ofReal.comp ((measurable_equilibriumGinibreDensity n).comp e.symm.measurable)
  have htransport : (ginibreMeasure n).map e =
      ((configurationVolume n).map e).withDensity
        (fun p => ENNReal.ofReal (equilibriumGinibreDensity n (e.symm p))) := by
    rw [ginibreMeasure_eq_equilibriumDensity n hn]
    have hd : (fun z => ENNReal.ofReal (equilibriumGinibreDensity n z)) =
        (fun p => ENNReal.ofReal (equilibriumGinibreDensity n (e.symm p))) ∘ e := by
      funext z
      simp
    rw [hd]
    exact MeasurePreserving.map_withDensity_comp e ⟨e.measurable, rfl⟩ hf
  have hprod : (ginibreMeasure n).map e = standardComplexGaussianMeasure.prod ν := by
    rw [htransport, hvol, withDensity_smul_measure]
    have hd : (fun p => ENNReal.ofReal (equilibriumGinibreDensity n (e.symm p))) =
        ENNReal.ofReal Real.pi • (fun p : ℂ × zeroSumHyperplane n =>
          complexCoordinateGaussianDensity 1 p.1 * recenteredEquilibriumDensity n p.2) := by
      funext p
      rw [equilibrium_density_in_coordinates]
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    have hg : Measurable (fun p : ℂ × zeroSumHyperplane n =>
        complexCoordinateGaussianDensity 1 p.1 * recenteredEquilibriumDensity n p.2) :=
      ((measurable_complexCoordinateGaussianDensity 1).comp measurable_fst).mul
        ((measurable_recenteredEquilibriumDensity n).comp measurable_snd)
    rw [hd, withDensity_smul _ hg, smul_smul]
    rw [← prod_withDensity (measurable_complexCoordinateGaussianDensity 1)
      (measurable_recenteredEquilibriumDensity n)]
    rw [← standardComplexGaussianMeasure_eq_withDensity]
    exact (Measure.prod_smul_right _).symm
  have hν : IsProbabilityMeasure ν := by
    have hμ := ginibreMeasure_isProbabilityMeasure hn
    constructor
    have htotal : ((ginibreMeasure n).map e) Set.univ = 1 := by
      rw [Measure.map_apply e.measurable MeasurableSet.univ, Set.preimage_univ,
        ginibreMeasureIsProbability n hn]
    rw [hprod, ← Set.univ_prod_univ, Measure.prod_prod, measure_univ, one_mul] at htotal
    exact htotal
  exact ⟨ν, hν, hprod, c, hc, rfl⟩

/-- The recentered configuration as a random variable valued in its hyperplane. -/
def recenteredCoordinate (n : ℕ) (z : Configuration n) : zeroSumHyperplane n :=
  ⟨recenteredConfiguration n z, coordinateSum_recentered n z⟩

theorem measurable_coordinateSum (n : ℕ) :
    Measurable (coordinateSum : Configuration n → ℂ) := by
  unfold coordinateSum
  fun_prop

theorem measurable_recenteredCoordinate (n : ℕ) : Measurable (recenteredCoordinate n) := by
  unfold recenteredCoordinate recenteredConfiguration projectToOrthogonal coordinateSum
  fun_prop

/-- The actual marginal law of the recentered configuration. -/
def recenteredGinibreMeasure (n : ℕ) : Measure (zeroSumHyperplane n) :=
  (ginibreMeasure n).map (recenteredCoordinate n)

/-- The coordinate sum has exactly the standard complex Gaussian law. -/
theorem coordinateSum_ginibre_gaussian (n : ℕ) (hn : 0 < n) :
    (ginibreMeasure n).map coordinateSum = standardComplexGaussianMeasure := by
  obtain ⟨ν, hν, hjoint, _⟩ := equilibrium_jointLaw_exists n hn
  have := hν
  let e := equilibriumMeasurableCoordinates n hn
  change (ginibreMeasure n).map (Prod.fst ∘ e) = _
  rw [← Measure.map_map measurable_fst e.measurable, hjoint,
    Measure.map_fst_prod, measure_univ, one_smul]

private theorem recentered_marginal_of_jointLaw (n : ℕ) (hn : 0 < n)
    (ν : Measure (zeroSumHyperplane n)) (hν : IsProbabilityMeasure ν)
    (hjoint : (ginibreMeasure n).map (equilibriumMeasurableCoordinates n hn) =
      standardComplexGaussianMeasure.prod ν) :
    recenteredGinibreMeasure n = ν := by
  have := hν
  let e := equilibriumMeasurableCoordinates n hn
  change (ginibreMeasure n).map (Prod.snd ∘ e) = _
  rw [← Measure.map_map measurable_snd e.measurable, hjoint,
    Measure.map_snd_prod, measure_univ, one_smul]

/-- The joint law is the product of its actual marginals. -/
theorem equilibrium_jointLaw (n : ℕ) (hn : 0 < n) :
    (ginibreMeasure n).map (equilibriumMeasurableCoordinates n hn) =
      standardComplexGaussianMeasure.prod (recenteredGinibreMeasure n) := by
  obtain ⟨ν, hν, hjoint, _⟩ := equilibrium_jointLaw_exists n hn
  rw [recentered_marginal_of_jointLaw n hn ν hν hjoint]
  exact hjoint

theorem recenteredGinibreMeasure_isProbabilityMeasure (n : ℕ) (hn : 0 < n) :
    IsProbabilityMeasure (recenteredGinibreMeasure n) := by
  obtain ⟨ν, hν, hjoint, _⟩ := equilibrium_jointLaw_exists n hn
  rw [recentered_marginal_of_jointLaw n hn ν hν hjoint]
  exact hν

/-- The hyperplane marginal has density proportional to the restriction of
`equilibriumGinibreDensity`, with a positive finite proportionality constant. -/
theorem recenteredGinibreMeasure_eq_withDensity (n : ℕ) (hn : 0 < n) :
    ∃ a : ℝ≥0∞, 0 < a ∧ a < ⊤ ∧ recenteredGinibreMeasure n =
      (recenteredVolume n).withDensity
        (fun w => a * ENNReal.ofReal (equilibriumGinibreDensity n w.val)) := by
  obtain ⟨ν, hprob, hjoint, c, hc, hν⟩ := equilibrium_jointLaw_exists n hn
  refine ⟨(c : ℝ≥0∞) * ENNReal.ofReal Real.pi, ?_, ?_, ?_⟩
  · exact ENNReal.mul_pos_iff.mpr
      ⟨by exact_mod_cast hc, ENNReal.ofReal_pos.mpr Real.pi_pos⟩
  · exact ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top
  · rw [recentered_marginal_of_jointLaw n hn ν hprob hjoint, hν,
      ← withDensity_smul _ (measurable_recenteredEquilibriumDensity n)]
    rfl

/-- Independence on the intrinsic zero-sum hyperplane. -/
theorem coordinateSum_recenteredCoordinate_indepFun (n : ℕ) (hn : 0 < n) :
    IndepFun (coordinateSum : Configuration n → ℂ) (recenteredCoordinate n)
      (ginibreMeasure n) := by
  have := ginibreMeasure_isProbabilityMeasure hn
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_coordinateSum n).aemeasurable
    (measurable_recenteredCoordinate n).aemeasurable).mpr
  rw [coordinateSum_ginibre_gaussian n hn]
  exact equilibrium_jointLaw n hn

/-- The coordinate sum and recentered configuration are independent under the
actual normalized Ginibre measure, also when `W` is viewed in `ℂⁿ`. -/
theorem coordinateSum_recentered_indepFun (n : ℕ) (hn : 0 < n) :
    IndepFun (coordinateSum : Configuration n → ℂ) (recenteredConfiguration n)
      (ginibreMeasure n) := by
  exact (coordinateSum_recenteredCoordinate_indepFun n hn).comp
    measurable_id measurable_subtype_coe

/-- The probabilistic equilibrium factorization: Gaussian center-of-mass law,
independence, and the recentered marginal density. -/
theorem equilibrium_probability_factorization (n : ℕ) (hn : 0 < n) :
    (ginibreMeasure n).map coordinateSum = standardComplexGaussianMeasure ∧
    IndepFun (coordinateSum : Configuration n → ℂ) (recenteredConfiguration n)
      (ginibreMeasure n) ∧
    ∃ a : ℝ≥0∞, 0 < a ∧ a < ⊤ ∧ recenteredGinibreMeasure n =
      (recenteredVolume n).withDensity
        (fun w => a * ENNReal.ofReal (equilibriumGinibreDensity n w.val)) :=
  ⟨coordinateSum_ginibre_gaussian n hn, coordinateSum_recentered_indepFun n hn,
    recenteredGinibreMeasure_eq_withDensity n hn⟩

end
end GinibrePoincare

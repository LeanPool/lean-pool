/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryGibbsInitialLaw.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsInitialLawHilbert
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsReversalAction
public import LeanPool.GinibrePoincare.Analysis.ComplexGaussianDensity
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianGaussianCoordinateLaw
/-!
# Alternative Bakry Emery Gibbs initial law

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmeryGibbsCoordinateInitialMeasure_assembly`,
`bakryEmeryGibbsCoordinateInitialMeasure_probability`.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section

/-- The density `exp (-(W z - n ‖z‖²))` of the relative Gibbs weight, evaluated at the
configuration `z` assembled from the real coordinates `x`. -/
def bakryEmeryGibbsCoordinateWeight (n : ℕ) (W : Configuration n → ℝ)
    (x : (Fin n × Fin 2) → ℝ) : ENNReal :=
  ENNReal.ofReal (Real.exp (-bakryEmeryGibbsRelativePotential W
      (ginibreHamiltonianOUCoordinateAssembly n x)))

/-- The product of centred Gaussians of variance `1/2` on the real coordinates, weighted by the
density `bakryEmeryGibbsCoordinateWeight n W`. -/
def bakryEmeryGibbsCoordinateRawMeasure (n : ℕ) (W : Configuration n → ℝ) :
    Measure ((Fin n × Fin 2) → ℝ) :=
  (Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2))).withDensity
    (bakryEmeryGibbsCoordinateWeight n W)

/-- The Gibbs initial law in real coordinates: `bakryEmeryGibbsCoordinateRawMeasure n W`
divided by its total mass. -/
def bakryEmeryGibbsCoordinateInitialMeasure (n : ℕ) (W : Configuration n → ℝ) :
    Measure ((Fin n × Fin 2) → ℝ) :=
  (bakryEmeryGibbsCoordinateRawMeasure n W univ)⁻¹ • bakryEmeryGibbsCoordinateRawMeasure n W

theorem bakryEmeryGibbsCoordinateRawMeasure_assembly {n : ℕ} (hn : 0 < n)
    (W : Configuration n → ℝ) (hW : Continuous W) :
    (bakryEmeryGibbsCoordinateRawMeasure n W).map (ginibreHamiltonianOUCoordinateAssembly n) =
      ENNReal.ofReal (((n : ℝ)/Real.pi)^n) •
        (volume : Measure (Configuration n)).withDensity (fun z => ENNReal.ofReal (Real.exp (-W z)))
            := by
  have hS : Continuous (bakryEmeryGibbsRelativePotential W) :=
    hW.sub (continuous_const.mul (contDiff_configurationNormSq.continuous))
  have hrel : Measurable (fun z => ENNReal.ofReal (Real.exp (-bakryEmeryGibbsRelativePotential W
      z))) := by
    fun_prop
  have hA : Measurable (ginibreHamiltonianOUCoordinateAssembly n) :=
    (ginibreHamiltonianOUCoordinateAssembly n).continuous.measurable
  have hc : 0 ≤ ((n : ℝ)/Real.pi)^n := by positivity
  unfold bakryEmeryGibbsCoordinateRawMeasure bakryEmeryGibbsCoordinateWeight
  have hm := ginibre_map_density_composition
    (Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2)))
    (ginibreHamiltonianOUCoordinateAssembly n) hA _ hrel
  simp only [Function.comp_def] at hm
  rw [hm, ginibreGaussian_coordinate_assembly_law hn, complexGaussianDensityIdentification n hn]
  unfold complexGaussianDensityMeasure configurationVolume
  rw [← withDensity_mul _ (by exact measurable_complexGaussianDensity n) hrel]
  have hp : (fun z => complexGaussianDensity n z * ENNReal.ofReal
      (Real.exp (-bakryEmeryGibbsRelativePotential W z))) =
      (fun z => ENNReal.ofReal (((n : ℝ)/Real.pi)^n)*ENNReal.ofReal (Real.exp (-W z))) := by
    funext z
    simp only [complexGaussianDensity, gaussianWeight, bakryEmeryGibbsRelativePotential]
    rw [← ENNReal.ofReal_mul (mul_nonneg hc (Real.exp_nonneg _)),← ENNReal.ofReal_mul hc]
    congr 1
    rw [mul_assoc,← Real.exp_add]
    congr 1
    congr 1
    ring
  change complexGaussianDensity n * (fun z => ENNReal.ofReal
    (Real.exp (-bakryEmeryGibbsRelativePotential W z))) = _ at hp
  rw [hp]
  change (volume : Measure (Configuration n)).withDensity
    (ENNReal.ofReal (((n : ℝ)/Real.pi)^n) • (fun z => ENNReal.ofReal (Real.exp (-W z)))) = _
  exact withDensity_smul _ (by fun_prop)

theorem bakryEmeryGibbsCoordinateRawMeasure_mass {n : ℕ} (hn : 0 < n)
    (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W) (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2)) :
    bakryEmeryGibbsCoordinateRawMeasure n W univ =
      ENNReal.ofReal (((n : ℝ)/Real.pi)^n) * ENNReal.ofReal (∫ z, Real.exp (-W z)) := by
  have hi := bakryEmeryConfiguration_density_integrable n W κ hκ hW hc
  have hm := congrArg (fun μ : Measure (Configuration n) => μ univ)
    (bakryEmeryGibbsCoordinateRawMeasure_assembly hn W hW.continuous)
  rw [Measure.map_apply (ginibreHamiltonianOUCoordinateAssembly n).continuous.measurable
      MeasurableSet.univ,
    preimage_univ, smul_apply, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun z => Real.exp_nonneg _))] at hm
  exact hm

theorem bakryEmeryGibbsCoordinateRawMeasure_mass_valid {n : ℕ} (hn : 0 < n)
    (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W) (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2)) :
    0 < bakryEmeryGibbsCoordinateRawMeasure n W univ ∧
      bakryEmeryGibbsCoordinateRawMeasure n W univ ≠ ⊤ := by
  rw [bakryEmeryGibbsCoordinateRawMeasure_mass hn W hW κ hκ hc]
  have hZ := integral_exp_pos (bakryEmeryConfiguration_density_integrable n W κ hκ hW hc)
  have hnp : 0 < ((n : ℝ)/Real.pi)^n := by positivity
  have hp : 0 < ENNReal.ofReal (((n : ℝ)/Real.pi)^n) * ENNReal.ofReal (∫ z, Real.exp (-W z)) := by
    rw [← ENNReal.ofReal_mul hnp.le]
    exact ENNReal.ofReal_pos.mpr (mul_pos hnp hZ)
  exact ⟨hp,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩

theorem bakryEmeryGibbsCoordinateInitialMeasure_assembly {n : ℕ} (hn : 0 < n)
    (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W) (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2)) :
    (bakryEmeryGibbsCoordinateInitialMeasure n W).map (ginibreHamiltonianOUCoordinateAssembly n) =
      bakryEmeryNormalizedGibbs volume W := by
  have hnp : 0 < ((n : ℝ)/Real.pi)^n := by positivity
  have hcn : ENNReal.ofReal (((n : ℝ)/Real.pi)^n) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hnp
  unfold bakryEmeryGibbsCoordinateInitialMeasure bakryEmeryNormalizedGibbs
  rw [Measure.map_smul _ (ginibreHamiltonianOUCoordinateAssembly
      n).continuous.measurable.aemeasurable,
    bakryEmeryGibbsCoordinateRawMeasure_assembly hn W hW.continuous,
    bakryEmeryGibbsCoordinateRawMeasure_mass hn W hW κ hκ hc, smul_smul]
  congr 1
  rw [ENNReal.mul_inv (Or.inl hcn) (Or.inl ENNReal.ofReal_ne_top)]
  calc
    (ENNReal.ofReal (((n : ℝ)/Real.pi)^n))⁻¹ * (ENNReal.ofReal (∫ z, Real.exp (-W z)))⁻¹ *
        ENNReal.ofReal (((n : ℝ)/Real.pi)^n) =
      ((ENNReal.ofReal (((n : ℝ)/Real.pi)^n))⁻¹*ENNReal.ofReal (((n : ℝ)/Real.pi)^n))*
        (ENNReal.ofReal (∫ z, Real.exp (-W z)))⁻¹ := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hcn ENNReal.ofReal_ne_top, one_mul]

theorem bakryEmeryGibbsCoordinateInitialMeasure_probability {n : ℕ} (hn : 0 < n)
    (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W) (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2)) :
    IsProbabilityMeasure (bakryEmeryGibbsCoordinateInitialMeasure n W) := by
  obtain ⟨hp, ht⟩ := bakryEmeryGibbsCoordinateRawMeasure_mass_valid hn W hW κ hκ hc
  constructor
  unfold bakryEmeryGibbsCoordinateInitialMeasure
  rw [smul_apply]
  exact ENNReal.inv_mul_cancel hp.ne' ht

end
end GinibrePoincare

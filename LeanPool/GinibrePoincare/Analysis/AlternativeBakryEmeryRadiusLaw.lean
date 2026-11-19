/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryRadiusLaw.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryRegularizedEuclidean
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsInitialLawHilbert
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Norm
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
/-!
# Alternative Bakry Emery radius law

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmeryEuclideanGibbs_radius_energy_integral`,
`bakryEmeryEuclideanGibbs_radius_entropy`.
-/

@[expose] public section
open MeasureTheory Set
namespace GinibrePoincare
noncomputable section

/-- Exact actual normalized Euclidean Gibbs radius law. -/
theorem bakryEmeryEuclideanGibbs_radius_law
    (n k : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ) (V : Potential)
    (hV : Continuous V) (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V) :
    (bakryEmeryNormalizedGibbs volume
      (bakryEmeryEuclideanLiftPotential (E := EuclideanSpace ℝ (Fin (k+1)×Fin 2)) n V)).map norm =
      (potentialSquaredRadiusLaw n k V).map Real.sqrt := by
  let W := bakryEmeryRegularizedConfigurationPotential n (k+1) V 0
  have hW : Continuous W :=
    continuous_const.mul (hV.comp (Complex.continuous_ofReal.comp
      (Real.continuous_sqrt.comp (contDiff_configurationNormSq.continuous.add continuous_const))))
  have hphys : (fun z : Configuration (k+1) =>
      bakryEmeryEuclideanLiftPotential n V (bakryEmeryBlockHilbertEquiv k z)) = W := by
    funext z
    have hq : ‖bakryEmeryBlockHilbertEquiv k z‖^2=configurationNormSq z := by
      change ‖(WithLp.toLp 2 z : BakryEmeryHilbertBlock k)‖^2 = _
      rw [PiLp.norm_sq_eq_of_L2]
      simp only [configurationNormSq, Complex.normSq_eq_norm_sq]
    simp only [W, bakryEmeryRegularizedConfigurationPotential, bakryEmeryEuclideanLiftPotential,
      zero_pow (by decide : 2 ≠ 0), add_zero,←hq, Real.sqrt_sq (norm_nonneg _)]
  have hp := bakryEmeryBlockLift_eq_normalizedGibbs n k hn ρ hρ V hV hrot hc
  rw [hphys] at hp
  have hm := bakryEmeryConfiguration_normalizedGibbs_map (k+1) W hW
  rw [←hp, bakryEmeryRegularizedConfigurationPotential_euclidean] at hm
  have hz : bakryEmeryRegularizedLiftPotential (E := EuclideanSpace ℝ (Fin (k+1)×Fin 2)) n V 0 =
      bakryEmeryEuclideanLiftPotential n V := by
    funext x
    simp only [bakryEmeryRegularizedLiftPotential, bakryEmeryEuclideanLiftPotential,
      zero_pow (by decide : 2 ≠ 0), add_zero, Real.sqrt_sq (norm_nonneg _)]
  rw [hz] at hm
  change (bakryEmeryBlockLift n k V).map (configurationEuclideanEquiv (k+1)) =
    bakryEmeryNormalizedGibbs volume
      (bakryEmeryEuclideanLiftPotential (E := EuclideanSpace ℝ (Fin (k+1)×Fin 2)) n V) at hm
  rw [←hm, Measure.map_map continuous_norm.measurable (configurationEuclideanEquiv
      (k+1)).continuous.measurable]
  have hfun : norm ∘ configurationEuclideanEquiv (k+1) =
      Real.sqrt ∘ gaussianBlockRadius 1 (k+1) := by
    funext z
    rw [Function.comp_apply, Function.comp_apply]
    rw [←Real.sqrt_sq (norm_nonneg (configurationEuclideanEquiv (k+1) z)),
      ginibre_configurationEuclidean_norm_sq]
    simp only [gaussianBlockRadius, Nat.cast_one, one_mul]
  rw [hfun,←Measure.map_map Real.continuous_sqrt.measurable
    (continuous_gaussianBlockRadius 1 (k+1)).measurable, bakryEmeryBlockLift_squaredRadius n k hV]

theorem bakryEmery_radius_gradient_energy
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [Nontrivial E] (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (x : E) (hx : x ≠ 0) :
    ‖gradient (fun y : E => f ‖y‖) x‖^2 = (deriv f ‖x‖)^2 := by
  have hn : DifferentiableAt ℝ (norm : E → ℝ) x :=
    (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 (norm : E → ℝ) x).differentiableAt one_ne_zero
  have hd := ((hf.differentiable one_ne_zero) ‖x‖).hasDerivAt.comp_hasFDerivAt x hn.hasFDerivAt
  have he : fderiv ℝ (fun y : E => f ‖y‖) x = deriv f ‖x‖ • fderiv ℝ norm x := hd.fderiv
  simp only [gradient, LinearIsometryEquiv.norm_map, he, norm_smul, norm_fderiv_norm hn,
    mul_one, Real.norm_eq_abs, sq_abs]

theorem bakryEmeryEuclideanGibbs_radius_gradient_energy_ae
    (n k : ℕ) (V : Potential) (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    ∀ᵐ x ∂bakryEmeryNormalizedGibbs volume
      (bakryEmeryEuclideanLiftPotential (E := EuclideanSpace ℝ (Fin (k+1)×Fin 2)) n V),
      ‖gradient (fun y : EuclideanSpace ℝ (Fin (k+1)×Fin 2) => f ‖y‖) x‖^2 =
        (deriv f ‖x‖)^2 := by
  let E := EuclideanSpace ℝ (Fin (k+1)×Fin 2)
  have ha : bakryEmeryNormalizedGibbs (volume : Measure E)
      (bakryEmeryEuclideanLiftPotential n V) ≪ volume := by
    unfold bakryEmeryNormalizedGibbs
    exact (withDensity_absolutelyContinuous _ _).smul_left _
  filter_upwards [((volume : Measure E).ae_ne 0).filter_mono ha.ae_le] with x hx
  exact bakryEmery_radius_gradient_energy f hf x hx

theorem bakryEmeryEuclideanGibbs_radius_energy_integral
    (n k : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ) (V : Potential)
    (hV : Continuous V) (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    (∫ x, ‖gradient (fun y : EuclideanSpace ℝ (Fin (k+1)×Fin 2) => f ‖y‖) x‖^2
      ∂bakryEmeryNormalizedGibbs volume (bakryEmeryEuclideanLiftPotential n V)) =
    ∫ r, (deriv f r)^2 ∂(potentialSquaredRadiusLaw n k V).map Real.sqrt := by
  rw [integral_congr_ae (bakryEmeryEuclideanGibbs_radius_gradient_energy_ae n k V f hf)]
  rw [←bakryEmeryEuclideanGibbs_radius_law n k hn ρ hρ V hV hrot hc]
  exact (integral_map continuous_norm.measurable.aemeasurable
    (show AEStronglyMeasurable (fun r => (deriv f r)^2) _ from
      (hf.continuous_deriv_one.pow 2).aestronglyMeasurable)).symm

theorem bakryEmeryEuclideanGibbs_radius_entropy
    (n k : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ) (V : Potential)
    (hV : Continuous V) (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (f : ℝ → ℝ) (hf : Continuous f) :
    squareEntropy (bakryEmeryNormalizedGibbs volume
      (bakryEmeryEuclideanLiftPotential (E := EuclideanSpace ℝ (Fin (k+1)×Fin 2)) n V))
      (fun x => f ‖x‖) = squareEntropy ((potentialSquaredRadiusLaw n k V).map Real.sqrt) f := by
  rw [←bakryEmeryEuclideanGibbs_radius_law n k hn ρ hρ V hV hrot hc]
  exact (squareEntropy_map _ norm continuous_norm.measurable.aemeasurable f
    (hf.pow 2).aestronglyMeasurable (continuous_square_mul_log hf).aestronglyMeasurable).symm

end
end GinibrePoincare

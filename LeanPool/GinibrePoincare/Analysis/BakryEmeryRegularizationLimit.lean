/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BakryEmeryRegularizationLimit.lean.
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

public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryRegularizedLift
public import LeanPool.GinibrePoincare.Analysis.GinibreEntropy
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Actual Gibbs-measure convergence under the smooth radial regularizations.
The Gaussian majorant is the proved confinement bound, not an assumed LSI.
-/

@[expose] public section
open MeasureTheory Set Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- Normalization by the actual integral of the positive Gibbs density. -/
def bakryEmeryNormalizedGibbs (μ : Measure E) (W : E → ℝ) : Measure E :=
  (ENNReal.ofReal (∫ x, Real.exp (-W x) ∂μ))⁻¹ •
    μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-W x)))

/-- Exact normalized Gibbs expectation, without a partition certificate. -/
theorem bakryEmeryNormalizedGibbs_integral (μ : Measure E) (W : E → ℝ)
    (hW : Continuous W) (f : E → ℝ) :
    (∫ x, f x ∂bakryEmeryNormalizedGibbs μ W) =
      (∫ x, Real.exp (-W x) * f x ∂μ) / (∫ x, Real.exp (-W x) ∂μ) := by
  unfold bakryEmeryNormalizedGibbs
  rw [integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul (μ := μ)
      (f := fun x => ENNReal.ofReal (Real.exp (-W x)))
      (by fun_prop)
      (Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)) f]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun x => Real.exp_nonneg _))]
  ring

omit [BorelSpace E] in
/-- The normalized positive integrable Gibbs density is a probability law. -/
theorem bakryEmeryNormalizedGibbs_probability (μ : Measure E) [NeZero μ]
    (W : E → ℝ) (_ : Continuous W)
    (hI : Integrable (fun x => Real.exp (-W x)) μ) :
    IsProbabilityMeasure (bakryEmeryNormalizedGibbs μ W) := by
  constructor
  have hpos := integral_exp_pos hI
  unfold bakryEmeryNormalizedGibbs
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall (fun x => Real.exp_nonneg _))]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hpos) ENNReal.ofReal_ne_top

/-- Every bounded measurable test converges under the actual unnormalized
smooth radial densities; the uniform domination is proved from strong convexity. -/
theorem bakryEmeryRegularizedLift_test_integral_tendsto (μ : Measure E)
    (n : ℕ) (ρ : ℝ) (V : Potential) (hV : Continuous V)
    (hρ : 0 ≤ ρ) (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (hG : Integrable (fun x : E => Real.exp (-((n : ℝ)*ρ)/2*‖x‖^2)) μ)
    (f : E → ℝ) (hf : AEStronglyMeasurable f μ) (C : ℝ)
    (_ : 0 ≤ C) (hb : ∀ x, ‖f x‖ ≤ C) :
    Tendsto (fun ε : ℝ => ∫ x, Real.exp (-bakryEmeryRegularizedLiftPotential n V ε x)*f x ∂μ)
      (𝓝 0) (𝓝 (∫ x, Real.exp (-bakryEmeryEuclideanLiftPotential n V x)*f x ∂μ)) := by
  let B : E → ℝ := fun x => C * Real.exp (-(n : ℝ)*V 0) *
    Real.exp (-((n : ℝ)*ρ)/2*‖x‖^2)
  have hmeas (ε : ℝ) : AEStronglyMeasurable
      (fun x : E => Real.exp (-bakryEmeryRegularizedLiftPotential n V ε x)*f x) μ := by
    have hcont : Continuous (fun x : E => bakryEmeryRegularizedLiftPotential n V ε x) :=
      continuous_const.mul (hV.comp (Complex.continuous_ofReal.comp
        (Real.continuous_sqrt.comp ((continuous_norm.pow 2).add continuous_const))))
    exact hcont.neg.rexp.aestronglyMeasurable.mul hf
  apply tendsto_integral_filter_of_dominated_convergence B
    (Eventually.of_forall hmeas)
    (Eventually.of_forall (fun ε => Eventually.of_forall (fun x => ?_)))
    (hG.const_mul (C * Real.exp (-(n : ℝ)*V 0)))
    (Eventually.of_forall (fun x => ?_))
  · dsimp [B]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    change _ * ‖f x‖ ≤ _
    have hd := bakryEmeryRegularizedLift_density_domination n ρ ε hρ hrot hc x
    calc
      Real.exp (-bakryEmeryRegularizedLiftPotential n V ε x) * ‖f x‖ ≤
          (Real.exp (-(n : ℝ)*V 0)*Real.exp (-((n : ℝ)*ρ)/2*‖x‖^2))*C :=
        mul_le_mul hd (hb x) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · exact (Real.continuous_exp.continuousAt.tendsto.comp
      (bakryEmeryRegularizedLift_tendsto n V hV x).neg).mul tendsto_const_nhds

/-- Bounded test expectations converge for the actual normalized Gibbs laws. -/
theorem bakryEmeryRegularizedLift_expectation_tendsto (μ : Measure E) [NeZero μ]
    (n : ℕ) (ρ : ℝ) (V : Potential) (hV : Continuous V)
    (hρ : 0 ≤ ρ) (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (hG : Integrable (fun x : E => Real.exp (-((n : ℝ)*ρ)/2*‖x‖^2)) μ)
    (f : E → ℝ) (hf : AEStronglyMeasurable f μ) (C : ℝ)
    (hC : 0 ≤ C) (hb : ∀ x, ‖f x‖ ≤ C) :
    Tendsto (fun ε : ℝ => ∫ x, f x ∂bakryEmeryNormalizedGibbs μ
      (bakryEmeryRegularizedLiftPotential n V ε)) (𝓝 0)
      (𝓝 (∫ x, f x ∂bakryEmeryNormalizedGibbs μ
        (bakryEmeryEuclideanLiftPotential n V))) := by
  have hcont (ε : ℝ) : Continuous (bakryEmeryRegularizedLiftPotential (E := E) n V ε) :=
    continuous_const.mul (hV.comp (Complex.continuous_ofReal.comp
      (Real.continuous_sqrt.comp ((continuous_norm.pow 2).add continuous_const))))
  have hcont0 : Continuous (bakryEmeryEuclideanLiftPotential (E := E) n V) :=
    continuous_const.mul (hV.comp (Complex.continuous_ofReal.comp continuous_norm))
  have hmass := bakryEmeryRegularizedLift_test_integral_tendsto μ n ρ V hV hρ hrot hc hG
    (fun _ => 1) aestronglyMeasurable_const 1 (by norm_num) (by simp)
  simp only [mul_one] at hmass
  have hI : Integrable (fun x => Real.exp (-bakryEmeryEuclideanLiftPotential n V x)) μ := by
    apply (hG.const_mul (Real.exp (-(n : ℝ)*V 0))).mono' hcont0.neg.rexp.aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    have hd := bakryEmeryRegularizedLift_density_domination n ρ 0 hρ hrot hc x
    simpa [bakryEmeryRegularizedLiftPotential, bakryEmeryEuclideanLiftPotential,
      Real.sqrt_sq (norm_nonneg x), Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hd
  simp_rw [bakryEmeryNormalizedGibbs_integral μ _ (hcont _) f]
  rw [bakryEmeryNormalizedGibbs_integral μ _ hcont0 f]
  exact (bakryEmeryRegularizedLift_test_integral_tendsto μ n ρ V hV hρ hrot hc hG f hf C hC hb).div
    hmass (integral_exp_pos hI).ne'

/-- In particular every continuous compact test has convergent expectations. -/
theorem bakryEmeryRegularizedLift_compact_expectation_tendsto (μ : Measure E) [NeZero μ]
    (n : ℕ) (ρ : ℝ) (V : Potential) (hV : Continuous V)
    (hρ : 0 ≤ ρ) (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (hG : Integrable (fun x : E => Real.exp (-((n : ℝ)*ρ)/2*‖x‖^2)) μ)
    (f : E → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (fun ε : ℝ => ∫ x, f x ∂bakryEmeryNormalizedGibbs μ
      (bakryEmeryRegularizedLiftPotential n V ε)) (𝓝 0)
      (𝓝 (∫ x, f x ∂bakryEmeryNormalizedGibbs μ
        (bakryEmeryEuclideanLiftPotential n V))) := by
  obtain ⟨C, hC⟩ := hf.norm.bddAbove_range_of_hasCompactSupport hfc.norm
  have hb (x : E) : ‖f x‖ ≤ C := hC (mem_range_self x)
  exact bakryEmeryRegularizedLift_expectation_tendsto μ n ρ V hV hρ hrot hc hG f
    hf.aestronglyMeasurable C ((norm_nonneg (f 0)).trans (hb 0)) hb

/-- Square entropy converges, including observables with zeros; continuity of
`u log u` supplies the zero-value passage rather than division by the profile. -/
theorem bakryEmeryRegularizedLift_entropy_tendsto (μ : Measure E) [NeZero μ]
    (n : ℕ) (ρ : ℝ) (V : Potential) (hV : Continuous V)
    (hρ : 0 ≤ ρ) (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (hG : Integrable (fun x : E => Real.exp (-((n : ℝ)*ρ)/2*‖x‖^2)) μ)
    (f : E → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (fun ε : ℝ => squareEntropy (bakryEmeryNormalizedGibbs μ
      (bakryEmeryRegularizedLiftPotential n V ε)) f) (𝓝 0)
      (𝓝 (squareEntropy (bakryEmeryNormalizedGibbs μ
        (bakryEmeryEuclideanLiftPotential n V)) f)) := by
  have hs := bakryEmeryRegularizedLift_compact_expectation_tendsto μ n ρ V hV hρ hrot hc hG
    (fun x => f x^2) (hf.pow 2) (by
      apply hfc.mono
      intro x hx hz
      apply hx
      simp [hz])
  have hl := bakryEmeryRegularizedLift_compact_expectation_tendsto μ n ρ V hV hρ hrot hc hG
    (fun x => f x^2*Real.log (f x^2)) (continuous_square_mul_log hf)
    (compactSupport_square_mul_log hfc)
  unfold squareEntropy
  exact hl.sub (Real.continuous_mul_log.continuousAt.tendsto.comp hs)

end
end GinibrePoincare

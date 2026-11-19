/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryGibbsLSIObservables.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsLSIContraction
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Analysis.Calculus.FDeriv.Const
/-!
# Alternative Bakry Emery Gibbs LSI observables

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmery_compactGradientEnergy_uniformContinuous`,
`bakryEmery_compactSquareEntropy_uniformContinuous`,
`bakryEmery_stationaryCoupling_expectation_tendsto`.
-/

@[expose] public section
open Set Filter MeasureTheory
open scoped Topology
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- The actual Fisher energy density of a compactly supported C¹ observable
is uniformly continuous, enabling synchronous equilibrium passage. -/
theorem bakryEmery_compactGradientEnergy_uniformContinuous
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    UniformContinuous (fun x => ‖gradient f x‖^2) := by
  have hc : Continuous (gradient f) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (hf.fderiv_right (m := 0) (by norm_num)).continuous
  have hgs : HasCompactSupport (gradient f) :=
    (hs.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ E).symm) (map_zero _)
  exact (hgs.comp_left (g := fun x => ‖x‖^2) (by simp)).uniformContinuous_of_continuous
    (hc.norm.pow 2)

omit [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The two literal square-entropy observables are uniformly continuous on
a compact test domain, including their value at zeros. -/
theorem bakryEmery_compactSquareEntropy_uniformContinuous
    (f : E → ℝ) (hf : Continuous f) (hs : HasCompactSupport f) :
    UniformContinuous (fun x => f x^2) ∧
    UniformContinuous (fun x => f x^2*Real.log (f x^2)) := by
  constructor
  · exact (hs.comp_left (g := fun x : ℝ => x^2) (by simp)).uniformContinuous_of_continuous
      (hf.pow 2)
  · exact (hs.comp_left (g := fun x : ℝ => x^2*Real.log (x^2)) (by
      simp)).uniformContinuous_of_continuous
      (continuous_square_mul_log hf)

/-- Dominated convergence for moving synchronous pairs. No convergence of
either marginal state and no moment condition on its position is assumed. -/
theorem bakryEmery_coupledObservable_integral_difference_tendsto
    {Ω A : Type*} [MeasurableSpace Ω] [PseudoMetricSpace A]
    (P : Measure Ω) [IsFiniteMeasure P]
    (g : A → ℝ) (hg : UniformContinuous g) (C : ℝ) (hC : ∀ x, |g x| ≤ C)
    (X Y : ℕ → Ω → A)
    (hX : ∀ n, AEStronglyMeasurable (fun ω => g (X n ω)) P)
    (hY : ∀ n, AEStronglyMeasurable (fun ω => g (Y n ω)) P)
    (hXY : ∀ᵐ ω ∂P, Tendsto (fun n => dist (X n ω) (Y n ω)) atTop (nhds 0)) :
    Tendsto (fun n => ∫ ω, g (X n ω)-g (Y n ω) ∂P) atTop (nhds 0) := by
  have hbound (n : ℕ) (ω : Ω) : ‖g (X n ω)-g (Y n ω)‖ ≤ 2*C := by
    rw [Real.norm_eq_abs]
    exact (abs_sub (g (X n ω)) (g (Y n ω))).trans (by linarith [hC (X n ω), hC (Y n ω)])
  have hh : Tendsto (fun n => ∫ ω, g (X n ω)-g (Y n ω) ∂P) atTop
      (nhds (∫ _ : Ω, (0 : ℝ) ∂P)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => 2*C)
      (Eventually.of_forall (fun n => (hX n).sub (hY n)))
      (Eventually.of_forall (fun n => ae_of_all _ (hbound n))) (integrable_const _) ?_
    filter_upwards [hXY] with ω hω
    exact bakryEmery_uniformObservable_difference_tendsto g hg
      (fun n => X n ω) (fun n => Y n ω) hω
  simpa only [integral_zero] using hh

/-- A bounded uniformly continuous marginal expectation converges to an
actual stationary marginal whenever the two states synchronously coalesce. -/
theorem bakryEmery_stationaryCoupling_expectation_tendsto
    {Ω A : Type*} [MeasurableSpace Ω] [PseudoMetricSpace A]
    [MeasurableSpace A] [BorelSpace A]
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure A)
    (g : A → ℝ) (hg : UniformContinuous g) (C : ℝ) (hC : ∀ x, |g x| ≤ C)
    (X Y : ℕ → Ω → A) (hX : ∀ n, AEMeasurable (X n) P)
    (hY : ∀ n, ProbabilityTheory.HasLaw (Y n) ν P)
    (hXY : ∀ᵐ ω ∂P, Tendsto (fun n => dist (X n ω) (Y n ω)) atTop (nhds 0)) :
    Tendsto (fun n => ∫ ω, g (X n ω) ∂P) atTop (nhds (∫ x, g x ∂ν)) := by
  have hx n : AEStronglyMeasurable (fun ω => g (X n ω)) P :=
    (hg.continuous.measurable.comp_aemeasurable (hX n)).aestronglyMeasurable
  have hy n : AEStronglyMeasurable (fun ω => g (Y n ω)) P :=
    (hg.continuous.measurable.comp_aemeasurable (hY n).aemeasurable).aestronglyMeasurable
  have hh := bakryEmery_coupledObservable_integral_difference_tendsto P g hg C hC X Y hx hy hXY
  have hxi n : Integrable (fun ω => g (X n ω)) P :=
    Integrable.of_bound (hx n) C (ae_of_all _ (fun ω => by simpa only [Real.norm_eq_abs] using hC (X
                                                             n ω)))
  have hyi n : Integrable (fun ω => g (Y n ω)) P :=
    Integrable.of_bound (hy n) C (ae_of_all _ (fun ω => by simpa only [Real.norm_eq_abs] using hC (Y
                                                             n ω)))
  have he n : (∫ ω, g (Y n ω) ∂P) = ∫ x, g x ∂ν :=
    (hY n).integral_comp hg.continuous.aestronglyMeasurable
  have ht := hh.add_const (∫ x, g x ∂ν)
  simp only [zero_add] at ht
  convert ht using 1
  funext n
  rw [integral_sub (hxi n) (hyi n), he n, sub_add_cancel]

end
end GinibrePoincare

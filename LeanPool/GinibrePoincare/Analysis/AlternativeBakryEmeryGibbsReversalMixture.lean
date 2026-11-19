/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryGibbsReversalMixture.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsReversalInitialPaths
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsReversalKilledLaw
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianKilledMixtureIntegration
/-!
# Alternative Bakry Emery Gibbs reversal mixture

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmeryGibbs_killed_gaussian_initial_identity`.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous configuration paths `C(Icc 0 T, Configuration n)`. -/
local instance bakryGibbsMixturePathMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
local instance bakryGibbsMixture_pathBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩

/-- Integration of the proved fixed-initial Girsanov laws against the actual
Gaussian initial distribution. The likelihood cancellation holds at every
initial state, without any collision exclusions. -/
theorem bakryEmeryGibbs_killed_gaussian_initial_identity {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W)
    (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2))
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) (hT : 0 < T) (R : ℝ) :
    let γ := Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2))
    (((γ.prod P).withDensity (fun x => ENNReal.ofReal
      (Real.exp (-bakryEmeryGibbsRelativePotential W (ginibreHamiltonianOUCoordinateAssembly n
          x.1))))).map
      (bakryEmeryGibbsGaussianInitialPath W hW κ hκ hc T B)).restrict
        (bakryEmeryGibbsCompactSurvival n T R) =
    ((γ.prod P).map (bakryEmeryGibbsGaussianInitialOUPath n T B)).withDensity
      (bakryEmeryGibbsKilledOUAction W T R) := by
  let γ := Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2))
  let C := bakryEmeryGibbsGaussianInitialPath W hW κ hκ hc T B
  let O := bakryEmeryGibbsGaussianInitialOUPath n T B
  let S := bakryEmeryGibbsCompactSurvival n T R
  let a := bakryEmeryGibbsOUAction W T T.property
  let w := fun x => ENNReal.ofReal (Real.exp
    (-bakryEmeryGibbsRelativePotential W (ginibreHamiltonianOUCoordinateAssembly n x)))
  let e := fun x => ENNReal.ofReal (Real.exp
    (bakryEmeryGibbsRelativePotential W (ginibreHamiltonianOUCoordinateAssembly n x)))
  have hC := bakryEmeryGibbsGaussianInitialPath_measurable W hW κ hκ hc T B P hB
  have hO := bakryEmeryGibbsGaussianInitialOUPath_measurable n T B P hB
  have hS := bakryEmeryGibbsCompactSurvival_measurableSet n T R
  have ha := bakryEmeryGibbsOUAction_measurable hW T T.property
  have hSW : ContDiff ℝ 2 (bakryEmeryGibbsRelativePotential W) :=
    hW.sub (contDiff_const.mul (contDiff_configurationNormSq.of_le (by simp)))
  have hpot := hSW.continuous.measurable.comp
    (ginibreHamiltonianOUCoordinateAssembly n).continuous.measurable
  have hw : Measurable w := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hpot.neg)
  have he : Measurable e := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hpot)
  have hCancel : ∀ᵐ x ∂γ, w x * e x = 1 := by
    apply Filter.Eventually.of_forall
    intro x
    change ENNReal.ofReal (Real.exp (-_)) * ENNReal.ofReal (Real.exp _) = 1
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    simp
  have hFiber : ∀ᵐ x ∂γ,
      (P.map (fun ω => C (x, ω))).restrict S =
      (P.withDensity (fun ω => e x * S.indicator a (O (x, ω)))).map (fun ω => O (x, ω)) := by
    apply Filter.Eventually.of_forall
    intro x
    have h := bakryEmeryGibbs_fixed_initial_killed_law hn W hW κ hκ hc P B hB hiB
      (ginibreHamiltonianOUCoordinateAssembly n x) T hT R
    have hOE : ginibreHamiltonianOUReferenceHorizon n ((n : ℝ)^2)
        (ginibreHamiltonianOUCoordinateAssembly n x) B T = (fun ω => O (x, ω)) := by
      funext ω
      rfl
    rw [hOE] at h
    simpa only [C, O, S, a, e, bakryEmeryGibbsGaussianInitialPath,
      bakryEmeryGibbsGaussianInitialOUPath, bakryEmeryGibbsKilledOUAction,
      ginibreHamiltonianOUReferenceHorizon] using h
  exact ginibre_killed_product_mixture γ P C O hC hO S hS a ha w e hw he hCancel hFiber

end
end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianCenterFunctional.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianProjectedNoise
public import Mathlib.MeasureTheory.Integral.Prod

/-! The actual center solution is a measurable OU functional of center noise only. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

/-- The complex path `t ↦ ∑ j, N t j` of coordinate sums of a driving noise path. -/
def ginibreContinuousNoiseCenter (n : ℕ) (N : GinibreContinuousNoise n) : C(ℝ, ℂ) :=
  (⟨coordinateSumCLM n, (coordinateSumCLM n).continuous⟩ : C(Configuration n, ℂ)).comp N.val

theorem ginibreContinuousNoiseCenter_continuous (n : ℕ) : Continuous (ginibreContinuousNoiseCenter
     n) :=
  (⟨coordinateSumCLM n, (coordinateSumCLM n).continuous⟩ : C(Configuration n,
      ℂ)).continuous_postcomp.comp
    continuous_subtype_val

/-- The value at time `t` of the complex Ornstein–Uhlenbeck path with rate `2α/n`, started at
`coordinateSum z` and driven by `N`. -/
def ginibreCenterOUValue (n : ℕ) (α : ℝ) (z : Configuration n) (t : ℝ≥0)
    (N : C(ℝ, ℂ)) : ℂ := drivenOUPath (2*α/(n : ℝ)) (coordinateSum z) N t

theorem ginibreCenterOUValue_measurable (n : ℕ) (α : ℝ) (z : Configuration n) (t : ℝ≥0) :
    @Measurable C(ℝ, ℂ) ℂ (borel _) _ (ginibreCenterOUValue n α z t) := by
  let : MeasurableSpace C(ℝ, ℂ) := borel _
  let : BorelSpace C(ℝ, ℂ) := ⟨rfl⟩
  have hj : Continuous (fun p : C(ℝ, ℂ) × ℝ => Real.exp ((2*α/(n : ℝ))*p.2) • p.1 p.2) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_snd)).smul continuous_eval
  have hInt : Measurable (fun N : C(ℝ, ℂ) => ∫ s in (0 : ℝ)..(t : ℝ),
      Real.exp ((2*α/(n : ℝ))*s) • N s) := by
    have hi := hj.measurable.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc (0 : ℝ) (t : ℝ)))
    simpa only [intervalIntegral.integral_of_le t.coe_nonneg] using hi.measurable
  exact (continuous_eval_const (t : ℝ)).measurable.add
    (measurable_const.smul (measurable_const.sub (measurable_const.smul hInt)))

theorem ginibreBrownian_center_OU_factorization {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      coordinateSum (ginibreBrownianMaximalProcess n α z B t ω) =
        ginibreCenterOUValue n α z t
          (ginibreContinuousNoiseCenter n (ginibreBrownianFullContinuousNoise n B α ω)) := by
  filter_upwards [(ginibreBrownianMaximalProcess_global_original_solution hn α z hz B P hB hind).2,
    ginibreBrownianFullContinuousNoise_ae n B P hB α] with ω hs hNoise
  intro t
  let X := fun u : ℝ => ginibreBrownianMaximalProcess n α z B (Real.toNNReal u) ω
  have hN : (ginibreBrownianFullContinuousNoise n B α ω).val = ginibreConfigurationBrownianNoise n B
      α ω :=
    funext hNoise
  have heq : IsGinibreDrivenPath n α (ginibreBrownianFullContinuousNoise n B α ω).val X := by
    rw [hN]
    exact hs.2.2.2
  have hh := ginibreDrivenPath_center_eq_OU
    (ginibreBrownianFullContinuousNoise n B α ω).val.continuous hs.1 heq (t : ℝ) t.coe_nonneg
  simp only [Real.toNNReal_zero, Real.toNNReal_coe, hs.2.1] at hh
  have hCenter : (ginibreContinuousNoiseCenter n (ginibreBrownianFullContinuousNoise n B α ω) : ℝ →
      ℂ) =
      (fun s => coordinateSum ((ginibreBrownianFullContinuousNoise n B α ω).val s)) := by
    funext s
    exact coordinateSumCLM_apply n _
  unfold ginibreCenterOUValue
  rw [hCenter]
  exact hh

end
end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticOUPast.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticOUStep

/-! # Adapted measurable convolution and independent actual OU innovations -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BigOperators
namespace GinibrePoincare
noncomputable section

theorem ginibreUniformBrownianTime_le_end (t : ℝ≥0) (n i : ℕ) (hi : i ≤ n + 1) :
    ginibreUniformBrownianTime t n i ≤ t := by
  have h := ginibreUniformBrownianTime_mono t n hi
  have he : ginibreUniformBrownianTime t n (n + 1) = t := by
    apply NNReal.eq
    rw [ginibreUniformBrownianTime_coe, ginibreUniformTime_end]
  rwa [he] at h

/-- The measurable convolution only reads the actual elapsed Brownian path. -/
theorem ginibreOUConvolutionFunctional_congr_interval (rate t : ℝ≥0)
    (path q : ℝ≥0 → ℝ) (heq : ∀ u ≤ t, path u = q u) :
    ginibreOUConvolutionFunctional rate t path = ginibreOUConvolutionFunctional rate t q := by
  unfold ginibreOUConvolutionFunctional
  congr 1
  funext n
  unfold ginibreBrownianOURiemannSum
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [heq _ (ginibreUniformBrownianTime_le_end t n i (Nat.le_of_lt i.is_lt)),
    heq _ (ginibreUniformBrownianTime_le_end t n (i.val + 1) (Nat.succ_le_of_lt i.is_lt))]

/-- Actual OU value as a measurable function of the Brownian past alone. -/
def ginibreOUPastFunctional (rate s : ℝ≥0) (x : ℝ) (past : Set.Iic s → ℝ) : ℝ :=
  ginibreOUDecay rate s * x + ginibreOUConvolutionFunctional rate s
    (fun u => past ⟨min u s, Set.mem_Iic.mpr (min_le_right _ _)⟩)

theorem ginibreOUPastFunctional_measurable (rate s : ℝ≥0) (x : ℝ) :
    Measurable (ginibreOUPastFunctional rate s x) := by
  apply measurable_const.add
  apply (ginibreOUConvolutionFunctional_measurable rate s).comp
  apply Measurable.of_eval
  intro u
  exact measurable_pi_apply _

theorem ginibreOUPastFunctional_ae_eq {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (rate s : ℝ≥0) (x : ℝ) :
    (fun ω => ginibreOUPastFunctional rate s x (fun v : Set.Iic s => B v ω)) =ᵐ[P]
      ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) x s := by
  filter_upwards [ginibreOUConvolutionFunctional_ae_eq B P hB rate s] with ω hω
  have he : ginibreOUConvolutionFunctional rate s (fun u => B (min u s) ω) =
      ginibreOUConvolutionFunctional rate s (fun u => B u ω) :=
    ginibreOUConvolutionFunctional_congr_interval rate s _ _ (fun u hu => by rw [min_eq_left hu])
  change ginibreOUDecay rate s * x +
    ginibreOUConvolutionFunctional rate s (fun u => B (min u s) ω) = _
  rw [he, hω]
  change Real.exp (-(rate : ℝ) * (s : ℝ)) * x +
    drivenOUPath rate 0 (ginibreBrownianNoise B (Real.sqrt (rate : ℝ)) ω) s =
      drivenOUPath rate x (ginibreBrownianNoise B (Real.sqrt (rate : ℝ)) ω) s
  conv_rhs => rw [drivenOUPath_initial_split]
  rfl

theorem ginibreBrownianOUInnovation_independent_value {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (rate s t : ℝ≥0) (x : ℝ) :
    IndepFun (ginibreBrownianOUInnovation B rate s t)
      (ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) x s) P := by
  have h := (ginibreBrownianOUInnovation_independent_past B P hB rate s t).comp
    measurable_id (ginibreOUPastFunctional_measurable rate s x)
  exact h.congr (Filter.Eventually.of_forall fun _ => rfl)
    (ginibreOUPastFunctional_ae_eq B P hB rate s x)

end
end GinibrePoincare

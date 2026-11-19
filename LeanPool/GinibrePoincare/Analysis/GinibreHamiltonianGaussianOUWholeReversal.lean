/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianGaussianOUWholeReversal.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianGaussianOUFiniteLaw
public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalPathLaw

/-!
# Ginibre Hamiltonian Gaussian OU whole reversal

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreBrownianOU_stationary_whole_horizon_law_reversal`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownianOU_stationary_whole_horizon_law_reversal
    {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : IsBrownianReal B P) (Z : Ω → ℝ) (hZ : HasLaw Z (gaussianReal 0 (1 / 2)) P)
    (hind : IndepFun Z (fun ω t => B t ω) P) (rate T : ℝ≥0) :
    P.map (fun ω => fun t : Icc (0 : ℝ≥0) T =>
      ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) (Z ω) t.val ω) =
    P.map (fun ω => fun t : Icc (0 : ℝ≥0) T =>
      ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) (Z ω) ((T-t.val : ℝ≥0) : ℝ) ω) := by
  classical
  let X : Ω → Icc (0 : ℝ≥0) T → ℝ := fun ω t =>
    ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) (Z ω) t.val ω
  let Y : Ω → Icc (0 : ℝ≥0) T → ℝ := fun ω t =>
    ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) (Z ω) ((T-t.val : ℝ≥0) : ℝ) ω
  have hG := ginibreBrownianOU_gaussian_initial_isGaussianProcess P B hB Z hZ.hasGaussianLaw hind
      rate
  have hmX : Measurable X := Measurable.of_eval (fun t =>
    aemeasurable_iff_measurable.mp (hG.aemeasurable t.val))
  have hmY : Measurable Y := Measurable.of_eval (fun t =>
    aemeasurable_iff_measurable.mp (hG.aemeasurable (T-t.val)))
  let μ (I : Finset (Icc (0 : ℝ≥0) T)) : Measure (I → ℝ) :=
    P.map (fun ω => I.restrict (X ω))
  have hx : IsProjectiveLimit (P.map X) μ := by
    intro I
    rw [Measure.map_map (show Measurable I.restrict by fun_prop) hmX]
    rfl
  have hy : IsProjectiveLimit (P.map Y) μ := by
    intro I
    rw [Measure.map_map (show Measurable I.restrict by fun_prop) hmY]
    have he := ginibreBrownianOU_stationary_finite_law_reversal B P hB Z hZ hind rate T
      (fun i : I => i.val.val) (fun i => i.val.property.2)
    let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℝ)
    have he' := congrArg (fun ν : Measure (EuclideanSpace ℝ I) => ν.map e) he
    rw [Measure.map_map e.continuous.measurable
      (show Measurable (fun ω => WithLp.toLp 2 (fun i : I => X ω i.val)) from
        (PiLp.continuous_toLp 2 _).measurable.comp (Measurable.of_eval (fun i =>
            (measurable_pi_apply i.val).comp hmX))),
      Measure.map_map e.continuous.measurable
      (show Measurable (fun ω => WithLp.toLp 2 (fun i : I => Y ω i.val)) from
        (PiLp.continuous_toLp 2 _).measurable.comp (Measurable.of_eval (fun i =>
            (measurable_pi_apply i.val).comp hmY)))] at he'
    exact he'.symm
  exact hx.unique hy

end
end GinibrePoincare

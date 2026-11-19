/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticOUPlanarInnovation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticIndependentBlocks
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticOUStep

/-! # Joint planar innovations independent of the entire joint Brownian past -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownianOU_innovation_past_block {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (rate s t : ℝ≥0) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ × (Set.Iic s → ℝ), Measurable F ∧
      (fun ω => F (fun u => B u ω)) =ᵐ[P]
        (fun ω => (ginibreBrownianOUInnovation B rate s t ω, fun v => B v ω)) := by
  refine ⟨fun p => (ginibreOUConvolutionFunctional rate t (fun u => p (s + u) - p s),
      fun v => p v), ?_, ?_⟩
  · apply Measurable.prodMk
    · exact (ginibreOUConvolutionFunctional_measurable rate t).comp (by fun_prop)
    · fun_prop
  · filter_upwards [ginibreOUConvolutionFunctional_ae_eq _ P (hB.shift s) rate t] with ω hω
    exact congrArg (fun y => (y, fun v : Set.Iic s => B v ω)) hω

theorem ginibreBrownianOU_planar_innovations_independent_past {Ω : Type*}
    [MeasurableSpace Ω] (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (hind : IndepFun (fun ω => fun u => Br u ω) (fun ω => fun u => Bi u ω) P)
    (rate s t : ℝ≥0) :
    IndepFun (fun ω => (ginibreBrownianOUInnovation Br rate s t ω,
        ginibreBrownianOUInnovation Bi rate s t ω))
      (fun ω => ((fun v : Set.Iic s => Br v ω), (fun v : Set.Iic s => Bi v ω))) P := by
  let : IsProbabilityMeasure P := hBr.isGaussianProcess.isProbabilityMeasure
  obtain ⟨Fr, hFr, hr⟩ := ginibreBrownianOU_innovation_past_block Br P hBr rate s t
  obtain ⟨Fi, hFi, hi⟩ := ginibreBrownianOU_innovation_past_block Bi P hBi rate s t
  have hblocks := (hind.comp hFr hFi).congr hr hi
  have hmBr : Measurable (fun ω (v : Set.Iic s) => Br v ω) := by
    apply Measurable.of_eval
    intro v
    exact aemeasurable_iff_measurable.mp (hBr.aemeasurable v)
  have hmBi : Measurable (fun ω (v : Set.Iic s) => Bi v ω) := by
    apply Measurable.of_eval
    intro v
    exact aemeasurable_iff_measurable.mp (hBi.aemeasurable v)
  let : IsProbabilityMeasure (P.map (fun ω (v : Set.Iic s) => Br v ω)) := by infer_instance
  let : IsProbabilityMeasure (P.map (fun ω (v : Set.Iic s) => Bi v ω)) := by infer_instance
  have hrPast : HasLaw (fun ω (v : Set.Iic s) => Br v ω)
      (P.map (fun ω (v : Set.Iic s) => Br v ω)) P := ⟨hmBr.aemeasurable, rfl⟩
  have hiPast : HasLaw (fun ω (v : Set.Iic s) => Bi v ω)
      (P.map (fun ω (v : Set.Iic s) => Bi v ω)) P := ⟨hmBi.aemeasurable, rfl⟩
  exact ginibre_independent_blocks_recombine P
    (ginibreBrownianOUInnovation_hasLaw Br P hBr rate s t) hrPast
    (ginibreBrownianOUInnovation_hasLaw Bi P hBi rate s t) hiPast
    (ginibreBrownianOUInnovation_independent_past Br P hBr rate s t)
    (ginibreBrownianOUInnovation_independent_past Bi P hBi rate s t) hblocks

theorem ginibreBrownianOU_planar_innovations_hasLaw {Ω : Type*}
    [MeasurableSpace Ω] (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (hind : IndepFun (fun ω => fun u => Br u ω) (fun ω => fun u => Bi u ω) P)
    (rate s t : ℝ≥0) :
    HasLaw (fun ω => (ginibreBrownianOUInnovation Br rate s t ω,
        ginibreBrownianOUInnovation Bi rate s t ω))
      ((gaussianReal 0 (ginibreOUVariance rate t)).prod
        (gaussianReal 0 (ginibreOUVariance rate t))) P := by
  let := hBr.isGaussianProcess.isProbabilityMeasure
  obtain ⟨Fr, hFr, hr⟩ := ginibreBrownianOU_innovation_past_block Br P hBr rate s t
  obtain ⟨Fi, hFi, hi⟩ := ginibreBrownianOU_innovation_past_block Bi P hBi rate s t
  have hblocks := (hind.comp hFr hFi).congr hr hi
  have h := hblocks.comp measurable_fst measurable_fst
  exact h.hasLaw_prod (ginibreBrownianOUInnovation_hasLaw Br P hBr rate s t)
    (ginibreBrownianOUInnovation_hasLaw Bi P hBi rate s t)

end
end GinibrePoincare

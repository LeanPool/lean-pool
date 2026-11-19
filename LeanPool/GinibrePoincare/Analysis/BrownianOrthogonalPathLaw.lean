/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianOrthogonalPathLaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalFuturePath

/-! The whole path law of an actual independent Brownian family is uniquely
 determined by its original finite-dimensional Brownian laws. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem brownianScalar_whole_path_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [P.IsComplete] (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P) :
    Measurable (fun ω t => B t ω) := by
  apply Measurable.of_eval
  intro t
  exact aemeasurable_iff_measurable.mp (hB.aemeasurable t)

theorem brownianScalar_whole_path_law_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [P.IsComplete] (B C : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C P) :
    P.map (fun ω t => B t ω) = P.map (fun ω t => C t ω) := by
  have hBm := brownianScalar_whole_path_measurable P B hB
  have hCm := brownianScalar_whole_path_measurable P C hC
  have hpB : IsProjectiveLimit (P.map (fun ω t => B t ω)) BrownianReal.projectiveFamily := by
    intro I
    rw [Measure.map_map (show Measurable I.restrict by fun_prop) hBm]
    exact (hB.hasLaw I).map_eq
  have hpC : IsProjectiveLimit (P.map (fun ω t => C t ω)) BrownianReal.projectiveFamily := by
    intro I
    rw [Measure.map_map (show Measurable I.restrict by fun_prop) hCm]
    exact (hC.hasLaw I).map_eq
  exact hpB.unique hpC

/-- Actual whole-family laws are equal, including all jointly indexed times. -/
theorem brownianFamily_whole_path_law_eq {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι] (P : Measure Ω) [P.IsComplete]
    (B C : ι → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hC : ∀ i, IsPreBrownianReal (C i) P)
    (hindB : iIndepFun (fun i ω t => B i t ω) P)
    (hindC : iIndepFun (fun i ω t => C i t ω) P) :
    P.map (fun ω i t => B i t ω) = P.map (fun ω i t => C i t ω) := by
  have := Fintype.ofFinite ι
  have hmB (i : ι) : AEMeasurable (fun ω t => B i t ω) P := (brownianScalar_whole_path_measurable P
      (B i) (hB i)).aemeasurable
  have hmC (i : ι) : AEMeasurable (fun ω t => C i t ω) P := (brownianScalar_whole_path_measurable P
      (C i) (hC i)).aemeasurable
  rw [hindB.map_fun_eq_pi_map hmB, hindC.map_fun_eq_pi_map hmC]
  congr 1
  funext i
  exact brownianScalar_whole_path_law_eq P (B i) (C i) (hB i) (hC i)

/-- Time shifts preserve the whole actual family path law. -/
theorem brownianFamily_shift_whole_path_law_eq {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι] (P : Measure Ω) [P.IsComplete]
    (B : ι → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (s : ℝ≥0) :
    P.map (fun ω i t => brownianFamilyShift B s i t ω) = P.map (fun ω i t => B i t ω) := by
  have := Fintype.ofFinite ι
  have hshift := brownianFamilyShift_isBrownian_independent B P hB hind s
  exact brownianFamily_whole_path_law_eq P _ _
    (fun i => (hshift.1 i).toIsPreBrownianReal) (fun i => (hB i).toIsPreBrownianReal) hshift.2 hind

end
end GinibrePoincare

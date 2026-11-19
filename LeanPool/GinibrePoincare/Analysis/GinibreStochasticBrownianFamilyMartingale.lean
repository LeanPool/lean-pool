/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticBrownianFamilyMartingale.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticBrownianFamilyFiltration
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticPredictableInnovation

/-! Actual Brownian coordinates are martingales in the entire family filtration. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownianFamilyFiltration_increment_conditional {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι] (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (i : ι) (s t : ℝ≥0) (hst : s ≤ t) :
    P[(fun ω => B i t ω-B i s ω) | ginibreBrownianFamilyFiltration B P hB s] =ᵐ[P] (fun _ => 0) :=
        by
  have := Fintype.ofFinite ι
  let := (hB i).isGaussianProcess.isProbabilityMeasure
  let Past := fun ω (p : ι × Set.Iic s) => B p.1 p.2 ω
  have hPast : Measurable Past := by
    apply Measurable.of_eval
    intro p
    exact aemeasurable_iff_measurable.mp ((hB p.1).aemeasurable p.2)
  have hZ := ginibreBrownian_increment_hasLaw (B i) P (hB i) s t hst
  have hInd := (ginibreBrownian_family_increment_independent_past B P hB hind s (t-s)).comp
    (measurable_pi_apply i) measurable_id
  have hInd' : IndepFun (fun ω => B i t ω-B i s ω) Past P := by
    simpa only [Function.comp_def, id_eq, add_tsub_cancel_of_le hst] using hInd
  have hMean : (∫ u : ℝ, u ∂gaussianReal 0 (t-s)) = 0 := integral_id_gaussianReal
  have h := ginibreIndependent_predictable_centered_conditional P Past (fun ω => B i t ω-B i s ω)
    hPast _ hZ hInd' (fun _ => (1 : ℝ)) measurable_const (integrable_const 1)
    (fun u : ℝ => u) measurable_id IsGaussian.integrable_id hMean
  simpa only [one_mul, ginibreBrownianFamilyFiltration, ginibreBrownianFamilyPastSpace, Past] using
      h

theorem ginibreBrownianFamilyFiltration_coordinate_martingale {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι] (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (i : ι) :
    Martingale (B i) (ginibreBrownianFamilyFiltration B P hB) P := by
  have := Fintype.ofFinite ι
  let := (hB i).isGaussianProcess.isProbabilityMeasure
  have hAdapt := ginibreBrownianFamilyFiltration_coordinate_stronglyAdapted B P hB i
  refine ⟨hAdapt, ?_⟩
  intro s t hst
  have hs : Integrable (B i s) P := ((hB i).isGaussianProcess.hasGaussianLaw_eval
      s).memLp_two.integrable (by norm_num)
  have ht : Integrable (B i t) P := ((hB i).isGaussianProcess.hasGaussianLaw_eval
      t).memLp_two.integrable (by norm_num)
  have hCs := condExp_of_stronglyMeasurable (ginibreBrownianFamilyFiltration B P hB |>.le s) (hAdapt
      s) hs
  have hSub := condExp_sub ht hs (ginibreBrownianFamilyFiltration B P hB s)
  rw [hCs] at hSub
  simp only [Pi.sub_def] at hSub
  have hZero := ginibreBrownianFamilyFiltration_increment_conditional B P hB hind i s t hst
  filter_upwards [hSub, hZero] with ω hω hz
  change _ = 0 at hz
  linarith

end
end GinibrePoincare

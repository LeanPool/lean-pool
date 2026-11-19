/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianContinuousPathIndependence.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianGaussianOUContinuousReversal

/-!
# Ginibre Hamiltonian continuous path independence

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibre_iIndepFun_continuousMap_of_raw_paths`,
`ginibreScalarBrownianNormalize_measurable`, `ginibreScalarBrownianNormalize_continuous`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibre_iIndepFun_continuousMap_of_raw_paths
    {Ω ι D E : Type*} [MeasurableSpace Ω] [TopologicalSpace D]
    [TopologicalSpace.SeparableSpace D] [Nonempty D]
    [TopologicalSpace E] [SecondCountableTopology E] [T2Space E]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace C(D, E)] [BorelSpace C(D, E)] [PolishSpace C(D, E)] [Nonempty C(D, E)]
    (P : Measure Ω) (X : ι → Ω → C(D, E))
    (h : iIndepFun (fun i ω t => X i ω t) P) : iIndepFun X P := by
  let d := TopologicalSpace.denseSeq D
  let e : C(D, E) → ℕ → E := fun x k => x (d k)
  have he : MeasurableEmbedding e :=
    (continuous_pi (fun k => continuous_eval_const (d k))).measurableEmbedding (by
      intro x y hxy
      apply DFunLike.coe_injective
      exact (TopologicalSpace.denseRange_denseSeq D).equalizer x.continuous y.continuous hxy)
  have hd : Measurable (fun x : D → E => fun k => x (d k)) :=
    Measurable.of_eval (fun k => measurable_pi_apply (d k))
  have hi := h.comp (fun _ => fun x : D → E => fun k => x (d k)) (fun _ => hd)
  have hj := hi.comp (fun _ => he.invFun) (fun _ => he.measurable_invFun)
  convert hj using 1
  funext i ω
  exact (he.leftInverse_invFun (X i ω)).symm

/-- The Borel σ-algebra on continuous real paths `C(ℝ≥0, ℝ)`. -/
local instance ginibreScalarBrownianCMMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance ginibreScalarBrownianCMBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

/-- Evaluation of a continuous path along the dense sequence `TopologicalSpace.denseSeq ℝ≥0`. -/
def ginibreScalarBrownianDenseEvaluation : C(ℝ≥0, ℝ) → ℕ → ℝ :=
  fun x k => x (TopologicalSpace.denseSeq ℝ≥0 k)

theorem ginibreScalarBrownianDenseEvaluation_embedding :
    MeasurableEmbedding ginibreScalarBrownianDenseEvaluation :=
  (continuous_pi (fun k => continuous_eval_const (TopologicalSpace.denseSeq ℝ≥0
      k))).measurableEmbedding (by
    intro x y hxy
    apply DFunLike.coe_injective
    exact (TopologicalSpace.denseRange_denseSeq ℝ≥0).equalizer x.continuous y.continuous hxy)

/-- A globally measurable normalization from the raw product path space. -/
def ginibreScalarBrownianNormalize (x : ℝ≥0 → ℝ) : C(ℝ≥0, ℝ) :=
  ginibreScalarBrownianDenseEvaluation_embedding.invFun
    (fun k => x (TopologicalSpace.denseSeq ℝ≥0 k))

theorem ginibreScalarBrownianNormalize_measurable : Measurable ginibreScalarBrownianNormalize :=
  ginibreScalarBrownianDenseEvaluation_embedding.measurable_invFun.comp
    (Measurable.of_eval (fun k => measurable_pi_apply (TopologicalSpace.denseSeq ℝ≥0 k)))

theorem ginibreScalarBrownianNormalize_continuous (x : ℝ≥0 → ℝ) (hx : Continuous x) :
    ∀ t, ginibreScalarBrownianNormalize x t = x t := by
  have he := ginibreScalarBrownianDenseEvaluation_embedding.leftInverse_invFun (⟨x, hx⟩ : C(ℝ≥0, ℝ))
  exact fun t => congrArg (fun y : C(ℝ≥0, ℝ) => y t) he

end
end GinibrePoincare

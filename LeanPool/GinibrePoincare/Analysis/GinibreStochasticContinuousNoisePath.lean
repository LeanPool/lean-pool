/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticContinuousNoisePath.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathMeasurableLocalFlow
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticLocalExistence
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Actual Brownian configuration noise as a measurable continuous-path random element. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibre_measurable_continuousMap_of_evaluations
    {Ω T E : Type*} [mΩ : MeasurableSpace Ω] [TopologicalSpace T] [TopologicalSpace.SeparableSpace
        T] [Nonempty T]
    [TopologicalSpace E] [SecondCountableTopology E] [T2Space E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace C(T, E)] [BorelSpace C(T, E)] [PolishSpace C(T, E)]
    (F : Ω → C(T, E)) (hF : ∀ t, Measurable (fun ω => F ω t)) : Measurable F := by
  let d := TopologicalSpace.denseSeq T
  let e : C(T, E) → ℕ → E := fun f k => f (d k)
  have he : Continuous e := continuous_pi (fun k => continuous_eval_const (d k))
  have hinj : Function.Injective e := by
    intro f g hfg
    apply DFunLike.coe_injective
    exact (TopologicalSpace.denseRange_denseSeq T).equalizer f.continuous g.continuous hfg
  apply he.measurableEmbedding hinj |>.measurable_comp_iff.mp
  apply Measurable.of_eval
  intro k
  exact hF (d k)

/-- The configuration Brownian noise of the sample `ω` on `[-1, 1]`, as a continuous map
(replaced by `0` if it is not continuous). -/
def ginibreConfigurationBrownianContinuousPath {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ) (ω : Ω) :
    C(Icc (-1 : ℝ) 1, Configuration n) :=
  ContinuousMap.mkD (fun t => ginibreConfigurationBrownianNoise n B α ω t) 0

theorem ginibreConfigurationBrownianContinuousPath_ae {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P) (α : ℝ) :
    ∀ᵐ ω ∂P, ∀ t : Icc (-1 : ℝ) 1,
      ginibreConfigurationBrownianContinuousPath n B α ω t = ginibreConfigurationBrownianNoise n B α
          ω t := by
  filter_upwards [ginibreConfigurationBrownianNoise_actual n B P hB α] with ω hω
  intro t
  have hc : Continuous (fun t : Icc (-1 : ℝ) 1 => ginibreConfigurationBrownianNoise n B α ω t) :=
      hω.1.comp continuous_subtype_val
  simp [ginibreConfigurationBrownianContinuousPath, ContinuousMap.mkD, hc]

theorem ginibreConfigurationBrownianContinuousPath_measurable {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (α : ℝ) :
    @Measurable _ _ _ (borel C(Icc (-1 : ℝ) 1, Configuration n))
      (ginibreConfigurationBrownianContinuousPath n B α) := by
  let : Nonempty (Icc (-1 : ℝ) 1) := ⟨⟨0, by norm_num⟩⟩
  let : MeasurableSpace C(Icc (-1 : ℝ) 1, Configuration n) := borel _
  let : BorelSpace C(Icc (-1 : ℝ) 1, Configuration n) := ⟨rfl⟩
  apply ginibre_measurable_continuousMap_of_evaluations
  intro t
  apply (aemeasurable_iff_measurable (μ := P)).mp
  have hNoise : Measurable (fun ω => ginibreConfigurationBrownianNoise n B α ω t) := by
    apply Measurable.of_eval
    intro j
    exact (((aemeasurable_iff_measurable.mp ((hB (j, 0)).aemeasurable
        t.val.toNNReal)).complex_ofReal).add
      (measurable_const.mul ((aemeasurable_iff_measurable.mp
        ((hB (j, 1)).aemeasurable t.val.toNNReal)).complex_ofReal))).const_smul (Real.sqrt (2*α/(n :
            ℝ)^2))
  exact hNoise.aemeasurable.congr (by
    filter_upwards [ginibreConfigurationBrownianContinuousPath_ae n B P hB α] with ω hω
    exact (hω t).symm)

end
end GinibrePoincare

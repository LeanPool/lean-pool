/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticContinuousConfigurationNoise.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCausalFlowAdaptation
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticContinuousStoppingTime

/-! An everywhere continuous, genuinely adapted realization of actual configuration noise up to time
one. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- Restricts a continuous path on `[-1, 1]` to `[0, 1]` and recentres it to vanish at `0`. -/
def ginibreConfigurationNoiseRestriction (n : ℕ)
    (N : C(Icc (-1 : ℝ) 1, Configuration n)) : C(Icc (0 : ℝ) 1, Configuration n) :=
  ⟨fun t => N ⟨t, ⟨by linarith [t.property.1], t.property.2⟩⟩-N ⟨0, by norm_num⟩,
    (N.continuous.comp (continuous_subtype_val.subtype_mk _)).sub continuous_const⟩

theorem ginibreConfigurationNoiseRestriction_continuous (n : ℕ) : Continuous
    (ginibreConfigurationNoiseRestriction n) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_eval.comp (continuous_fst.prodMk
    ((continuous_subtype_val.comp continuous_snd).subtype_mk _))).sub
      ((continuous_eval_const _).comp continuous_fst)

/-- The continuous configuration noise of the sample `ω` at time `t`, obtained from the
restricted continuous Brownian path on `[0, 1]` (times projected onto `[0, 1]`). -/
def ginibreConfigurationContinuousNoise {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ) (t : ℝ≥0) (ω : Ω) : Configuration n :=
  ginibreConfigurationNoiseRestriction n (ginibreConfigurationBrownianContinuousPath n B α ω)
    (Set.projIcc 0 1 (by norm_num) (t : ℝ))

theorem ginibreConfigurationContinuousNoise_continuous {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ) (ω : Ω) :
    Continuous (fun t => ginibreConfigurationContinuousNoise n B α t ω) :=
  (ginibreConfigurationNoiseRestriction n _).continuous.comp (continuous_projIcc.comp
      NNReal.continuous_coe)

theorem ginibreConfigurationContinuousNoise_zero {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ) (ω : Ω) :
    ginibreConfigurationContinuousNoise n B α 0 ω = 0 := by
  simp [ginibreConfigurationContinuousNoise, ginibreConfigurationNoiseRestriction, Set.projIcc_left]

theorem ginibreConfigurationContinuousNoise_stronglyAdapted {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (α : ℝ) :
    StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
      (ginibreConfigurationContinuousNoise n B α) := by
  apply ginibreBrownian_causal_flow_stronglyAdapted n B P hB α 1 (by norm_num)
    (ginibreConfigurationNoiseRestriction n) (ginibreConfigurationNoiseRestriction_continuous
        n).borel_measurable
  intro N Q t hPast
  have h0 := hPast 0 ⟨le_rfl, t.property.1⟩
  have ht := hPast t ⟨t.property.1, le_rfl⟩
  have htm : (t : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [t.property.1], t.property.2⟩
  simp only [Set.projIcc_of_mem (by norm_num : (-1 : ℝ) ≤ 1) htm] at ht
  simp only [Set.projIcc_of_mem (by norm_num : (-1 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ∈ Icc (-1 : ℝ)
                                                                   1)] at h0
  exact congrArg₂ (fun x y : Configuration n => x-y) ht h0

theorem ginibreConfigurationContinuousNoise_actual_ae {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P) (α : ℝ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ 1 → ginibreConfigurationContinuousNoise n B α t ω =
      ginibreConfigurationBrownianNoise n B α ω (t : ℝ) := by
  filter_upwards [ginibreConfigurationBrownianContinuousPath_ae n B P hB α,
    ginibreConfigurationBrownianNoise_actual n B P hB α] with ω hPath hNoise
  intro t ht
  have htm : (t : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨t.coe_nonneg, by exact_mod_cast ht⟩
  simp only [ginibreConfigurationContinuousNoise, Set.projIcc_of_mem (by norm_num) htm]
  change ginibreConfigurationBrownianContinuousPath n B α ω _-
    ginibreConfigurationBrownianContinuousPath n B α ω _ = _
  rw [hPath _, hPath _, hNoise.2, sub_zero]

end
end GinibrePoincare

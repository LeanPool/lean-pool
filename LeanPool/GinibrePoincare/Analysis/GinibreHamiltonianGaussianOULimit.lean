/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianGaussianOULimit.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticGaussianLimit
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Topology.Sequences
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Ginibre Hamiltonian Gaussian OU limit

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `centeredGaussian_vector_ae_limit_hasGaussianLaw_of_second_moment_bound`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem centeredGaussian_ae_limit_hasGaussianLaw_of_variance_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (Y : Ω → ℝ) (v : ℕ → ℝ≥0)
    (hLaw : ∀ m, HasLaw (X m) (gaussianReal 0 (v m)) P)
    (C : ℝ≥0) (hC : ∀ m, v m ≤ C)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun m => X m ω) atTop (𝓝 (Y ω))) :
    HasGaussianLaw Y P := by
  obtain ⟨v₀, hv₀, r, hr, hv⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := C)).tendsto_subseq
    (fun m => ⟨zero_le, hC m⟩)
  have hY := ginibreGaussian_hasLaw_of_ae_limit P (fun m => X (r m)) Y
    (fun _ => 0) (fun m => v (r m)) 0 v₀ (fun m => hLaw (r m)) tendsto_const_nhds hv
    (hlim.mono (fun ω hω => hω.comp hr.tendsto_atTop))
  exact hY.hasGaussianLaw

theorem centeredGaussian_vector_ae_limit_hasGaussianLaw_of_second_moment_bound
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → E) (Y : Ω → E)
    (hG : ∀ m, HasGaussianLaw (X m) P) (hMean : ∀ m, (∫ ω, X m ω ∂P) = 0)
    (C : ℝ) (hC : ∀ m, (∫ ω, ‖X m ω‖ ^ 2 ∂P) ≤ C)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun m => X m ω) atTop (𝓝 (Y ω))) :
    HasGaussianLaw Y P := by
  have hYm : AEMeasurable Y P := aemeasurable_of_tendsto_metrizable_ae
    atTop (fun m => (hG m).aemeasurable) hlim
  refine ⟨hYm, ?_⟩
  apply isGaussian_of_isGaussian_map
  intro L
  have hLG (m : ℕ) : HasGaussianLaw (fun ω => L (X m ω)) P := (hG m).map L
  have hLMean (m : ℕ) : (∫ ω, L (X m ω) ∂P)=0 := by
    rw [L.integral_comp_comm (hG m).integrable, hMean m, map_zero]
  let v : ℕ → ℝ≥0 := fun m => (variance (fun ω => L (X m ω)) P).toNNReal
  have hLaw (m : ℕ) : HasLaw (fun ω => L (X m ω)) (gaussianReal 0 (v m)) P :=
    ⟨(hLG m).aemeasurable, by simpa only [hLMean m] using (hLG m).map_eq_gaussianReal⟩
  have hv (m : ℕ) : v m ≤ (‖L‖^2*C).toNNReal := by
    apply Real.toNNReal_mono
    calc
      variance (fun ω => L (X m ω)) P ≤ ∫ ω, (L (X m ω))^2 ∂P :=
        variance_le_expectation_sq (hLG m).aemeasurable.aestronglyMeasurable
      _ ≤ ∫ ω, ‖L‖^2*‖X m ω‖^2 ∂P := by
        apply integral_mono (hLG m).memLp_two.integrable_sq
          (((hG m).memLp_two.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).const_mul _)
        intro ω
        have h := mul_self_le_mul_self (norm_nonneg (L (X m ω))) (L.le_opNorm (X m ω))
        simpa only [← sq, norm_pow, Real.norm_eq_abs, sq_abs, mul_pow] using h
      _ = ‖L‖^2*(∫ ω, ‖X m ω‖^2 ∂P) := integral_const_mul _ _
      _ ≤ ‖L‖^2*C := mul_le_mul_of_nonneg_left (hC m) (sq_nonneg _)
  have hYLG := centeredGaussian_ae_limit_hasGaussianLaw_of_variance_bound P
    (fun m ω => L (X m ω)) (fun ω => L (Y ω)) v hLaw (‖L‖^2*C).toNNReal hv
    (hlim.mono (fun ω hω => L.continuous.continuousAt.tendsto.comp hω))
  rw [AEMeasurable.map_map_of_aemeasurable L.continuous.measurable.aemeasurable hYm]
  exact hYLG.isGaussian_map

end
end GinibrePoincare

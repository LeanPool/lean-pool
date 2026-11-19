/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticVolterraTaylorRemainder.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathBrownianQuadraticControl
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCompactTaylorMeasurability
public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoConvergenceInMeasure

/-! Actual Brownian-driven compact Volterra paths have vanishing local C² Taylor remainder. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreCompactVolterra_taylor_remainder_tendstoInProbability
    {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0)
    (X : ℝ≥0 → Ω → Configuration n)
    (hX : StronglyAdapted (ginibreBrownianAugmentedFiltration B P hB) X)
    (hCont : ∀ ω, Continuous (fun t => X t ω))
    (f : Configuration n → ℝ) (U K : Set (Configuration n))
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hRange : ∀ t ω, X t ω ∈ K) (T : ℝ≥0)
    (b : ℝ → Ω → Configuration n) (hb : ∀ ω, ContinuousOn (fun s => b s ω) (Icc (0 : ℝ) T))
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ s ∈ Icc (0 : ℝ) T, ∀ ω, ‖b s ω‖ ≤ M)
    (hVolterra : ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, X t ω = X 0 ω +
      (ginibreConfigurationBrownianNoise n B α ω t - ginibreConfigurationBrownianNoise n B α ω 0) +
      ∫ s in (0 : ℝ)..(t : ℝ), b s ω) :
    TendstoInMeasure P (fun k ω => itoActualPathTaylorRemainderSum f (fun t => X t ω) T k)
      atTop (fun _ => 0) := by
  classical
  let R := fun k ω => itoActualPathTaylorRemainderSum f (fun t => X t ω) T k
  let Q := fun k ω => itoActualPathQuadraticSum (fun t => X t ω) T k
  let N := ginibreConfigurationBrownianCoordinateQuadraticSum n B α T
  let d := fun k : ℕ => 2*(M*((T : ℝ)/((k : ℝ)+1)))*(M*(T : ℝ))
  let S := fun k ω => 2*N k ω+d k
  have hmB (i : Fin n × Fin 2) (t : ℝ≥0) : Measurable (B i t) :=
    aemeasurable_iff_measurable.mp ((hB i).aemeasurable t)
  have hmN (k : ℕ) : Measurable (N k) := by
    have he : N k = fun ω => (2*(α : ℝ)/(n : ℝ)^2)*ginibreBrownianFamilyQuadraticSum B T k ω :=
      funext (fun ω => ginibreConfigurationBrownianCoordinateQuadraticSum_eq n B α T k ω)
    rw [he]
    apply measurable_const.mul
    exact Finset.measurable_sum Finset.univ (fun i hi => Finset.measurable_sum Finset.univ
      (fun l hl => ((hmB i _).sub (hmB i _)).pow_const 2))
  have hmR (k : ℕ) : AEStronglyMeasurable (R k) P := by
    exact (Finset.measurable_sum Finset.univ (fun (i : Fin (k+1)) hi =>
      ginibreCompactProcess_taylor_remainder_measurable n
        (ginibreBrownianAugmentedFiltration B P hB) X hX hCont f U K hU hf hK hKU hRange
        (ginibreUniformBrownianTime T k i) (ginibreUniformBrownianTime T k
            (i.val+1)))).aestronglyMeasurable
  have hd : Tendsto d atTop (𝓝 0) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      (2*M*(T : ℝ)*(M*(T : ℝ)))
    have he : d = fun k : ℕ => (2*M*(T : ℝ)*(M*(T : ℝ)))*(1/((k : ℝ)+1)) := by
      funext k
      dsimp [d]
      ring
    rw [he]
    simpa only [mul_zero] using hh
  have hdP : TendstoInMeasure P (fun k (_ : Ω) => d k) atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_ae (fun k => aestronglyMeasurable_const)
      (Filter.Eventually.of_forall (fun ω => hd))
  have hN := ginibreConfigurationBrownianCoordinateQuadraticSum_tendstoInProbability n B P hB hind α
      T
  have hS : TendstoInMeasure P S atTop
      (fun _ => 2*((2*(α : ℝ)/(n : ℝ)^2)*((2*n : ℕ) : ℝ)*(T : ℝ))) := by
    have h := ginibre_tendstoInMeasure_add P _ _ _ _
      (ginibre_tendstoInMeasure_const_mul P N _ 2 hN) hdP
    simpa only [add_zero] using h
  refine itoNormalizedDominatedError_tendstoInMeasure P R Q S _ hmR
    (fun k => ((measurable_const.mul (hmN k)).add measurable_const).aestronglyMeasurable) ?_ hS ?_
  · intro k
    filter_upwards [hVolterra] with ω hω
    exact ⟨Finset.sum_nonneg (fun i hi => sq_nonneg _),
      ginibreDrivenPath_brownian_quadratic_control n B α ω (fun t => X t ω)
        (fun s => b s ω) T (hb ω) M hM (fun s hs => hbound s hs ω) hω k⟩
  · exact Filter.Eventually.of_forall (fun ω =>
      itoActualPathRemainder_div_one_add_quadratic_tendsto f U hU hf (fun t => X t ω) T
        (hCont ω).continuousOn (fun t ht => hKU (hRange t ω)))
end
end GinibrePoincare

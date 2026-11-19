/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticRestrictedHessianCorrection.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticRestrictedDriftRiemann
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticProbabilityRestriction
public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoActualDriftQuadratic

/-! True Hessian correction for original local solutions on their actual solution event. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- The sum of directional Hessians `∑ D²f(X tₗ)(ΔₗX, ΔₗX)` of `f` along the increments of `X`
over the uniform partition of `[0, T]` into `k + 1` steps. -/
def ginibreConfigurationPathHessianSum {Ω : Type*} (n : ℕ)
    (X : ℝ≥0 → Ω → Configuration n) (f : Configuration n → ℝ)
    (T : ℝ≥0) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ l : Fin (k+1), itoDirectionalHessian f (X (ginibreUniformBrownianTime T k l) ω)
    (X (ginibreUniformBrownianTime T k (l.val+1)) ω-X (ginibreUniformBrownianTime T k l) ω)

theorem ginibreCompactVolterra_restricted_hessian_tendstoInProbability
    {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0)
    (X : ℝ≥0 → Ω → Configuration n)
    (hX : StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB
        i).toIsPreBrownianReal)) X)
    (hCont : ∀ ω, Continuous (fun t => X t ω))
    (f : Configuration n → ℝ) (U K : Set (Configuration n))
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hRange : ∀ t ω, X t ω ∈ K) (T : ℝ≥0)
    (b : ℝ → Ω → Configuration n) (hb : ∀ ω, ContinuousOn (fun s => b s ω) (Icc (0 : ℝ) T))
    (E : Set Ω) (hE : MeasurableSet E)
    (hVolterra : ∀ᵐ ω ∂P, ω ∈ E → ∀ t ∈ Icc 0 T, X t ω = X 0 ω +
      (ginibreConfigurationBrownianNoise n B α ω t - ginibreConfigurationBrownianNoise n B α ω 0) +
      ∫ s in (0 : ℝ)..(t : ℝ), b s ω) :
    TendstoInMeasure P (fun k => E.indicator (ginibreConfigurationPathHessianSum n X f T k))
      atTop (E.indicator (fun ω => (2*(α : ℝ)/(n : ℝ)^2)*
        ∫ s in (0 : ℝ)..T, configurationLaplacian f (X s.toNNReal ω))) := by
  classical
  let A := ginibreConfigurationPathHessianSum n X f T
  let N := ginibreConfigurationBrownianHessianSum n B α X f T
  let D := fun k ω => A k ω-N k ω
  have hmX (t : ℝ≥0) : Measurable (X t) :=
    ((hX t).mono ((ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)).le
        t)).measurable
  have hmW (t : ℝ≥0) := ginibreConfigurationBrownianNoise_measurable n B P
    (fun i => (hB i).toIsPreBrownianReal) α t
  have hmA (k : ℕ) : Measurable (A k) := Finset.measurable_sum Finset.univ
    (fun (l : Fin (k+1)) hl => ginibreCompact_hessian_apply_measurable n _ _ (hmX _)
      ((hmX _).sub (hmX _)) f U K hU hf hKU (hRange _))
  have hmN (k : ℕ) : Measurable (N k) := Finset.measurable_sum Finset.univ
    (fun (l : Fin (k+1)) hl => ginibreCompact_hessian_apply_measurable n _ _ (hmX _)
      ((hmW _).sub (hmW _)) f U K hU hf hKU (hRange _))
  have hd : TendstoInMeasure P (fun k => E.indicator (D k)) atTop (fun _ => 0) := by
    apply tendstoInMeasure_of_tendsto_ae
      (fun k => ((hmA k).sub (hmN k)).indicator hE |>.aestronglyMeasurable)
    filter_upwards [hVolterra, ginibreConfigurationBrownianNoise_actual n B P hB α] with ω hω hW
    by_cases he : ω ∈ E
    · simp only [Set.indicator_of_mem he]
      have h := itoActualPath_drift_hessian_tendsto f U K hU hf hK hKU T
        (fun t => X t ω) (fun t => ginibreConfigurationBrownianNoise n B α ω t)
        (fun s => b s ω) (fun t ht => hRange t ω)
        ((hW.1.comp continuous_subtype_val).continuousOn) (hb ω)
      convert! h using 1
      funext k
      dsimp [D, A, N, ginibreConfigurationPathHessianSum, ginibreConfigurationBrownianHessianSum]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro l hl
      rw [itoVolterra_uniform_increment (fun t => X t ω)
        (fun t => ginibreConfigurationBrownianNoise n B α ω t) (fun s => b s ω) T (hb ω) (hω he) k
            l]
    · simp only [Set.indicator_of_notMem he]
      exact tendsto_const_nhds
  have hn := ginibre_tendstoInMeasure_indicator P E N _
    (ginibreCompactProcess_configuration_hessian_correction n B P
      (fun i => (hB i).toIsPreBrownianReal) hind α X hX hCont f U K hU hf hK hKU hRange T)
  have h := ginibre_tendstoInMeasure_add P _ _ _ _ hd hn
  convert! h using 1
  · funext k ω
    by_cases he : ω ∈ E <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, he, D, A, N]
  · funext ω
    simp
end
end GinibrePoincare

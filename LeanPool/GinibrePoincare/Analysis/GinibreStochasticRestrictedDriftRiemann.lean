/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticRestrictedDriftRiemann.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticRestrictedTaylorRemainder
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCompactDerivativeMeasurability
public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoDriftRiemann

/-! Genuine drift Riemann limits restricted to actual local-solution events. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- The left-point sum `∑ Df(X tₗ) (ΔₗX - ΔₗW)` of the gradient of `f` against the increments of
`X` minus those of the configuration Brownian noise `W`, over the uniform partition of `[0, T]`
into `k + 1` steps. -/
def ginibreConfigurationDriftReconstructionSum {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ)
    (X : ℝ≥0 → Ω → Configuration n) (f : Configuration n → ℝ)
    (T : ℝ≥0) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ l : Fin (k+1), fderiv ℝ f (X (ginibreUniformBrownianTime T k l) ω)
    ((X (ginibreUniformBrownianTime T k (l.val+1)) ω-X (ginibreUniformBrownianTime T k l) ω)-
      (ginibreConfigurationBrownianNoise n B α ω (ginibreUniformBrownianTime T k (l.val+1))-
        ginibreConfigurationBrownianNoise n B α ω (ginibreUniformBrownianTime T k l)))

theorem ginibreConfigurationBrownianNoise_measurable {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (α : ℝ) (t : ℝ) :
    Measurable (fun ω => ginibreConfigurationBrownianNoise n B α ω t) := by
  have hm (i : Fin n × Fin 2) : Measurable (B i t.toNNReal) :=
    aemeasurable_iff_measurable.mp ((hB i).aemeasurable _)
  apply Measurable.of_eval
  intro j
  exact (measurable_const : Measurable (fun _ : Ω => Real.sqrt (2*α/(n : ℝ)^2))).smul
    ((Complex.continuous_ofReal.measurable.comp (hm (j, 0))).add
      (measurable_const.mul (Complex.continuous_ofReal.measurable.comp (hm (j, 1)))))

theorem ginibreCompactVolterra_restricted_drift_riemann_tendstoInProbability
    {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsPreBrownianReal (B i) P)
    (α : ℝ) (X : ℝ≥0 → Ω → Configuration n)
    (hX : StronglyAdapted (ginibreBrownianAugmentedFiltration B P hB) X)
    (hCont : ∀ ω, Continuous (fun t => X t ω))
    (f : Configuration n → ℝ) (U K : Set (Configuration n))
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hKU : K ⊆ U)
    (hRange : ∀ t ω, X t ω ∈ K) (T : ℝ≥0)
    (b : ℝ → Ω → Configuration n) (hb : ∀ ω, ContinuousOn (fun s => b s ω) (Icc (0 : ℝ) T))
    (E : Set Ω) (hE : MeasurableSet E)
    (hVolterra : ∀ᵐ ω ∂P, ω ∈ E → ∀ t ∈ Icc 0 T, X t ω = X 0 ω +
      (ginibreConfigurationBrownianNoise n B α ω t - ginibreConfigurationBrownianNoise n B α ω 0) +
      ∫ s in (0 : ℝ)..(t : ℝ), b s ω) :
    TendstoInMeasure P (fun k => E.indicator (ginibreConfigurationDriftReconstructionSum n B α X f T
        k))
      atTop (E.indicator (fun ω => ∫ s in (0 : ℝ)..T, fderiv ℝ f (X s.toNNReal ω) (b s ω))) := by
  classical
  have hmX (t : ℝ≥0) : Measurable (X t) :=
    ((hX t).mono ((ginibreBrownianAugmentedFiltration B P hB).le t)).measurable
  have hmW (t : ℝ≥0) := ginibreConfigurationBrownianNoise_measurable n B P hB α t
  have hm (k : ℕ) : AEStronglyMeasurable
      (E.indicator (ginibreConfigurationDriftReconstructionSum n B α X f T k)) P := by
    apply Measurable.aestronglyMeasurable
    apply Measurable.indicator _ hE
    exact Finset.measurable_sum Finset.univ (fun (l : Fin (k+1)) hl =>
      ginibreCompact_fderiv_apply_measurable n _ _ (hmX _)
        (((hmX _).sub (hmX _)).sub ((hmW _).sub (hmW _))) f U K hU hf hKU (hRange _))
  apply tendstoInMeasure_of_tendsto_ae hm
  filter_upwards [hVolterra] with ω hω
  by_cases he : ω ∈ E
  · simp only [Set.indicator_of_mem he]
    have hA : ContinuousOn (fun s : ℝ => fderiv ℝ f (X s.toNNReal ω)) (Icc (0 : ℝ) T) :=
      (hf.continuousOn_fderiv_of_isOpen hU (by norm_num)).comp
        (((hCont ω).comp continuous_real_toNNReal).continuousOn)
        (fun s hs => hKU (hRange _ _))
    have h := itoContinuousOperatorDriftRiemann_fin_tendsto
      (fun s : ℝ => fderiv ℝ f (X s.toNNReal ω)) (fun s => b s ω) T hA (hb ω)
    have hi (k : ℕ) (l : Fin (k+1)) := itoVolterra_uniform_increment (fun t => X t ω)
      (fun t => ginibreConfigurationBrownianNoise n B α ω t) (fun s => b s ω) T (hb ω) (hω he) k l
    convert! h using 1
    funext k
    unfold ginibreConfigurationDriftReconstructionSum
    apply Finset.sum_congr rfl
    intro l hl
    rw [hi]
    simp [itoUniformDriftIncrement]
  · simp only [Set.indicator_of_notMem he]
    exact tendsto_const_nhds
end
end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticRestrictedIto.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticRestrictedHessianCorrection
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCompactGradientIntegral

/-! A genuine local C² Itô identity on actual original-solution events, derived from Brownian left
sums. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreConfigurationPath_discrete_chain {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ)
    (X : ℝ≥0 → Ω → Configuration n) (f : Configuration n → ℝ)
    (T : ℝ≥0) (k : ℕ) (ω : Ω) :
    f (X T ω)-f (X 0 ω) =
      ginibreConfigurationBrownianGradientSum n B α X f T k ω+
      ginibreConfigurationDriftReconstructionSum n B α X f T k ω+
      (1/2 : ℝ)*ginibreConfigurationPathHessianSum n X f T k ω+
      itoActualPathTaylorRemainderSum f (fun t => X t ω) T k := by
  classical
  have h := itoUniformPathTaylor_identity f (fun t => X t ω) T k
  have he : ginibreConfigurationBrownianGradientSum n B α X f T k ω+
      ginibreConfigurationDriftReconstructionSum n B α X f T k ω =
      ∑ l : Fin (k+1), fderiv ℝ f (X (ginibreUniformBrownianTime T k l) ω)
        (X (ginibreUniformBrownianTime T k (l.val+1)) ω-X (ginibreUniformBrownianTime T k l) ω) :=
            by
    unfold ginibreConfigurationBrownianGradientSum ginibreConfigurationDriftReconstructionSum
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    rw [← map_add]
    simp
  rw [he]
  exact h

theorem ginibreCompactVolterra_restricted_ito_exists
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
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ s ∈ Icc (0 : ℝ) T, ∀ ω, ‖b s ω‖ ≤ M)
    (E : Set Ω) (hE : MeasurableSet E)
    (hVolterra : ∀ᵐ ω ∂P, ω ∈ E → ∀ t ∈ Icc 0 T, X t ω = X 0 ω +
      (ginibreConfigurationBrownianNoise n B α ω t - ginibreConfigurationBrownianNoise n B α ω 0) +
      ∫ s in (0 : ℝ)..(t : ℝ), b s ω) :
    ∃ I : (Fin n × Fin 2) → Lp ℝ 2 P,
      TendstoInMeasure P (ginibreConfigurationBrownianGradientSum n B α X f T) atTop
        (fun ω => Real.sqrt (2*(α : ℝ)/(n : ℝ)^2)*∑ i, I i ω) ∧
      ∀ᵐ ω ∂P, ω ∈ E → f (X T ω)-f (X 0 ω)=
        Real.sqrt (2*(α : ℝ)/(n : ℝ)^2)*∑ i, I i ω+
        (∫ s in (0 : ℝ)..T, fderiv ℝ f (X s.toNNReal ω) (b s ω))+
        ((α : ℝ)/(n : ℝ)^2)*(∫ s in (0 : ℝ)..T, configurationLaplacian f (X s.toNNReal ω)) := by
  classical
  obtain ⟨I, hI⟩ := ginibreCompactProcess_gradient_integral_exists n B P
    (fun i => (hB i).toIsPreBrownianReal) hind α X hX hCont f U K hU hf hK hKU hRange T
  have hg := ginibre_tendstoInMeasure_indicator P E _ _ hI
  have hd := ginibreCompactVolterra_restricted_drift_riemann_tendstoInProbability n B P
    (fun i => (hB i).toIsPreBrownianReal) α X hX hCont f U K hU hf hKU hRange T b hb E hE hVolterra
  have hh := ginibreCompactVolterra_restricted_hessian_tendstoInProbability n B P hB hind
    α X hX hCont f U K hU hf hK hKU hRange T b hb E hE hVolterra
  have hr := ginibreCompactVolterra_restricted_taylor_remainder_tendstoInProbability n B P
    (fun i => (hB i).toIsPreBrownianReal) hind α X hX hCont f U K hU hf hK hKU hRange T b hb M hM
        hbound E hE hVolterra
  have hsum := ginibre_tendstoInMeasure_add P _ _ _ _
    (ginibre_tendstoInMeasure_add P _ _ _ _
      (ginibre_tendstoInMeasure_add P _ _ _ _ hg hd)
      (ginibre_tendstoInMeasure_const_mul P _ _ (1/2 : ℝ) hh)) hr
  let Z := E.indicator (fun ω => f (X T ω)-f (X 0 ω))
  have hZ : Measurable Z := by
    have hm (t : ℝ≥0) : Measurable (fun ω => f (X t ω)) :=
      ((ginibreCompactProcess_scalar_stronglyAdapted n _ X hX K hRange f
        (hf.continuousOn.mono hKU) t).mono
        ((ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)).le
            t)).measurable
    exact ((hm T).sub (hm 0)).indicator hE
  have hc : TendstoInMeasure P (fun _ : ℕ => Z) atTop Z :=
    tendstoInMeasure_of_tendsto_ae (fun _ => hZ.aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun _ => tendsto_const_nhds))
  have heq : (fun k ω =>
      E.indicator (ginibreConfigurationBrownianGradientSum n B α X f T k) ω+
      E.indicator (ginibreConfigurationDriftReconstructionSum n B α X f T k) ω+
      (1/2 : ℝ)*E.indicator (ginibreConfigurationPathHessianSum n X f T k) ω+
      E.indicator (fun ω => itoActualPathTaylorRemainderSum f (fun t => X t ω) T k) ω)=
      fun _ : ℕ => Z := by
    funext k ω
    by_cases he : ω ∈ E
    · simp only [Set.indicator_of_mem he, Z]
      exact (ginibreConfigurationPath_discrete_chain n B α X f T k ω).symm
    · simp [Set.indicator_of_notMem he, Z]
  rw [heq] at hsum
  refine ⟨I, hI,?_⟩
  filter_upwards [tendstoInMeasure_ae_unique hc hsum] with ω hω
  intro he
  simp only [Z, Set.indicator_of_mem he, add_zero] at hω
  convert hω using 1; ring
theorem ginibreCompactVolterra_restricted_ito_identify
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
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ s ∈ Icc (0 : ℝ) T, ∀ ω, ‖b s ω‖ ≤ M)
    (E : Set Ω) (hE : MeasurableSet E)
    (hVolterra : ∀ᵐ ω ∂P, ω ∈ E → ∀ t ∈ Icc 0 T, X t ω = X 0 ω +
      (ginibreConfigurationBrownianNoise n B α ω t - ginibreConfigurationBrownianNoise n B α ω 0) +
      ∫ s in (0 : ℝ)..(t : ℝ), b s ω) (J : Ω → ℝ)
    (hJ : TendstoInMeasure P (ginibreConfigurationBrownianGradientSum n B α X f T) atTop J) :
    ∀ᵐ ω ∂P, ω ∈ E → f (X T ω)-f (X 0 ω)=J ω+
      (∫ s in (0 : ℝ)..T, fderiv ℝ f (X s.toNNReal ω) (b s ω))+
      ((α : ℝ)/(n : ℝ)^2)*(∫ s in (0 : ℝ)..T, configurationLaplacian f (X s.toNNReal ω)) := by
  obtain ⟨I, hI, hEq⟩ := ginibreCompactVolterra_restricted_ito_exists n B P hB hind α X hX hCont
    f U K hU hf hK hKU hRange T b hb M hM hbound E hE hVolterra
  filter_upwards [hEq, tendstoInMeasure_ae_unique hI hJ] with ω hω hJω
  intro he
  simpa only [hJω] using hω he

end
end GinibrePoincare

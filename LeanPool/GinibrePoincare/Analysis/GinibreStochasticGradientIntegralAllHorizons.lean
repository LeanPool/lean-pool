/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticGradientIntegralAllHorizons.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCompactGradientIntegral
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralHorizon

/-! The actual gradient integral is a genuine continuous square-integrable martingale. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreCompactProcess_continuous_gradient_integral_all_horizons
    {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ)
    (X : ℝ≥0 → Ω → Configuration n)
    (hX : StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB
        i).toIsPreBrownianReal)) X)
    (hCont : ∀ ω, Continuous (fun t => X t ω))
    (f : Configuration n → ℝ) (U K : Set (Configuration n))
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hRange : ∀ t ω, X t ω ∈ K) (T : ℝ≥0) :
    ∃ J : ℝ≥0 → Ω → ℝ,
      Martingale J (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) P
          ∧
      (∀ ω, Continuous (fun t => J t ω)) ∧ (∀ t, MemLp (J t) 2 P) ∧ J 0 =ᵐ[P] (fun _ => 0) ∧
      (∀ t, TendstoInMeasure P (fun k ω => Real.sqrt (2*α/(n : ℝ)^2)*
        ∑ i : Fin n × Fin 2, brownianUniformPartialSum (B i)
          (fun s ω => fderiv ℝ f (X s ω) (ginibreCoordinateDirection i)) T (k+1) t ω)
        atTop (J t)) ∧
      ∀ t ≤ T, TendstoInMeasure P (ginibreConfigurationBrownianGradientSum n B α X f t) atTop (J t)
          := by
  classical
  let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
  obtain ⟨C, hC, hG, hH⟩ := ginibreCompactProcess_test_coefficients n F X hX hCont
    f U K hU hf hK hKU hRange
  let A := fun (i : Fin n × Fin 2) t ω => fderiv ℝ f (X t ω) (ginibreCoordinateDirection i)
  have hex (i : Fin n × Fin 2) := brownianContinuousIntegral_exists_all_horizons B P hB hind i (A i)
    (fun t => ((hG i).1 t).measurable) T
    (Filter.Eventually.of_forall (fun ω => ((hG i).2.1 ω).continuousOn)) C hC
    (fun t ω => (hG i).2.2 t ω)
  choose M hM hMC hML hM0 hMP hMStd using hex
  let σ := Real.sqrt (2*α/(n : ℝ)^2)
  let J : ℝ≥0 → Ω → ℝ := σ • ∑ i : Fin n × Fin 2, M i
  have hJe (t : ℝ≥0) (ω : Ω) : J t ω=σ*∑ i : Fin n × Fin 2, M i t ω := by
    simp only [J, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  have hsum (S : Finset (Fin n × Fin 2)) : Martingale (∑ i ∈ S, M i) F P := by
    induction S using Finset.induction_on with
    | empty => simpa using martingale_zero ℝ F P
    | @insert i S hi ih =>
      rw [Finset.sum_insert hi]
      exact (hM i).add ih
  have hJ : Martingale J F P := (hsum Finset.univ).smul σ
  have hJC (ω : Ω) : Continuous (fun t => J t ω) := by
    simp_rw [hJe]
    exact continuous_const.mul (continuous_finsetSum Finset.univ (fun i hi => hMC i ω))
  have hJL (t : ℝ≥0) : MemLp (J t) 2 P := by
    have he : J t=(fun ω => σ*∑ i : Fin n × Fin 2, M i t ω) := funext (hJe t)
    rw [he]
    exact (memLp_finsetSum Finset.univ (fun i hi => hML i t)).const_mul σ
  have hz : J 0 =ᵐ[P] (fun _ => 0) := by
    have hall := ae_all_iff.mpr hM0
    filter_upwards [hall] with ω hω
    simp [J, hω]
  have hp (t : ℝ≥0) : TendstoInMeasure P (fun k ω => σ*
      ∑ i : Fin n × Fin 2, brownianUniformPartialSum (B i) (A i) T (k+1) t ω)
      atTop (J t) := by
    have hFi (i : Fin n × Fin 2) (s : ℝ≥0) : MemLp (A i s) 2 P := MemLp.of_bound
      ((((hG i).1 s).mono (F.le s)).aestronglyMeasurable)
      C (Filter.Eventually.of_forall (fun ω => (hG i).2.2 s ω))
    have hh := itoTendstoInMeasure_finset_sum P Finset.univ
      (fun i k => brownianUniformPartialSum (B i) (A i) T (k+1) t) (fun i => M i t)
      (fun i k => (brownianUniformPartialSum_memLp_two B P (fun i => (hB i).toIsPreBrownianReal)
          hind
        i (A i) (fun s => ((hG i).1 s).measurable) (hFi i) T (k+1) t).aestronglyMeasurable)
      (fun i => hMP i t)
    convert! ginibre_tendstoInMeasure_const_mul P _ _ σ hh using 1
    funext ω
    exact hJe t ω
  refine ⟨J, hJ, hJC, hJL, hz, hp,?_⟩
  intro t ht
  have hFi (i : Fin n × Fin 2) (s : ℝ≥0) : MemLp (A i s) 2 P := MemLp.of_bound
    ((((hG i).1 s).mono (F.le s)).aestronglyMeasurable)
    C (Filter.Eventually.of_forall (fun ω => (hG i).2.2 s ω))
  have hh := itoTendstoInMeasure_finset_sum P Finset.univ
    (fun i k => brownianUniformLeftSum (B i) (A i) t (k+1)) (fun i => M i t)
    (fun i k => (brownianUniformLeftSum_memLp_two B P (fun i => (hB i).toIsPreBrownianReal) hind
      i (A i) (fun s => ((hG i).1 s).measurable) (hFi i) t (k+1)).aestronglyMeasurable)
    (fun i => hMStd i t ht)
  have h := ginibre_tendstoInMeasure_const_mul P _ _ σ hh
  convert! h using 1
  · funext k ω
    exact ginibreConfigurationBrownianGradientSum_eq n B α X f t k ω
  · funext ω
    exact hJe t ω
end
end GinibrePoincare

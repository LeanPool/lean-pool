/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralTiltEndpoint.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGirsanovPrefixLaw
public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGirsanovTiltLawLimit
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralExponentialNatural

/-!
# Ginibre Brownian integral tilt endpoint

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianBoundedVector_exponential_integral_exists_gaussian_endpoints`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section

/-- Genuine Girsanov endpoint law: the literal Brownian endpoint minus its
ordinary adapted drift integral is Gaussian under the actual normalized
exponential stochastic-integral density. -/
theorem brownianVectorExponentialIntegralDensity_corrected_endpoint_gaussian
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (F : ι → ℝ≥0 → Ω → ℝ)
    (hF : ∀ i t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F i t))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t ω, (∑ i, (F i t ω) ^ 2) ≤ C ^ 2)
    (T : ℝ≥0)
    (hc : ∀ i, ∀ᵐ ω ∂P, ContinuousOn (fun s => F i s ω) (Set.Icc 0 T))
    (hs : ∀ i n, AEStronglyMeasurable (brownianUniformLeftSum (B i) (F i) T (n + 1)) P)
    (I : ι → Ω → ℝ)
    (hI : ∀ i, TendstoInMeasure P
      (fun n => brownianUniformLeftSum (B i) (F i) T (n + 1)) atTop (I i))
    (i : ι) :
    HasLaw (fun ω => B i T ω-B i 0 ω-
      ∫ s in (0 : ℝ)..(T : ℝ), F i (Real.toNNReal s) ω)
      (gaussianReal 0 T)
      (P.withDensity (fun ω => ENNReal.ofReal (brownianVectorExponentialIntegralDensity F T I ω)))
          := by
  classical
  let τ := fun n => itoUniformNNTime T (n+1)
  let h := fun n k ω j => F j (τ n k) ω
  let D := fun n => brownianPredictableVectorGaussianDensity B (h n) (τ n) (n+1)
  let X := fun n => brownianGirsanovCorrectedPrefix B (h n) (τ n) i (n+1)
  let x := fun ω => B i T ω-B i 0 ω-∫ s in (0 : ℝ)..(T : ℝ), F i (Real.toNNReal s) ω
  have hh (n k : ℕ) : @Measurable Ω (ι→ℝ)
      (ginibreBrownianAugmentedFiltration B P hB (τ n k)) _ (h n k) := by
    let : MeasurableSpace Ω := ginibreBrownianAugmentedFiltration B P hB (τ n k)
    exact Measurable.of_eval (fun j => hF j _)
  have hzero (n : ℕ) : τ n 0=0 := by
    change (itoUniformTime T (n+1) 0).toNNReal=0
    simp only [itoUniformTime, Nat.cast_zero, mul_zero, zero_div, Real.toNNReal_zero]
  have hdm (n : ℕ) : Measurable (D n) :=
    (brownianPredictableVectorGaussianDensity_measurable_at B P hB (h n) (τ n)
      (itoUniformNNTime_mono _ _) (hh n) (n+1)).mono
      ((ginibreBrownianAugmentedFiltration B P hB).le _) le_rfl
  have hdp (n : ℕ) : 0≤ᵐ[P] D n := Eventually.of_forall fun ω =>
    (brownianPredictableVectorGaussianDensity_pos B _ _ _ ω).le
  have hdli (n : ℕ) : (∫⁻ ω, ENNReal.ofReal (D n ω) ∂P)=1 :=
    brownianPredictableVectorGaussianDensity_lintegral B P hB hind (h n) (τ n)
      (itoUniformNNTime_mono _ _) (hh n) (n+1)
  have hdi (n : ℕ) : Integrable (D n) P :=
    ⟨(hdm n).aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (hdp n)).mpr (by rw [hdli]; simp)⟩
  have hdn (n : ℕ) : (∫ ω, D n ω ∂P)=1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (hdp n) (hdm n).aestronglyMeasurable, hdli]
    simp
  have hxmeas (n : ℕ) : Measurable (X n) := by
    unfold X brownianGirsanovCorrectedPrefix
    apply Finset.measurable_sum
    intro k hk
    exact (((ginibreBrownian_augmented_coordinate_measurable_at B P hB (τ n (k+1)) _ le_rfl i).mono
      ((ginibreBrownianAugmentedFiltration B P hB).le _) le_rfl).sub
      ((ginibreBrownian_augmented_coordinate_measurable_at B P hB (τ n k) _ le_rfl i).mono
        ((ginibreBrownianAugmentedFiltration B P hB).le _) le_rfl)).sub
      (((hF i _).mono ((ginibreBrownianAugmentedFiltration B P hB).le _) le_rfl).mul_const _)
  have heq (n : ℕ) (ω : Ω) : X n ω = B i T ω-B i 0 ω-
      ∑ k : Fin (n+1), F i (ginibreUniformBrownianTime T n k) ω*((T : ℝ)/((n : ℝ)+1)) := by
    dsimp only [X]
    rw [brownianGirsanovCorrectedPrefix_eq]
    simp only [τ, h, itoUniformNNTime_end T (n+1) (Nat.succ_pos n), hzero]
    simp_rw [itoUniformNNTime_increment_sub_coe, itoUniformNNTime_eq_ginibreUniformBrownianTime]
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => F i (ginibreUniformBrownianTime T n k) ω*((T :
        ℝ)/((n : ℝ)+1))) (n+1)]
    simp only [Nat.cast_add, Nat.cast_one]
  have hae : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (x ω)) := by
    filter_upwards [hc i] with ω hω
    have hf : ContinuousOn (fun s : ℝ => F i (Real.toNNReal s) ω) (Set.Icc 0 (T : ℝ)) :=
      hω.comp continuous_real_toNNReal.continuousOn (by
        intro s hs
        exact ⟨by positivity, by simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal
                                   hs.2⟩)
    have ht := itoContinuousScalarRiemann_fin_tendsto (fun s : ℝ => F i (Real.toNNReal s) ω) T hf
    simpa only [heq, Real.toNNReal_coe, x] using tendsto_const_nhds.sub ht
  have hxl := tendstoInMeasure_of_tendsto_ae (fun n => (hxmeas n).aestronglyMeasurable) hae
  have hx : AEMeasurable x P := hxl.aemeasurable (fun n => (hxmeas n).aemeasurable)
  have hd := brownianVectorExponentialIntegralDensity_normalized B P hB hind F hF C hC hb T hc hs I
      hI
  apply actualVaryingDensity_constantLaw_limit P D _ hdi hd.1 hdp hd.2.1 hdn hd.2.2.1
    (by simpa only [D, h, τ, brownianPredictableVectorGaussianDensity_uniform_eq] using hd.2.2.2)
    X x (fun n => (hxmeas n).aemeasurable) hx hxl (gaussianReal 0 T)
  intro n
  have hl := brownianGirsanovCorrectedPrefix_gaussian B P hB hind (h n) (τ n)
    (itoUniformNNTime_mono _ _) (hh n) i (n+1) (n+1) le_rfl
  have hend : τ n (n+1)=T := itoUniformNNTime_end T (n+1) (Nat.succ_pos n)
  rw [monotoneGrid_duration_sum (τ n) (itoUniformNNTime_mono _ _) (hzero n), hend] at hl
  exact hl

/-- Actual bounded continuous adapted fields have stochastic integrals whose
literal exponential tilt gives every corrected coordinate endpoint its true
Gaussian law. All integrals and likelihood convergence are constructed. -/
theorem brownianBoundedVector_exponential_integral_exists_gaussian_endpoints {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (F : ι → ℝ≥0 → Ω → ℝ)
    (hF : ∀ i t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal) t) _ (F i t))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t ω, (∑ i, (F i t ω) ^ 2) ≤ C ^ 2)
    (T : ℝ≥0)
    (hc : ∀ i, ∀ᵐ ω ∂P, ContinuousOn (fun s => F i s ω) (Set.Icc 0 T)) :
    ∃ M : ι → ℝ≥0 → Ω → ℝ,
      (∀ i, Martingale (M i) (ginibreBrownianAugmentedFiltration B P
        (fun i => (hB i).toIsPreBrownianReal)) P ∧
        (∀ ω, Continuous (fun t => M i t ω)) ∧ (∀ t, MemLp (M i t) 2 P) ∧
        M i 0 =ᵐ[P] (fun _ => 0) ∧
        ∀ t ≤ T, TendstoInMeasure P
          (fun n => brownianUniformLeftSum (B i) (F i) t (n+1)) atTop (M i t)) ∧
      Integrable (brownianVectorExponentialIntegralDensity F T (fun i => M i T)) P ∧
      (∫ ω, brownianVectorExponentialIntegralDensity F T (fun i => M i T) ω ∂P)=1 ∧
      ∀ i, HasLaw (fun ω => B i T ω-B i 0 ω-
        ∫ s in (0 : ℝ)..(T : ℝ), F i (Real.toNNReal s) ω) (gaussianReal 0 T)
        (P.withDensity (fun ω => ENNReal.ofReal
          (brownianVectorExponentialIntegralDensity F T (fun i => M i T) ω))) := by
  classical
  obtain ⟨M, hM, hi, hn, hL⟩ := brownianBoundedVector_exponential_integral_exists_normalized
    B P hB hind F hF C hC hb T hc
  refine ⟨M, hM, hi, hn,?_⟩
  have hFi (i : ι) (t : ℝ≥0) : MemLp (F i t) 2 P := by
    apply MemLp.of_bound
      ((hF i t).mono ((ginibreBrownianAugmentedFiltration B P
        (fun i => (hB i).toIsPreBrownianReal)).le t) le_rfl).aestronglyMeasurable C
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    apply abs_le_of_sq_le_sq _ hC
    exact (Finset.single_le_sum (fun j _ => sq_nonneg (F j t ω)) (Finset.mem_univ i)).trans (hb t ω)
  intro i
  apply brownianVectorExponentialIntegralDensity_corrected_endpoint_gaussian B P
    (fun i => (hB i).toIsPreBrownianReal) hind F hF C hC hb T hc
    (fun i n => (brownianUniformLeftSum_memLp_two B P
      (fun i => (hB i).toIsPreBrownianReal) hind i (F i) (hF i) (hFi i) T
          (n+1)).aestronglyMeasurable)
    (fun i => M i T)
    (fun i => (hM i).2.2.2.2 T le_rfl)

end
end GinibrePoincare

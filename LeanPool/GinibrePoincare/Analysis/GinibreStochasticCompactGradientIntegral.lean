/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCompactGradientIntegral.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticVolterraTaylorRemainder
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralL2Limit

/-! Actual local C² gradient Brownian left sums have genuine L²-integral limits. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- The left-point sum `∑ Df(X tₗ) (W tₗ₊₁ - W tₗ)` of the gradient of `f` along `X` against the
configuration Brownian noise `W`, over the uniform partition of `[0, T]` into `k + 1` steps. -/
def ginibreConfigurationBrownianGradientSum {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ)
    (X : ℝ≥0 → Ω → Configuration n) (f : Configuration n → ℝ)
    (T : ℝ≥0) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ l : Fin (k+1), fderiv ℝ f (X (ginibreUniformBrownianTime T k l) ω)
    (ginibreConfigurationBrownianNoise n B α ω (ginibreUniformBrownianTime T k (l.val+1))-
      ginibreConfigurationBrownianNoise n B α ω (ginibreUniformBrownianTime T k l))

theorem ginibreConfigurationBrownianGradientSum_eq {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ)
    (X : ℝ≥0 → Ω → Configuration n) (f : Configuration n → ℝ)
    (T : ℝ≥0) (k : ℕ) (ω : Ω) :
    ginibreConfigurationBrownianGradientSum n B α X f T k ω =
      Real.sqrt (2*α/(n : ℝ)^2)*∑ i : Fin n × Fin 2,
        brownianUniformLeftSum (B i)
          (fun t ω => fderiv ℝ f (X t ω) (ginibreCoordinateDirection i)) T (k+1) ω := by
  classical
  unfold ginibreConfigurationBrownianGradientSum
  have hcoord (l : Fin (k+1)) := ginibreConfiguration_fderiv_coordinate_sum f
    (X (ginibreUniformBrownianTime T k l) ω)
    (ginibreConfigurationBrownianNoise n B α ω (ginibreUniformBrownianTime T k (l.val+1))-
      ginibreConfigurationBrownianNoise n B α ω (ginibreUniformBrownianTime T k l))
  simp_rw [hcoord, ginibreConfigurationBrownianNoise_increment_coordinate]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  unfold brownianUniformLeftSum
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [itoUniformNNTime_eq_brownianTime, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  ring

theorem ginibreCompactProcess_gradient_integral_exists {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ)
    (X : ℝ≥0 → Ω → Configuration n)
    (hX : StronglyAdapted (ginibreBrownianAugmentedFiltration B P hB) X)
    (hCont : ∀ ω, Continuous (fun t => X t ω))
    (f : Configuration n → ℝ) (U K : Set (Configuration n))
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hRange : ∀ t ω, X t ω ∈ K) (T : ℝ≥0) :
    ∃ I : (Fin n × Fin 2) → Lp ℝ 2 P,
      TendstoInMeasure P (ginibreConfigurationBrownianGradientSum n B α X f T) atTop
        (fun ω => Real.sqrt (2*α/(n : ℝ)^2)*∑ i, I i ω) := by
  classical
  obtain ⟨C, hC, hG, hH⟩ := ginibreCompactProcess_test_coefficients n
    (ginibreBrownianAugmentedFiltration B P hB) X hX hCont f U K hU hf hK hKU hRange
  let A := fun (i : Fin n × Fin 2) t ω => fderiv ℝ f (X t ω) (ginibreCoordinateDirection i)
  have hm (i : Fin n × Fin 2) (t : ℝ≥0) :
      @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (A i t) :=
    ((hG i).1 t).measurable
  have hLp (i : Fin n × Fin 2) (t : ℝ≥0) : MemLp (A i t) 2 P :=
    MemLp.of_bound ((hm i t).mono ((ginibreBrownianAugmentedFiltration B P hB).le t)
        le_rfl).aestronglyMeasurable
      C (Filter.Eventually.of_forall (fun ω => (hG i).2.2 t ω))
  have hex (i : Fin n × Fin 2) := brownianUniformLeftSum_exists_L2_limit B P hB hind i (A i)
    (hm i) (hLp i) T (Filter.Eventually.of_forall (fun ω => ((hG i).2.1 ω).continuousOn))
    C hC (fun t ht ω => (hG i).2.2 t ω)
  choose I hI using hex
  have hprob (i : Fin n × Fin 2) : TendstoInMeasure P
      (fun k => brownianUniformLeftSum (B i) (A i) T (k+1)) atTop (I i) := by
    have h := tendstoInMeasure_of_tendsto_Lp (hI i)
    refine h.congr' (Filter.Eventually.of_forall (fun k => ?_)) Filter.EventuallyEq.rfl
    exact (brownianUniformLeftSum_memLp_two B P hB hind i (A i) (hm i) (hLp i) T (k+1)).coeFn_toLp
  have hsum := itoTendstoInMeasure_finset_sum P Finset.univ
    (fun i k => brownianUniformLeftSum (B i) (A i) T (k+1)) (fun i => (I i : Ω → ℝ))
    (fun i k => (brownianUniformLeftSum_memLp_two B P hB hind i (A i) (hm i) (hLp i) T
        (k+1)).aestronglyMeasurable)
    (fun i => hprob i)
  refine ⟨I,?_⟩
  have h := ginibre_tendstoInMeasure_const_mul P _ _ (Real.sqrt (2*α/(n : ℝ)^2)) hsum
  convert! h using 1
  funext k ω
  exact ginibreConfigurationBrownianGradientSum_eq n B α X f T k ω
end
end GinibrePoincare

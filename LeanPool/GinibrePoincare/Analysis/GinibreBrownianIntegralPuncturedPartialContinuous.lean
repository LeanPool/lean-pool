/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralPuncturedPartialContinuous.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralApproximationTransfer
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralPuncturedPartialBound
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralPuncturedPartialApproximation
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralMartingaleCap

/-! The actual bounded adapted stochastic integral remains a continuous L²
martingale when the integrand is continuous only at positive times. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem brownianPuncturedPartialIntegral_exists {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal) t) _ (F t))
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => F t ω) (Set.Ioi 0))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t ω, ‖F t ω‖ ≤ C)
    (T : ℝ≥0) (hT : 0 < T) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      Martingale M (ginibreBrownianAugmentedFiltration B P
        (fun i => (hB i).toIsPreBrownianReal)) P ∧
      (∀ ω, Continuous (fun t => M t ω)) ∧
      (∀ t, MemLp (M t) 2 P) ∧ M 0 =ᵐ[P] (fun _ => 0) ∧
      ∀ t, t ≤ T → Tendsto (fun k => ∫ ω,
        (brownianUniformPartialSum (B j) F T (k+1) t ω-M t ω)^2 ∂P) atTop (𝓝 0) := by
  have := Fintype.ofFinite ι
  let hbrown := fun i => (hB i).toIsPreBrownianReal
  let ℱ := ginibreBrownianAugmentedFiltration B P hbrown
  obtain ⟨A, hAM, hAC, hAL, hA0, hAS, hAPS, hAT⟩ :=
    brownianPuncturedIntegral_partial_approximants B P hB hind j F hF hc C hC hb T hT
  let K := fun n => realMartingaleHorizonCap (A n) T
  have hKM (n : ℕ) : Martingale (K n) ℱ P :=
    realMartingaleHorizonCap_martingale P ℱ (A n) (hAM n) (hAL n) T
  have hKL (n : ℕ) (t : ℝ≥0) : MemLp (K n t) 2 P := hAL n (min t T)
  have hKC (n : ℕ) : ∀ᵐ ω ∂P, ContinuousOn (fun t => K n t ω) (Set.Icc 0 T) :=
    ae_of_all P fun ω => (realMartingaleHorizonCap_continuous (A n) (hAC n) T ω).continuousOn
  have hcap (n : ℕ) (t : ℝ≥0) (ω : Ω) : K n t ω=K n (min t T) ω := by
    simp [K, realMartingaleHorizonCap]
  have hterm : Tendsto (fun q : ℕ × ℕ => ∫ ω, (K q.2 T ω-K q.1 T ω)^2 ∂P)
      atTop (𝓝 0) := by
    convert hAT using 1
    funext q
    apply integral_congr_ae
    exact ae_of_all P fun ω => by simp only [K, realMartingaleHorizonCap, min_self]; ring
  obtain ⟨M, hMM, hMC, hML, hMP, hMS⟩ := realMartingale_terminal_cauchy_exists_continuous_martingale
    P ℱ (ginibreBrownianFamilyPastSpace B) (ginibreBrownianFamilyPastSpace_le B P hbrown)
    (fun t => rfl) K hKM T (fun n => hKL n T) hKC hcap hterm
  have hz : M 0 =ᵐ[P] (fun _ => 0) := by
    have hK0 (n : ℕ) : K n 0 =ᵐ[P] (fun _ => 0) := by
      simpa only [K, realMartingaleHorizonCap, zero_min] using hA0 n
    have hp := (hMP 0).congr hK0 EventuallyEq.rfl
    have hpz : TendstoInMeasure P (fun _ : ℕ => (fun _ : Ω => (0 : ℝ))) atTop (fun _ => 0) :=
      tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
        (ae_of_all P fun _ => tendsto_const_nhds)
    exact tendstoInMeasure_ae_unique hp hpz
  refine ⟨M, hMM, hMC, hML, hz,?_⟩
  intro t htT
  by_cases ht0 : t=0
  · subst t
    have he (k : ℕ) : (∫ ω, (brownianUniformPartialSum (B j) F T (k+1) 0 ω-M 0 ω)^2 ∂P)=0 := by
      have hh : (fun ω => (brownianUniformPartialSum (B j) F T (k+1) 0 ω-M 0 ω)^2) =ᵐ[P]
          (fun _ => (0 : ℝ)) := by
        filter_upwards [hz] with ω hω
        simp only [brownianUniformPartialSum_zero, hω, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0)]
      rw [integral_congr_ae hh, integral_zero]
    simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have ht : 0 < t := lt_of_le_of_ne bot_le (Ne.symm ht0)
  let ε := fun n : ℕ => 1/((n : ℝ)+1)
  let S := fun k => brownianUniformPartialSum (B j) F T (k+1) t
  let D := fun n k => brownianUniformPartialSum (B j) (brownianInitialTimeCutoff F (ε n)) T (k+1) t
  have hFi (s : ℝ≥0) : MemLp (F s) 2 P := MemLp.of_bound
    ((hF s).mono (ℱ.le s) le_rfl).aestronglyMeasurable C (ae_of_all P (hb s))
  have hSL (k : ℕ) : MemLp (S k) 2 P :=
    brownianUniformPartialSum_memLp_two B P hbrown hind j F hF hFi T (k+1) t
  have hDL (n k : ℕ) : MemLp (D n k) 2 P := by
    have had := brownianInitialTimeCutoff_adapted F (ε n) ℱ hF
    have hi (s : ℝ≥0) : MemLp (brownianInitialTimeCutoff F (ε n) s) 2 P := MemLp.of_bound
      ((had s).mono (ℱ.le s) le_rfl).aestronglyMeasurable C
      (ae_of_all P fun ω => brownianInitialTimeCutoff_bound F (ε n) C hb s ω)
    exact brownianUniformPartialSum_memLp_two B P hbrown hind j _ had hi T (k+1) t
  apply actualMeanSquareLimit_initial_cutoff_transfer P S D (fun n => K n t) (M t)
    hSL hDL (fun n => hKL n t) (hML t)
    (fun n => C^2*(2*ε n)) (fun k => C^2*((T : ℝ)/((k : ℝ)+1)))
  · convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (C^2*2) using 1 <;> (try
      funext k) <;> (try dsimp [ε]) <;> ring_nf
  · convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (C^2*(T : ℝ)) using 1 <;>
      (try funext k) <;> ring_nf
  · intro n k
    have hh := brownianUniformPartialSum_initial_cutoff_error_bound B P hbrown hind j F hF
      C (ε n) hC (by dsimp [ε]; positivity) hb T t hT htT (k+1) (Nat.succ_pos k)
    simpa only [S, D, Nat.cast_add, Nat.cast_one, mul_add] using hh
  · intro n
    simpa only [D, ε, K, realMartingaleHorizonCap, min_eq_left htT] using hAPS n t
  · exact hMS t

end
end GinibrePoincare

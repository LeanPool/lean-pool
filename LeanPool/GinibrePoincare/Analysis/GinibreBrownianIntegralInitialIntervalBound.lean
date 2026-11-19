/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralInitialIntervalBound.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralUniformSums

/-! Uniform second-moment control of actual predictable left sums supported
near the initial time. This supports integrands continuous only at positive times. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem actual_sum_range_le_support_bound (f : ℕ → ℝ) (N m : ℕ) (D : ℝ)
    (hD : 0 ≤ D) (hb : ∀ k, f k ≤ D) (hz : ∀ k, m ≤ k → f k = 0) :
    ∑ k ∈ Finset.range N, f k ≤ (m : ℝ)*D := by
  by_cases hNm : N ≤ m
  · calc
      _ ≤ ∑ _k ∈ Finset.range N, D := Finset.sum_le_sum fun k _ => hb k
      _ = (N : ℝ)*D := by simp
      _ ≤ (m : ℝ)*D := mul_le_mul_of_nonneg_right (by exact_mod_cast hNm) hD
  · have hmN : m ≤ N := (not_le.mp hNm).le
    have he : (∑ k ∈ Finset.range N, f k) = ∑ k ∈ Finset.range m, f k := by
      symm
      apply Finset.sum_subset (Finset.range_mono hmN)
      intro k hkN hkm
      exact hz k (Nat.le_of_not_gt (fun h => hkm (Finset.mem_range.mpr h)))
    rw [he]
    calc
      _ ≤ ∑ _k ∈ Finset.range m, D := Finset.sum_le_sum fun k _ => hb k
      _ = (m : ℝ)*D := by simp

theorem brownianUniformLeftSum_initial_interval_secondMoment_le {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F t))
    (C δ : ℝ) (_ : 0 ≤ C) (hδ : 0 ≤ δ)
    (hb : ∀ t ω, ‖F t ω‖ ≤ C) (hz : ∀ (t : ℝ≥0) ω, δ ≤ (t : ℝ) → F t ω = 0)
    (T : ℝ≥0) (hT : 0 < T) (N : ℕ) (hN : 0 < N) :
    (∫ ω, (brownianUniformLeftSum (B j) F T N ω)^2 ∂P) ≤ C^2*(δ+(T : ℝ)/(N : ℝ)) := by
  have := Fintype.ofFinite ι
  have hTR : 0 < (T : ℝ) := hT
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hFi (t : ℝ≥0) : MemLp (F t) 2 P := MemLp.of_bound
    ((hF t).mono ((ginibreBrownianAugmentedFiltration B P hB).le t) le_rfl).aestronglyMeasurable
    C (ae_of_all P (hb t))
  let s := fun k : Fin N => itoUniformNNTime T N k
  let d := fun k : Fin N => itoUniformNNTime T N (k.val+1)-s k
  have hend (k : Fin N) : s k+d k=itoUniformNNTime T N (k.val+1) :=
    add_tsub_cancel_of_le (itoUniformNNTime_mono T N (Nat.le_succ k.val))
  have hd (k : Fin N) : (d k : ℝ)=(T : ℝ)/(N : ℝ) := itoUniformNNTime_increment_sub_coe T N k
  have hiso := ginibreBrownian_augmented_linear_sum_isometry B P hB hind j N s d
    (fun i k hik => by rw [hend]; exact itoUniformNNTime_mono T N (Nat.succ_le_of_lt hik))
    (fun k => F (s k)) (fun k => hF _) (fun k => hFi _)
  simp only [hend, hd,← Finset.mul_sum] at hiso
  have he : (∫ ω, (brownianUniformLeftSum (B j) F T N ω)^2 ∂P) =
      (T : ℝ)/(N : ℝ)*∑ k ∈ Finset.range N, ∫ ω, (F (itoUniformNNTime T N k) ω)^2 ∂P := by
    rw [← Fin.sum_univ_eq_sum_range]
    convert hiso using 1
    congr 1
    funext ω
    unfold brownianUniformLeftSum
    congr 1
    exact (Fin.sum_univ_eq_sum_range _ N).symm
  rw [he]
  let m := Nat.ceil (δ*(N : ℝ)/(T : ℝ))
  have hbound (k : ℕ) : (∫ ω, (F (itoUniformNNTime T N k) ω)^2 ∂P) ≤ C^2 := by
    calc
      _ ≤ ∫ _ω, C^2 ∂P := integral_mono (hFi _).integrable_sq (integrable_const _) (fun ω => by
        have hh := pow_le_pow_left₀ (abs_nonneg (F (itoUniformNNTime T N k) ω))
          (show |F (itoUniformNNTime T N k) ω| ≤ C from hb _ ω) 2
        simpa only [Real.norm_eq_abs, sq_abs] using hh)
      _ = C^2 := by simp
  have hzero (k : ℕ) (hk : m ≤ k) : (∫ ω, (F (itoUniformNNTime T N k) ω)^2 ∂P)=0 := by
    have hmk : δ*(N : ℝ)/(T : ℝ) ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hk)
    have htime : δ ≤ (itoUniformNNTime T N k : ℝ) := by
      rw [itoUniformNNTime_coe, itoUniformTime]
      have hh := (div_le_iff₀ hTR).mp hmk
      apply (le_div_iff₀ hNR).mpr
      nlinarith
    simp [hz _ _ htime]
  have hs := actual_sum_range_le_support_bound
    (fun k => ∫ ω, (F (itoUniformNNTime T N k) ω)^2 ∂P) N m (C^2) (sq_nonneg _) hbound hzero
  have hm : (m : ℝ) ≤ δ*(N : ℝ)/(T : ℝ)+1 := (Nat.ceil_lt_add_one (by positivity)).le
  calc
    _ ≤ ((T : ℝ)/(N : ℝ))*((m : ℝ)*C^2) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ ((T : ℝ)/(N : ℝ))*((δ*(N : ℝ)/(T : ℝ)+1)*C^2) := by gcongr
    _ = C^2*(δ+(T : ℝ)/(N : ℝ)) := by field_simp

end
end GinibrePoincare

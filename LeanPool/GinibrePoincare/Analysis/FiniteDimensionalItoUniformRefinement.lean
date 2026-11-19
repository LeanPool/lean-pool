/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/FiniteDimensionalItoUniformRefinement.lean.
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

public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoPathMesh

/-!
# Finite dimensional Ito uniform refinement

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `itoUniformNNTime_increment_sub_coe`, `itoUniformNNTime_common_samples_mem`,
`itoUniformNNTime_two_coarse_dist_le`, `itoUniformNNWeightedSum_difference_common_grid`.
-/

@[expose] public section

open scoped BigOperators NNReal
namespace GinibrePoincare
noncomputable section

/-- A uniform grid with a positive number N of intervals. -/
def itoUniformTime (T : ℝ) (N i : ℕ) : ℝ := T*(i : ℝ)/(N : ℝ)

theorem itoUniformTime_refined (T : ℝ) (N M i : ℕ) (hM : 0 < M) :
    itoUniformTime T (N*M) (i*M) = itoUniformTime T N i := by
  unfold itoUniformTime
  simp only [Nat.cast_mul]
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp

theorem itoSum_range_mul_blocks {A : Type*} [AddCommMonoid A] (g : ℕ → A) (N M : ℕ) :
    ∑ k ∈ Finset.range (N*M), g k =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M, g (i*M+j) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- Exact common-refinement telescoping for arbitrary actual scalar weights and paths. -/
theorem itoUniformWeightedSum_refinement (F B : ℝ → ℝ) (T : ℝ) (N M : ℕ)
    (hM : 0 < M) :
    (∑ i ∈ Finset.range N, F (itoUniformTime T N i)*
      (B (itoUniformTime T N (i+1))-B (itoUniformTime T N i))) =
    ∑ k ∈ Finset.range (N*M), F (itoUniformTime T N (k/M))*
      (B (itoUniformTime T (N*M) (k+1))-B (itoUniformTime T (N*M) k)) := by
  rw [itoSum_range_mul_blocks]
  apply Finset.sum_congr rfl
  intro i hi
  have hdiv (j : ℕ) (hj : j < M) : (i*M+j)/M = i := by
    rw [Nat.mul_comm i M, Nat.mul_add_div hM i j, Nat.div_eq_of_lt hj, Nat.add_zero]
  have he : (∑ j ∈ Finset.range M, F (itoUniformTime T N ((i*M+j)/M))*
      (B (itoUniformTime T (N*M) (i*M+j+1))-B (itoUniformTime T (N*M) (i*M+j)))) =
      F (itoUniformTime T N i) *
        (B (itoUniformTime T (N*M) (i*M+M))-B (itoUniformTime T (N*M) (i*M))) := by
    calc
      _ = ∑ j ∈ Finset.range M, F (itoUniformTime T N i)*
          (B (itoUniformTime T (N*M) (i*M+(j+1)))-B (itoUniformTime T (N*M) (i*M+j))) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hdiv j (Finset.mem_range.mp hj)]
        simp only [Nat.add_assoc]
      _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_range_sub
          (fun j => B (itoUniformTime T (N*M) (i*M+j))) M]
        simp
  rw [he, ← Nat.succ_mul, itoUniformTime_refined T N M (i+1) hM,
    itoUniformTime_refined T N M i hM]

/-- The nonnegative-time version of the same genuine uniform grid. -/
def itoUniformNNTime (T : ℝ≥0) (N i : ℕ) : ℝ≥0 := (itoUniformTime T N i).toNNReal

@[simp] theorem itoUniformNNTime_eq_brownianTime (T : ℝ≥0) (n i : ℕ) :
    itoUniformNNTime T (n+1) i = ginibreUniformBrownianTime T n i := by
  simp [itoUniformNNTime, itoUniformTime, ginibreUniformBrownianTime, ginibreUniformTime]

theorem itoUniformNNWeightedSum_refinement (F B : ℝ≥0 → ℝ) (T : ℝ≥0) (N M : ℕ)
    (hM : 0 < M) :
    (∑ i ∈ Finset.range N, F (itoUniformNNTime T N i)*
      (B (itoUniformNNTime T N (i+1))-B (itoUniformNNTime T N i))) =
    ∑ k ∈ Finset.range (N*M), F (itoUniformNNTime T N (k/M))*
      (B (itoUniformNNTime T (N*M) (k+1))-B (itoUniformNNTime T (N*M) k)) := by
  exact itoUniformWeightedSum_refinement (fun s => F s.toNNReal) (fun s => B s.toNNReal) T N M hM

@[simp] theorem itoUniformNNTime_coe (T : ℝ≥0) (N i : ℕ) :
    (itoUniformNNTime T N i : ℝ) = itoUniformTime T N i := by
  apply Real.coe_toNNReal
  unfold itoUniformTime
  positivity

theorem itoUniformNNTime_mono (T : ℝ≥0) (N : ℕ) : Monotone (itoUniformNNTime T N) := by
  intro i j hij
  apply Real.toNNReal_mono
  unfold itoUniformTime
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hij) T.coe_nonneg) (Nat.cast_nonneg N)

/-- Coarse left samples are actual past times of the common fine-grid interval. -/
theorem itoUniformNNTime_coarse_le_fine (T : ℝ≥0) (N M k : ℕ) (hM : 0 < M) :
    itoUniformNNTime T N (k/M) ≤ itoUniformNNTime T (N*M) k := by
  have he : itoUniformNNTime T (N*M) ((k/M)*M) = itoUniformNNTime T N (k/M) :=
    congrArg Real.toNNReal (itoUniformTime_refined T N M (k/M) hM)
  rw [← he]
  exact itoUniformNNTime_mono T (N*M) (Nat.div_mul_le_self k M)

@[simp] theorem itoUniformNNTime_end (T : ℝ≥0) (N : ℕ) (hN : 0 < N) :
    itoUniformNNTime T N N = T := by
  unfold itoUniformNNTime itoUniformTime
  rw [mul_div_cancel_right₀ _ (show (N : ℝ) ≠ 0 by exact_mod_cast hN.ne')]
  exact Real.toNNReal_coe

theorem itoUniformNNTime_le_end (T : ℝ≥0) (N i : ℕ) (hN : 0 < N) (hi : i ≤ N) :
    itoUniformNNTime T N i ≤ T := by
  simpa only [itoUniformNNTime_end T N hN] using itoUniformNNTime_mono T N hi

/-- Exact fine interval length after taking real coordinates. -/
theorem itoUniformNNTime_increment_coe (T : ℝ≥0) (N i : ℕ) :
    (itoUniformNNTime T N (i+1) : ℝ) - itoUniformNNTime T N i = (T : ℝ)/(N : ℝ) := by
  simp only [itoUniformNNTime_coe, itoUniformTime, Nat.cast_add, Nat.cast_one]
  ring

/-- Exact nonnegative interval length of the actual uniform partition. -/
theorem itoUniformNNTime_increment_sub_coe (T : ℝ≥0) (N i : ℕ) :
    ((itoUniformNNTime T N (i+1)-itoUniformNNTime T N i : ℝ≥0) : ℝ) =
      (T : ℝ)/(N : ℝ) := by
  rw [NNReal.coe_sub (itoUniformNNTime_mono T N (Nat.le_succ i)),
    itoUniformNNTime_increment_coe]

/-- All actual coarse and fine endpoints lie in the original time interval. -/
theorem itoUniformNNTime_common_samples_mem (T : ℝ≥0) (N M k : ℕ)
    (hN : 0 < N) (hM : 0 < M) (hk : k < N * M) :
    itoUniformNNTime T N (k/M) ∈ Set.Icc 0 T ∧
      itoUniformNNTime T M (k/N) ∈ Set.Icc 0 T ∧
      itoUniformNNTime T (N*M) k ∈ Set.Icc 0 T ∧
      itoUniformNNTime T (N*M) (k+1) ∈ Set.Icc 0 T := by
  have hpos : 0 < N*M := Nat.mul_pos hN hM
  have hf := itoUniformNNTime_le_end T (N*M) k hpos hk.le
  have hc1 := itoUniformNNTime_coarse_le_fine T N M k hM
  have hc2 := itoUniformNNTime_coarse_le_fine T M N k hN
  rw [Nat.mul_comm M N] at hc2
  exact ⟨⟨bot_le, hc1.trans hf⟩, ⟨bot_le, hc2.trans hf⟩, ⟨bot_le, hf⟩,
    ⟨bot_le, itoUniformNNTime_le_end T (N*M) (k+1) hpos (Nat.succ_le_of_lt hk)⟩⟩

/-- A coarse sample and its fine-grid start are within one coarse time step. -/
theorem itoUniformNNTime_coarse_dist_le_step (T : ℝ≥0) (N M k : ℕ) (hM : 0 < M) :
    dist (itoUniformNNTime T N (k/M)) (itoUniformNNTime T (N*M) k) ≤ (T : ℝ)/(N : ℝ) := by
  have hk : k ≤ (k/M+1)*M := by
    have hh := Nat.mod_add_div k M
    have hm := Nat.mod_lt k hM
    nlinarith
  have he : itoUniformNNTime T (N*M) ((k/M+1)*M) = itoUniformNNTime T N (k/M+1) :=
    congrArg Real.toNNReal (itoUniformTime_refined T N M (k/M+1) hM)
  have hupper := itoUniformNNTime_mono T (N*M) hk
  rw [he] at hupper
  have hlower := itoUniformNNTime_coarse_le_fine T N M k hM
  have hlowerR : (itoUniformNNTime T N (k/M) : ℝ) ≤ itoUniformNNTime T (N*M) k := hlower
  have hupperR : (itoUniformNNTime T (N*M) k : ℝ) ≤ itoUniformNNTime T N (k/M+1) := hupper
  rw [NNReal.dist_eq, abs_of_nonpos (sub_nonpos.mpr hlowerR)]
  have hstep : (itoUniformNNTime T N (k/M+1) : ℝ) - itoUniformNNTime T N (k/M) =
      (T : ℝ)/(N : ℝ) := by
    simp only [itoUniformNNTime_coe, itoUniformTime, Nat.cast_add, Nat.cast_one]
    ring
  linarith

/-- Both coarse predictable samples approach each other on the common fine grid. -/
theorem itoUniformNNTime_two_coarse_dist_le (T : ℝ≥0) (N M k : ℕ)
    (hN : 0 < N) (hM : 0 < M) :
    dist (itoUniformNNTime T N (k/M)) (itoUniformNNTime T M (k/N)) ≤
      (T : ℝ)/(N : ℝ)+(T : ℝ)/(M : ℝ) := by
  have h1 := itoUniformNNTime_coarse_dist_le_step T N M k hM
  have h2 := itoUniformNNTime_coarse_dist_le_step T M N k hN
  rw [Nat.mul_comm M N, dist_comm] at h2
  exact (dist_triangle _ (itoUniformNNTime T (N*M) k) _).trans (add_le_add h1 h2)

/-- Two arbitrary uniform left sums share an exact common fine-grid expression. -/
theorem itoUniformNNWeightedSum_difference_common_grid (F G B : ℝ≥0 → ℝ)
    (T : ℝ≥0) (N M : ℕ) (hN : 0 < N) (hM : 0 < M) :
    (∑ i ∈ Finset.range N, F (itoUniformNNTime T N i)*
      (B (itoUniformNNTime T N (i+1))-B (itoUniformNNTime T N i))) -
    (∑ j ∈ Finset.range M, G (itoUniformNNTime T M j)*
      (B (itoUniformNNTime T M (j+1))-B (itoUniformNNTime T M j))) =
    ∑ k ∈ Finset.range (N*M),
      (F (itoUniformNNTime T N (k/M))-G (itoUniformNNTime T M (k/N)))*
        (B (itoUniformNNTime T (N*M) (k+1))-B (itoUniformNNTime T (N*M) k)) := by
  rw [itoUniformNNWeightedSum_refinement F B T N M hM,
    itoUniformNNWeightedSum_refinement G B T M N hN, Nat.mul_comm M N,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring

end
end GinibrePoincare

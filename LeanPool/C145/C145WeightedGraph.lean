/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-! Concrete counting-metric weighted graph Laplacian and its exact ground kernel. -/

@[expose] public section

noncomputable section
namespace C145.WeightedGraph
open scoped BigOperators
open Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The weighted degree diagonal minus the weight matrix. -/
def laplacian (W : Matrix V V ℝ) : Matrix V V ℝ :=
  Matrix.diagonal (fun v => ∑ u, W v u) - W

/-- The simple graph of positive off-diagonal weights in a symmetric weight matrix. -/
def supportGraph (W : Matrix V V ℝ) (hs : W.IsSymm) : SimpleGraph V where
  Adj v u := v ≠ u ∧ 0 < W v u
  symm := ⟨by intro v u h; exact ⟨h.1.symm, by rw [hs.apply]; exact h.2⟩⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

theorem laplacian_symm (W : Matrix V V ℝ) (hs : W.IsSymm) :
    (laplacian W).IsSymm := (Matrix.isSymm_diagonal _).sub hs

theorem laplacian_mulVec (W : Matrix V V ℝ) (x : V → ℝ) (v : V) :
    (laplacian W *ᵥ x) v = ∑ u, W v u * (x v - x u) := by
  rw [laplacian, Matrix.sub_mulVec]
  simp only [Pi.sub_apply, Matrix.mulVec_diagonal]
  change (∑ u, W v u) * x v - ∑ u, W v u * x u = _
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  congr 1; ext u; ring

theorem laplacian_const (W : Matrix V V ℝ) (c : ℝ) :
    laplacian W *ᵥ (fun _ => c) = 0 := by
  ext v; simp [laplacian_mulVec]

theorem laplacian_energy (W : Matrix V V ℝ) (hs : W.IsSymm) (x : V → ℝ) :
    x ⬝ᵥ (laplacian W *ᵥ x) =
      (∑ v, ∑ u, W v u * (x v - x u) ^ 2) / 2 := by
  simp only [dotProduct, laplacian_mulVec, Finset.mul_sum]
  have hswap : (∑ v, ∑ u, x v * (W v u * (x v - x u))) =
      ∑ v, ∑ u, x u * (W v u * (x u - x v)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro v _
    apply Finset.sum_congr rfl; intro u _
    rw [hs.apply]
  rw [← add_self_div_two (∑ v, ∑ u, x v * (W v u * (x v - x u)))]
  conv_lhs => enter [1, 2]; rw [hswap]
  rw [← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl; intro v _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro u _; ring

theorem laplacian_posSemidef (W : Matrix V V ℝ) (hs : W.IsSymm)
    (hn : ∀ v u, 0 ≤ W v u) : (laplacian W).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (laplacian_symm W hs).eq
  · intro x
    rw [star_trivial, laplacian_energy W hs]
    exact div_nonneg (Finset.sum_nonneg fun v _ =>
      Finset.sum_nonneg fun u _ => mul_nonneg (hn v u) (sq_nonneg _)) (by norm_num)

theorem laplacian_kernel_const (W : Matrix V V ℝ) (hs : W.IsSymm)
    (hn : ∀ v u, 0 ≤ W v u) (hc : (supportGraph W hs).Connected)
    (x : V → ℝ) (hx : laplacian W *ᵥ x = 0) : ∀ v u, x v = x u := by
  have he : (∑ v, ∑ u, W v u * (x v - x u) ^ 2) = 0 := by
    have hh := laplacian_energy W hs x
    rw [hx, dotProduct_zero] at hh
    linarith
  have ht : ∀ v u, W v u * (x v - x u) ^ 2 = 0 := by
    have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ =>
      Finset.sum_nonneg fun u _ => mul_nonneg (hn v u) (sq_nonneg _))).mp he
    intro v u
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun u _ => mul_nonneg (hn v u) (sq_nonneg _))).mp (hh v (by simp)) u (by simp)
  have hadj : ∀ v u, (supportGraph W hs).Adj v u → x v = x u := by
    intro v u h
    have hh := (mul_eq_zero.mp (ht v u)).resolve_left (ne_of_gt h.2)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hh)
  intro v u
  obtain ⟨p⟩ := hc.preconnected v u
  induction p with
  | nil => rfl
  | cons h _ ih => exact (hadj _ _ h).trans ih

end C145.WeightedGraph

end

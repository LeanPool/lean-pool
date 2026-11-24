/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.HarvestAnnularSplit
public import LeanPool.ShellsortMean.HarvestProjectedFar

/-! High-grid ring decomposition with the far interaction already bounded. -/
@[expose] public noncomputable section
namespace Shellsort.HarvestAnnularSplit
open Finset RoughGapDenominatorAverage HarvestActualRings RoughGapEndpoint
open scoped ComplexConjugate

theorem amp_eq_coeff {n h : ℕ} [NeZero h] (v : Fin n → ℂ) (a : ℕ) :
    amp 0 v (a, h) =
        HarvestProjectedFar.coeff (fun i : Fin n => i.val) v (a : ZMod h) := by
  simp [amp, HarvestProjectedFar.coeff_exp]

/-- There are no far predecessors when k<m. At k=m the inner prefix
contains ring 0, whose radius is H. -/
def farWeight (h D H m k : ℕ) : ℝ :=
  if m ≤ k then 2 * ((h : ℝ) + (2 + (D : ℝ) ^ 2) * (2 * rad H (k - m) : ℕ)) else 0

theorem dyadic_far_cost {n T H h : ℕ} [NeZero h] (ht : T ≤ n) (hp : 0 < H)
    (p : RankPlacement n) (D m k : ℕ) (hk : k < n + 1) :
    let label := fun i : Fin n => (band ht hp i).val
    let v := fun i : Fin n => (slotError p T i : ℂ)
    (∑ a ∈ Actual214.highGrid h D,
        2 * dot (amp 0 (piece label k v) (a, h)) (amp 0 (prefixPiece label (k + 1 - m) v) (a, h))) ≤
      farWeight h D H m k * ∑ i, ‖piece label k v i‖ := by
  intro label v
  let k' : Fin (n + 1) := ⟨k, hk⟩
  by_cases le : m ≤ k
  · have outer (i : Fin n) : piece label k v i = (ringVec ht hp p k' i : ℂ) := by
      simp [piece, label, v, ringVec, k', Fin.ext_iff, eq_comm]
    have inner (i : Fin n) : prefixPiece label (k + 1 - m) v i = (mergedVec ht hp p (k - m) i :
      ℂ) := by
      have hb : (band ht hp i).val < k + 1 - m ↔ (band ht hp i).val ≤ k - m := by omega
      simp [prefixPiece, mergedVec, label, hb, v]
    let A (a : ℕ) := HarvestProjectedFar.coeff (fun i : Fin n => i.val)
        (fun i => (ringVec ht hp p k' i : ℂ)) (a : ZMod h)
    let B (a : ℕ) := HarvestProjectedFar.coeff (fun i : Fin n => i.val)
        (fun i => (mergedVec ht hp p (k - m) i : ℂ)) (a : ZMod h)
    have ab (a : ℕ) : dot (amp 0 (piece label k v) (a, h))
        (amp 0 (prefixPiece label (k + 1 - m) v) (a, h)) = (B a * conj (A a)).re := by
      rw [funext outer, funext inner, amp_eq_coeff, amp_eq_coeff]
      change dot (A a) (B a) = _
      simp [dot, Complex.mul_re]; ring
    simp only [farWeight, le, ite_true]
    simp_rw [ab, outer, Complex.norm_intCast]
    rw [←mul_sum, ←Complex.re_sum]
    have R := HarvestProjectedFar.actual_projected_far (h := h) ht hp p D (k - m) k'
    change ‖∑ a ∈ Actual214.highGrid h D, B a * conj (A a)‖ ≤ _ at R
    calc
      _ ≤ 2 * ‖∑ a ∈ Actual214.highGrid h D, B a * conj (A a)‖ :=
        mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (by norm_num)
      _ ≤ _ := by linarith
  · have small : k + 1 - m = 0 := by omega
    have empty : prefixPiece label (k + 1 - m) v = 0 := by funext i; simp [prefixPiece, small]
    simp [farWeight, le, empty, amp, dot]

/-- One deterministic cut of the actual permutation at one high-frequency grid.
The diagonal term is ready for the short-interval sieve. The second term
has no unresolved Fourier cross products. -/
theorem actual_high_diagonal_and_mass {n T H h : ℕ} [NeZero h]
    (ht : T ≤ n) (hp : 0 < H) (p : RankPlacement n) (D m : ℕ) (hm : 0 < m) :
    let label := fun i : Fin n => (band ht hp i).val
    let v := fun i : Fin n => (slotError p T i : ℂ)
    (∑ a ∈ Actual214.highGrid h D, energy 0 v (a, h)) ≤
      ((2 * m - 1 : ℕ) : ℝ) * (∑ k ∈ range (n + 1), ∑ a ∈ Actual214.highGrid h D,
        energy 0 (piece label k v) (a, h)) +
      ∑ k ∈ range (n + 1), farWeight h D H m k * ∑ i, ‖piece label k v i‖ := by
  intro label v
  apply (actual_cut_high_split p T h D label (fun i => (band ht hp i).isLt) m hm).trans
  apply add_le_add le_rfl
  exact sum_le_sum fun k hk => dyadic_far_cost ht hp p D m k (mem_range.mp hk)

/-- The pointwise energy bound, with all far-ring charges paid by total
error mass and the cut moment and the diagonal in the physical sieve's form. -/
theorem actual_high_diagonal_and_moment {n T H h : ℕ} [NeZero h]
    (ht : T ≤ n) (hp : 0 < H) (p : RankPlacement n) (D m : ℕ) (hm : 0 < m) :
    (∑ a ∈ Actual214.highGrid h D, energy 0 (fun i => (slotError p T i : ℂ)) (a, h)) ≤
      ((2 * m - 1 : ℕ) : ℝ) *
        (∑ k : Fin (n + 1), ∑ a ∈ Actual214.highGrid h D,
          energy 0 (fun i => (ringVec ht hp p k i : ℂ)) (a, h)) +
      (2 * (h : ℝ) * (∑ i, |(slotError p T i : ℝ)|) +
        (8 * (2 + (D : ℝ) ^ 2) * (1 / (2 : ℝ) ^ m)) * (cutMoment p T : ℝ)) := by
  let label := fun i : Fin n => (band ht hp i).val
  let v := fun i : Fin n => (slotError p T i : ℂ)
  let charge (k : Fin (n + 1)) :=
    farWeight h D H m k.val * ∑ i, |(ringVec ht hp p k i : ℝ)|
  have same (k : Fin (n + 1)) :
      piece label k.val v = fun i => (ringVec ht hp p k i : ℂ) := by
    funext i
    simp [piece, label, v, ringVec, Fin.ext_iff, eq_comm]
  have raw := actual_high_diagonal_and_mass (h := h) ht hp p D m hm
  change _ ≤ _ * (∑ k ∈ range (n + 1), ∑ a ∈ Actual214.highGrid h D,
      energy 0 (piece label k v) (a, h)) +
    ∑ k ∈ range (n + 1), farWeight h D H m k * ∑ i, ‖piece label k v i‖ at raw
  rw [←Fin.sum_univ_eq_sum_range, ←Fin.sum_univ_eq_sum_range] at raw
  simp only [same, Complex.norm_intCast] at raw
  apply raw.trans
  apply add_le_add le_rfl
  change (∑ k, charge k) ≤ _
  have sum_eq : (∑ k, charge k) = ∑ k ∈ univ.filter (fun k : Fin (n + 1) => m ≤ k.val),
      charge k := by
    rw [sum_filter]
    apply sum_congr rfl
    intro k _
    by_cases le : m ≤ k.val
    · simp [le]
    · simp [le, charge, farWeight]
  rw [sum_eq]
  have bound := sum_far_charges ht hp hm p (2 * (h : ℝ)) (2 * (2 + (D : ℝ) ^ 2))
    (by positivity) (by positivity) charge (by
      intro k le
      dsimp [charge, farWeight]
      simp only [le, ite_true]
      apply le_of_eq
      ring)
  convert bound using 1; ring

end Shellsort.HarvestAnnularSplit

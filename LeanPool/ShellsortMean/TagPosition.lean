/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import Mathlib.Data.Fintype.Fin
public import LeanPool.ShellsortMean.ThresholdSort
public import LeanPool.ShellsortMean.ResidueCount

/-! The position of a tagged rank after one or two gap passes. -/

@[expose] public noncomputable section
namespace Shellsort

theorem chainOrdinal_eq_residuePrefixCount {n : ℕ} (k : ℕ) (i : Fin n) :
    chainOrdinal k i = residuePrefixCount k (i.val % k) i.val := by
  let S := (Finset.range i.val).filter (fun v => v % k = i.val % k)
  let e : {j : Fin n // j.val % k = i.val % k ∧ j < i} ≃ S := {
    toFun := fun j => ⟨j.val.val, by
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.property.2, j.property.1⟩⟩
    invFun := fun v => ⟨⟨v.val, lt_trans
      (Finset.mem_range.mp (Finset.mem_filter.mp v.property).1) i.isLt⟩,
      (Finset.mem_filter.mp v.property).2,
      Finset.mem_range.mp (Finset.mem_filter.mp v.property).1⟩
    left_inv := by intro j; rfl
    right_inv := by intro v; rfl }
  have h := Fintype.card_congr e
  simpa [Fintype.card_subtype, chainOrdinal, chainPositions,
    Finset.filter_filter, S, residuePrefixCount] using h

theorem chainOrdinal_eq_div {n : ℕ} (k : ℕ) (hk : 0 < k) (i : Fin n) :
    chainOrdinal k i = i.val / k := by
  rw [chainOrdinal_eq_residuePrefixCount,
    residuePrefixCount_formula k (i.val % k) i.val hk (Nat.mod_lt _ hk)]
  simp

/-- The final chain ordinal of a tagged key is its original within-chain rank. -/
theorem gapSort_tag_chain_rank {n : ℕ} (p : RankPlacement n) (k : ℕ) (x : Fin n) :
    chainOrdinal k (gapSort p k x) =
      chainLowerCount (thresholdSet p x.val) k ((p x).val % k) := by
  let q := gapSort p k
  have hs : (chainPositions n k ((q x).val % k)).filter (fun j => j < q x) =
      (thresholdSet q x.val).filter (fun j => j.val % k = (q x).val % k) := by
    ext j
    simp only [Finset.mem_filter, chainPositions, Finset.mem_univ, true_and,
      threshold_mem]
    constructor
    · rintro ⟨hc, hlt⟩
      have hsort := gapSort_sorted p k (q.symm j) x (by simpa [q] using hc)
      exact ⟨hsort.mp (by simpa [q] using hlt), hc⟩
    · rintro ⟨hlt, hc⟩
      have hsort := gapSort_sorted p k (q.symm j) x (by simpa [q] using hc)
      exact ⟨hc, by simpa [q] using hsort.mpr hlt⟩
  change ((chainPositions n k ((q x).val % k)).filter (fun j => j < q x)).card = _
  rw [hs]
  change chainLowerCount (thresholdSet (gapSort p k) x.val) k
    ((gapSort p k x).val % k) = _
  rw [gapSort_threshold_chain_count, gapSort_preserves_residue]

/-- Exact physical endpoint of the tagged key, derived from the actual sorter. -/
theorem gapSort_tag_position {n : ℕ} (p : RankPlacement n) (k : ℕ)
    (hk : 0 < k) (x : Fin n) :
    (gapSort p k x).val = (p x).val % k +
      k * chainLowerCount (thresholdSet p x.val) k ((p x).val % k) := by
  have h := Nat.mod_add_div (gapSort p k x).val k
  rw [← chainOrdinal_eq_div k hk, gapSort_tag_chain_rank,
    gapSort_preserves_residue] at h
  exact h.symm

/-- The complete two-pass tagged endpoint, already expressed using only the
original threshold subset and the binary local-sort operator. -/
theorem two_pass_tag_position {n : ℕ} (p : RankPlacement n) (h g : ℕ)
    (hh : 0 < h) (hg : 0 < g) (x : Fin n) :
    let B := thresholdSet p x.val
    let s := (p x).val % h
    let j := (s + h * chainLowerCount B h s) % g
    (gapSort (gapSort p h) g x).val =
      j + g * chainLowerCount (lowerStep B h) g j := by
  dsimp only
  have ht := gapSort_tag_position (gapSort p h) g hg x
  rw [gapSort_tag_position p h hh x, gapSort_threshold_commutes] at ht
  exact ht

theorem thresholdSet_card {n : ℕ} (p : RankPlacement n) (t : ℕ) :
    (thresholdSet p t).card = min n t := by
  let e : {x : Fin n // x.val < t} ≃ {i : Fin n // (p.symm i).val < t} :=
    Equiv.subtypeEquiv p (by intro x; simp)
  have h := Fintype.card_congr e
  rw [Fintype.card_subtype, Fintype.card_subtype] at h
  simpa [thresholdSet, Fin.card_filter_val_lt] using h.symm

theorem tagged_threshold_card {n : ℕ} (p : RankPlacement n) (x : Fin n) :
    (thresholdSet p x.val).card = x.val := by
  rw [thresholdSet_card, min_eq_right (Nat.le_of_lt x.isLt)]

end Shellsort
end

/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.GapSort
public import Mathlib.Data.Fintype.Card

/-! Threshold sets and the prefix characterization of their images under a gap pass. -/

@[expose] public noncomputable section
namespace Shellsort
open scoped BigOperators

/-- Positions holding keys whose global rank is strictly below t. -/
def thresholdSet {n : ℕ} (p : RankPlacement n) (t : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (p.symm i).val < t)

def chainPositions (n k r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.val % k = r)

def chainLowerCount {n : ℕ} (B : Finset (Fin n)) (k r : ℕ) : ℕ :=
  (B.filter (fun i => i.val % k = r)).card

def chainOrdinal {n : ℕ} (k : ℕ) (i : Fin n) : ℕ :=
  ((chainPositions n k (i.val % k)).filter (fun j => j < i)).card

/-- Binary local sorting, defined from the original subset's chain counts. -/
def lowerStep {n : ℕ} (B : Finset (Fin n)) (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => chainOrdinal k i < chainLowerCount B k (i.val % k))

theorem threshold_mem {n : ℕ} (p : RankPlacement n) (t : ℕ) (i : Fin n) :
    i ∈ thresholdSet p t ↔ (p.symm i).val < t := by
  simp [thresholdSet]

theorem threshold_chain_count_keys {n : ℕ} (p : RankPlacement n) (t k r : ℕ) :
    chainLowerCount (thresholdSet p t) k r =
      Fintype.card {x : Fin n // (p x).val % k = r ∧ x.val < t} := by
  let e : {x : Fin n // (p x).val % k = r ∧ x.val < t} ≃
      {i : Fin n // i.val % k = r ∧ (p.symm i).val < t} :=
    Equiv.subtypeEquiv p (by intro x; simp)
  have hc := Fintype.card_congr e
  rw [Fintype.card_subtype] at hc
  rw [Fintype.card_subtype] at hc
  simpa [Fintype.card_subtype, chainLowerCount, thresholdSet, Finset.filter_filter, and_comm]
    using hc.symm

theorem gapSort_threshold_chain_count {n : ℕ} (p : RankPlacement n) (t k r : ℕ) :
    chainLowerCount (thresholdSet (gapSort p k) t) k r =
      chainLowerCount (thresholdSet p t) k r := by
  rw [threshold_chain_count_keys, threshold_chain_count_keys]
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (fun x => by simp only [gapSort_preserves_residue])

theorem gapSort_threshold_prefix {n : ℕ} (p : RankPlacement n) (t k : ℕ)
    (i j : Fin n) (hi : i ∈ thresholdSet (gapSort p k) t)
    (hchain : j.val % k = i.val % k) (hji : j < i) :
    j ∈ thresholdSet (gapSort p k) t := by
  rw [threshold_mem] at hi ⊢
  have hs := gapSort_sorted p k ((gapSort p k).symm j) ((gapSort p k).symm i)
    (by simpa using hchain)
  have hrank : (gapSort p k).symm j < (gapSort p k).symm i :=
    hs.mp (by simpa using hji)
  exact lt_trans hrank hi

/-- A finite initial segment is determined by its cardinality. -/
theorem prefix_membership_iff_card {α : Type*} [LinearOrder α]
    (A B : Finset α) (hsub : B ⊆ A)
    (hprefix : ∀ i ∈ B, ∀ j ∈ A, j < i → j ∈ B)
    (x : α) (hxA : x ∈ A) :
    x ∈ B ↔ (A.filter (fun y => y < x)).card < B.card := by
  constructor
  · intro hxB
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro y hy
      obtain ⟨hyA, hyx⟩ := Finset.mem_filter.mp hy
      exact hprefix x hxB y hyA hyx
    · intro heq
      have : x ∈ A.filter (fun y => y < x) := heq.symm ▸ hxB
      exact (lt_irrefl x) ((Finset.mem_filter.mp this).2)
  · intro hcard
    by_contra hxB
    have hsubset : B ⊆ A.filter (fun y => y < x) := by
      intro y hy
      apply Finset.mem_filter.mpr
      refine ⟨hsub hy, ?_⟩
      by_contra hnot
      have hxy : x ≤ y := le_of_not_gt hnot
      rcases lt_or_eq_of_le hxy with hlt | heq
      · exact hxB (hprefix y hy x hxA hlt)
      · exact hxB (heq ▸ hy)
    have hle := Finset.card_le_card hsubset
    omega

/-- Thresholding commutes with actual gap sorting for every finite permutation. -/
theorem gapSort_threshold_commutes {n : ℕ} (p : RankPlacement n) (t k : ℕ) :
    thresholdSet (gapSort p k) t = lowerStep (thresholdSet p t) k := by
  ext i
  let A := chainPositions n k (i.val % k)
  let B := (thresholdSet (gapSort p k) t).filter (fun j => j.val % k = i.val % k)
  have hsub : B ⊆ A := by
    intro j hj
    have h := (Finset.mem_filter.mp hj).2
    simpa [A, chainPositions] using h
  have hprefix : ∀ x ∈ B, ∀ y ∈ A, y < x → y ∈ B := by
    intro x hx y hy hyx
    obtain ⟨hxT, hxC⟩ := Finset.mem_filter.mp hx
    have hyC : y.val % k = i.val % k := by simpa [A, chainPositions] using hy
    apply Finset.mem_filter.mpr
    exact ⟨gapSort_threshold_prefix p t k x y hxT (hyC.trans hxC.symm) hyx, hyC⟩
  have hiA : i ∈ A := by simp [A, chainPositions]
  have h := prefix_membership_iff_card A B hsub hprefix i hiA
  change i ∈ thresholdSet (gapSort p k) t ↔ i ∈ lowerStep (thresholdSet p t) k
  have hcount : B.card = chainLowerCount (thresholdSet p t) k (i.val % k) :=
    gapSort_threshold_chain_count p t k (i.val % k)
  simp only [lowerStep, Finset.mem_filter, Finset.mem_univ, true_and]
  simpa [B, A, chainOrdinal, hcount] using h

end Shellsort
end

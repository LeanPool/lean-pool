/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.SparseSearchMask
public import LeanPool.KLRandomness.ComputableRational
public import LeanPool.KLRandomness.SparseCodeCount

/-!
# A finite checker for coded sparse candidate lists

An entry consists of a Boolean support mask and an ordinary affine-matrix
code. The matrix has ambient width `M`, with zero columns off its support.
Certificates and syndromes are irrelevant to this candidate-list check.
The rank tests use the certificate-free exhaustive checker.

All multiplicities are list multiplicities: repeated candidates count as
separate entries. Both density thresholds are rational numbers.
-/

@[expose] public section

namespace Klr.SparseListSearch

open AffineCode SparseSearch

/-- A support mask paired with a coded binary affine system. -/
abbrev Entry := List Bool × AffineCode.Data
/-- A finite list of candidate supports and affine codes. -/
abbrev CodeList := List Entry
/-- Dimensions, list length and rational thresholds of the finite candidate search. -/
abbrev Parameters := ℕ × ℕ × ℕ × ℕ × ℚ × ℚ

/-- Number of available positions. -/
def universeSize (p : Parameters) : ℕ := p.1
/-- Required number of selected positions in each support mask. -/
def supportSize (p : Parameters) : ℕ := p.2.1
/-- Required rank of the affine matrix in each entry. -/
def rowRank (p : Parameters) : ℕ := p.2.2.1
/-- Required number of candidate entries. -/
def listLength (p : Parameters) : ℕ := p.2.2.2.1
/-- Minimum density of the coordinate restrictions tested for rank. -/
def density (p : Parameters) : ℚ := p.2.2.2.2.1
/-- Maximum allowed fraction of entries losing rank on a tested restriction. -/
def badFraction (p : Parameters) : ℚ := p.2.2.2.2.2

/-- Mathematical specification of one supported, full-row-rank candidate. -/
def GoodEntry (M m r : ℕ) (a : Entry) : Prop :=
  a.1.length = M ∧ a.1.countP id = m ∧ width a.2 = M ∧ rank a.2 = r ∧
    Function.Surjective (matrix a.2).mulVecLin ∧
    ∀ i < r, ∀ j < M, a.1.getD j false = false → entry (rows a.2) i j = false

/-- Deleting the zero padding preserves the candidate's full row rank. -/
theorem GoodEntry.maskedFullRank {M m r : ℕ} {a : Entry} (h : GoodEntry M m r a) :
    SparseSearch.maskedFullRank a.2 a.1 = true := by
  obtain ⟨_, _, hw, hr, hf, hz⟩ := h
  have hmatrix : matrix (maskCode a.2 a.1) = matrix a.2 := by
    rw [matrix_maskCode]
    ext i j
    cases hb : a.1.getD j.val false with
    | true => simp
    | false =>
      have hi : i.val < r := by simpa only [hr] using i.isLt
      have hj : j.val < M := by simpa only [hw] using j.isLt
      simp [matrix, hz i.val hi j.val hj hb]
  rw [SparseSearch.maskedFullRank, fullRank_eq_true, hmatrix]
  exact hf

/-- The retained support has exactly the prescribed number of columns. -/
theorem GoodEntry.selectedColumns_card {M m r : ℕ} {a : Entry} (h : GoodEntry M m r a) :
    (selectedColumns a.2 a.1).card = m := by
  obtain ⟨hl, hm, hw, _⟩ := h
  change (SparseListCode.maskSet (width a.2) a.1).card = m
  rw [SparseListCode.card_maskSet _ _ (hl.trans hw.symm), hm]

/-- Each accepted padded code gives a genuine full-rank system on its `m` selected columns. -/
theorem GoodEntry.restricted_fullRank {M m r : ℕ} {a : Entry} (h : GoodEntry M m r a) :
    Function.Surjective (RandomMatrix.restrictedMap
      (fun j i => matrix a.2 i j) (selectedColumns a.2 a.1) (K := ZMod 2)) :=
  (SparseSearch.maskedFullRank_eq_true a.2 a.1).mp h.maskedFullRank

/-- The finite sparse-list contract, using exact rational comparisons.
`maskedFullRank_eq_true` identifies the final count with failures of the
actual restricted linear map. -/
def Good (M m r J : ℕ) (τ θ : ℚ) (L : CodeList) : Prop :=
  L.length = J ∧ (∀ a ∈ L, GoodEntry M m r a) ∧
    (∀ i < M, M * L.countP (fun a => a.1.getD i false) ≤ 2 * m * J) ∧
    ∀ d : List Bool, d.length = M → τ * (M : ℚ) ≤ (d.countP id : ℚ) →
      (L.countP (fun a => !maskedFullRank a.2 d) : ℚ) ≤ θ * (J : ℚ)

/-- Check that every column outside the support mask is zero. -/
def offSupportCheck (p : Parameters) (a : Entry) : Bool :=
  EffectiveScan.boundedAll (fun i => EffectiveScan.boundedAll
    (fun j => a.1.getD j false || !entry (rows a.2) i j) (universeSize p)) (rowRank p)

theorem offSupportCheck_eq_true (p : Parameters) (a : Entry) :
    offSupportCheck p a = true ↔ ∀ i < rowRank p, ∀ j < universeSize p,
      a.1.getD j false = false → entry (rows a.2) i j = false := by
  have hb (b v : Bool) : (b || !v) = true ↔ (b = false → v = false) := by
    cases b <;> cases v <;> simp
  simp only [offSupportCheck, EffectiveScan.boundedAll_eq_true, hb]

/-- Check the dimensions, support and full-rank certificate of a candidate entry. -/
def entryCheck (p : Parameters) (a : Entry) : Bool :=
  decide (a.1.length = universeSize p) &&
    (decide (a.1.countP id = supportSize p) &&
      (decide (width a.2 = universeSize p) &&
        (decide (rank a.2 = rowRank p) && (fullRank a.2 && offSupportCheck p a))))

theorem entryCheck_eq_true (p : Parameters) (a : Entry) :
    entryCheck p a = true ↔ GoodEntry (universeSize p) (supportSize p) (rowRank p) a := by
  simp only [entryCheck, Bool.and_eq_true, decide_eq_true_eq, fullRank_eq_true,
    offSupportCheck_eq_true, GoodEntry]

/-- Check the bound on how many candidates use each position. -/
def incidenceCheck (p : Parameters) (L : CodeList) : Bool :=
  EffectiveScan.boundedAll (fun i => decide
    (universeSize p * L.countP (fun a => a.1.getD i false) ≤
      2 * supportSize p * listLength p)) (universeSize p)

theorem incidenceCheck_eq_true (p : Parameters) (L : CodeList) :
    incidenceCheck p L = true ↔ ∀ i < universeSize p,
      universeSize p * L.countP (fun a => a.1.getD i false) ≤
        2 * supportSize p * listLength p := by
  simp only [incidenceCheck, EffectiveScan.boundedAll_eq_true, decide_eq_true_eq]

/-- Check the rank-loss bound when the coordinate mask meets the density threshold. -/
def restrictionCheck (p : Parameters) (L : CodeList) (d : List Bool) : Bool :=
  !decide (density p * (universeSize p : ℚ) ≤ (d.countP id : ℚ)) ||
    decide ((L.countP (fun a => !maskedFullRank a.2 d) : ℚ) ≤
      badFraction p * (listLength p : ℚ))

theorem restrictionCheck_eq_true (p : Parameters) (L : CodeList) (d : List Bool) :
    restrictionCheck p L d = true ↔
      density p * (universeSize p : ℚ) ≤ (d.countP id : ℚ) →
        (L.countP (fun a => !maskedFullRank a.2 d) : ℚ) ≤
          badFraction p * (listLength p : ℚ) := by
  by_cases h : density p * (universeSize p : ℚ) ≤ (d.countP id : ℚ)
  · simp [restrictionCheck, h]
  · simp [restrictionCheck, h]

/-- The complete finite verifier for an ordinary finite candidate-list code. -/
def check (p : Parameters) (L : CodeList) : Bool :=
  decide (L.length = listLength p) &&
    (L.all (entryCheck p) && (incidenceCheck p L &&
      (words (universeSize p)).all (restrictionCheck p L)))

theorem check_eq_true (p : Parameters) (L : CodeList) :
    check p L = true ↔
      Good (universeSize p) (supportSize p) (rowRank p) (listLength p)
        (density p) (badFraction p) L := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    entryCheck_eq_true, incidenceCheck_eq_true, restrictionCheck_eq_true, mem_words_iff, Good]

end Klr.SparseListSearch

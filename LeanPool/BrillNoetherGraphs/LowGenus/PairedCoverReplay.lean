/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import LeanPool.BrillNoetherGraphs.LowGenus.CompactCellTreeLookup

/-!
# Paired replay of integral closed-cover receipts

Each leaf pairs its receipt indices with the cone rows in order. The active rows stay
shared across the receipt checks, and each check looks up the appended violation separately.
The soundness theorem transfers the result back to the existing compact-tree checker.

The generated proofs state the initial context once in a paired check. Their wrappers recover
the original check proposition by applying soundness and retain the original auxiliary proof
declaration with `as_aux_lemma`.
-/

@[expose] public section

open Utilities.Certificate

namespace Utilities.Certificate.AffineCover.FarkasData

/-- Sum one coordinate of the sparse integral combination without an intermediate list. -/
def integralSumBy {dimension : ℕ} (data : FarkasData)
    (rows : ℕ → AffineForm dimension) (coefficient : AffineForm dimension → ℤ) : ℤ :=
  data.terms.foldr (fun term total => term.weight.num * coefficient (rows term.row) + total) 0

private theorem integralSumBy_eq {dimension : ℕ} (data : FarkasData)
    (rows : ℕ → AffineForm dimension) (coefficient : AffineForm dimension → ℤ) :
    data.integralSumBy rows coefficient =
      (data.terms.map (fun term => term.weight.num * coefficient (rows term.row))).sum := by
  unfold integralSumBy
  induction data.terms with
  | nil => rfl
  | cons term terms ih => simp only [List.foldr_cons, List.map_cons, List.sum_cons, ih]

/-- Replay the integral combination with an abstract lookup for active rows. -/
def checkIntegralLookup {dimension : ℕ} (data : FarkasData) (rowCount : ℕ)
    (rows : ℕ → AffineForm dimension) : Bool :=
  (data.terms.all fun term =>
    decide (term.row < rowCount) && decide (0 ≤ term.weight.num) &&
      decide (term.weight.den = 1)) &&
  (allFin fun coordinate => decide (data.integralSumBy rows (·.coefficient coordinate) = 0)) &&
  decide (data.integralSumBy rows AffineForm.fixedValue < 0)

private theorem checkIntegralLookup_sound {dimension : ℕ} (data : FarkasData)
    (rows : List (AffineForm dimension)) (lookup : ℕ → AffineForm dimension)
    (lookup_eq : ∀ index < rows.length, lookup index = rowAt rows index)
    (checked : data.checkIntegralLookup rows.length lookup = true) :
    data.check rows = true := by
  simp only [checkIntegralLookup, Bool.and_eq_true, List.all_eq_true, allFin_eq_true_iff,
    decide_eq_true_eq, integralSumBy_eq] at checked
  obtain ⟨⟨terms, coefficients⟩, constantNegative⟩ := checked
  have integral : data.integralWeights = true :=
    data.integralWeights_eq_true_iff.mpr (fun term member => (terms term member).2)
  have sum_eq (coefficient : AffineForm dimension → ℤ) :
      (data.terms.map (fun term => term.weight.num * coefficient (lookup term.row))).sum =
        (data.terms.map (fun term => term.weight.num * coefficient (rowAt rows term.row))).sum := by
    congr 1
    apply List.map_congr_left
    intro term member
    rw [lookup_eq term.row (terms term member).1.1]
  simp only [check, integral, integralCheck, Bool.and_eq_true, List.all_eq_true,
    allFin_eq_true_iff, decide_eq_true_eq]
  refine ⟨⟨fun term member => (terms term member).1, fun coordinate =>
    (sum_eq (·.coefficient coordinate)).symm.trans (coefficients coordinate)⟩,
    ?_⟩
  unfold constantSumInt
  rw [← sum_eq AffineForm.fixedValue]
  exact constantNegative

/-- Look up an existing row or the separately supplied final row. -/
def lookupWithLast {dimension : ℕ} (rows : List (AffineForm dimension))
    (last : AffineForm dimension) (index : ℕ) : AffineForm dimension :=
  if index = rows.length then last else rowAt rows index

private theorem lookupWithLast_eq {dimension : ℕ} (rows : List (AffineForm dimension))
    (last : AffineForm dimension) (index : ℕ) (bound : index < (rows ++ [last]).length) :
    lookupWithLast rows last index = rowAt (rows ++ [last]) index := by
  simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at bound
  rcases Nat.lt_succ_iff_lt_or_eq.mp bound with before | atLast
  · simp [lookupWithLast, ne_of_lt before, rowAt, List.getD_eq_getElem?_getD,
      List.getElem?_append_left before]
  · subst index
    simp [lookupWithLast, rowAt, List.getD_eq_getElem?_getD]

/-- Replay integral Farkas data while looking up the extra inequality separately. -/
def checkWithLast {dimension : ℕ} (data : FarkasData)
    (rows : List (AffineForm dimension)) (last : AffineForm dimension) : Bool :=
  checkIntegralLookup data (rows.length + 1) (lookupWithLast rows last)

/-- The separate lookup checks the same rows as an appended inequality. -/
theorem checkWithLast_sound {dimension : ℕ} (data : FarkasData)
    (rows : List (AffineForm dimension)) (last : AffineForm dimension)
    (checked : data.checkWithLast rows last = true) : data.check (rows ++ [last]) = true := by
  apply data.checkIntegralLookup_sound (rows ++ [last]) _ (lookupWithLast_eq rows last)
  simpa only [List.length_append, List.length_singleton, checkWithLast] using checked

end Utilities.Certificate.AffineCover.FarkasData

namespace AtanasovRanganathan.GenusFiveClosedCover.CompactCellTree

open ExplicitPotential (Core)
open AffineCover

/-- Pair cone inequalities and receipt indices directly during tree replay. -/
def checkPaired {vertices edges : ℕ} {core : Core vertices edges}
    (tree : CompactCellTree) (forms : List (AffineForm edges)) (lookup : ℕ → FarkasData)
    (cells : List (CoordinateCell core)) (active : List (AffineForm edges)) : Bool :=
  match tree with
  | .cell index indices =>
      let cone := CellTree.coneAt cells index
      decide (index < cells.length) &&
        decide (indices.length = cone.length) &&
        (indices.zipWith (fun receipt form => (lookup receipt).checkWithLast active form.violation)
          cone).all id
  | .absurd index => (lookup index).check active
  | .split index nonnegative negative =>
      let form := forms.getD index 0
      checkPaired nonnegative forms lookup cells (active ++ [form]) &&
        checkPaired negative forms lookup cells (active ++ [form.violation])

/-- Pairwise traversal establishes the existing tree check for the same receipt lookup. -/
theorem checkLookup_of_checkPaired {vertices edges : ℕ} {core : Core vertices edges}
    {tree : CompactCellTree} {forms : List (AffineForm edges)} {lookup : ℕ → FarkasData}
    {cells : List (CoordinateCell core)} {active : List (AffineForm edges)}
    (checked : tree.checkPaired forms lookup cells active = true) :
    tree.checkLookup forms lookup cells active = true := by
  induction tree generalizing active with
  | cell index indices =>
    simp only [checkPaired, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, id_eq] at checked
    obtain ⟨⟨inBounds, length_eq⟩, paired⟩ := checked
    simp only [checkLookup, decodeLookup, CellTree.check, Bool.and_eq_true, List.length_map,
      decide_eq_true_eq, ExplicitPotential.allFin_eq_true_iff]
    refine ⟨⟨inBounds, length_eq⟩, fun i => ?_⟩
    let cone := CellTree.coneAt cells index
    have within : i.val < indices.length := by simpa only [length_eq] using i.isLt
    have inZip : i.val < (indices.zipWith
        (fun receipt form => (lookup receipt).checkWithLast active form.violation)
        cone).length := by
      simp [List.length_zipWith, length_eq, cone]
    have check := paired _ (List.getElem_mem inZip)
    rw [List.getElem_zipWith] at check
    have mapWithin : i.val < (indices.map lookup).length := by simpa using within
    rw [List.getD_eq_getElem _ _ mapWithin, List.getElem_map]
    exact (lookup indices[i.val]).checkWithLast_sound active _ check
  | absurd index => exact checked
  | split index nonnegative negative ihNonnegative ihNegative =>
    obtain ⟨nonnegativeChecked, negativeChecked⟩ := Bool.and_eq_true_iff.mp checked
    exact Bool.and_eq_true_iff.mpr
      ⟨ihNonnegative nonnegativeChecked, ihNegative negativeChecked⟩

end AtanasovRanganathan.GenusFiveClosedCover.CompactCellTree

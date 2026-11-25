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

/-- Recognize the unit-weight contradiction between an active row and its closed violation. -/
def checkOpposite {dimension : ℕ} (data : FarkasData)
    (active : List (AffineForm dimension)) (form : AffineForm dimension) : Bool :=
  match data.terms with
  | [first, second] =>
    let activeRow := rowAt active first.row
    decide (first.row < active.length) && decide (second.row = active.length) &&
      decide (first.weight = 1) && decide (second.weight = 1) &&
      decide (activeRow.fixedValue ≤ form.fixedValue) &&
      allFin fun coordinate =>
        decide (activeRow.coefficient coordinate = form.coefficient coordinate)
  | _ => false

private theorem checkWithLast_of_checkOpposite {dimension : ℕ} (data : FarkasData)
    (active : List (AffineForm dimension)) (form : AffineForm dimension)
    (checked : data.checkOpposite active form = true) :
    data.checkWithLast active form.violation = true := by
  unfold checkOpposite at checked
  split at checked
  next first second terms =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, allFin_eq_true_iff] at checked
    obtain ⟨⟨⟨⟨⟨firstBound, secondIndex⟩, firstWeight⟩, secondWeight⟩, constantBound⟩,
      coefficients⟩ := checked
    have notLast := Nat.ne_of_lt firstBound
    have nonnegative : (0 : ℤ) ≤ 1 := by decide
    rw [checkWithLast, checkIntegralLookup]
    simp only [terms, List.all_cons, List.all_nil, firstWeight, secondWeight, secondIndex,
      Rat.num_one, Rat.den_one, Nat.lt_succ_of_lt firstBound, Nat.lt_succ_self, nonnegative,
      decide_true, Bool.and_true, Bool.true_and]
    simp only [integralSumBy, terms, List.foldr_cons, List.foldr_nil, firstWeight, secondWeight,
      Rat.num_one, one_mul, add_zero, lookupWithLast, notLast, secondIndex, ite_false, ite_true,
      AffineForm.violation, Bool.and_eq_true, allFin_eq_true_iff, decide_eq_true_eq]
    refine ⟨fun coordinate => ?_, by omega⟩
    rw [coefficients coordinate, add_neg_cancel]
  next => cases checked

/-- Use the unit-weight identity for matching rows and the integral check for other receipts. -/
def checkViolation {dimension : ℕ} (data : FarkasData)
    (active : List (AffineForm dimension)) (form : AffineForm dimension) : Bool :=
  data.checkOpposite active form || data.checkWithLast active form.violation

/-- The shortcut establishes the same integral receipt check. -/
theorem checkWithLast_of_checkViolation {dimension : ℕ} (data : FarkasData)
    (active : List (AffineForm dimension)) (form : AffineForm dimension)
    (checked : data.checkViolation active form = true) :
    data.checkWithLast active form.violation = true := by
  obtain opposite | integral := Bool.or_eq_true_iff.mp checked
  · exact data.checkWithLast_of_checkOpposite active form opposite
  · exact integral

/-- Replay two unit-weight rows with proof-free integer comparisons. -/
noncomputable def checkKernelOpposite {dimension : ℕ} (data : FarkasData)
    (active : List (AffineForm dimension)) (form : AffineForm dimension) : Bool :=
  match data.terms with
  | [first, second] =>
    let activeRow := rowAt active first.row
    (first.row < active.length) && (second.row == active.length) &&
      decide (first.weight = 1) && decide (second.weight = 1) &&
      decide (activeRow.fixedValue ≤ form.fixedValue) &&
      allFinFold (fun coordinate =>
        Int.beq' (activeRow.coefficient coordinate) (form.coefficient coordinate))
  | _ => false

theorem checkKernelOpposite_eq {dimension : ℕ} (data : FarkasData)
    (active : List (AffineForm dimension)) (form : AffineForm dimension) :
    data.checkKernelOpposite active form = data.checkOpposite active form := by
  unfold checkKernelOpposite checkOpposite
  cases data with
  | mk terms =>
    cases terms with
    | nil => rfl
    | cons first terms =>
      cases terms with
      | nil => rfl
      | cons second terms =>
        cases terms with
        | nil => simp only [allFinFold_eq, Int.beq'_eq_beq, beq_eq_decide]
        | cons => rfl

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

/-- Pair receipts and cone rows in a single traversal that also checks their lengths. -/
def checkReceipts {edges : ℕ} (lookup : ℕ → FarkasData) (active : List (AffineForm edges)) :
    List ℕ → List (AffineForm edges) → Bool
  | [], [] => true
  | index :: indices, form :: forms =>
      (lookup index).checkViolation active form && checkReceipts lookup active indices forms
  | _, _ => false

private theorem checkReceipts_sound {edges : ℕ} (lookup : ℕ → FarkasData)
    (active : List (AffineForm edges)) (indices : List ℕ) (forms : List (AffineForm edges))
    (checked : checkReceipts lookup active indices forms = true) :
    indices.length = forms.length ∧
      (indices.zipWith (fun index form => (lookup index).checkWithLast active form.violation)
        forms).all id = true := by
  induction indices generalizing forms with
  | nil =>
    cases forms with
    | nil => exact ⟨rfl, rfl⟩
    | cons form forms => cases checked
  | cons index indices inductionHypothesis =>
    cases forms with
    | nil => cases checked
    | cons form forms =>
      obtain ⟨first, rest⟩ := Bool.and_eq_true_iff.mp checked
      obtain ⟨lengthEquality, accepted⟩ := inductionHypothesis forms rest
      refine ⟨congrArg Nat.succ lengthEquality, ?_⟩
      exact Bool.and_eq_true_iff.mpr
        ⟨(lookup index).checkWithLast_of_checkViolation active form first, accepted⟩

/-- Replay leaves with the unit-weight shortcut for an active row and its violation. -/
def checkWithOpposites {vertices edges : ℕ} {core : Core vertices edges}
    (tree : CompactCellTree) (forms : List (AffineForm edges)) (lookup : ℕ → FarkasData)
    (cells : List (CoordinateCell core)) (active : List (AffineForm edges)) : Bool :=
  match tree with
  | .cell index indices =>
      decide (index < cells.length) &&
        checkReceipts lookup active indices (CellTree.coneAt cells index)
  | .absurd index => (lookup index).check active
  | .split index nonnegative negative =>
      let form := forms.getD index 0
      checkWithOpposites nonnegative forms lookup cells (active ++ [form]) &&
        checkWithOpposites negative forms lookup cells (active ++ [form.violation])

/-- A replay using opposite rows still proves the paired check for each leaf. -/
theorem checkPaired_of_checkWithOpposites {vertices edges : ℕ} {core : Core vertices edges}
    {tree : CompactCellTree} {forms : List (AffineForm edges)} {lookup : ℕ → FarkasData}
    {cells : List (CoordinateCell core)} {active : List (AffineForm edges)}
    (checked : tree.checkWithOpposites forms lookup cells active = true) :
    tree.checkPaired forms lookup cells active = true := by
  induction tree generalizing active with
  | cell index indices =>
    simp only [checkWithOpposites, checkPaired, Bool.and_eq_true] at checked ⊢
    obtain ⟨lengthEquality, receipts⟩ := checkReceipts_sound lookup active indices _ checked.2
    exact ⟨⟨checked.1, decide_eq_true lengthEquality⟩, receipts⟩
  | absurd index => exact checked
  | split index nonnegative negative ihNonnegative ihNegative =>
    obtain ⟨nonnegativeChecked, negativeChecked⟩ := Bool.and_eq_true_iff.mp checked
    exact Bool.and_eq_true_iff.mpr
      ⟨ihNonnegative nonnegativeChecked, ihNegative negativeChecked⟩

/-- Decide the paired checker through the unit-weight shortcut when it succeeds. -/
@[instance_reducible]
def decidableCheckPaired {vertices edges : ℕ} {core : Core vertices edges}
    (tree : CompactCellTree) (forms : List (AffineForm edges)) (lookup : ℕ → FarkasData)
    (cells : List (CoordinateCell core)) (active : List (AffineForm edges)) :
    Decidable (tree.checkPaired forms lookup cells active = true) :=
  if checked : tree.checkWithOpposites forms lookup cells active = true then
    isTrue (checkPaired_of_checkWithOpposites checked)
  else inferInstance

/-- Match each cone inequality to its verified receipt in one pass. -/
noncomputable def checkKernelReceipts {edges : ℕ} (lookup : ℕ → FarkasData)
    (active : List (AffineForm edges)) : List ℕ → List (AffineForm edges) → Bool
  | [], [] => true
  | index :: indices, form :: forms =>
    let receipt := lookup index
    (receipt.checkKernelOpposite active form || receipt.checkWithLast active form.violation) &&
      checkKernelReceipts lookup active indices forms
  | _, _ => false

private theorem checkKernelReceipts_eq {edges : ℕ} (lookup : ℕ → FarkasData)
    (active : List (AffineForm edges)) (indices : List ℕ) (forms : List (AffineForm edges)) :
    checkKernelReceipts lookup active indices forms =
      checkReceipts lookup active indices forms := by
  induction indices generalizing forms with
  | nil => cases forms <;> rfl
  | cons index indices ih =>
    cases forms with
    | nil => rfl
    | cons form forms =>
      simp only [checkKernelReceipts, checkReceipts, FarkasData.checkKernelOpposite_eq,
        FarkasData.checkViolation, ih]

/-- Replay tree leaves with proof-free integer tests and a supplied cone lookup. -/
noncomputable def checkKernelTree {edges : ℕ}
    (tree : CompactCellTree) (forms : List (AffineForm edges)) (lookup : ℕ → FarkasData)
    (cellCount : ℕ) (coneAt : ℕ → List (AffineForm edges))
    (active : List (AffineForm edges)) : Bool :=
  match tree with
  | .cell index indices =>
      decide (index < cellCount) && checkKernelReceipts lookup active indices (coneAt index)
  | .absurd index => (lookup index).check active
  | .split index nonnegative negative =>
      let form := forms.getD index 0
      checkKernelTree nonnegative forms lookup cellCount coneAt (active ++ [form]) &&
        checkKernelTree negative forms lookup cellCount coneAt (active ++ [form.violation])

theorem checkKernelTree_eq {vertices edges : ℕ} {core : Core vertices edges}
    (tree : CompactCellTree) (forms : List (AffineForm edges)) (lookup : ℕ → FarkasData)
    (cells : List (CoordinateCell core)) (active : List (AffineForm edges))
    (cellCount : ℕ) (coneAt : ℕ → List (AffineForm edges))
    (count_eq : cellCount = cells.length)
    (cone_eq : ∀ index, coneAt index = CellTree.coneAt cells index) :
    tree.checkKernelTree forms lookup cellCount coneAt active =
      tree.checkWithOpposites forms lookup cells active := by
  induction tree generalizing active with
  | cell index indices =>
    simp only [checkKernelTree, checkWithOpposites, count_eq, cone_eq, checkKernelReceipts_eq]
  | absurd index => rfl
  | split index nonnegative negative ihNonnegative ihNegative =>
    simp only [checkKernelTree, checkWithOpposites, ihNonnegative, ihNegative]

/-- Use a verified index for cone lookup in the kernel replay. -/
noncomputable def decidableCheckPairedKernelWithLookup {vertices edges : ℕ}
    {core : Core vertices edges} (tree : CompactCellTree) (forms : List (AffineForm edges))
    (lookup : ℕ → FarkasData) (cells : List (CoordinateCell core))
    (active : List (AffineForm edges)) (cellCount : ℕ) (coneAt : ℕ → List (AffineForm edges))
    (count_eq : cellCount = cells.length)
    (cone_eq : ∀ index, coneAt index = CellTree.coneAt cells index) :
    Decidable (tree.checkPaired forms lookup cells active = true) :=
  if checked : tree.checkKernelTree forms lookup cellCount coneAt active = true then
    isTrue (checkPaired_of_checkWithOpposites
      (checkKernelTree_eq tree forms lookup cells active cellCount coneAt count_eq cone_eq ▸
        checked))
  else inferInstance

/-- Decide paired replay using proof-free comparisons in the unit-weight case. -/
@[instance_reducible]
noncomputable def decidableCheckPairedKernel {vertices edges : ℕ} {core : Core vertices edges}
    (tree : CompactCellTree) (forms : List (AffineForm edges)) (lookup : ℕ → FarkasData)
    (cells : List (CoordinateCell core)) (active : List (AffineForm edges)) :
    Decidable (tree.checkPaired forms lookup cells active = true) :=
  decidableCheckPairedKernelWithLookup tree forms lookup cells active
    cells.length (CellTree.coneAt cells) rfl (fun _ => rfl)

end AtanasovRanganathan.GenusFiveClosedCover.CompactCellTree

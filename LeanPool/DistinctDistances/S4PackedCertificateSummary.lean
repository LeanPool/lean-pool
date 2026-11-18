/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.FarkasPackedCheck

/-!
# Checked summaries of weighted row subtrees

Combine exact kernel-verified subtree results before applying the full certificate checker.
-/

@[expose] public section

namespace Esgk.FarkasPackedCheck

deriving instance DecidableEq for PackTrie

/-- The quantities the certificate checker computes from a weighted tree. -/
structure PackedSummary where
  /-- The weighted cost, including penalties for missing and invalid rows. -/
  cost : Nat
  /-- The weighted right-hand side. -/
  rhs : Int
  /-- The combined positive coefficients. -/
  positive : PackTrie
  /-- The combined negative coefficients. -/
  negative : PackTrie

/-- The summary of a node combines its two child summaries. -/
noncomputable def PackedSummary.combine (left right : PackedSummary) : PackedSummary :=
  ⟨left.cost + right.cost, left.rhs + right.rhs, left.positive.add right.positive,
    left.negative.add right.negative⟩

/-- The four fields match the checker’s calculations for the original subtree. -/
structure SummaryValid {T : Type} (width : Nat) (box : Box) (build : T → Option Row)
    (rows : WTree T) (summary : PackedSummary) : Prop where
  /-- The same cost that the checker computes. -/
  cost_eq : rows.sumNat (leafCost width box.nv build) = summary.cost
  /-- The same right-hand side that the checker computes. -/
  rhs_eq : rows.sumInt (leafRhs build) = summary.rhs
  /-- The same packed positive sum that the checker computes. -/
  positive_eq :
    rows.sumTrie (leafPack width (chunkLen box.nv 4) 4 build Row.pos) = summary.positive
  /-- The same packed negative sum that the checker computes. -/
  negative_eq :
    rows.sumTrie (leafPack width (chunkLen box.nv 4) 4 build Row.neg) = summary.negative

/-- Exact child quantities imply the exact quantities for a node. -/
theorem SummaryValid.node {T : Type} {width : Nat} {box : Box} {build : T → Option Row}
    {left right : WTree T} {leftSummary rightSummary : PackedSummary}
    (hl : SummaryValid width box build left leftSummary)
    (hr : SummaryValid width box build right rightSummary) :
    SummaryValid width box build (.node left right) (leftSummary.combine rightSummary) :=
  ⟨congr (congrArg Nat.add hl.cost_eq) hr.cost_eq,
    congr (congrArg Int.add hl.rhs_eq) hr.rhs_eq,
    congr (congrArg PackTrie.add hl.positive_eq) hr.positive_eq,
    congr (congrArg PackTrie.add hl.negative_eq) hr.negative_eq⟩

/-- The checker’s final comparisons, performed on exact summary values. -/
noncomputable def checkSummary (width : Nat) (box : Box) (summary : PackedSummary) : Bool :=
  Nat.blt summary.cost (2 ^ width) &&
    fracGt summary.rhs
      (decodeTrie width (chunkLen box.nv 4) box 4 0 summary.positive summary.negative)

/-- A passing exact summary certifies the original full tree. -/
theorem SummaryValid.checked {T : Type} {width : Nat} {box : Box} {build : T → Option Row}
    {rows : WTree T} {summary : PackedSummary}
    (e : SummaryValid width box build rows summary)
    (h : checkSummary width box summary = true) : check width box build rows = true := by
  unfold FarkasPackedCheck.check checkWith
  rw [e.cost_eq, e.rhs_eq, e.positive_eq, e.negative_eq]
  exact h

end Esgk.FarkasPackedCheck

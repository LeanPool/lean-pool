/-
Copyright (c) 2026 Nathan Pflueger and OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger, OpenAI
-/
module

public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveClosedCover

/-!
# Equivalent receipt lookups for compact cover replay

The generated row proofs keep their original tables and checker statements. Their private
`_chunked` lemmas replay the same trees with a size-checked block lookup, skipping complete
receipt blocks rather than repeatedly traversing a concatenated prefix.

The original proofs transfer these results through `checkLookup_eq_check`. Their `as_aux_lemma`
wrappers also preserve the names and types of the original kernel-check auxiliary declarations.
-/

@[expose] public section

open Utilities Utilities.Certificate

namespace AtanasovRanganathan.GenusFiveClosedCover.CompactCellTree

/-- Decode receipt indices through a supplied lookup function. -/
def decodeLookup {p : ℕ}
    (forms : List (ExplicitPotential.AffineForm p))
    (lookupReceipt : ℕ → Certificate.AffineCover.FarkasData) : CompactCellTree → CellTree p
  | .cell index indices => .cell index (indices.map lookupReceipt)
  | .absurd index => .absurd (lookupReceipt index)
  | .split index nonnegative negative =>
      .split (forms.getD index 0)
        (decodeLookup forms lookupReceipt nonnegative)
        (decodeLookup forms lookupReceipt negative)

/-- List lookup recovers the original compact-tree decoder. -/
theorem decodeLookup_getD {p : ℕ} (tree : CompactCellTree)
    (forms : List (ExplicitPotential.AffineForm p))
    (receipts : List Certificate.AffineCover.FarkasData) :
    decodeLookup forms (fun index => receipts.getD index { terms := [] }) tree =
      tree.decode forms receipts := by
  induction tree with
  | cell index indices => rfl
  | absurd index => rfl
  | split index nonnegative negative ihNonnegative ihNegative =>
      simp only [decodeLookup, decode, ihNonnegative, ihNegative]

/-- Replay a compact tree using an extensionally equivalent receipt lookup. -/
def checkLookup {n p : ℕ} {core : ExplicitPotential.Core n p}
    (tree : CompactCellTree) (forms : List (ExplicitPotential.AffineForm p))
    (lookupReceipt : ℕ → Certificate.AffineCover.FarkasData)
    (cells : List (CoordinateCell core))
    (active : List (ExplicitPotential.AffineForm p)) : Bool :=
  (decodeLookup forms lookupReceipt tree).check cells active

/-- Changing the lookup implementation preserves every original replay result. -/
theorem checkLookup_eq_check {n p : ℕ} {core : ExplicitPotential.Core n p}
    (tree : CompactCellTree) (forms : List (ExplicitPotential.AffineForm p))
    (receipts : List Certificate.AffineCover.FarkasData)
    (lookupReceipt : ℕ → Certificate.AffineCover.FarkasData)
    (hLookup : ∀ index, lookupReceipt index = receipts.getD index { terms := [] })
    (cells : List (CoordinateCell core))
    (active : List (ExplicitPotential.AffineForm p)) :
    checkLookup tree forms lookupReceipt cells active = tree.check forms receipts cells active := by
  have hFunctions : lookupReceipt = fun index => receipts.getD index { terms := [] } :=
    funext hLookup
  rw [checkLookup, hFunctions, decodeLookup_getD]
  rfl
end AtanasovRanganathan.GenusFiveClosedCover.CompactCellTree

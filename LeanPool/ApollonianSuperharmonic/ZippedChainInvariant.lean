/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Pairwise

/-!
# Invariants across zipped chains

Adapted from Wesley Pegden's Apache-2.0 Trellis formalization.
-/

@[expose] public section

namespace ApollonianSuperharmonic

variable {α β γ : Type*}

/-- Invariants on two zipped chains agree when the first head is the second last endpoint. -/
theorem zippedChainInvariant (invariant : α × β → γ)
    (tiles reverseTiles : List α) (hs reverseHs : List β) (R : α) (hendpoint : β)
    (tileHead : tiles.head? = some R) (valueHead : hs.head? = some hendpoint)
    (tileLast : reverseTiles.getLast? = some R)
    (valueLast : reverseHs.getLast? = some hendpoint)
    (lastLengths : reverseTiles.length = reverseHs.length)
    (hfirstChain : (tiles.zip hs).IsChain (fun X Y => invariant X = invariant Y))
    (hsecondChain : (reverseTiles.zip reverseHs).IsChain (fun X Y => invariant X = invariant Y))
    (U V : α) (g k : β) (hU : (U, g) ∈ tiles.zip hs)
    (hV : (V, k) ∈ reverseTiles.zip reverseHs) : invariant (U, g) = invariant (V, k) := by
  let invRel := fun X Y : α × β => invariant X = invariant Y
  let : Trans invRel invRel invRel := ⟨by
    intro a b c hab hbc
    exact hab.trans hbc⟩
  let : Std.Refl invRel := ⟨fun _ => rfl⟩
  have hfirstPairwise := List.isChain_iff_pairwise.mp hfirstChain
  have hsecondPairwise := List.isChain_iff_pairwise.mp hsecondChain
  obtain ⟨postTiles, hpostTiles⟩ := List.head?_eq_some_iff.mp tileHead
  obtain ⟨postHs, hpostHs⟩ := List.head?_eq_some_iff.mp valueHead
  have hzipHead : tiles.zip hs = (R, hendpoint) :: postTiles.zip postHs := by
    rw [hpostTiles, hpostHs]
    rfl
  obtain ⟨preTiles, hpreTiles⟩ := List.getLast?_eq_some_iff.mp tileLast
  obtain ⟨preHs, hpreHs⟩ := List.getLast?_eq_some_iff.mp valueLast
  have hlenPre : preTiles.length = preHs.length := by
    have hlen := lastLengths
    rw [hpreTiles, hpreHs, List.length_append, List.length_singleton,
      List.length_append, List.length_singleton] at hlen
    omega
  have hzipLast : reverseTiles.zip reverseHs = preTiles.zip preHs ++ [(R, hendpoint)] := by
    rw [hpreTiles, hpreHs, List.zip_append hlenPre]
    simp
  have hInvU : invariant (R, hendpoint) = invariant (U, g) := by
    rw [hzipHead] at hfirstPairwise hU
    simpa using hfirstPairwise.rel_head hU
  have hInvV : invariant (V, k) = invariant (R, hendpoint) := by
    rw [hzipLast] at hsecondPairwise hV
    simpa using hsecondPairwise.rel_getLast hV
  exact hInvU.symm.trans hInvV.symm

end ApollonianSuperharmonic

end

/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4733T1ContainedWalk
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import Mathlib.Data.List.Chain

-- [TABLET NODE: P4733T1WalkTransport]

/-!
# P4733T1WalkTransport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4733T1WalkTransport (T U : ProtoTile) (x y : GaussianInt)
    (p : List GaussianInt) (h : P4733T1ContainedWalk T U x y p) :
    P4733T1ContainedWalk T U y x p.reverse ∧
    ∀ w : GaussianInt, P4733T1ContainedWalk
      (TileTranslation T w) (TileTranslation U w) (x + w) (y + w)
      (p.map (fun z => z + w)) := by
-- BODY
  rcases h with ⟨hh, hl, hv, he⟩
  constructor
  · refine ⟨by simpa using hl, by simpa using hh, ?_, ?_⟩
    · intro z hz
      exact hv z (List.mem_reverse.mp hz)
    · intro a b l₁ l₂ hp
      have hp' : p = l₂.reverse ++ b :: a :: l₁.reverse := by
        simpa [List.reverse_append, List.reverse_cons, List.append_assoc]
          using congrArg List.reverse hp
      simpa only [Finset.pair_comm] using he b a _ _ hp'
  · intro w
    have vertex (V : ProtoTile) (z : GaussianInt) (hz : z ∈ FootprintVertices V) :
        z + w ∈ FootprintVertices (TileTranslation V w) := by
      rw [(TileTranslationFormulas V w).2.2.2.2.2.1]
      exact ⟨z, hz, rfl⟩
    have edge (V : ProtoTile) (a b : GaussianInt)
        (hab : {a, b} ∈ FootprintEdges V) :
        {a + w, b + w} ∈ FootprintEdges (TileTranslation V w) := by
      rw [(TileTranslationFormulas V w).2.2.2.2.2.2.1]
      exact ⟨{a, b}, hab, by simp [GaussianTranslation]⟩
    refine ⟨by simp [hh], by simp [hl], ?_, ?_⟩
    · intro z hz
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
      exact ⟨vertex T a (hv a ha).1, vertex U a (hv a ha).2⟩
    · have chain := List.isChain_iff_forall_rel_of_append_cons_cons.mpr he
      have mapped : List.IsChain (fun a b =>
          {a, b} ∈ FootprintEdges (TileTranslation T w) ∩
            FootprintEdges (TileTranslation U w)) (p.map (fun z => z + w)) :=
        List.isChain_map_of_isChain (fun z => z + w)
        (fun a b hab => ⟨edge T a b hab.1, edge U a b hab.2⟩) chain
      exact List.isChain_iff_forall_rel_of_append_cons_cons.mp mapped

end ApollonianSuperharmonic

end

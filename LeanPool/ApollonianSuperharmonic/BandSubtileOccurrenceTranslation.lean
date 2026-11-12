/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandSubtileOccurrence
public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslation
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: BandSubtileOccurrenceTranslation]

/-!
# BandSubtileOccurrenceTranslation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandSubtileOccurrenceTranslation :
    ∀ (q : Fin 4 → CircleCoordinates) (T S : ProtoTile)
      (i : Fin 3) (s : Bool) (u : GaussianInt),
    BandSubtileOccurrence q T i s S ↔
      BandSubtileOccurrence q (TileTranslation T u) i s
        (TileTranslation S u) := by
-- BODY
  intro q T S i s u
  have cancel (R : ProtoTile) :
      TileTranslation (TileTranslation R u) (-u) = R := by
    cases R with
    | mk cells anchor =>
      change ProtoTile.mk ((cells.image (GaussianTranslation u)).image
          (GaussianTranslation (-u)))
        (GaussianTranslation (-u) (GaussianTranslation u anchor)) =
        ProtoTile.mk cells anchor
      congr
      · ext x
        simp [GaussianTranslation, add_assoc, add_comm]
      · simp [GaussianTranslation, add_assoc, add_comm]
  have forward (A B : ProtoTile) (v : GaussianInt) :
      BandSubtileOccurrence q A i s B →
        BandSubtileOccurrence q (TileTranslation A v) i s
          (TileTranslation B v) := by
    intro h
    rcases h with ⟨hband, hfoot, hcent⟩
    refine ⟨BandPrototileTranslation (q i.succ) B v hband, ?_, ?_⟩
    · rw [(TileTranslationFormulas B v).2.2.2.2.2.1,
      (TileTranslationFormulas A v).2.2.2.2.2.1]
      exact Set.image_mono hfoot
    · rw [(TileTranslationFormulas B v).2.2.2.2.1,
      (TileTranslationFormulas A v).2.2.2.2.1]
      simpa [Prod.ext_iff, sub_eq_add_neg, add_assoc, add_comm, add_left_comm,
        smul_add] using hcent
  constructor
  · exact forward T S u
  · intro h
    have hback := forward (TileTranslation T u) (TileTranslation S u) (-u) h
    rw [cancel T, cancel S] at hback
    exact hback

end ApollonianSuperharmonic

end

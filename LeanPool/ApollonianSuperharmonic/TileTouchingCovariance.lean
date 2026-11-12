/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.SimpleGridPathEquivariance
public import LeanPool.ApollonianSuperharmonic.TileQuarterTurnFormulas
public import LeanPool.ApollonianSuperharmonic.TileReflectionFormulas
public import LeanPool.ApollonianSuperharmonic.TileTouching
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: TileTouchingCovariance]

/-!
# TileTouchingCovariance

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem TileTouchingCovariance : ∀ (T U : ProtoTile) (u : GaussianInt),
    (TileTouching T U ↔
      TileTouching (TileTranslation T u) (TileTranslation U u)) ∧
    (TileTouching T U ↔
      TileTouching (TileQuarterTurn T) (TileQuarterTurn U)) ∧
    (TileTouching T U ↔
      TileTouching (TileReflection T) (TileReflection U)) := by
-- BODY
  have image_intersection : ∀ {α β : Type} (A B : Set α) (f : α → β),
      Function.Injective f →
      f '' (A ∩ B) = (f '' A) ∩ (f '' B) := by
    intro α β A B f hf
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy.1, rfl⟩, ⟨y, hy.2, rfl⟩⟩
    · rintro ⟨⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩
      have hab : a = b := hf (hax.trans hbx.symm)
      exact ⟨a, ⟨ha, hab ▸ hb⟩, hax⟩
  have image_disjoint : ∀ (A B : Set GaussianInt) (f : GaussianInt → GaussianInt),
      Function.Injective f →
      (Disjoint A B ↔ Disjoint (f '' A) (f '' B)) := by
    intro A B f hf
    exact (Set.disjoint_image_iff hf).symm
  have image_mem : ∀ (A : Set GaussianInt) (f : GaussianInt → GaussianInt),
      Function.Bijective f → ∀ x, (x ∈ A ↔ f x ∈ f '' A) := by
    intro A f hf x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      have hyx : y = x := hf.1 hxy
      exact hyx ▸ hy
  have generic_covariance : ∀ (T U T' U' : ProtoTile)
      (c f : GaussianInt → GaussianInt),
      T'.cells = T.cells.image c → U'.cells = U.cells.image c →
      T'.anchor = f T.anchor → U'.anchor = f U.anchor →
      ((T'.cells = ∅ ↔ T.cells = ∅) ∧ (U'.cells = ∅ ↔ U.cells = ∅)) →
      BoundaryFootprintVertices T' = f '' BoundaryFootprintVertices T →
      BoundaryFootprintVertices U' = f '' BoundaryFootprintVertices U →
      BoundaryFootprintEdges T' = (fun e : Finset GaussianInt => e.image f) ''
        BoundaryFootprintEdges T →
      BoundaryFootprintEdges U' = (fun e : Finset GaussianInt => e.image f) ''
        BoundaryFootprintEdges U →
      Function.Injective c → Function.Bijective f →
      (∀ (V : Set GaussianInt) (E : Set (Finset GaussianInt)),
        SimpleGridPath V E ↔
          SimpleGridPath (f '' V) ((fun e : Finset GaussianInt => e.image f) '' E)) →
      (TileTouching T U ↔ TileTouching T' U') := by
    intro T U T' U' c f htc huc hta hua hem hvT hvU heT heU hc hf hpath
    unfold TileTouching
    rw [htc, huc, hvT, hvU, heT, heU, hta, hua]
    have cell_empty (A : Finset GaussianInt) :
        A.image c = ∅ ↔ A = ∅ := Finset.image_eq_empty
    have cell_nonempty (A : Finset GaussianInt) :
        (A.image c).Nonempty ↔ A.Nonempty := Finset.image_nonempty
    have image_disjoint_finset : ∀ (A B : Finset GaussianInt),
        Disjoint A B ↔ Disjoint (A.image c) (B.image c) := by
      intro A B
      exact (Finset.disjoint_image hc).symm
    have edge_inter :
        (fun e : Finset GaussianInt => e.image f) ''
            (BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U) =
          ((fun e : Finset GaussianInt => e.image f) '' BoundaryFootprintEdges T) ∩
            ((fun e : Finset GaussianInt => e.image f) '' BoundaryFootprintEdges U) := by
      apply image_intersection (A := BoundaryFootprintEdges T)
        (B := BoundaryFootprintEdges U)
        (f := fun e : Finset GaussianInt => e.image f)
      exact Finset.image_injective hf.1
    have vertex_inter := image_intersection
      (BoundaryFootprintVertices T) (BoundaryFootprintVertices U) f hf.1
    have disj := image_disjoint_finset T.cells U.cells
    have paths := hpath
      (BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U)
      (BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U)
    have anchorT := image_mem (BoundaryFootprintVertices U) f hf T.anchor
    have anchorU := image_mem (BoundaryFootprintVertices T) f hf U.anchor
    rw [cell_empty, cell_empty]
    rw [cell_nonempty, cell_nonempty, disj]
    rw [← vertex_inter, ← edge_inter]
    rw [paths]
    simp [anchorT, anchorU]
  have translation_injective (u : GaussianInt) :
      Function.Injective (GaussianTranslation u) := by
    intro a b h
    dsimp [GaussianTranslation] at h ⊢
    exact add_right_cancel h
  have translation_bijective (u : GaussianInt) :
      Function.Bijective (GaussianTranslation u) := by
    constructor
    · exact translation_injective u
    · intro a
      refine ⟨a - u, ?_⟩
      dsimp [GaussianTranslation]
      exact sub_add_cancel a u
  have quarter_injective : Function.Injective GaussianQuarterTurn := by
    intro a b h
    have him := congrArg (fun z : GaussianInt => z.im) h
    have hre := congrArg (fun z : GaussianInt => z.re) h
    apply Zsqrtd.ext
    · simpa [GaussianQuarterTurn] using him
    · simpa [GaussianQuarterTurn] using hre
  have quarter_bijective : Function.Bijective GaussianQuarterTurn := by
    constructor
    · exact quarter_injective
    · intro a
      refine ⟨⟨a.im, -a.re⟩, ?_⟩
      dsimp [GaussianQuarterTurn]
      ext <;> simp
  have reflection_injective : Function.Injective GaussianReflection := by
    intro a b h
    have hre := congrArg (fun z : GaussianInt => z.re) h
    have him := congrArg (fun z : GaussianInt => -z.im) h
    apply Zsqrtd.ext
    · simpa [GaussianReflection] using hre
    · simpa [GaussianReflection] using him
  have reflection_bijective : Function.Bijective GaussianReflection := by
    constructor
    · exact reflection_injective
    · intro a
      refine ⟨⟨a.re, -a.im⟩, ?_⟩
      dsimp [GaussianReflection]
      ext <;> simp
  intro T U u
  have translation_result : TileTouching T U ↔
      TileTouching (TileTranslation T u) (TileTranslation U u) := by
    apply generic_covariance T U (TileTranslation T u) (TileTranslation U u)
      (GaussianTranslation u) (GaussianTranslation u)
    · exact (TileTranslationFormulas T u).1
    · exact (TileTranslationFormulas U u).1
    · exact (TileTranslationFormulas T u).2.1
    · exact (TileTranslationFormulas U u).2.1
    · exact ⟨(TileTranslationFormulas T u).2.2.1,
        (TileTranslationFormulas U u).2.2.1⟩
    · exact (TileTranslationFormulas T u).2.2.2.2.2.2.2.1
    · exact (TileTranslationFormulas U u).2.2.2.2.2.2.2.1
    · exact (TileTranslationFormulas T u).2.2.2.2.2.2.2.2
    · exact (TileTranslationFormulas U u).2.2.2.2.2.2.2.2
    · exact translation_injective u
    · exact translation_bijective u
    · exact fun V E => (SimpleGridPathEquivariance V E u).1
  have quarter_result : TileTouching T U ↔
      TileTouching (TileQuarterTurn T) (TileQuarterTurn U) := by
    apply generic_covariance T U (TileQuarterTurn T) (TileQuarterTurn U)
      (fun x => GaussianQuarterTurn x - 1) GaussianQuarterTurn
    · exact (TileQuarterTurnFormulas T).1
    · exact (TileQuarterTurnFormulas U).1
    · exact (TileQuarterTurnFormulas T).2.1
    · exact (TileQuarterTurnFormulas U).2.1
    · exact ⟨(TileQuarterTurnFormulas T).2.2.1,
        (TileQuarterTurnFormulas U).2.2.1⟩
    · exact (TileQuarterTurnFormulas T).2.2.2.2.2.2.2.1
    · exact (TileQuarterTurnFormulas U).2.2.2.2.2.2.2.1
    · exact (TileQuarterTurnFormulas T).2.2.2.2.2.2.2.2
    · exact (TileQuarterTurnFormulas U).2.2.2.2.2.2.2.2
    · intro a b h
      apply quarter_injective
      have shifted := congrArg (fun z : GaussianInt => z + 1) h
      simpa using shifted
    · exact quarter_bijective
    · exact fun V E => (SimpleGridPathEquivariance V E u).2.1
  have reflection_result : TileTouching T U ↔
      TileTouching (TileReflection T) (TileReflection U) := by
    apply generic_covariance T U (TileReflection T) (TileReflection U)
      (fun x => GaussianReflection x - ⟨0, 1⟩) GaussianReflection
    · exact (TileReflectionFormulas T).1
    · exact (TileReflectionFormulas U).1
    · exact (TileReflectionFormulas T).2.1
    · exact (TileReflectionFormulas U).2.1
    · exact ⟨(TileReflectionFormulas T).2.2.1,
        (TileReflectionFormulas U).2.2.1⟩
    · exact (TileReflectionFormulas T).2.2.2.2.2.2.2.1
    · exact (TileReflectionFormulas U).2.2.2.2.2.2.2.1
    · exact (TileReflectionFormulas T).2.2.2.2.2.2.2.2
    · exact (TileReflectionFormulas U).2.2.2.2.2.2.2.2
    · intro a b h
      apply reflection_injective
      have shifted := congrArg (fun z : GaussianInt => z + ⟨0, 1⟩) h
      simpa using shifted
    · exact reflection_bijective
    · exact fun V E => (SimpleGridPathEquivariance V E u).2.2
  exact ⟨translation_result, quarter_result, reflection_result⟩

end ApollonianSuperharmonic

end

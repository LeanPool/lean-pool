/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.TileTouchingCovariance
public import LeanPool.ApollonianSuperharmonic.TouchingTriple

-- [TABLET NODE: TouchingTripleCovariance]

/-!
# TouchingTripleCovariance

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem TouchingTripleCovariance :
    ∀ (T U V : ProtoTile) (u : GaussianInt),
    (TouchingTriple T U V ↔
      TouchingTriple (TileTranslation T u) (TileTranslation U u)
        (TileTranslation V u)) ∧
    (TouchingTriple T U V ↔
      TouchingTriple (TileQuarterTurn T) (TileQuarterTurn U)
        (TileQuarterTurn V)) ∧
    (TouchingTriple T U V ↔
      TouchingTriple (TileReflection T) (TileReflection U)
        (TileReflection V)) := by
-- BODY
  have image_unique : ∀ (A B C : Set GaussianInt) (f : GaussianInt → GaussianInt),
      Function.Bijective f →
      ((∃! x, x ∈ A ∧ x ∈ B ∧ x ∈ C) ↔
        (∃! y, y ∈ f '' A ∧ y ∈ f '' B ∧ y ∈ f '' C)) := by
    intro A B C f hf
    constructor
    · rintro ⟨x, hx, hxu⟩
      refine ⟨f x, ?_, ?_⟩
      · exact ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2.1, rfl⟩, ⟨x, hx.2.2, rfl⟩⟩
      · intro y hy
        rcases hy with ⟨⟨a, ha, hac⟩, ⟨b, hb, hbc⟩, ⟨c, hc, hcc⟩⟩
        have hab : a = b := hf.1 (hac.trans hbc.symm)
        have hac' : a = c := hf.1 (hac.trans hcc.symm)
        exact hac.symm.trans (congrArg f (hxu a ⟨ha, hab ▸ hb, hac' ▸ hc⟩))
    · rintro ⟨y, hy, hyu⟩
      obtain ⟨x, rfl⟩ := hf.2 y
      refine ⟨x, ?_, ?_⟩
      · rcases hy with ⟨⟨a, ha, haa⟩, ⟨b, hb, hba⟩, ⟨c, hc, hca⟩⟩
        have hax : a = x := hf.1 (haa.trans rfl.symm)
        have hbx : b = x := hf.1 (hba.trans rfl.symm)
        have hcx : c = x := hf.1 (hca.trans rfl.symm)
        exact ⟨hax ▸ ha, hbx ▸ hb, hcx ▸ hc⟩
      · intro z hz
        apply hf.1
        exact hyu (f z) ⟨⟨z, hz.1, rfl⟩, ⟨z, hz.2.1, rfl⟩, ⟨z, hz.2.2, rfl⟩⟩
  intro T U V u
  have translate_bijective : Function.Bijective (GaussianTranslation u) := by
    constructor
    · intro a b h
      dsimp [GaussianTranslation] at h ⊢
      exact add_right_cancel h
    · intro a
      refine ⟨a - u, ?_⟩
      dsimp [GaussianTranslation]
      exact sub_add_cancel a u
  have quarter_bijective : Function.Bijective GaussianQuarterTurn := by
    constructor
    · intro a b h
      dsimp [GaussianQuarterTurn] at h ⊢
      cases a
      cases b
      simp_all
    · intro a
      refine ⟨⟨a.im, -a.re⟩, ?_⟩
      dsimp [GaussianQuarterTurn]
      ext <;> simp
  have reflection_bijective : Function.Bijective GaussianReflection := by
    constructor
    · intro a b h
      dsimp [GaussianReflection] at h ⊢
      cases a
      cases b
      simp_all
    · intro a
      refine ⟨⟨a.re, -a.im⟩, ?_⟩
      dsimp [GaussianReflection]
      ext <;> simp
  have translate_sets (W : ProtoTile) :
      BoundaryFootprintVertices (TileTranslation W u) =
        GaussianTranslation u '' BoundaryFootprintVertices W :=
    (TileTranslationFormulas W u).2.2.2.2.2.2.2.1
  have quarter_sets (W : ProtoTile) :
      BoundaryFootprintVertices (TileQuarterTurn W) =
        GaussianQuarterTurn '' BoundaryFootprintVertices W :=
    (TileQuarterTurnFormulas W).2.2.2.2.2.2.2.1
  have reflection_sets (W : ProtoTile) :
      BoundaryFootprintVertices (TileReflection W) =
        GaussianReflection '' BoundaryFootprintVertices W :=
    (TileReflectionFormulas W).2.2.2.2.2.2.2.1
  have translate_result :
      TouchingTriple T U V ↔
        TouchingTriple (TileTranslation T u) (TileTranslation U u)
          (TileTranslation V u) := by
    rcases TileTouchingCovariance T U u with ⟨t₁, q₁, r₁⟩
    rcases TileTouchingCovariance U V u with ⟨t₂, q₂, r₂⟩
    rcases TileTouchingCovariance V T u with ⟨t₃, q₃, r₃⟩
    unfold TouchingTriple
    rw [translate_sets, translate_sets, translate_sets]
    constructor
    · rintro ⟨h₁, h₂, h₃, huniq⟩
      exact ⟨t₁.mp h₁, t₂.mp h₂, t₃.mp h₃,
        (image_unique _ _ _ _ translate_bijective).mp huniq⟩
    · rintro ⟨h₁, h₂, h₃, huniq⟩
      exact ⟨t₁.mpr h₁, t₂.mpr h₂, t₃.mpr h₃,
        (image_unique _ _ _ _ translate_bijective).mpr huniq⟩
  have quarter_result :
      TouchingTriple T U V ↔
        TouchingTriple (TileQuarterTurn T) (TileQuarterTurn U)
          (TileQuarterTurn V) := by
    rcases TileTouchingCovariance T U u with ⟨t₁, q₁, r₁⟩
    rcases TileTouchingCovariance U V u with ⟨t₂, q₂, r₂⟩
    rcases TileTouchingCovariance V T u with ⟨t₃, q₃, r₃⟩
    unfold TouchingTriple
    rw [quarter_sets, quarter_sets, quarter_sets]
    constructor
    · rintro ⟨h₁, h₂, h₃, huniq⟩
      exact ⟨q₁.mp h₁, q₂.mp h₂, q₃.mp h₃,
        (image_unique _ _ _ _ quarter_bijective).mp huniq⟩
    · rintro ⟨h₁, h₂, h₃, huniq⟩
      exact ⟨q₁.mpr h₁, q₂.mpr h₂, q₃.mpr h₃,
        (image_unique _ _ _ _ quarter_bijective).mpr huniq⟩
  have reflection_result :
      TouchingTriple T U V ↔
        TouchingTriple (TileReflection T) (TileReflection U)
          (TileReflection V) := by
    rcases TileTouchingCovariance T U u with ⟨t₁, q₁, r₁⟩
    rcases TileTouchingCovariance U V u with ⟨t₂, q₂, r₂⟩
    rcases TileTouchingCovariance V T u with ⟨t₃, q₃, r₃⟩
    unfold TouchingTriple
    rw [reflection_sets, reflection_sets, reflection_sets]
    constructor
    · rintro ⟨h₁, h₂, h₃, huniq⟩
      exact ⟨r₁.mp h₁, r₂.mp h₂, r₃.mp h₃,
        (image_unique _ _ _ _ reflection_bijective).mp huniq⟩
    · rintro ⟨h₁, h₂, h₃, huniq⟩
      exact ⟨r₁.mpr h₁, r₂.mpr h₂, r₃.mpr h₃,
        (image_unique _ _ _ _ reflection_bijective).mpr huniq⟩
  exact ⟨translate_result, quarter_result, reflection_result⟩

end ApollonianSuperharmonic

end

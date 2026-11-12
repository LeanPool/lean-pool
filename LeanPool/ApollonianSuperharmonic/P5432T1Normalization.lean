/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5432T1Interior
public import LeanPool.ApollonianSuperharmonic.DiamondTileOdometerRestriction
public import LeanPool.ApollonianSuperharmonic.TileOdometerTranslationUniqueness
public import LeanPool.ApollonianSuperharmonic.GlobalOdometerExtends
public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacian

-- [TABLET NODE: P5432T1Normalization]

/-!
# P5432T1Normalization

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5432T1Normalization (K : DiamondParameter)
    (T : ProtoTile) (h : PartialOdometer) (g : IntegerLatticeFunction)
    (hodo : TileOdometer ((DiamondRecursiveQuadruple K) 0) T h)
    (hdom : (h.domain : Set GaussianInt) = FootprintVertices T)
    (hext : GlobalOdometerExtends g h) :
    ∃ u : GaussianInt,
      (∀ x, (x ∈ h.domain ∧ x ∉ BoundaryFootprintVertices T) ↔
        x - u ∈ DiamondVertexDomains K true) ∧
      (∀ x, x - u ∈ DiamondVertexDomains K true →
        FourNeighborLaplacian g x =
          FourNeighborLaplacian (DiamondOdometer K) (x - u)) := by
-- BODY
  classical
  obtain ⟨hK, hKodo, hKdom, _, _, hKval, _⟩ := DiamondTileOdometerRestriction K
  have hpos : 0 < ((DiamondRecursiveQuadruple K) 0).1 := by
    change 0 < ((2 * K.1 * (K.1 + 1) : Nat) : Int)
    have hk := K.2
    positivity
  obtain ⟨u, ⟨hcells, hanchor, a, b, hshift, hval⟩, _⟩ :=
    TileOdometerTranslationUniqueness _ T (DiamondTile K.1) h hK
      hpos hodo hKodo
  obtain ⟨c, hc⟩ := hext
  have obs := ProtoTileObservableExtensionality T
    (TileTranslation (DiamondTile K.1) u) hcells hanchor
  obtain ⟨_, _, _, _, _, hfoot, _, hboundary, _⟩ :=
    TileTranslationFormulas (DiamondTile K.1) u
  have image (S : Set GaussianInt) (x : GaussianInt) :
      x ∈ GaussianTranslation u '' S ↔ x-u ∈ S := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [GaussianTranslation] using hy
    · intro hx
      exact ⟨x-u, hx, by simp [GaussianTranslation]⟩
  have interior (x : GaussianInt) :
      (x ∈ h.domain ∧ x ∉ BoundaryFootprintVertices T) ↔
        x-u ∈ DiamondVertexDomains K true := by
    have hm : x ∈ h.domain ↔ x ∈ FootprintVertices T := by
      change x ∈ (h.domain : Set GaussianInt) ↔ _
      rw [hdom]
    rw [hm, obs.1, obs.2.1, hfoot, hboundary, image, image]
    exact (P5432T1Interior K).1 (x-u)
  refine ⟨u, interior, ?_⟩
  intro x hx
  have eval (d : GaussianInt)
      (hd : d ∈ ({0, 1, -1, ⟨0, 1⟩, -⟨0, 1⟩} : Finset GaussianInt)) :
      g (x+d) = DiamondOdometer K (x-u+d) +
        a.re * (x+d).re + a.im * (x+d).im + b + c := by
    have hz : x-u+d ∈ hK.domain := by
      change x-u+d ∈ (hK.domain : Set GaussianInt)
      rw [hKdom]
      exact (P5432T1Interior K).2 (x-u) hx d hd
    have he : x+d-u = x-u+d := by abel
    have hy : x+d ∈ h.domain := (hshift _).mpr (he.symm ▸ hz)
    rw [hc _ hy, hval _ hy, he, hKval _ hz]
  have e0 : g x = DiamondOdometer K (x-u) +
      a.re * x.re + a.im * x.im + b + c := by
    simpa using eval 0 (by simp)
  simp only [FourNeighborLaplacian, sub_eq_add_neg]
  rw [eval 1 (by simp), eval (-1) (by simp),
    eval ⟨0, 1⟩ (by simp), eval (-⟨0, 1⟩) (by simp), e0]
  simp only [sub_eq_add_neg, Zsqrtd.re_add, Zsqrtd.im_add,
    Zsqrtd.re_neg, Zsqrtd.im_neg]
  norm_num
  ring

end ApollonianSuperharmonic

end

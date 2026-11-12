/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTilingTransport
public import LeanPool.ApollonianSuperharmonic.P4055T1PackingGridEquivalence
public import LeanPool.ApollonianSuperharmonic.P4055T1ExactTripleImage

-- [TABLET NODE: ExactTileInterfaceTriplePackingSymmetryCovariance]

/-!
# ExactTileInterfaceTriplePackingSymmetryCovariance

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem ExactTileInterfaceTriplePackingSymmetryCovariance
    (g : BandPackingSymmetry) (A B C : ProtoTile) :
    Nonempty (ExactTileInterfaceTriple A B C) ↔
      Nonempty (ExactTileInterfaceTriple
        (BandPackingSymmetryTileAction g A)
        (BandPackingSymmetryTileAction g B)
        (BandPackingSymmetryTileAction g C)) := by
-- BODY
  obtain ⟨f, hf, hs, hi⟩ := P4055T1PackingGridEquivalence g
  have hfun : (f : GaussianInt → GaussianInt) = BandPackingSymmetryVectorAction g :=
    funext hf
  have hv (T : ProtoTile) :
      FootprintVertices (BandPackingSymmetryTileAction g T) = f '' FootprintVertices T := by
    simpa only [hfun] using (BandPackingSymmetryTilingTransport g).2.2.2.2.2.2.2.1 T
  have he (T : ProtoTile) :
      FootprintEdges (BandPackingSymmetryTileAction g T) =
        (fun e : Finset GaussianInt => e.image f) '' FootprintEdges T := by
    simpa only [hfun] using (BandPackingSymmetryTilingTransport g).2.2.2.2.2.2.2.2.1 T
  have hiv (T : ProtoTile) :
      FootprintVertices T = f.symm '' FootprintVertices (BandPackingSymmetryTileAction g T) := by
    rw [hv]
    simp [Set.image_image]
  have hie (T : ProtoTile) :
      FootprintEdges T = (fun e : Finset GaussianInt => e.image f.symm) ''
        FootprintEdges (BandPackingSymmetryTileAction g T) := by
    rw [he]
    simp [Set.image_image, Finset.image_image]
  constructor
  · rintro ⟨d⟩
    obtain ⟨d', _⟩ := P4055T1ExactTripleImage f f.injective hs
      A B C _ _ _ (hv A) (hv B) (hv C) (he A) (he B) (he C) d
    exact ⟨d'⟩
  · rintro ⟨d⟩
    obtain ⟨d', _⟩ := P4055T1ExactTripleImage f.symm f.symm.injective hi
      _ _ _ A B C (hiv A) (hiv B) (hiv C) (hie A) (hie B) (hie C) d
    exact ⟨d'⟩

end ApollonianSuperharmonic

end

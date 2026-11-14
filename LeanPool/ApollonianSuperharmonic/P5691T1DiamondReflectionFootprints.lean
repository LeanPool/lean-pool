/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4194T1DiamondCellRows
public import LeanPool.ApollonianSuperharmonic.DiamondTile
public import LeanPool.ApollonianSuperharmonic.TileReflectionFormulas
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: P5691T1DiamondReflectionFootprints]

/-!
# P5691T1DiamondReflectionFootprints

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace DiamondReflectionFootprintConstruction

private noncomputable abbrev J (k : Nat) : GaussianInt → GaussianInt := by
  classical
  exact fun z =>
    GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)

private theorem diamondCellsNonempty (m : Nat) (hm : 0 < m) :
      (DiamondTile m).cells.Nonempty := by
  classical
  refine ⟨0, (P4194T1DiamondCellRows m 0).1.mpr ?_⟩
  norm_num
  omega

private theorem sameCellObs (T T' : ProtoTile) (hc : T.cells = T'.cells)
      (hne : T.cells.Nonempty) :
      FootprintVertices T = FootprintVertices T' ∧
        FootprintEdges T = FootprintEdges T' := by
  classical
  cases T with
  | mk tc ta =>
    cases T' with
    | mk uc ua =>
      dsimp only at hc
      subst uc
      simp [FootprintVertices, FootprintEdges, hne]

private theorem centeredCellEq (m : Nat) :
      (TileTranslation (TileReflection (DiamondTile m))
        ⟨0, 2 * (m : Int)⟩).cells = (DiamondTile m).cells := by
  classical
  let rho : GaussianInt → GaussianInt := fun z =>
    ⟨z.re, 2 * (m : Int) - 1 - z.im⟩
  have hrho (z : GaussianInt) : rho (rho z) = z := by
    apply Zsqrtd.ext <;> simp [rho]
  have hrhoMem (z : GaussianInt) (hz : z ∈ DiamondCellDomain m) :
      rho z ∈ DiamondCellDomain m := by
    apply (P4194T1DiamondCellRows m (rho z)).1.mpr
    have h := (P4194T1DiamondCellRows m z).1.mp hz
    dsimp [rho]
    omega
  change ((DiamondCellDomain m).image
      (fun w => GaussianReflection w - ⟨0, 1⟩)).image
        (GaussianTranslation ⟨0, 2 * (m : Int)⟩) = DiamondCellDomain m
  rw [Finset.image_image]
  ext z
  have hmap (w : GaussianInt) :
      GaussianTranslation ⟨0, 2 * (m : Int)⟩
          (GaussianReflection w - ⟨0, 1⟩) = rho w := by
    apply Zsqrtd.ext <;> simp [rho, GaussianTranslation, GaussianReflection]
    omega
  rw [show (GaussianTranslation ⟨0, 2 * (m : Int)⟩ ∘
      (fun w => GaussianReflection w - ⟨0, 1⟩)) = rho from funext hmap]
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hrhoMem w hw
  · intro hz
    exact ⟨rho z, hrhoMem z hz, hrho z⟩

private theorem centeredVertices (m : Nat) (hm : 0 < m) :
      GaussianTranslation ⟨0, 2 * (m : Int)⟩ ''
        FootprintVertices (TileReflection (DiamondTile m)) =
          FootprintVertices (DiamondTile m) := by
  classical
  have diamondCellsNonempty (m : Nat) (hm : 0 < m) :
      (DiamondTile m).cells.Nonempty := diamondCellsNonempty m hm
  have sameCellObs (T T' : ProtoTile) (hc : T.cells = T'.cells)
      (hne : T.cells.Nonempty) :
      FootprintVertices T = FootprintVertices T' ∧
        FootprintEdges T = FootprintEdges T' := sameCellObs T T' hc hne
  have centeredCellEq (m : Nat) :
      (TileTranslation (TileReflection (DiamondTile m))
        ⟨0, 2 * (m : Int)⟩).cells = (DiamondTile m).cells := centeredCellEq m
  have hobs := sameCellObs
    (TileTranslation (TileReflection (DiamondTile m)) ⟨0, 2 * (m : Int)⟩)
    (DiamondTile m) (centeredCellEq m) (by
      rw [centeredCellEq]
      exact diamondCellsNonempty m hm)
  have hformula :=
    (TileTranslationFormulas (TileReflection (DiamondTile m))
      ⟨0, 2 * (m : Int)⟩).2.2.2.2.2.1
  exact hformula.symm.trans hobs.1

private theorem centeredEdges (m : Nat) (hm : 0 < m) :
      (fun e : Finset GaussianInt =>
        e.image (GaussianTranslation ⟨0, 2 * (m : Int)⟩)) ''
        FootprintEdges (TileReflection (DiamondTile m)) =
          FootprintEdges (DiamondTile m) := by
  classical
  have diamondCellsNonempty (m : Nat) (hm : 0 < m) :
      (DiamondTile m).cells.Nonempty := diamondCellsNonempty m hm
  have sameCellObs (T T' : ProtoTile) (hc : T.cells = T'.cells)
      (hne : T.cells.Nonempty) :
      FootprintVertices T = FootprintVertices T' ∧
        FootprintEdges T = FootprintEdges T' := sameCellObs T T' hc hne
  have centeredCellEq (m : Nat) :
      (TileTranslation (TileReflection (DiamondTile m))
        ⟨0, 2 * (m : Int)⟩).cells = (DiamondTile m).cells := centeredCellEq m
  have hobs := sameCellObs
    (TileTranslation (TileReflection (DiamondTile m)) ⟨0, 2 * (m : Int)⟩)
    (DiamondTile m) (centeredCellEq m) (by
      rw [centeredCellEq]
      exact diamondCellsNonempty m hm)
  have hformula :=
    (TileTranslationFormulas (TileReflection (DiamondTile m))
      ⟨0, 2 * (m : Int)⟩).2.2.2.2.2.2.1
  exact hformula.symm.trans hobs.2

private theorem rhoVertexImage (m : Nat) (hm : 0 < m) :
      (fun z => GaussianTranslation ⟨0, 2 * (m : Int)⟩
        (GaussianReflection z)) ''
        FootprintVertices (DiamondTile m) = FootprintVertices (DiamondTile m) := by
  classical
  have centeredVertices (m : Nat) (hm : 0 < m) :
      GaussianTranslation ⟨0, 2 * (m : Int)⟩ ''
        FootprintVertices (TileReflection (DiamondTile m)) =
          FootprintVertices (DiamondTile m) := centeredVertices m hm
  have h := centeredVertices m hm
  have href := TileReflectionFormulas (DiamondTile m)
  rw [href.2.2.2.2.2.1] at h
  rw [Set.image_image] at h
  exact h

private theorem rhoEdgeImage (m : Nat) (hm : 0 < m) :
      (fun e : Finset GaussianInt =>
        e.image (fun z => GaussianTranslation ⟨0, 2 * (m : Int)⟩
          (GaussianReflection z))) ''
        FootprintEdges (DiamondTile m) = FootprintEdges (DiamondTile m) := by
  classical
  have centeredEdges (m : Nat) (hm : 0 < m) :
      (fun e : Finset GaussianInt =>
        e.image (GaussianTranslation ⟨0, 2 * (m : Int)⟩)) ''
        FootprintEdges (TileReflection (DiamondTile m)) =
          FootprintEdges (DiamondTile m) := centeredEdges m hm
  have h := centeredEdges m hm
  have href := TileReflectionFormulas (DiamondTile m)
  rw [href.2.2.2.2.2.2.1] at h
  rw [Set.image_image] at h
  change (fun e : Finset GaussianInt =>
    (e.image GaussianReflection).image
      (GaussianTranslation ⟨0, 2 * (m : Int)⟩)) ''
      FootprintEdges (DiamondTile m) = _ at h
  have hfun (e : Finset GaussianInt) :
      (e.image GaussianReflection).image
          (GaussianTranslation ⟨0, 2 * (m : Int)⟩) =
        e.image (fun z => GaussianTranslation ⟨0, 2 * (m : Int)⟩
          (GaussianReflection z)) := by
    rw [Finset.image_image]
    rfl
  rw [show (fun e : Finset GaussianInt =>
      (e.image GaussianReflection).image
        (GaussianTranslation ⟨0, 2 * (m : Int)⟩)) =
      (fun e => e.image (fun z => GaussianTranslation ⟨0, 2 * (m : Int)⟩
        (GaussianReflection z))) from funext hfun] at h
  exact h

private theorem JtranslatedVertices (k : Nat) (m : Nat) (hm : 0 < m)
      (s t : GaussianInt) (hst : t = ⟨s.re, 2 * (k : Int) -
        2 * (m : Int) - s.im⟩) :
      (J k) '' FootprintVertices (TileTranslation (DiamondTile m) s) =
        FootprintVertices (TileTranslation (DiamondTile m) t) := by
  classical
  let J : GaussianInt → GaussianInt := fun z =>
    GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
  have rhoVertexImage (m : Nat) (hm : 0 < m) :
      (fun z => GaussianTranslation ⟨0, 2 * (m : Int)⟩
        (GaussianReflection z)) ''
        FootprintVertices (DiamondTile m) = FootprintVertices (DiamondTile m) := rhoVertexImage m hm
  change (J '' FootprintVertices (TileTranslation (DiamondTile m) s) =
        FootprintVertices (TileTranslation (DiamondTile m) t))
  have hs := (TileTranslationFormulas (DiamondTile m) s).2.2.2.2.2.1
  have ht := (TileTranslationFormulas (DiamondTile m) t).2.2.2.2.2.1
  have hfun : J ∘ GaussianTranslation s =
      (fun z => GaussianTranslation t
        (GaussianTranslation ⟨0, 2 * (m : Int)⟩ (GaussianReflection z))) := by
    funext z
    apply Zsqrtd.ext
    · have hre : t.re = s.re := by simpa using congrArg Zsqrtd.re hst
      simp [J, GaussianTranslation, GaussianReflection]
      omega
    · have him : t.im = 2 * (k : Int) - 2 * (m : Int) - s.im := by
        simpa using congrArg Zsqrtd.im hst
      simp [J, GaussianTranslation, GaussianReflection]
      omega
  calc
    J '' FootprintVertices (TileTranslation (DiamondTile m) s) =
        (fun x => J (GaussianTranslation s x)) '' FootprintVertices (DiamondTile m) := by
          rw [hs, Set.image_image]
    _ =
        (J ∘ GaussianTranslation s) '' FootprintVertices (DiamondTile m) := by
          rfl
    _ = (fun z => GaussianTranslation t
        (GaussianTranslation ⟨0, 2 * (m : Int)⟩ (GaussianReflection z))) ''
          FootprintVertices (DiamondTile m) := by rw [hfun]
    _ = GaussianTranslation t '' FootprintVertices (DiamondTile m) := by
      rw [← Set.image_image, rhoVertexImage m hm]
    _ = _ := ht.symm

private theorem JtranslatedEdges (k : Nat) (m : Nat) (hm : 0 < m)
      (s t : GaussianInt) (hst : t = ⟨s.re, 2 * (k : Int) -
        2 * (m : Int) - s.im⟩) :
      (fun e : Finset GaussianInt => e.image (J k)) ''
          FootprintEdges (TileTranslation (DiamondTile m) s) =
        FootprintEdges (TileTranslation (DiamondTile m) t) := by
  classical
  let J : GaussianInt → GaussianInt := fun z =>
    GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
  have rhoEdgeImage (m : Nat) (hm : 0 < m) :
      (fun e : Finset GaussianInt =>
        e.image (fun z => GaussianTranslation ⟨0, 2 * (m : Int)⟩
          (GaussianReflection z))) ''
        FootprintEdges (DiamondTile m) = FootprintEdges (DiamondTile m) := rhoEdgeImage m hm
  change ((fun e : Finset GaussianInt => e.image J) ''
          FootprintEdges (TileTranslation (DiamondTile m) s) =
        FootprintEdges (TileTranslation (DiamondTile m) t))
  have hs := (TileTranslationFormulas (DiamondTile m) s).2.2.2.2.2.2.1
  have ht := (TileTranslationFormulas (DiamondTile m) t).2.2.2.2.2.2.1
  have hpoint (z : GaussianInt) :
      J (GaussianTranslation s z) =
        GaussianTranslation t
          (GaussianTranslation ⟨0, 2 * (m : Int)⟩ (GaussianReflection z)) := by
    apply Zsqrtd.ext
    · have hre : t.re = s.re := by simpa using congrArg Zsqrtd.re hst
      simp [J, GaussianTranslation, GaussianReflection]
      omega
    · have him : t.im = 2 * (k : Int) - 2 * (m : Int) - s.im := by
        simpa using congrArg Zsqrtd.im hst
      simp [J, GaussianTranslation, GaussianReflection]
      omega
  have hfun (e : Finset GaussianInt) :
      (e.image (GaussianTranslation s)).image J =
        (e.image (fun z => GaussianTranslation ⟨0, 2 * (m : Int)⟩
          (GaussianReflection z))).image (GaussianTranslation t) := by
    rw [Finset.image_image, Finset.image_image]
    congr 1
    funext z
    exact hpoint z
  calc
    (fun e : Finset GaussianInt => e.image J) ''
        FootprintEdges (TileTranslation (DiamondTile m) s) =
        ((fun e : Finset GaussianInt => e.image J) ∘
          (fun e : Finset GaussianInt => e.image (GaussianTranslation s))) ''
            FootprintEdges (DiamondTile m) := by
      rw [hs]
      exact Set.image_image _ _ _
    _ = ((fun e : Finset GaussianInt => e.image (GaussianTranslation t)) ∘
          (fun e : Finset GaussianInt => e.image
            (fun z => GaussianTranslation ⟨0, 2 * (m : Int)⟩
              (GaussianReflection z)))) '' FootprintEdges (DiamondTile m) := by
      congr 1
      funext e
      exact hfun e
    _ = (fun e : Finset GaussianInt => e.image (GaussianTranslation t)) ''
          FootprintEdges (DiamondTile m) := by
      exact (Set.image_image
        (fun e : Finset GaussianInt => e.image (GaussianTranslation t))
        (fun e : Finset GaussianInt => e.image
          (fun z => GaussianTranslation ⟨0, 2 * (m : Int)⟩
            (GaussianReflection z)))
        (FootprintEdges (DiamondTile m))).symm.trans
        (congrArg (fun S : Set (Finset GaussianInt) =>
          (fun e : Finset GaussianInt => e.image (GaussianTranslation t)) '' S)
          (rhoEdgeImage m hm))
    _ = _ := ht.symm

end DiamondReflectionFootprintConstruction

theorem P5691T1DiamondReflectionFootprints
    (k m : Nat) (hm : 0 < m) (s t : GaussianInt)
    (hst : t = ⟨s.re, 2 * (k : Int) - 2 * (m : Int) - s.im⟩) :
    (fun z => GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)) ''
        FootprintVertices (TileTranslation (DiamondTile m) s) =
      FootprintVertices (TileTranslation (DiamondTile m) t) ∧
    (fun e : Finset GaussianInt => e.image (fun z =>
        GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z))) ''
        FootprintEdges (TileTranslation (DiamondTile m) s) =
      FootprintEdges (TileTranslation (DiamondTile m) t) := by
-- BODY
  classical
  let J : GaussianInt → GaussianInt := fun z =>
    GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
  have JtranslatedVertices (m : Nat) (hm : 0 < m)
      (s t : GaussianInt) (hst : t = ⟨s.re, 2 * (k : Int) -
        2 * (m : Int) - s.im⟩) :
      J '' FootprintVertices (TileTranslation (DiamondTile m) s) =
        FootprintVertices (TileTranslation (DiamondTile m) t) :=
            DiamondReflectionFootprintConstruction.JtranslatedVertices k m hm s t hst
  have JtranslatedEdges (m : Nat) (hm : 0 < m)
      (s t : GaussianInt) (hst : t = ⟨s.re, 2 * (k : Int) -
        2 * (m : Int) - s.im⟩) :
      (fun e : Finset GaussianInt => e.image J) ''
          FootprintEdges (TileTranslation (DiamondTile m) s) =
        FootprintEdges (TileTranslation (DiamondTile m) t) :=
            DiamondReflectionFootprintConstruction.JtranslatedEdges k m hm s t hst
  exact ⟨JtranslatedVertices m hm s t hst, JtranslatedEdges m hm s t hst⟩

end ApollonianSuperharmonic

end

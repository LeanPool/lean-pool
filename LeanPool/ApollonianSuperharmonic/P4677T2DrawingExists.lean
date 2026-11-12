/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4677T2DrawingData
public import LeanPool.ApollonianSuperharmonic.P4715T1LatticeCoordinates
public import LeanPool.ApollonianSuperharmonic.P4715T1PlaneMap
public import LeanPool.ApollonianSuperharmonic.P4715T1CoefficientEdges
public import LeanPool.ApollonianSuperharmonic.P4715T1CoefficientFaces
public import LeanPool.ApollonianSuperharmonic.P4715T1CoefficientTranslation
public import LeanPool.ApollonianSuperharmonic.P4715T1OrbitRepresentatives

-- [TABLET NODE: P4677T2DrawingExists]

/-!
# P4677T2DrawingExists

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4677T2DrawingExists (u v : GaussianInt)
    (L : AddSubgroup GaussianInt) (hu : u ∈ L) (hv : v ∈ L)
    (hcoords : ∀ w : L, ∃! mn : Int × Int,
      ((mn.1 : GaussianInt) * u + (mn.2 : GaussianInt) * v) =
        (w : GaussianInt)) :
    Nonempty (P4677T2DrawingData u v L) := by
-- BODY
  classical
  obtain ⟨hinj, c, hc, hcsurj⟩ := P4715T1LatticeCoordinates u v L hu hv hcoords
  obtain ⟨hdet, E, hE⟩ := P4715T1PlaneMap u v hinj
  obtain ⟨hsymm, hinterval, hinter⟩ := P4715T1CoefficientEdges
  obtain ⟨hopen, hconnected, hdisjoint, hboundary, hcover⟩ := P4715T1CoefficientFaces
  obtain ⟨hvzero, hvadd, hfzero, hfadd, hadj, hvertices⟩ := P4715T1IndexAction
  obtain ⟨vr, er, fr, hvr, her, hfr, hvo, heo, hfo⟩ := P4715T1OrbitRepresentatives
  have Eint (k : Int × Int) :
      E ((k.1 : Real), (k.2 : Real)) =
        GaussianRealPoint ((k.1 : GaussianInt) * u + (k.2 : GaussianInt) * v) := by
    rw [hE]
    ext <;> simp [GaussianRealPoint]
  have Ec (w : L) : E (((c w).1 : Real), ((c w).2 : Real)) = GaussianRealPoint w := by
    rw [Eint, hc]
  refine ⟨{
    position := fun a => E (P4715T1Position a)
    edgeArc := fun a b => E '' P4715T1Arc a b
    faceRegion := fun f => E '' P4715T1Region f
    position_injective := E.injective.comp P4715T1PositionInjective
    arc_symmetric := fun a b => congrArg (fun s => E '' s) (hsymm a b)
    arc_homeomorph := ?_
    arc_intersections := ?_
    region_open := fun f => E.toHomeomorph.isOpen_image.mpr (hopen f)
    region_connected := fun f => (hconnected f).image E E.continuous.continuousOn
    region_disjoint := fun f g hfg =>
      Set.disjoint_image_of_injective E.injective (hdisjoint hfg)
    face_boundary := ?_
    plane_cover := ?_
    coordinates := c
    coordinates_spec := hc
    shift := fun w => P4715T1VertexShift (c w)
    faceShift := fun w => P4715T1FaceShift (c w)
    shift_eq := fun _ _ => rfl
    faceShift_eq := fun _ _ => rfl
    shift_zero := ?_
    shift_add := ?_
    faceShift_zero := ?_
    faceShift_add := ?_
    edge_periodic := fun w => hadj (c w)
    face_vertices_periodic := fun w => hvertices (c w)
    position_periodic := ?_
    edgeArc_periodic := ?_
    faceRegion_periodic := ?_
    vertexReps := vr
    edgeReps := er
    faceReps := fr
    vertex_reps := hvr
    edge_reps_allowed := her
    face_reps := hfr
    vertex_orbits := ?_
    edge_orbits := ?_
    face_orbits := ?_ }⟩
  · intro a b hab
    obtain ⟨h, h0, h1⟩ := hinterval a b hab
    refine ⟨h.trans (E.toHomeomorph.image (P4715T1Arc a b)), ?_, ?_⟩
    · change E (h ⟨0, by norm_num⟩ : Real × Real) = E (P4715T1Position a)
      rw [h0]
    · change E (h ⟨1, by norm_num⟩ : Real × Real) = E (P4715T1Position b)
      rw [h1]
  · intro a b d e hab hde hne
    rw [← Set.image_inter E.injective, hinter a b d e hab hde hne, Set.image_image]
  · intro f
    calc
      frontier (E '' P4715T1Region f) = E '' frontier (P4715T1Region f) :=
        (E.toHomeomorph.image_frontier _).symm
      _ = _ := by rw [hboundary f, Set.image_union, Set.image_union]
  · apply Set.eq_univ_of_forall
    intro p
    obtain ⟨y, rfl⟩ := E.surjective p
    have hy : y ∈ Set.range P4715T1Position ∪
        {p | ∃ a b, AllowedSubtileIncidence a b ∧ p ∈ P4715T1Arc a b} ∪
        {p | ∃ f, p ∈ P4715T1Region f} := by rw [hcover]; trivial
    rcases hy with (⟨a, rfl⟩ | ⟨a, b, hab, hy⟩) | ⟨f, hy⟩
    · exact Or.inl (Or.inl ⟨a, rfl⟩)
    · exact Or.inl (Or.inr ⟨a, b, hab, Set.mem_image_of_mem E hy⟩)
    · exact Or.inr ⟨f, Set.mem_image_of_mem E hy⟩
  · intro a
    simpa only [map_zero] using hvzero a
  · intro w z a
    simpa only [map_add] using hvadd (c w) (c z) a
  · intro f
    simpa only [map_zero] using hfzero f
  · intro w z f
    simpa only [map_add] using hfadd (c w) (c z) f
  · intro w a
    rw [(P4715T1CoefficientTranslation (c w)).1 a, map_add, Ec]
  · intro w a b
    rw [(P4715T1CoefficientTranslation (c w)).2.1 a b]
    simp only [Set.image_image]
    congr 1
    funext p
    exact (map_add E p _).trans (congrArg (fun z => E p + z) (Ec w))
  · intro w f
    rw [(P4715T1CoefficientTranslation (c w)).2.2 f]
    simp only [Set.image_image]
    congr 1
    funext p
    exact (map_add E p _).trans (congrArg (fun z => E p + z) (Ec w))
  · intro a
    obtain ⟨r, hr, huniq⟩ := hvo a
    refine ⟨r, ⟨hr.1, ?_⟩, ?_⟩
    · obtain ⟨k, hk⟩ := hr.2
      obtain ⟨w, hw⟩ := hcsurj k
      exact ⟨w, hw.symm ▸ hk⟩
    · intro s hs
      apply huniq s
      obtain ⟨w, hw⟩ := hs.2
      exact ⟨hs.1, c w, hw⟩
  · intro a b hab
    obtain ⟨r, hr, k, ha, hb⟩ := heo a b hab
    obtain ⟨w, hw⟩ := hcsurj k
    exact ⟨r, hr, w, hw.symm ▸ ha, hw.symm ▸ hb⟩
  · intro f
    obtain ⟨r, hr, k, hf⟩ := hfo f
    obtain ⟨w, hw⟩ := hcsurj k
    exact ⟨r, hr, w, hw.symm ▸ hf⟩

end ApollonianSuperharmonic

end

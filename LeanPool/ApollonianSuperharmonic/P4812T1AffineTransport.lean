/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4812T1AffineDrawing

-- [TABLET NODE: P4812T1AffineTransport]

/-!
# P4812T1AffineTransport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4812T1AffineTransport
    (L : AddSubgroup GaussianInt) (k : (Int × Int) ≃+ L)
    (P : PlaneTriangulation (Int × Int))
    (up down : (Int × Int) → P.Face)
    (hadj : ∀ x y, P.adjacent x y ↔ TriangularLatticeAdjacent x y)
    (hu : Function.Injective up) (hd : Function.Injective down)
    (hud : ∀ x y, up x ≠ down y)
    (hall : ∀ f, (∃ x, f = up x) ∨ ∃ x, f = down x)
    (hup : ∀ x, P.faceVertex (up x) 0 = x ∧
      P.faceVertex (up x) 1 = x + (1, 0) ∧
      P.faceVertex (up x) 2 = x - (0, 1))
    (hdown : ∀ x, P.faceVertex (down x) 0 = x ∧
      P.faceVertex (down x) 1 = x - (1, 0) ∧
      P.faceVertex (down x) 2 = x + (0, 1))
    (hpos : ∀ x, P.position x =
      (((x.1 : Real) - (x.2 : Real) / 2), (x.2 : Real)))
    (harc : ∀ z x y, P.edgeArc (z + x) (z + y) =
      (fun p => p + (((z.1 : Real) - (z.2 : Real) / 2), (z.2 : Real))) ''
        P.edgeArc x y)
    (hregions : ∀ z x,
      P.faceRegion (up (z + x)) =
        (fun p => p + (((z.1 : Real) - (z.2 : Real) / 2), (z.2 : Real))) ''
          P.faceRegion (up x) ∧
      P.faceRegion (down (z + x)) =
        (fun p => p + (((z.1 : Real) - (z.2 : Real) / 2), (z.2 : Real))) ''
          P.faceRegion (down x))
    (H : (Real × Real) ≃ₜ (Real × Real))
    (hadd : ∀ p r, H (p + r) = H p + H r)
    (hcoord : ∀ x, H (((x.1 : Real) - (x.2 : Real) / 2), (x.2 : Real)) =
      GaussianRealPoint (k x : GaussianInt)) :
    Nonempty (P4812T1AffineDrawing L k) := by
-- BODY
  classical
  let ev : Sum L L → P.Face := Sum.elim (fun x => up (k.symm x))
    (fun x => down (k.symm x))
  have hev : Function.Bijective ev := by
    constructor
    · intro f g h
      cases f with
      | inl x =>
        cases g with
        | inl y => exact congrArg Sum.inl (k.symm.injective (hu h))
        | inr y => exact (hud _ _ h).elim
      | inr x =>
        cases g with
        | inl y => exact (hud _ _ h.symm).elim
        | inr y => exact congrArg Sum.inr (k.symm.injective (hd h))
    · intro f
      rcases hall f with ⟨x, rfl⟩ | ⟨x, rfl⟩
      · exact ⟨.inl (k x), by simp [ev]⟩
      · exact ⟨.inr (k x), by simp [ev]⟩
  let faces := Equiv.ofBijective ev hev
  let Q : PlaneTriangulation L := {
    adjacent := fun x y => P.adjacent (k.symm x) (k.symm y)
    Face := P.Face
    faceVertex := fun f i => k (P.faceVertex f i)
    position := fun x => H (P.position (k.symm x))
    edgeArc := fun x y => H '' P.edgeArc (k.symm x) (k.symm y)
    faceRegion := fun f => H '' P.faceRegion f
    adjacent_symmetric := fun _ _ => P.adjacent_symmetric _ _
    adjacent_irreflexive := fun _ => P.adjacent_irreflexive _
    locally_finite := by
      intro x
      exact ((P.locally_finite (k.symm x)).image k).subset (by
        intro y hy
        exact ⟨k.symm y, hy, k.apply_symm_apply y⟩)
    three_connected := by
      intro D hD x hx y hy
      let E := D.image k.symm
      have hE : E.card < 3 := (Finset.card_image_le).trans_lt hD
      have hxE : k.symm x ∉ E := by simpa [E] using hx
      have hyE : k.symm y ∉ E := by simpa [E] using hy
      obtain ⟨p, hp, hlast, havoid, hstep⟩ := P.three_connected E hE _ hxE _ hyE
      refine ⟨p.map k, ?_, ?_, ?_, ?_⟩
      · simp [List.head?_map, hp]
      · simp [List.getLast?_map, hlast]
      · intro a ha
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        intro hk
        exact havoid b hb (Finset.mem_image.mpr ⟨k b, hk, k.symm_apply_apply b⟩)
      · have hc : List.IsChain P.adjacent p :=
          List.isChain_iff_forall_rel_of_append_cons_cons.mpr hstep
        have hc' : List.IsChain (fun a b => P.adjacent (k.symm a) (k.symm b))
            (p.map k) := by simpa only [List.isChain_map, k.symm_apply_apply] using hc
        exact List.isChain_iff_forall_rel_of_append_cons_cons.mp hc'
    face_vertices_distinct := fun f => k.injective.comp (P.face_vertices_distinct f)
    face_edges := by
      intro f i j hij
      simpa using P.face_edges f i j hij
    every_edge_two_faces := by
      intro x y hxy
      obtain ⟨f, g, hfg, hf, hg, huniq⟩ := P.every_edge_two_faces _ _ hxy
      have inc (h : P.Face) (z : L) :
          (∃ i, k (P.faceVertex h i) = z) ↔ ∃ i, P.faceVertex h i = k.symm z := by
        constructor
        · rintro ⟨i, hi⟩
          exact ⟨i, k.injective (by simpa using hi)⟩
        · rintro ⟨i, hi⟩
          exact ⟨i, by simpa using congrArg k hi⟩
      refine ⟨f, g, hfg, ?_, ?_, ?_⟩
      · exact ⟨(inc f x).mpr hf.1, (inc f y).mpr hf.2⟩
      · exact ⟨(inc g x).mpr hg.1, (inc g y).mpr hg.2⟩
      · intro h hh
        exact huniq h ⟨(inc h x).mp hh.1, (inc h y).mp hh.2⟩
    position_injective := H.injective.comp (P.position_injective.comp k.symm.injective)
    arc_symmetric := by intro x y; rw [P.arc_symmetric]
    arc_homeomorph := by
      intro x y hxy
      obtain ⟨h, h0, h1⟩ := P.arc_homeomorph _ _ hxy
      refine ⟨h.trans (H.image _), ?_, ?_⟩
      · change H ((h ⟨0, by norm_num⟩ : P.edgeArc _ _) : Real × Real) = _
        rw [h0]
      · change H ((h ⟨1, by norm_num⟩ : P.edgeArc _ _) : Real × Real) = _
        rw [h1]
    arc_intersections := by
      intro a b c d hab hcd hne
      have hne' : ({k.symm a, k.symm b} : Set (Int × Int)) ≠
          {k.symm c, k.symm d} := by
        intro he
        apply hne
        simpa only [Set.image_insert_eq, Set.image_singleton,
          k.apply_symm_apply] using congrArg (fun s : Set (Int × Int) => k '' s) he
      rw [← Set.image_inter H.injective, P.arc_intersections _ _ _ _ hab hcd hne']
      ext p
      simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨z, ⟨w, ⟨hw, hw'⟩, rfl⟩, rfl⟩
        refine ⟨k w, ⟨?_, ?_⟩, by simp⟩
        · rcases hw with rfl | rfl <;> simp
        · rcases hw' with rfl | rfl <;> simp
      · rintro ⟨w, ⟨hw, hw'⟩, rfl⟩
        refine ⟨P.position (k.symm w), ⟨k.symm w, ⟨?_, ?_⟩, rfl⟩, rfl⟩
        · rcases hw with rfl | rfl <;> simp
        · rcases hw' with rfl | rfl <;> simp
    region_open := fun f => H.isOpenMap _ (P.region_open f)
    region_connected := fun f => (P.region_connected f).image H H.continuous.continuousOn
    region_disjoint := by
      intro f g hfg
      exact (P.region_disjoint hfg).image H.injective.injOn
        (Set.subset_univ _) (Set.subset_univ _)
    face_boundary := by
      intro f
      rw [← H.image_frontier, P.face_boundary]
      simp only [Set.image_union, k.symm_apply_apply]
    plane_cover := by
      apply Set.eq_univ_of_forall
      intro p
      have hp : H.symm p ∈ Set.range P.position ∪
          {p | ∃ a b, P.adjacent a b ∧ p ∈ P.edgeArc a b} ∪
          {p | ∃ f, p ∈ P.faceRegion f} := by rw [P.plane_cover]; trivial
      rcases hp with (⟨x, hx⟩ | ⟨a, b, hab, hp⟩) | ⟨f, hf⟩
      · exact Or.inl (Or.inl ⟨k x, by simp [hx]⟩)
      · exact Or.inl (Or.inr ⟨k a, k b, by simpa using hab,
          ⟨H.symm p, by simpa using hp, H.apply_symm_apply p⟩⟩)
      · exact Or.inr ⟨f, H.symm p, hf, H.apply_symm_apply p⟩ }
  refine ⟨{
    plane := Q
    faces := faces
    adjacent_iff := fun _ _ => hadj _ _
    up_vertices := ?_
    down_vertices := ?_
    position_eq := ?_
    edgeArc_periodic := ?_
    faceRegion_periodic := ?_ }⟩
  · intro x
    change k (P.faceVertex (up (k.symm x)) 0) = x ∧
      k (P.faceVertex (up (k.symm x)) 1) = x + k (1, 0) ∧
      k (P.faceVertex (up (k.symm x)) 2) = x - k (0, 1)
    rw [(hup _).1, (hup _).2.1, (hup _).2.2]
    simp
  · intro x
    change k (P.faceVertex (down (k.symm x)) 0) = x ∧
      k (P.faceVertex (down (k.symm x)) 1) = x - k (1, 0) ∧
      k (P.faceVertex (down (k.symm x)) 2) = x + k (0, 1)
    rw [(hdown _).1, (hdown _).2.1, (hdown _).2.2]
    simp
  · intro x
    change H (P.position (k.symm x)) = _
    rw [hpos, hcoord, k.apply_symm_apply]
  · intro u x y
    change H '' P.edgeArc (k.symm (u + x)) (k.symm (u + y)) =
      (fun p => p + GaussianRealPoint (u : GaussianInt)) ''
        (H '' P.edgeArc (k.symm x) (k.symm y))
    rw [map_add, map_add, harc]
    simp only [Set.image_image]
    congr 1
    funext p
    rw [hadd, hcoord, k.apply_symm_apply]
  · intro u f
    cases f with
    | inl x =>
      change H '' P.faceRegion (up (k.symm (u + x))) =
        (fun p => p + GaussianRealPoint (u : GaussianInt)) ''
          (H '' P.faceRegion (up (k.symm x)))
      rw [map_add, (hregions _ _).1]
      simp only [Set.image_image]
      congr 1
      funext p
      rw [hadd, hcoord, k.apply_symm_apply]
    | inr x =>
      change H '' P.faceRegion (down (k.symm (u + x))) =
        (fun p => p + GaussianRealPoint (u : GaussianInt)) ''
          (H '' P.faceRegion (down (k.symm x)))
      rw [map_add, (hregions _ _).2]
      simp only [Set.image_image]
      congr 1
      funext p
      rw [hadd, hcoord, k.apply_symm_apply]

end ApollonianSuperharmonic

end

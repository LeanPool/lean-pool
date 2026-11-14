/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.PlaneEmbeddingAgreement
public import LeanPool.ApollonianSuperharmonic.P3723T1ContactPortsExist
public import LeanPool.ApollonianSuperharmonic.P3723T1AllContactDrawingExists
public import LeanPool.ApollonianSuperharmonic.P3861T1RoutedFacialDomains
public import LeanPool.ApollonianSuperharmonic.P3861T1RoutedFaceOrientation
public import LeanPool.ApollonianSuperharmonic.P3861T1ExtraArcLocalization

-- [TABLET NODE: PeriodicTileContactRoutingRigidity]

/-!
# PeriodicTileContactRoutingRigidity

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ContactRoutingGeometry

private theorem contact :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ {a : ι}, ∀ {b : ι}, (P.plane.adjacent a b)
            → (P3723T1EdgeContact P a b) ) := by
  classical
  intro ι P a b hab
  exact ⟨fun heq => P.plane.adjacent_irreflexive a (heq ▸ hab),
    P.adjacent_has_common_edge a b hab⟩

private theorem hne :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), (∀
            {a : ι}, ∀ {b : ι}, (P.plane.adjacent a b) → (P3723T1EdgeContact P a b)) → (∀ (a :
            ι), ∀ (b : ι), (P.plane.adjacent a b) → (D.port a b ≠ none)) ) := by
  classical
  intro ι P D contact a b hab hn
  exact (D.port_eq_none_iff a b).mp hn (contact hab)

end ContactRoutingGeometry

private noncomputable def restrictContactDrawing {ι : Type} (P : PeriodicTileComplex ι)
    (ports : P3723T1ContactPorts P) (D : P3723T1AllContactRouting P)
    (retained_position : D.position = ports.position)
    (contact : ∀ {a b : ι}, P.plane.adjacent a b → P3723T1EdgeContact P a b)
    (symmetric : ∀ {a b : ι}, P.plane.adjacent a b → P.plane.adjacent b a) :
    PeriodicTileContactRouting P := by
  classical
  exact {
    position := D.position
    portEdge := fun a b => if P.plane.adjacent a b then D.portEdge a b else ∅
    port := fun a b => if P.plane.adjacent a b then D.port a b else none
    halfArc := fun a b => if P.plane.adjacent a b then D.halfArc a b else ∅
    edgeArc := fun a b => if P.plane.adjacent a b then D.edgeArc a b else ∅
    portEdge_symmetric := by
      intro a b
      by_cases hab : P.plane.adjacent a b
      · simp only [ite_eq_left hab, ite_eq_left (symmetric hab)]
        exact D.portEdge_symmetric a b
      · have hba : ¬ P.plane.adjacent b a := fun h => hab (symmetric h)
        simp only [ite_eq_right hab, ite_eq_right hba]
    port_symmetric := by
      intro a b
      by_cases hab : P.plane.adjacent a b
      · simp only [ite_eq_left hab, ite_eq_left (symmetric hab)]
        exact D.port_symmetric a b
      · have hba : ¬ P.plane.adjacent b a := fun h => hab (symmetric h)
        simp only [ite_eq_right hab, ite_eq_right hba]
    portEdge_common := by
      intro a b hab
      simpa only [ite_eq_left hab] using D.portEdge_common a b (contact hab)
    portEdge_two := by
      intro a b hab
      simpa only [ite_eq_left hab] using D.portEdge_two a b (contact hab)
    port_midpoint := by
      intro a b hab
      simpa only [ite_eq_left hab] using D.port_midpoint a b (contact hab)
    port_eq_none_iff := by
      intro a b
      by_cases hab : P.plane.adjacent a b
      · have hne : D.port a b ≠ none := ContactRoutingGeometry.hne ι P D contact a b hab
        simp only [hne, hab, not_true_eq_false, ite_true]
      · simp only [hab, not_false_eq_true, ite_false, eq_self]
    nonedge_has_no_portEdge := by
      intro a b hab
      simp only [ite_eq_right hab]
    nonedge_has_no_halfArc := by
      intro a b hab
      simp only [ite_eq_right hab]
    nonedge_has_no_edgeArc := by
      intro a b hab
      simp only [ite_eq_right hab]
    position_in_tile_interior := by
      rw [retained_position]
      exact ports.position_in_tile_interior
    position_injective := by
      rw [retained_position]
      exact ports.position_injective
    incident_ports_distinct := by
      intro a b c p q hp hq hbc
      by_cases hab : P.plane.adjacent a b
      · by_cases hac : P.plane.adjacent a c
        · simp only [ite_eq_left hab] at hp
          simp only [ite_eq_left hac] at hq
          exact D.incident_ports_distinct a b c p q hp hq hbc
        · simp only [ite_eq_right hac, reduceCtorEq] at hq
      · simp only [ite_eq_right hab, reduceCtorEq] at hp
    halfArc_homeomorph := by
      intro a b p hp
      by_cases hab : P.plane.adjacent a b
      · simp only [ite_eq_left hab] at hp
        rw [ite_eq_left hab]
        exact D.halfArc_homeomorph a b p hp
      · simp only [ite_eq_right hab, reduceCtorEq] at hp
    halfArc_supported := by
      intro a b p hp
      by_cases hab : P.plane.adjacent a b
      · simp only [ite_eq_left hab] at hp ⊢
        exact D.halfArc_supported a b p hp
      · simp only [ite_eq_right hab, reduceCtorEq] at hp
    incident_halfArc_intersections := by
      intro a b c hab hac hbc
      simpa only [ite_eq_left hab, ite_eq_left hac] using
        D.incident_halfArc_intersections a b c (contact hab) (contact hac) hbc
    edgeArc_symmetric := by
      intro a b
      by_cases hab : P.plane.adjacent a b
      · simp only [ite_eq_left hab, ite_eq_left (symmetric hab)]
        exact D.edgeArc_symmetric a b
      · have hba : ¬ P.plane.adjacent b a := fun h => hab (symmetric h)
        simp only [ite_eq_right hab, ite_eq_right hba]
    edgeArc_from_halfArcs := by
      intro a b p hp
      by_cases hab : P.plane.adjacent a b
      · simp only [ite_eq_left hab] at hp
        simpa only [ite_eq_left hab, ite_eq_left (symmetric hab)] using
          D.edgeArc_from_halfArcs a b p hp
      · simp only [ite_eq_right hab, reduceCtorEq] at hp
    edgeArc_homeomorph := by
      intro a b hab
      rw [ite_eq_left hab]
      exact D.edgeArc_homeomorph a b (contact hab)
    edgeArc_intersections := by
      intro a b c d hab hcd hne
      simpa only [ite_eq_left hab, ite_eq_left hcd] using
        D.edgeArc_intersections a b c d (contact hab) (contact hcd) hne
    compact_local_finiteness := by
      intro K hK
      apply (D.compact_local_finiteness K hK).subset
      rintro ⟨a, b⟩ ⟨hab, hmeet⟩
      exact ⟨contact hab, by simpa only [ite_eq_left hab] using hmeet⟩
    position_periodic := D.position_periodic
    portEdge_periodic := by
      intro u a b
      by_cases hab : P.plane.adjacent a b
      · simpa only [ite_eq_left hab, ite_eq_left ((P.edge_periodic u a b).mpr hab)] using
          D.portEdge_periodic u a b
      · have hn : ¬ P.plane.adjacent (P.shift u a) (P.shift u b) := by
          simpa only [P.edge_periodic] using hab
        simp only [ite_eq_right hab, ite_eq_right hn, Finset.image_empty]
    port_periodic := by
      intro u a b
      by_cases hab : P.plane.adjacent a b
      · simpa only [ite_eq_left hab, ite_eq_left ((P.edge_periodic u a b).mpr hab)] using
          D.port_periodic u a b
      · have hn : ¬ P.plane.adjacent (P.shift u a) (P.shift u b) := by
          simpa only [P.edge_periodic] using hab
        simp only [ite_eq_right hab, ite_eq_right hn, Option.map_none]
    halfArc_periodic := by
      intro u a b
      by_cases hab : P.plane.adjacent a b
      · simpa only [ite_eq_left hab, ite_eq_left ((P.edge_periodic u a b).mpr hab)] using
          D.halfArc_periodic u a b
      · have hn : ¬ P.plane.adjacent (P.shift u a) (P.shift u b) := by
          simpa only [P.edge_periodic] using hab
        simp only [ite_eq_right hab, ite_eq_right hn, Set.image_empty]
    edgeArc_periodic := by
      intro u a b
      by_cases hab : P.plane.adjacent a b
      · simpa only [ite_eq_left hab, ite_eq_left ((P.edge_periodic u a b).mpr hab)] using
          D.edgeArc_periodic u a b
      · have hn : ¬ P.plane.adjacent (P.shift u a) (P.shift u b) := by
          simpa only [P.edge_periodic] using hab
        simp only [ite_eq_right hab, ite_eq_right hn, Set.image_empty]
  }

namespace ContactRoutingGeometry

private theorem traces :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (ports : P3723T1ContactPorts P), ∀ (D :
            P3723T1AllContactRouting P), ∀ (retained_position : D.position = ports.position), ∀
            (contact : ∀ {a : ι}, ∀ {b : ι}, (P.plane.adjacent a b) → (P3723T1EdgeContact P a
            b)), ∀ (symmetric : ∀ {a : ι}, ∀ {b : ι}, (P.plane.adjacent a b) → (P.plane.adjacent
            b a)),
        let R := restrictContactDrawing P ports D retained_position contact symmetric
        (Set.range R.position ∪ {p | ∃ a b, P.plane.adjacent a b ∧ p ∈ R.edgeArc a b}) =
            (Set.range D.position ∪ {p | ∃ a b, P.plane.adjacent a b ∧ p ∈ D.edgeArc a b}) ) := by
  classical
  intro ι P ports D retained_position contact symmetric R
  ext x
  constructor
  · rintro (hx | ⟨a, b, hab, hx⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨a, b, hab, by simpa only [R, restrictContactDrawing, ite_eq_left hab] using hx⟩
  · rintro (hx | ⟨a, b, hab, hx⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨a, b, hab, by simpa only [R, restrictContactDrawing, ite_eq_left hab] using hx⟩

private theorem face_frontier :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (f : P.plane.Face), frontier (F.region f) ⊆ Set.range
            D.position ∪ {p | ∃ a b, P.plane.adjacent a b ∧ p ∈ D.edgeArc a b} ) := by
  classical
  intro ι P D F f
  rw [F.region_frontier]
  rintro x ((hx | hx) | hx)
  · exact Or.inr ⟨_, _, P.plane.face_edges f 0 1 (by decide), hx⟩
  · exact Or.inr ⟨_, _, P.plane.face_edges f 1 2 (by decide), hx⟩
  · exact Or.inr ⟨_, _, P.plane.face_edges f 2 0 (by decide), hx⟩

private theorem edge_frontier :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (f : P.plane.Face), ∀ (a : ι), ∀ (b : ι),
            (P.plane.adjacent a b) → ((∃ i, P.plane.faceVertex f i = a) → ((∃ i,
            P.plane.faceVertex f i = b) → (D.edgeArc a b ⊆ frontier (F.region f)))) ) := by
  classical
  intro ι P D F f a b hab ha hb
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  intro x hx
  rw [F.region_frontier]
  fin_cases i <;> fin_cases j
  · exact (P.plane.adjacent_irreflexive _ hab).elim
  · exact Or.inl (Or.inl hx)
  · rw [D.edgeArc_symmetric] at hx
    exact Or.inr hx
  · rw [D.edgeArc_symmetric] at hx
    exact Or.inl (Or.inl hx)
  · exact (P.plane.adjacent_irreflexive _ hab).elim
  · exact Or.inl (Or.inr hx)
  · exact Or.inr hx
  · rw [D.edgeArc_symmetric] at hx
    exact Or.inl (Or.inr hx)
  · exact (P.plane.adjacent_irreflexive _ hab).elim

private theorem different :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), (∀ {a : ι}, ∀ {b : ι}, (P.plane.adjacent a
            b) → (P.plane.adjacent b a)) → (∀ (a : ι), ∀ (b : ι), (a ≠ b) → ((¬P.plane.adjacent a
            b) → (∀ {c : ι}, ∀ {d : ι}, (P.plane.adjacent c d) → (({a, b} : Set ι) ≠ {c, d})))) )
            := by
  classical
  intro ι P symmetric a b hab hn c d hcd heq
  have hacd : a = c ∨ a = d := by
    have hm : a ∈ ({c, d} : Set ι) := heq ▸ (by simp)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
  have hbcd : b = c ∨ b = d := by
    have hm : b ∈ ({c, d} : Set ι) := heq ▸ (by simp)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
  rcases hacd with hac | had <;> rcases hbcd with hbc | hbd
  · exact hab (hac.trans hbc.symm)
  · exact hn (by simpa only [hac, hbd] using hcd)
  · exact hn (by simpa only [had, hbc] using symmetric hcd)
  · exact hab (had.trans hbd.symm)

private theorem avoid :
    (by
      classical
      exact
        ∀ (ι : Type),
          ∀ (P : PeriodicTileComplex ι),
            ∀ (D : P3723T1AllContactRouting P),
              (∀ {a : ι}, ∀ {b : ι}, P.plane.adjacent a b → P3723T1EdgeContact P a b) →
                ∀ [Nontrivial ι],
                  ∀ (a : ι),
                    ∀ (b : ι),
                      a ≠ b →
                        P3723T1EdgeContact P a b →
                          ∀
                            (h :
                              (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) ≃ₜ
                                (↑(D.edgeArc a b) : Type)),
                            (↑((h :
                                (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) →
                                (↑(D.edgeArc a b) : Type))
                                ⟨(0 : ℝ), by norm_num⟩) :
                                ℝ × ℝ) =
                                D.position a →
                              (↑((h :
                                (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) →
                                (↑(D.edgeArc a b) : Type))
                                ⟨(1 : ℝ), by norm_num⟩) :
                                ℝ × ℝ) =
                                D.position b →
                                let g : Set.Icc (0 : Real) 1 → Real × Real := fun t =>
                                h t;
                              Function.Injective g →
                                (∀ {c : ι},
                                ∀ {d : ι},
                                P.plane.adjacent c d → ({ a, b } : Set ι) ≠ { c, d }) →
                                ∀ t : Set.Icc (0 : Real) 1,
                                0 < (t : Real) →
                                (t : Real) < 1 →
                                g t ∉
                                Set.range D.position ∪
                                {p | ∃ c d, P.plane.adjacent c d ∧ p ∈ D.edgeArc c d}
    ) := by
  classical
  intro ι P D contact this a b hab saved_contact h hstart hend g gi different t ht0 ht1
  have hga : g t ≠ D.position a := by
    intro heq
    have ht := gi (heq.trans hstart.symm)
    have hv : (t : Real) = 0 := congrArg Subtype.val ht
    linarith
  have hgb : g t ≠ D.position b := by
    intro heq
    have ht := gi (heq.trans hend.symm)
    have hv : (t : Real) = 1 := congrArg Subtype.val ht
    linarith
  have no_arc (c d : ι) (hcd : P.plane.adjacent c d) :
      g t ∉ D.edgeArc c d := by
    intro hx
    have hm : g t ∈ D.edgeArc a b ∩ D.edgeArc c d := ⟨(h t).property, hx⟩
    rw [D.edgeArc_intersections a b c d saved_contact (contact hcd)
      (different hcd)] at hm
    obtain ⟨v, hv, heq⟩ := hm
    rcases Set.mem_insert_iff.mp hv.1 with rfl | hvb
    · exact hga heq.symm
    · have hvb' : v = b := Set.mem_singleton_iff.mp hvb
      exact hgb (hvb' ▸ heq.symm)
  rintro (⟨c, hc⟩ | ⟨c, d, hcd, hx⟩)
  · obtain ⟨d, hcd⟩ := (P3767T1VertexEdgeIncidence P.plane c).1
    obtain ⟨hcmap, hc0, _⟩ := D.edgeArc_homeomorph c d (contact hcd)
    apply no_arc c d hcd
    rw [← hc, ← hc0]
    exact (hcmap ⟨0, by norm_num⟩).property
  · exact no_arc c d hcd hx

private theorem hij :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (a : ι), ∀ (b : ι), (a ≠ b) → (∀ (f :
            P.plane.Face), ∀ (i : Fin (3 : ℕ)), (P.plane.faceVertex f i = a) → (∀ (j : Fin (3 :
            ℕ)), (P.plane.faceVertex f j = b) → (i ≠ j))) ) := by
  classical
  intro ι P a b hab f i hi j hj heq
  exact hab (hi.symm.trans (heq ▸ hj))

end ContactRoutingGeometry

theorem PeriodicTileContactRoutingRigidity {ι : Type}
    (P : PeriodicTileComplex ι) :
    ∃ R : PeriodicTileContactRouting P,
      (∀ a b, a ≠ b →
        ((FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b)).Nonempty ↔
          P.plane.adjacent a b)) ∧
      Nonempty (PlaneEmbeddingAgreement P R) := by
-- BODY
  classical
  obtain ⟨ports⟩ := P3723T1ContactPortsExist P
  obtain ⟨D, retained_ports⟩ := P3723T1AllContactDrawingExists P ports
  have retained_position : D.position = ports.position :=
    congrArg P3723T1ContactPorts.position retained_ports
  have contact {a b : ι} (hab : P.plane.adjacent a b) :
      P3723T1EdgeContact P a b := ContactRoutingGeometry.contact ι P (a := a) (b := b) hab
  have symmetric {a b : ι} (hab : P.plane.adjacent a b) :
      P.plane.adjacent b a := (P.plane.adjacent_symmetric a b).mp hab
  let R := restrictContactDrawing P ports D retained_position contact symmetric
  obtain ⟨F⟩ := P3861T1RoutedFacialDomains P D
  obtain ⟨disjoint_faces, ⟨O⟩⟩ := P3861T1RoutedFaceOrientation P D F
  let : Nontrivial ι := (P3776T1FixedGeometry P.toPeriodicTileCore).1
  have traces :
      (Set.range R.position ∪
        {p | ∃ a b, P.plane.adjacent a b ∧ p ∈ R.edgeArc a b}) =
      (Set.range D.position ∪
        {p | ∃ a b, P.plane.adjacent a b ∧ p ∈ D.edgeArc a b}) := ContactRoutingGeometry.traces ι
            P ports D retained_position contact symmetric
  have face_frontier (f : P.plane.Face) := ContactRoutingGeometry.face_frontier ι P D F f
  have edge_frontier (f : P.plane.Face) (a b : ι)
      (hab : P.plane.adjacent a b)
      (ha : ∃ i, P.plane.faceVertex f i = a)
      (hb : ∃ i, P.plane.faceVertex f i = b) := ContactRoutingGeometry.edge_frontier ι P D F f a
          b hab ha hb
  refine ⟨R, ?_, ?_⟩
  · intro a b hab
    constructor
    · intro hcontact
      have saved_contact : P3723T1EdgeContact P a b := ⟨hab, hcontact⟩
      obtain ⟨h, hstart, hend⟩ := D.edgeArc_homeomorph a b saved_contact
      by_contra hn
      let g : Set.Icc (0 : Real) 1 → Real × Real := fun t => h t
      have gc : Continuous g := continuous_subtype_val.comp h.continuous
      have gi : Function.Injective g := fun s t hst =>
        h.injective (Subtype.ext hst)
      have different {c d : ι} (hcd : P.plane.adjacent c d) := ContactRoutingGeometry.different ι
          P symmetric a b hab hn (c := c) (d := d) hcd
      have avoid := ContactRoutingGeometry.avoid ι P D contact a b hab
          saved_contact h hstart hend gi different
      obtain ⟨f, ⟨i, hi⟩, ⟨j, hj⟩, _⟩ :=
        P3861T1ExtraArcLocalization P D F disjoint_faces a b g gc gi hstart hend avoid
      apply hn
      have hij : i ≠ j := ContactRoutingGeometry.hij ι P a b hab f i hi j hj
      simpa only [hi, hj] using P.plane.face_edges f i j hij
    · exact P.adjacent_has_common_edge a b
  · refine ⟨{
      fixedOrientation := O
      routedLeftFace := O.leftFace
      routedLeftSide := fun a b => F.region (O.leftFace a b)
      reversed := false
      routed_left_incident := O.left_incident
      routed_opposite_faces := O.opposite_sides
      routed_sides_exhaust_faces := O.sides_exhaust_faces
      routed_side_open := fun a b _ => F.region_open (O.leftFace a b)
      routed_side_connected := fun a b _ => F.region_connected (O.leftFace a b)
      routed_side_avoids_drawing := ?_
      routed_edge_in_side_frontiers := ?_
      routed_opposite_sides := ?_
      routed_side_component := ?_
      same_face_same_side := ?_
      face_side_agreement := ?_
    }⟩
    · intro a b _
      rw [traces]
      exact F.region_avoids_trace (O.leftFace a b)
    · intro a b hab x hx
      have hD : x ∈ D.edgeArc a b := by simpa only [R, restrictContactDrawing, ite_eq_left hab]
          using hx
      have hD' : x ∈ D.edgeArc b a := by rwa [D.edgeArc_symmetric]
      exact ⟨edge_frontier _ a b hab (O.left_incident a b hab).1
          (O.left_incident a b hab).2 hD,
        edge_frontier _ b a (symmetric hab) (O.left_incident b a (symmetric hab)).1
          (O.left_incident b a (symmetric hab)).2 hD'⟩
    · intro a b hab
      exact disjoint_faces (O.opposite_sides a b hab)
    · intro a b _ U _ hU havoid hmeet
      apply P3767T1BarrierRegionMaximal (F.region (O.leftFace a b)) _ U
        (F.region_open _) _ hU.isPreconnected havoid hmeet
      rw [traces]
      exact face_frontier _
    · intro a b c d _ _ heq
      exact congrArg F.region heq
    · intro a b _
      simp

end ApollonianSuperharmonic

end

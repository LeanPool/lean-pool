/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3861T1FacialDomains
public import LeanPool.ApollonianSuperharmonic.P3889T1ExactRadialStar
public import LeanPool.ApollonianSuperharmonic.P3889T1TwoRaySectors
public import LeanPool.ApollonianSuperharmonic.P3889T1FaceGapCoverage

-- [TABLET NODE: P3861T1ExtraArcLocalization]

/-!
# P3861T1ExtraArcLocalization

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3861T1ExtraArcLocalization :
    ∀ {ι : Type}, ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
        P3861T1FacialDomains P D), (Pairwise (fun f g : P.plane.Face => Disjoint
        (F.region f) (F.region g))) → (∀ (a : ι), ∀ (b : ι), ∀ (g : Set.Icc (0 : Real) 1 → Real ×
        Real), (Continuous g) → ((Function.Injective g) → ((g ⟨0, by norm_num⟩ =
        D.position a) → ((g ⟨1, by norm_num⟩ = D.position b) → ((∀ t : Set.Icc (0 : Real) 1, 0 < (t
        : Real) → (t : Real) < 1 →
      g t ∉ Set.range D.position ∪
        {p | ∃ c d, P.plane.adjacent c d ∧ p ∈ D.edgeArc c d}) → (∃ f : P.plane.Face,
      (∃ i, P.plane.faceVertex f i = a) ∧
      (∃ i, P.plane.faceVertex f i = b) ∧
      ∀ t : Set.Icc (0 : Real) 1, 0 < (t : Real) → (t : Real) < 1 →
        g t ∈ F.region f)))))) := by
  intro ι P D F hd a b g hc hi h0 h1 ha
-- BODY
  classical
  let : Nontrivial ι := (P3776T1FixedGeometry P.toPeriodicTileCore).1
  have hposition_edge_endpoint (v c d : ι) (hcd : P.plane.adjacent c d)
      (hv : D.position v ∈ D.edgeArc c d) : v = c ∨ v = d := by
    obtain ⟨z, hvz⟩ := (P3767T1VertexEdgeIncidence P.plane v).1
    have hvzContact : P3723T1EdgeContact P v z := by
      exact ⟨by intro h; subst z; exact P.plane.adjacent_irreflexive v hvz,
        P.adjacent_has_common_edge v z hvz⟩
    have hcdContact : P3723T1EdgeContact P c d := by
      exact ⟨by intro h; subst d; exact P.plane.adjacent_irreflexive c hcd,
        P.adjacent_has_common_edge c d hcd⟩
    have hvz' : D.position v ∈ D.edgeArc v z := by
      obtain ⟨h, h0, _⟩ := D.edgeArc_homeomorph v z hvzContact
      rw [← h0]
      exact (h ⟨0, by norm_num⟩).property
    by_cases heq : ({v, z} : Set ι) = {c, d}
    · have hmem : v ∈ ({c, d} : Set ι) := heq ▸ (by simp)
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
    · have hmem : D.position v ∈
          D.position '' (({v, z} : Set ι) ∩ ({c, d} : Set ι)) := by
        rw [← D.edgeArc_intersections v z c d hvzContact hcdContact heq]
        exact ⟨hvz', hv⟩
      obtain ⟨w, hw, hpos⟩ := hmem
      have hwv : w = v := D.position_injective hpos
      subst w
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hw.2
  have hfrontier_trace (f : P.plane.Face) :
      frontier (F.region f) ⊆ Set.range D.position ∪
        {p | ∃ c d, P.plane.adjacent c d ∧ p ∈ D.edgeArc c d} := by
    rw [F.region_frontier]
    rintro x ((hx | hx) | hx)
    · exact Or.inr ⟨_, _, P.plane.face_edges f 0 1 (by decide), hx⟩
    · exact Or.inr ⟨_, _, P.plane.face_edges f 1 2 (by decide), hx⟩
    · exact Or.inr ⟨_, _, P.plane.face_edges f 2 0 (by decide), hx⟩
  have hfrontier_position_incident (f : P.plane.Face) (v : ι)
      (hv : D.position v ∈ frontier (F.region f)) :
      ∃ i, P.plane.faceVertex f i = v := by
    rw [F.region_frontier] at hv
    rcases hv with (hv | hv) | hv
    · have hend := hposition_edge_endpoint v _ _
        (P.plane.face_edges f 0 1 (by decide)) hv
      rcases hend with h | h
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
    · have hend := hposition_edge_endpoint v _ _
        (P.plane.face_edges f 1 2 (by decide)) hv
      rcases hend with h | h
      · exact ⟨1, h.symm⟩
      · exact ⟨2, h.symm⟩
    · have hend := hposition_edge_endpoint v _ _
        (P.plane.face_edges f 2 0 (by decide)) hv
      rcases hend with h | h
      · exact ⟨2, h.symm⟩
      · exact ⟨0, h.symm⟩
  let s : Set (Set.Icc (0 : Real) 1) :=
    Set.Ioo (⟨0, by norm_num⟩ : Set.Icc (0 : Real) 1) ⟨1, by norm_num⟩
  have hAconnected : IsPreconnected (g '' s) := by
    exact isPreconnected_Ioo.image g hc.continuousOn
  have hAavoid : Disjoint (g '' s)
      (Set.range D.position ∪
        {p | ∃ c d, P.plane.adjacent c d ∧ p ∈ D.edgeArc c d}) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨t, ht, rfl⟩ hx
    have ht' : 0 < (t : Real) ∧ (t : Real) < 1 := by
      exact ⟨lt_of_le_of_lt (by norm_num : (0 : Real) ≤ 0) ht.1,
        lt_of_lt_of_le ht.2 (by norm_num : (1 : Real) ≤ 1)⟩
    exact ha t ht'.1 ht'.2 hx
  have hzero_mem : (⟨0, by norm_num⟩ : Set.Icc (0 : Real) 1) ∈ closure s := by
    rw [show s = Set.Ioo (⟨0, by norm_num⟩ : Set.Icc (0 : Real) 1)
      ⟨1, by norm_num⟩ from rfl, closure_Ioo (by norm_num)]
    simp
  have hone_mem : (⟨1, by norm_num⟩ : Set.Icc (0 : Real) 1) ∈ closure s := by
    rw [show s = Set.Ioo (⟨0, by norm_num⟩ : Set.Icc (0 : Real) 1)
      ⟨1, by norm_num⟩ from rfl, closure_Ioo (by norm_num)]
    simp
  have hconditional (f : P.plane.Face) (hmeet : (g '' s ∩ F.region f).Nonempty) :
      (∃ i, P.plane.faceVertex f i = a) ∧
      (∃ i, P.plane.faceVertex f i = b) ∧
      ∀ t : Set.Icc (0 : Real) 1, 0 < (t : Real) → (t : Real) < 1 →
        g t ∈ F.region f := by
    have hAsub : g '' s ⊆ F.region f := by
      apply P3767T1BarrierRegionMaximal (F.region f)
        (Set.range D.position ∪
          {p | ∃ c d, P.plane.adjacent c d ∧ p ∈ D.edgeArc c d})
        (g '' s) (F.region_open f) (hfrontier_trace f) hAconnected hAavoid hmeet
    have hclosure0 : D.position a ∈ closure (F.region f) := by
      have h := mem_closure_image hc.continuousAt hzero_mem
      rw [h0] at h
      exact (closure_mono hAsub) h
    have hclosure1 : D.position b ∈ closure (F.region f) := by
      have h := mem_closure_image hc.continuousAt hone_mem
      rw [h1] at h
      exact (closure_mono hAsub) h
    have hnot0 : D.position a ∉ F.region f := by
      intro hx
      exact (Set.disjoint_left.mp (F.region_avoids_trace f)) hx (Or.inl ⟨a, rfl⟩)
    have hnot1 : D.position b ∉ F.region f := by
      intro hx
      exact (Set.disjoint_left.mp (F.region_avoids_trace f)) hx (Or.inl ⟨b, rfl⟩)
    have hfront0 : D.position a ∈ frontier (F.region f) := by
      rw [frontier, (F.region_open f).interior_eq]
      exact ⟨hclosure0, hnot0⟩
    have hfront1 : D.position b ∈ frontier (F.region f) := by
      rw [frontier, (F.region_open f).interior_eq]
      exact ⟨hclosure1, hnot1⟩
    refine ⟨hfrontier_position_incident f a hfront0,
      hfrontier_position_incident f b hfront1, ?_⟩
    intro t ht0 ht1
    have hts : t ∈ s := by
      change (0 : Real) < (t : Real) ∧ (t : Real) < 1
      exact ⟨ht0, ht1⟩
    exact hAsub ⟨t, hts, rfl⟩
  obtain ⟨r, hr, u, hunit, hinj, hedge, hforeign, htrace⟩ :=
    P3889T1ExactRadialStar P D a
  have hsectors (c d : ι) (hc : P.plane.adjacent a c)
      (hd : P.plane.adjacent a d) (hne : c ≠ d) :
      Nonempty (P3889T1TwoRaySectorDecomposition
        (D.position a) r (u c) (u d)) := by
    apply P3889T1TwoRaySectors (D.position a) r (u c) (u d) hr
      (hunit c hc) (hunit d hd)
    intro heq
    exact hne (hinj c d hc hd heq)
  have hcover := P3889T1FaceGapCoverage P D F hd a r hr u
    hunit hinj hedge hforeign htrace hsectors
  have hstart : ∃ f : P.plane.Face, (g '' s ∩ F.region f).Nonempty := by
    have hcl : D.position a ∈ closure (g '' s) := by
      have h := mem_closure_image hc.continuousAt hzero_mem
      simpa only [h0] using h
    obtain ⟨p, hpA, hpdist⟩ := Metric.mem_closure_iff.mp hcl r hr
    have hpB : p ∈ Metric.ball (D.position a) r := by
      simpa only [Metric.mem_ball, dist_comm] using hpdist
    have hpavoid : p ∉ Set.range D.position ∪
        {q | ∃ c d, P.plane.adjacent c d ∧ q ∈ D.edgeArc c d} :=
      fun hp => Set.disjoint_left.mp hAavoid hpA hp
    obtain ⟨f, _, hpf⟩ := hcover p hpB hpavoid
    exact ⟨f, p, hpA, hpf⟩
  obtain ⟨f, hmeet⟩ := hstart
  obtain ⟨haFace, hbFace, hcontain⟩ := hconditional f hmeet
  exact ⟨f, haFace, hbFace, hcontain⟩

end ApollonianSuperharmonic

end

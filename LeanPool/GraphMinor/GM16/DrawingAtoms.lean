/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
public import LeanPool.GraphMinor.GM15.Cited
import LeanPool.GraphMinor.GM16.MetricPoints
import LeanPool.GraphMinor.GM16.DrawingConnected
import LeanPool.GraphMinor.Surface.Skeleton
import LeanPool.GraphMinor.GM11.Regions
import LeanPool.GraphMinor.GM11.Section5b
import LeanPool.GraphMinor.GM11.NiceStatements

import LeanPool.GraphMinor.GM11.CitedResults

/-!
# Atoms near an edge end

The path arguments for XVI (8.3) use an original atom that meets a new edge
and has the edge end in its closure. A region cannot become an edge: a region
is open in the surface, whereas a line or circle contains no embedded open
ball. This makes the atom-preservation condition of a rearrangement useful
for incident edges as well as for points.
-/

public section
namespace GraphMinor.GM16
open Set Topology Metric GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe u v w
variable {S : Type w} [TopologicalSpace S] [T2Space S]

/-- Near a point in the closure of a set, some drawing atom meets the set
and has that point in its closure. Finiteness of the atoms is essential. -/
theorem exists_atom_meeting_of_mem_closure (hS : IsClosedSurface S) [ConnectedSpace S]
    (H : Drawing S) {F : Set S} {x : S} (hx : x ∈ closure F) :
    ∃ a ∈ H.A, x ∈ closure a ∧ (a ∩ F).Nonempty := by
  have hfin : H.A.Finite := ((H.finite_V.image _).union H.finite_edges).union
    (finite_R hS H)
  have hcover : F ⊆ ⋃ a ∈ H.A, a ∩ F := by
    intro y hy
    obtain ⟨a, ha, hya⟩ := exists_atom H y
    exact mem_iUnion₂.mpr ⟨a, ha, hya, hy⟩
  have hx' := closure_mono hcover hx
  rw [hfin.closure_biUnion] at hx'
  obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hx'
  exact ⟨a, ha, closure_mono inter_subset_left hxa, Set.Nonempty.of_closure ⟨x, hxa⟩⟩

/-- No nonempty open subset of a closed surface is contained in the closure
of an edge of a drawing. -/
theorem not_open_subset_edge_closure (hS : IsClosedSurface S) {H : Drawing S}
    {e O : Set S} (he : e ∈ H.E) (hO : IsOpen O) (hne : O.Nonempty) : ¬ O ⊆ closure e := by
  intro hsub
  obtain ⟨x, hx⟩ := hne
  obtain ⟨U, j, g, c, hU, _⟩ := (hS.2.2 x).exists_ballChart hO hx (R := 1) (by norm_num)
  have himg : g '' ball (0 : ℂ) 1 ⊆ closure e := by
    rintro _ ⟨z, hz, rfl⟩
    exact hsub (hU (c.gm hz))
  rcases H.edge_cond e he with ⟨a, b, _, _, f, _, _⟩ | ⟨a, _, hcircle⟩
  · let γ : unitInterval → S := fun t => (f t).val
    have hγ : IsArcMap γ := ⟨continuous_subtype_val.comp f.continuous,
      Subtype.val_injective.comp f.injective⟩
    have hrange : range γ = closure e := by
      ext y
      constructor
      · rintro ⟨t, rfl⟩
        exact (f t).property
      · intro hy
        obtain ⟨t, ht⟩ := f.surjective ⟨y, hy⟩
        exact ⟨t, congrArg Subtype.val ht⟩
    exact not_image_ball_subset_arc hγ (by norm_num) c.gc c.hg.injOn (hrange ▸ himg)
  · exact not_image_ball_subset_oArc hcircle (by norm_num) c.gc c.hg.injOn himg

/-- An original region cannot equal an edge of another drawing in the same
closed surface. -/
theorem region_ne_edge (hS : IsClosedSurface S) {H H' : Drawing S} {a e : Set S}
    (ha : a ∈ H.R) (he : e ∈ H'.E) : a ≠ e := by
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  intro heq
  exact not_open_subset_edge_closure hS he (region_isOpen ha) (region_nonempty ha)
    (heq ▸ subset_closure)

omit [T2Space S] in
/-- A singleton is not open in a closed surface. -/
theorem not_isOpen_singleton (hS : IsClosedSurface S) (x : S) :
    ¬ IsOpen ({x} : Set S) := by
  intro hopen
  obtain ⟨U, j, g, c, hU, _⟩ := (hS.2.2 x).exists_ballChart hopen
    (mem_singleton x) (R := 1) (by norm_num)
  have hzero : (0 : ℂ) ∈ ball 0 1 := by simp
  have hhalf : (1 / 2 : ℂ) ∈ ball 0 1 := by norm_num [mem_ball, dist_eq_norm]
  have h0 : g 0 = x := mem_singleton_iff.mp (hU (c.gm hzero))
  have h1 : g (1 / 2) = x := mem_singleton_iff.mp (hU (c.gm hhalf))
  have heq := c.hg.injOn hzero hhalf (h0.trans h1.symm)
  norm_num at heq

/-- If a singleton is an atom of a drawing in a closed surface, its point
is a vertex. Edges have vertex ends, and regions are open. -/
theorem vertex_of_singleton_mem_atoms (hS : IsClosedSurface S) {H : Drawing S}
    {x : S} (hx : ({x} : Set S) ∈ H.A) : x ∈ H.V := by
  rcases hx with (⟨y, hy, heq⟩ | he) | hr
  · have hxy : y = x := by simpa using Set.ext_iff.mp heq y
    exact hxy ▸ hy
  · obtain ⟨a, b, hab⟩ := H.toGraph.exists_isLink_of_mem_edgeSet he
    have ha : a ∈ closure ({x} : Set S) := (hab.2.2.2 ▸ mem_insert a {b}).1
    rw [closure_singleton, mem_singleton_iff] at ha
    exact ha ▸ hab.2.1
  · let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
    exact (not_isOpen_singleton hS x (region_isOpen hr)).elim

/-- If an atom far from the rearrangement centre equals a new edge, it was
already an edge. This is used in the proof of XVI (8.3), Claims (5) and (12). -/
theorem rearranged_edge_of_atom (hS : IsClosedSurface S)
    {α : Type u} {β : Type v} {G : Graph α β} {H H' : Drawing S}
    {η : SpanEmbedding H G} {η' : SpanEmbedding H' G} {θ_star θ lam : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {z a : Set S}
    (h : IsRearrangedWithin G H H' η η' θ_star θ lam T_star T T' d d' z)
    (ha : a ∈ H.A) (hfar : lam < d z a) (ha' : a ∈ H'.E) : a ∈ H.E := by
  rcases ha with (⟨x, hx, rfl⟩ | ha) | ha
  · have hx' := (h.vMap_eq x hx hfar).1
    have hxedge : x ∈ ({x} : Set S) := mem_singleton x
    exact ((ha'.2.1 hxedge).2 hx').elim
  · exact ha
  · exact (region_ne_edge hS ha ha' rfl).elim

/-- The corrected XI proximity bounds give distance at most two from a vertex
 to any atom whose closure contains it. Small tangle orders use the order bound. -/
theorem vertex_atom_dist_le_two
    (hS : IsClosedSurface S) {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hm : HasTangleMetric H θ T d) :
    ∀ x ∈ H.V, ∀ a ∈ H.A, x ∈ closure a → d {x} a ≤ 2 := by
  obtain ⟨_, hs, hb, _, _, hr, he⟩ := GraphMinor.GM11.gm15_theorem_9_1.{w} H θ T d hS hm.1.1.1 hm
  intro x hx a ha hxa
  have hxA : ({x} : Set S) ∈ H.A := Or.inl (Or.inl ⟨x, hx, rfl⟩)
  by_cases hθ : θ ≤ 2
  · exact (hb _ hxA _ ha).trans hθ
  rcases ha with (⟨y, hy, rfl⟩ | ha) | ha
  · have hxy : x = y := by simpa only [closure_singleton, mem_singleton_iff] using hxa
    subst y
    exact (hs _ hxA).le.trans (Nat.zero_le _)
  · exact he x hx a ha hxa
  · exact (hr (edges_nonempty_of_tangle hS hm.1 (by omega)) x hx a ha hxa).trans (by omega)

/-- Far from the rearrangement centre, a new edge incident with an original
vertex is an unchanged original edge. This is the last-edge argument in
Graph Minors XVI, proof of (8.3), Claims (5) and (12), pages 66 and 68. -/
theorem rearranged_incident_edge_eq (hS : IsClosedSurface S)
    {α : Type u} {β : Type v} {G : Graph α β} {H H' : Drawing S}
    {η : SpanEmbedding H G} {η' : SpanEmbedding H' G} {θ_star θ lam : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {z : Set S}
    (h : IsRearrangedWithin G H H' η η' θ_star θ lam T_star T T' d d' z)
    (hsymm : ∀ a ∈ H.A, ∀ b ∈ H.A, d a b = d b a)
    (htri : ∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A,
      d a c ≤ d a b + d b c)
    (hprox : ∀ x ∈ H.V, ∀ a ∈ H.A, x ∈ closure a → d {x} a ≤ 2)
    {x : S} {f : Set S} (hx : x ∈ H.V) (hf : f ∈ H'.E)
    (hxf : x ∈ closure f) (hfar : lam + 3 ≤ d z {x}) :
    f ∈ H.E ∧ η'.eMap f = η.eMap f := by
  let : ConnectedSpace S := h.isSpan.isConnected
  obtain ⟨a, ha, hxa, w, hwa, hwf⟩ := exists_atom_meeting_of_mem_closure hS H hxf
  have hxA : ({x} : Set S) ∈ H.A := Or.inl (Or.inl ⟨x, hx, rfl⟩)
  have hclose := hprox x hx a ha hxa
  have hbound := htri z h.z_mem a ha {x} hxA
  rw [hsymm a ha {x} hxA] at hbound
  have hfar_a : lam < d z a := by omega
  have ha' := h.atom_mem a ha hfar_a
  have heq : a = f := atom_eq_of_mem ha' (Or.inl (Or.inr hf)) hwa hwf
  subst a
  have hfH := rearranged_edge_of_atom hS h ha hfar_a hf
  exact ⟨hfH, (h.eMap_eq f hfH hfar_a).2⟩

/-- A new vertex lying in a preserved original atom is an original vertex,
and its two embeddings agree. -/
theorem old_vertex_of_far_atom (hS : IsClosedSurface S)
    {α : Type u} {β : Type v} {G : Graph α β} {H H' : Drawing S}
    {η : SpanEmbedding H G} {η' : SpanEmbedding H' G} {θ_star θ lam : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {z a : Set S} {x : S}
    (h : IsRearrangedWithin G H H' η η' θ_star θ lam T_star T T' d d' z)
    (ha : a ∈ H.A) (hx : x ∈ a) (hx' : x ∈ H'.V) (hfar : lam < d z a) :
    a = {x} ∧ x ∈ H.V ∧ η'.vMap x = η.vMap x := by
  have heq := atom_eq_of_mem (h.atom_mem a ha hfar)
    (Or.inl (Or.inl ⟨x, hx', rfl⟩)) hx (mem_singleton x)
  have hxold := vertex_of_singleton_mem_atoms hS (heq ▸ ha)
  have hfar' : lam < d z {x} := by simpa only [heq] using hfar
  exact ⟨heq, hxold, (h.vMap_eq x hxold hfar').2⟩

end GraphMinor.GM16

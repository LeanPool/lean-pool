/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section6
import LeanPool.GraphMinor.GM16.Section6HairGraphs
import LeanPool.GraphMinor.GM16.Section6HairUnion
public import LeanPool.GraphMinor.GM16.Section6Components
import LeanPool.GraphMinor.GM09.Basic

/-!
# Choosing the paths witnessing the hairs of an animal

The hair clause in the definition of an animal supplies one path and one
far end for each hair. This file records those choices and proves the
properties of their endpoint-deleted union used in XVI (6.3), pages 59–60.
Connectedness and degree bounds are proved from the chosen paths.
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM11
  GraphMinor.GM14 GraphMinor.GM15
universe u v w
variable {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}

/-- Choices witnessing exactly the hair clause in the definition of an
animal (XVI, Section 5, page 55), used on page 59 in the proof of (6.3).
The maps are total, with their side conditions required on `Y`. -/
structure HairFamily (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (d : Set S → Set S → ℕ) (X : Set α) (Y : Set S) (θ : ℕ) where
  /-- The other end of the chosen hair at a vertex. -/
  far : S → S
  /-- The graph of the chosen hair at a vertex. -/
  path : S → Graph α β
  far_mem : ∀ y ∈ Y, far y ∈ H.V
  ne : ∀ y ∈ Y, y ≠ far y
  is_hPath : ∀ y ∈ Y, IsHPathWithEnds G η.imageGraph (path y) (η.vMap y) (η.vMap (far y))
  avoids_horns : ∀ y ∈ Y, Disjoint X V(path y)
  dist : ∀ y ∈ Y, θ ≤ d {y} {far y}

/-- Make the path choices in the hair clause of an animal. -/
theorem IsAnimal.exists_hairFamily [T2Space S]
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G} {d : Set S → Set S → ℕ}
    {X : Set α} {Y : Set S} {θ_star θ_span χ δ θ σ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (h : IsAnimal G T_star θ_star H η θ_span T d X Y χ δ θ σ) :
    Nonempty (HairFamily G H η d X Y θ) := by
  classical
  have hh := h.2.2.2.2.2.2.2.2.2.1
  choose far path hfar hne hpath hdisj hdist using (fun y : Y => hh y.val y.property)
  let far' : S → S := fun y => if hy : y ∈ Y then far ⟨y, hy⟩ else y
  let path' : S → Graph α β := fun y => if hy : y ∈ Y then path ⟨y, hy⟩ else G
  refine ⟨⟨far', path', ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro y hy
    simpa only [far', dite_eq_left hy] using hfar ⟨y, hy⟩
  · intro y hy
    simpa only [far', dite_eq_left hy] using hne ⟨y, hy⟩
  · intro y hy
    simpa only [far', path', dite_eq_left hy] using hpath ⟨y, hy⟩
  · intro y hy
    simpa only [path', dite_eq_left hy] using hdisj ⟨y, hy⟩
  · intro y hy
    simpa only [far', dite_eq_left hy] using hdist ⟨y, hy⟩

namespace HairFamily
variable {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
  {d : Set S → Set S → ℕ} {X : Set α} {Y : Set S} {θ : ℕ}

/-- The path with its far end deleted, called `Q_y` in XVI (6.3). -/
def tail (F : HairFamily G H η d X Y θ) (y : S) : Graph α β :=
  deleteVertices (F.path y) {η.vMap (F.far y)}

/-- The union of the truncated hair paths, called `G₀` in XVI (6.3). -/
def unionGraph (F : HairFamily G H η d X Y θ) : Graph α β :=
  subgraphSUnion G (range (fun y : Y => F.tail y.val))

/-- The marked near ends in components of `G₀` containing two near ends,
called `Y₁` in XVI (6.3). -/
def active (F : HairFamily G H η d X Y θ) : Set S :=
  {y ∈ Y | η.vMap y ∈ activeMarkedVertices F.unionGraph (η.vMap '' Y)}

theorem tail_le (F : HairFamily G H η d X Y θ) {y : S} (hy : y ∈ Y) : F.tail y ≤ G :=
  (deleteVertices_le _ _).trans (F.is_hPath y hy).2.1.le

theorem union_le (F : HairFamily G H η d X Y θ) : F.unionGraph ≤ G := by
  apply subgraphSUnion_le
  rintro R ⟨y, rfl⟩
  exact F.tail_le y.property

theorem tail_le_union (F : HairFamily G H η d X Y θ) {y : S} (hy : y ∈ Y) :
    F.tail y ≤ F.unionGraph := by
  apply le_subgraphSUnion
  · rintro R ⟨z, rfl⟩
    exact F.tail_le z.property
  · exact ⟨⟨y, hy⟩, rfl⟩

theorem tail_connected (F : HairFamily G H η d X Y θ) {y : S} (hy : y ∈ Y) :
    IsGraphConnected (F.tail y) :=
  path_delete_endpoint_connected (F.is_hPath y hy).2.1 (F.is_hPath y hy).2.2.1

theorem tail_inter_old (F : HairFamily G H η d X Y θ) {y : S} (hy : y ∈ Y) :
    V(F.tail y) ∩ V(η.imageGraph) = {η.vMap y} :=
  truncated_hair_inter (F.is_hPath y hy)

theorem near_mem_tail (F : HairFamily G H η d X Y θ) {y : S} (hy : y ∈ Y) :
    η.vMap y ∈ V(F.tail y) := by
  have hm : η.vMap y ∈ V(F.tail y) ∩ V(η.imageGraph) := by
    rw [F.tail_inter_old hy]
    exact mem_singleton _
  exact hm.1

/-- The old-graph vertices of `G₀` are exactly the marked near ends. -/
theorem union_inter_old (F : HairFamily G H η d X Y θ) :
    V(F.unionGraph) ∩ V(η.imageGraph) = η.vMap '' Y := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hxH⟩
    obtain ⟨R, ⟨y, rfl⟩, hxR⟩ := mem_iUnion₂.mp hx
    have heq := mem_singleton_iff.mp ((F.tail_inter_old y.property).subset ⟨hxR, hxH⟩)
    exact ⟨y.val, y.property, heq.symm⟩
  · rintro x ⟨y, hy, rfl⟩
    exact ⟨(F.tail_le_union hy).vertexSet_mono (F.near_mem_tail hy),
      ((F.tail_inter_old hy).symm ▸ mem_singleton (η.vMap y)).2⟩

/-- Every old-graph vertex has at most one neighbor in `G₀`. -/
theorem union_old_neighbors_subsingleton (F : HairFamily G H η d X Y θ)
    (hY : Y ⊆ H.V) {x : α} (hx : x ∈ V(η.imageGraph)) :
    {z | F.unionGraph.Adj x z}.Subsingleton := by
  apply hair_union_old_neighbors_subsingleton
    (P := fun y : Y => F.path y.val) (a := fun y : Y => η.vMap y.val)
    (b := fun y : Y => η.vMap (F.far y.val))
    (fun y => (F.is_hPath y.val y.property).2.1)
    (fun _ => deleteVertices_le _ _) (fun y => F.tail_inter_old y.property) ?_ hx
  intro y z heq
  exact Subtype.ext (η.bijOn_v.injOn (hY y.property) (hY z.property) heq)

/-- Truncated hairs with near ends outside `Y₁` are disjoint. -/
theorem tails_disjoint_of_not_active (F : HairFamily G H η d X Y θ)
    (hY : Y ⊆ H.V) {y z : S} (hy : y ∈ Y) (hz : z ∈ Y) (hyz : y ≠ z)
    (hyactive : y ∉ F.active) : Disjoint V(F.tail y) V(F.tail z) := by
  apply disjoint_connected_hairs_of_not_active (Z := η.vMap '' Y) (F.tail_le_union hy)
    (F.tail_le_union hz)
    (F.tail_connected hy) (F.tail_connected hz) (F.near_mem_tail hy) (F.near_mem_tail hz)
    ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
    (fun h => hyz (η.bijOn_v.injOn (hY hy) (hY hz) h))
  intro hactive
  exact hyactive ⟨hy, hactive⟩

/-- No horn vertex lies on the truncated hair union. -/
theorem union_avoids_horns (F : HairFamily G H η d X Y θ) : Disjoint X V(F.unionGraph) := by
  apply Set.disjoint_left.mpr
  intro x hxX hxU
  obtain ⟨R, ⟨y, rfl⟩, hxR⟩ := mem_iUnion₂.mp hxU
  exact (Set.disjoint_left.mp (F.avoids_horns y.val y.property)) hxX
    ((deleteVertices_le _ _).vertexSet_mono hxR)

/-- The truncated hair union has no edge of the embedded drawing. -/
theorem union_edges_disjoint_old (F : HairFamily G H η d X Y θ) :
    Disjoint E(F.unionGraph) E(η.imageGraph) := by
  have hFG : ∀ R ∈ range (fun y : Y => F.tail y.val), R ≤ G := by
    rintro R ⟨y, rfl⟩
    exact F.tail_le y.property
  apply Set.disjoint_left.mpr
  intro e heU heH
  change e ∈ E(subgraphSUnion G (range (fun y : Y => F.tail y.val))) at heU
  rw [edgeSet_subgraphSUnion hFG] at heU
  obtain ⟨R, ⟨y, rfl⟩, heR⟩ := mem_iUnion₂.mp heU
  exact (Set.disjoint_left.mp (F.is_hPath y.val y.property).2.2.2.2.2.2)
    ((deleteVertices_le _ _).edgeSet_mono heR) heH

/-- The drawing labels of active near ends count the same vertices as
`Y₁` in the embedded graph. -/
theorem active_card_eq (F : HairFamily G H η d X Y θ) (hY : Y ⊆ H.V) :
    F.active.ncard = (activeMarkedVertices F.unionGraph (η.vMap '' Y)).ncard := by
  have hinj : InjOn η.vMap F.active := η.bijOn_v.injOn.mono (fun _ h => hY h.1)
  have heq : η.vMap '' F.active = activeMarkedVertices F.unionGraph (η.vMap '' Y) := by
    apply Set.Subset.antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact hy.2
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := hx.1
      exact ⟨y, ⟨hy, hx⟩, rfl⟩
  rw [← heq, hinj.ncard_image]

/-- Outside the active components, full hair paths are disjoint when
their ends have different labels. This is used for the separated family
`Y₂` in XVI (6.3), page 60. -/
theorem full_hairs_disjoint (F : HairFamily G H η d X Y θ)
    (hY : Y ⊆ H.V) {y z : S} (hy : y ∈ Y) (hz : z ∈ Y) (hyz : y ≠ z)
    (hyactive : y ∉ F.active)
    (hfy_z : F.far y ≠ z) (hfy_fz : F.far y ≠ F.far z)
    (hy_fz : y ≠ F.far z) : Disjoint V(F.path y) V(F.path z) := by
  apply Set.disjoint_left.mpr
  intro a hay haz
  by_cases hafy : a = η.vMap (F.far y)
  · have haH : a ∈ V(η.imageGraph) := hafy ▸ η.bijOn_v.mapsTo (F.far_mem y hy)
    have haends : a ∈ ({η.vMap z, η.vMap (F.far z)} : Set α) :=
      (F.is_hPath z hz).2.2.2.2.2.1 ▸ ⟨haz, haH⟩
    rcases haends with haz' | haz'
    · exact hfy_z (η.bijOn_v.injOn (F.far_mem y hy) (hY hz) (hafy.symm.trans haz'))
    · exact hfy_fz (η.bijOn_v.injOn (F.far_mem y hy) (F.far_mem z hz)
        (hafy.symm.trans (mem_singleton_iff.mp haz')))
  · by_cases hafz : a = η.vMap (F.far z)
    · have haH : a ∈ V(η.imageGraph) := hafz ▸ η.bijOn_v.mapsTo (F.far_mem z hz)
      have haends : a ∈ ({η.vMap y, η.vMap (F.far y)} : Set α) :=
        (F.is_hPath y hy).2.2.2.2.2.1 ▸ ⟨hay, haH⟩
      rcases haends with hay' | hay'
      · exact hy_fz (η.bijOn_v.injOn (hY hy) (F.far_mem z hz) (hay'.symm.trans hafz))
      · exact hafy (mem_singleton_iff.mp hay')
    · exact (Set.disjoint_left.mp (F.tails_disjoint_of_not_active hY hy hz hyz hyactive))
        ⟨hay, by simpa using hafy⟩ ⟨haz, by simpa using hafz⟩

end HairFamily
end GraphMinor.GM16

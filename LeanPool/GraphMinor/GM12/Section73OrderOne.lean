/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73Tangle
import LeanPool.GraphMinor.GM11.RadialBasics
import LeanPool.GraphMinor.GM14.DiscSlope
import LeanPool.GraphMinor.GM14.Section7a
import LeanPool.GraphMinor.GM12.Section72Tangle
import LeanPool.GraphMinor.GM11.Section64
import LeanPool.GraphMinor.GM11.RadialExists
import LeanPool.GraphMinor.GM11.Theorem61
import LeanPool.GraphMinor.GM12.Section77
import LeanPool.GraphMinor.GM11.Section91

/-!
# The order-one case after vertex deletion

For the endpoint case of XII (7.3), page 261, the deleted tangle has
order one. A normal circle with fewer than one vertex lies in one
region of the two-cell drawing and bounds a disc there. The disc
misses the whole drawing, so the tangle selects it: the reverse
orientation would put every vertex on the small side.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM10 GM11 GM14 Hypergraph

/-- Every order-one tangle in a two-cell drawing is respectful.
This proves the endpoint respectfulness case used in XII (7.3),
page 261. -/
theorem isRespectful_order_one
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S}
    (htwo : (PaintingOrDrawing.drawing Γ).IsTwoCell)
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsTangle Γ.toHypergraph 1 T) : IsRespectfulDrawingTangle Γ 1 T := by
  refine ⟨htwo, hT, inferInstance, ?_⟩
  intro F hF hn hcard
  have hFV : F ∩ Γ.V = ∅ := by
    apply (ncard_eq_zero (Γ.finite_V.subset inter_subset_right)).mp
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hcard)
  have hdis : Disjoint F Γ.U := by
    apply disjoint_left.mpr
    intro x hxF hxU
    have hxV := hn ⟨hxF, hxU⟩
    exact (hFV.subset ⟨hxF, hxV⟩).elim
  obtain ⟨x, hxF⟩ := GM14.IsOArc.nonempty hF
  obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem (disjoint_left.mp hdis hxF)
  have hFr : F ⊆ r := subset_region hr (GM14.IsOArc.isPreconnected hF) hdis hxF hxr
  obtain ⟨D, hDr, hD, hbd⟩ := exists_disc_in_openDisc (htwo.2 r hr) hF hFr
  have hbd' : subBd D = F := (IsClosedDisc.subBd_eq_discBd hS hD).trans hbd
  have hnD : (PaintingOrDrawing.drawing Γ).IsNormal (frontier D) := by
    rw [← subBd_eq_frontier, hbd']
    exact hn
  have hsep := isSeparation_inter hD.isClosed hnD
  have hord : separationOrder ((PaintingOrDrawing.drawing Γ).inter D)
      ((PaintingOrDrawing.drawing Γ).interOutside D) < 1 := by
    apply lt_of_le_of_lt _ hcard
    rw [← hbd', subBd_eq_frontier]
    exact ncard_le_ncard (fun x hx => inter_outside_subset hx)
      (Γ.finite_V.subset inter_subset_right)
  refine ⟨D, hD, hbd', (hT.axiom1 hsep hord).resolve_right ?_⟩
  intro hrev
  apply hT.axiom3 hrev
  apply Subset.antisymm
  · exact inter_subset_left
  · intro x hxV
    refine ⟨hxV, subset_closure ⟨mem_univ _, ?_⟩⟩
    intro hxD
    exact region_subset hr (hDr hxD) (Γ.V_subset_U hxV)

/-- An order-one respectful tangle has a metric. This supplies the
metric needed in the endpoint case of XII (7.3), page 261. -/
theorem exists_metric_order_one
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S}
    (htwo : (PaintingOrDrawing.drawing Γ).IsTwoCell)
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsTangle Γ.toHypergraph 1 T) :
    ∃ d : Set S → Set S → ℕ, HasTangleMetric Γ 1 T d := by
  have hresp := isRespectful_order_one hS htwo hT
  obtain ⟨K, hK⟩ := exists_radialDrawing hS htwo
  obtain ⟨ins, hins⟩ := exists_derivedSlope hS hresp.2.2 hK.2.1
  exact ⟨tangleMetric Γ K ins 1, hresp, K, ins, hK, hins, fun _ _ _ _ => rfl⟩

/-- The order-two endpoint of Graph Minors XII, (7.3), pages
261–262. The deleted tangle has order one. The first bound follows
from the old metric's order bound. For the second, distinct atoms
have positive new distance; if the atoms agree, the old distance to
the deleted vertex is zero. These are precisely the endpoint cases
excluded by the strict-distance assumptions in the paper's proof. -/
theorem theorem_7_3_order_two
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hd : HasTangleMetric Γ 2 T d)
    {v : S} (hv : v ∈ Γ.V)
    (htwo : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsTwoCell) :
    ∃ (d' : Set S → Set S → ℕ) (r' : Set S),
      HasTangleMetric (deleteVertices Γ {v}) 1
        (GM10.deleteVerticesTangle Γ.toHypergraph {v} T 2) d' ∧
      r' ∈ (deleteVertices Γ {v}).R ∧ v ∈ r' ∧
      (∀ a ∈ Γ.A ∩ (deleteVertices Γ {v}).A,
        ∀ b ∈ Γ.A ∩ (deleteVertices Γ {v}).A, d a b - 2 ≤ d' a b) ∧
      (∀ a ∈ Γ.A ∩ (deleteVertices Γ {v}).A, d a {v} - 1 ≤ d' a r') := by
  have hT' : IsTangle (deleteVertices Γ {v}).toHypergraph 1
      (GM10.deleteVerticesTangle Γ.toHypergraph {v} T 2) := by
    simpa using theorem_7_3_tangle (by decide : 2 ≤ 2) hd.1.2.1 hv
  obtain ⟨d', hd'⟩ := exists_metric_order_one hS htwo hT'
  have hdelete := deleteVertices_isSubdrawing Γ {v}
  have hvnot : v ∉ (deleteVertices Γ {v}).U := by
    intro hvU
    have hvV := (isSubdrawing_U_inter_V hdelete).subset ⟨hvU, hv⟩
    exact ((deleteVertices_V Γ {v}).subset hvV).2 rfl
  obtain ⟨r', hr', hvr'⟩ := exists_region_of_notMem hvnot
  have hbound : ∀ a ∈ Γ.A, ∀ b ∈ Γ.A, d a b ≤ 2 := by
    obtain ⟨_, K, ins, hK, _, heq⟩ := hd
    intro a ha b hb
    rw [heq a ha b hb]
    exact tangleMetric_le_order hK.2.1 a b
  have hvA : ({v} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v, hv, rfl⟩)
  refine ⟨d', r', hd', hr', hvr', ?_, ?_⟩
  · intro a ha b hb
    exact (Nat.sub_eq_zero_of_le (hbound a ha.1 b hb.1)) ▸ Nat.zero_le (d' a b)
  · intro a ha
    by_cases har : a = r'
    · have hva : v ∈ a := har.symm ▸ hvr'
      have hav : a = {v} := atom_eq_of_inter_nonempty ha.1 hvA ⟨v, hva, rfl⟩
      have hd0 : d a {v} = 0 := by rw [hav]; exact metric_self hd hvA
      rw [hd0, Nat.zero_sub]
      exact Nat.zero_le _
    · have hpositive : 1 ≤ d' a r' := Nat.one_le_iff_ne_zero.mpr
        (fun h0 => har ((tangleMetric_eq_zero_iff hS hd' ha.2 (Or.inr hr')).mp h0))
      have hle : d a {v} ≤ 2 := hbound a ha.1 {v} hvA
      omega

end GraphMinor.GM12

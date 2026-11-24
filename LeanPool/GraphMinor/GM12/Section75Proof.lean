/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section75Case2
public import LeanPool.GraphMinor.GM12.Section75OrderTwo
public import LeanPool.GraphMinor.GM12.Section75TwoCell
public import LeanPool.GraphMinor.GM12.Section73MetricComparison
public import LeanPool.GraphMinor.GM12.SurfaceDualContract
import LeanPool.GraphMinor.GM11.Theorem63

/-!
# Graph Minors XII, (7.5)

Case 1 of (7.5) is `exists_theorem_7_5_disc_reduction`. It leaves a drawing in which no `O`-arc
through
one vertex has an edge in its selected disc. `theorem_7_5_case_2_chain` runs the chain of Case 2 on
such a
drawing, `Γ` to the dual `Γ₁` to `Γ₂ = Γ₁ \ r*` to the dual `Γ₃` of `Γ₂`, and ends with
`theorem_7_5_case_2`.
-/


@[expose] public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 GraphMinor.GM14 Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- The form of `exists_dual_tangleMetric_of_common_radial` at order 2, for the tangle of `Γ₂` that
comes
from a tangle of order 3 in `Γ₁`. The tangle in `Γ₃` is `isTangle_induced_of_order_three`. -/
theorem exists_dual_tangleMetric_order_two (hS : IsClosedSurface S) {Γ₁ Γ₃ J : Drawing S} {v : S}
    {T₁ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins : Drawing S → Set S}
    (hT₁ : IsTangle Γ₁.toHypergraph 3 T₁) (hv : v ∈ Γ₁.V)
    (hresp : (PaintingOrDrawing.drawing (deleteVertices Γ₁ {v})).IsRespectful 2
      (deleteVerticesTangle Γ₁.toHypergraph {v} T₁ 3))
    (hJ₂ : (PaintingOrDrawing.drawing (deleteVertices Γ₁ {v})).IsRadialDrawing J)
    (hJ₃ : (PaintingOrDrawing.drawing Γ₃).IsRadialDrawing J)
    (hins : IsDerivedSlope (PaintingOrDrawing.drawing (deleteVertices Γ₁ {v})) J 2
      (deleteVerticesTangle Γ₁.toHypergraph {v} T₁ 3) ins)
    (hE₂ : (deleteVertices Γ₁ {v}).E.Nonempty) (hE₃ : Γ₃.E.Nonempty) :
    ∃ (T₃ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d₃ : Set S → Set S → ℕ),
      HasTangleMetric Γ₃ 2 T₃ d₃ ∧
      (∀ a ∈ (deleteVertices Γ₁ {v}).A, ∀ b ∈ (deleteVertices Γ₁ {v}).A,
        ∀ a_star ∈ Γ₃.A, ∀ b_star ∈ Γ₃.A,
        (a = b ↔ a_star = b_star) →
        (∀ x' : Set S, IsCorrespondingAtom (deleteVertices Γ₁ {v}) J a x' ↔
          IsCorrespondingAtom Γ₃ J a_star x') →
        (∀ y' : Set S, IsCorrespondingAtom (deleteVertices Γ₁ {v}) J b y' ↔
          IsCorrespondingAtom Γ₃ J b_star y') →
        d₃ a_star b_star = tangleMetric (deleteVertices Γ₁ {v}) J ins 2 a b) := by
  have hT₃ := isTangle_induced_of_order_three hS hT₁ hv hresp hJ₂ hJ₃ hins hE₂ hE₃
  have hp₂ : IsPretangle (PaintingOrDrawing.drawing (deleteVertices Γ₁ {v})).toHypergraph 2
      (deleteVerticesTangle Γ₁.toHypergraph {v} T₁ 3) :=
    IsTangle.isPretangle (theorem_7_3_tangle (by decide) hT₁ hv)
  have hsl := isSlope_of_derived hS hp₂ hJ₂.2.1.1 hins
  obtain ⟨-, hr₃, hd₃⟩ := theorem_6_1_proof (Γ := PaintingOrDrawing.drawing Γ₃) hS hE₃ hJ₃
    (by norm_num) hsl
  refine ⟨_, tangleMetric Γ₃ J ins 2, ⟨⟨hJ₃.1, hT₃, hr₃⟩, J, ins, hJ₃, hd₃, fun _ _ _ _ => rfl⟩, ?_⟩
  intro a _ b _ a_star _ b_star _ heq ha hb
  exact tangleMetric_eq_of_correspondingAtom_iff heq ha hb

/-- The vertex `v` of `K` in `r` has at most one spoke to each vertex of `Γ`, once no `O`-arc
through
one vertex in `r ∪ {v}` has an edge in its selected disc. This is where the paper's "`rBar - r` is
an
`O`-arc" is used. -/
theorem unique_spokes_of_no_disc (hS : IsClosedSurface S) {Γ K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hθ : 2 ≤ θ) (hT : IsRespectfulDrawingTangle Γ θ T)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {r : Set S} (hr : r ∈ Γ.R)
    (hno : ∀ Δ F : Set S, ∀ v : S, IsClosedDisc Δ → subBd Δ = F →
      (PaintingOrDrawing.drawing Γ).IsNormal F → F ∩ Γ.V = {v} →
      F \ {v} ⊆ r →
      ((PaintingOrDrawing.drawing Γ).inter Δ,
        (PaintingOrDrawing.drawing Γ).interOutside Δ) ∈ T →
      ∀ e ∈ Γ.E, ¬ e ⊆ Δ)
    {v : S} (hvr : v ∈ r) (hvK : v ∈ K.V) :
    ∀ g ∈ K.E, ∀ h ∈ K.E, ∀ c : S, c ∈ K.V →
      closure g ∩ K.V = {v, c} → closure h ∩ K.V = {v, c} → g = h := by
  intro g hg h hh c hc hcapg hcaph
  by_contra hgh
  obtain ⟨x, hx, y, hy, hxy⟩ := hK.2.1.2.2.2.2.1 g hg
  have hvΓ : v ∉ Γ.V := fun h' => region_subset hr hvr (Γ.V_subset_U h')
  have hxm : x ∈ closure g ∩ K.V := by rw [hxy]; simp
  rw [hcapg] at hxm
  have hxc : x = c := hxm.resolve_left fun h' => hvΓ (h' ▸ hx)
  subst hxc
  refine no_parallel_spokes_at_region_hub hS hθ hT hK.2.1 hr hno hx hg hh hgh hvr hvK ?_ ?_
  · rw [hcapg, pair_comm]
  · rw [hcaph, pair_comm]

/-- The chain of Case 2 of **(7.5)** (Graph Minors XII, page 265), for a drawing `Γ` in which no
`O`-arc through one vertex in `r ∪ {v}` has an edge in its selected disc. -/
theorem theorem_7_5_case_2_chain (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {r : Set S}
    (hθ : 3 ≤ θ) (hM : HasTangleMetric Γ θ T d) (hr : r ∈ Γ.R)
    (hno : ∀ Δ F : Set S, ∀ v : S, IsClosedDisc Δ → subBd Δ = F →
      (PaintingOrDrawing.drawing Γ).IsNormal F → F ∩ Γ.V = {v} →
      F \ {v} ⊆ r →
      ((PaintingOrDrawing.drawing Γ).inter Δ,
        (PaintingOrDrawing.drawing Γ).interOutside Δ) ∈ T →
      ∀ e ∈ Γ.E, ¬ e ⊆ Δ) :
    ∃ (Γ' : Drawing S)
      (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d' : Set S → Set S → ℕ) (r' : Set S),
      Γ'.IsSubdrawing (deleteVertices Γ {u ∈ Γ.V | u ∈ closure r}) ∧
      (PaintingOrDrawing.drawing Γ').IsTwoCell ∧
      HasTangleMetric Γ' (θ - 2) T' d' ∧
      r' ∈ Γ'.R ∧ r ⊆ r' ∧
      Γ.U ⊆ Γ'.U ∪ r' ∧
      (∀ a ∈ Γ.A ∩ Γ'.A, ∀ b ∈ Γ.A ∩ Γ'.A, d a b - 4 ≤ d' a b) ∧
      (∀ a ∈ Γ.A ∩ Γ'.A, d a r - 2 ≤ d' a r') ∧
      (∀ a ∈ Γ.A, a ⊆ r' → d a r ≤ 3) := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨hT, K, ins, hK, hins, heq⟩ := id hM
  have hE : Γ.E.Nonempty := edgeSet_nonempty_of_isTangle_of_two_le hT.2.1 (by omega)
  -- The dual `Γ₁`, with `T₁`, `d₁` by (6.6).
  obtain ⟨Γ₁, hK₁, hdual⟩ := exists_lineDual_of_radial hS hE hK
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hV₁, hE₁eq⟩ := id hdual
  have hE₁ : Γ₁.E.Nonempty := by
    rw [hE₁eq]
    exact hE.image _
  obtain ⟨T₁, d₁, hM₁, hins₁, heq₁, hd₁⟩ :=
    exists_dual_tangleMetric_of_common_radial hS hθ hT hE₁ hK hK₁ hins
  have hT₁ := hM₁.1
  -- The vertex `v = r*`, and `Γ₂ = Γ₁ \ v`, which is 2-cell.
  obtain ⟨v, ⟨hvr, hvK⟩, -⟩ := hK.2.1.2.2.1 r hr
  have hv₁ : v ∈ Γ₁.V := by
    rw [hV₁]
    exact ⟨hvK, fun h' => region_subset hr hvr (Γ.V_subset_U h')⟩
  have hspoke := unique_spokes_of_no_disc hS (by omega) hT hK hr hno hvr hvK
  have hother : ∃ w ∈ Γ₁.V, w ≠ v := by
    by_contra hn
    push Not at hn
    obtain ⟨e, he⟩ := hE₁
    have hheV : Γ₁.toHypergraph.ends e = Γ₁.toHypergraph.vertexSet := by
      apply Subset.antisymm fun _ h => Γ₁.toHypergraph.vertex_mem_of_inc h
      obtain ⟨y, hy⟩ := (drawing_toHypergraph_isGraph Γ₁ e he).1
      have hyv : y = v := hn y (Γ₁.toHypergraph.vertex_mem_of_inc hy)
      intro w hw
      have hwv : w = v := hn w hw
      rw [hwv, ← hyv]
      exact hy
    have hsize : edgeSize Γ₁.toHypergraph e < θ := by
      have := (drawing_toHypergraph_isGraph Γ₁ e he).2
      unfold edgeSize
      omega
    have hm := (GraphMinor.GM10.theorem_2_7_proof hT₁.2.1.one_le hT₁.2.1.isSeparation
      hT₁.2.1.order_lt hT₁.2.1.axiom1
      hT₁.2.1.axiom2).mp hT₁.2.1 e he hsize
    exact hT₁.2.1.axiom3 hm hheV
  have htwo := isTwoCell_delete_vertex_of_unique_spokes hS hK₁ hv₁ hother hspoke
  have hE₂ : (deleteVertices Γ₁ {v}).E.Nonempty :=
    edgeSet_nonempty_of_isTangle_of_two_le (theorem_7_3_tangle (by omega) hT₁.2.1 hv₁) (by omega)
  have hvnot : v ∉ (deleteVertices Γ₁ {v}).U := by
    intro hvU
    have hvV := (isSubdrawing_U_inter_V (deleteVertices_isSubdrawing Γ₁ {v})).subset ⟨hvU, hv₁⟩
    exact ((deleteVertices_V Γ₁ {v}).subset hvV).2 rfl
  obtain ⟨r₂, hr₂, hvr₂⟩ := exists_region_of_notMem hvnot
  -- (7.3) on `Γ₁`.
  have hunique : ∀ e ∈ K.E, ∀ g ∈ K.E, ∀ u : S,
      K.toGraph.IsLink e v u → K.toGraph.IsLink g v u → e = g := fun e he g hg u h₁ h₂ =>
    hspoke e he g hg u h₁.2.2.1 h₁.2.2.2 h₂.2.2.2
  obtain ⟨D, f, H, J, ins₂, hc, hJ, hins₂, hm, -, hi, hii⟩ :=
    exists_starContraction_with_vertex_deletion_bounds_of_unique_spokes hS (by omega) hT₁ hins₁ hK₁
      hE₁ hv₁ htwo hE₂ hunique hr₂ hvr₂
  -- The dual `Γ₃` of `Γ₂`, with `T₃`, `d₃` by (6.6).
  obtain ⟨Γ₃, hcd⟩ := exists_contracted_dual hS hE hK hK₁ hdual hr hvr hvK hr₂ hvr₂ hc hJ hE₂
  obtain ⟨T₃, d₃, hM₃, hd₃⟩ : ∃ (T₃ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d₃ : Set S → Set S → ℕ), HasTangleMetric Γ₃ (θ - 1) T₃ d₃ ∧
      (∀ a ∈ (deleteVertices Γ₁ {v}).A, ∀ b ∈ (deleteVertices Γ₁ {v}).A,
        ∀ a_star ∈ Γ₃.A, ∀ b_star ∈ Γ₃.A,
        (a = b ↔ a_star = b_star) →
        (∀ x' : Set S, IsCorrespondingAtom (deleteVertices Γ₁ {v}) J a x' ↔
          IsCorrespondingAtom Γ₃ J a_star x') →
        (∀ y' : Set S, IsCorrespondingAtom (deleteVertices Γ₁ {v}) J b y' ↔
          IsCorrespondingAtom Γ₃ J b_star y') →
        d₃ a_star b_star = tangleMetric (deleteVertices Γ₁ {v}) J ins₂ (θ - 1) a b) := by
    by_cases h3 : θ = 3
    · subst h3
      exact exists_dual_tangleMetric_order_two hS hT₁.2.1 hv₁ hm.1.2.2 hJ hcd.radial hins₂ hE₂
        hcd.nonempty_E
    · obtain ⟨T₃, d₃, h, -, -, hh⟩ := exists_dual_tangleMetric_of_common_radial hS (by omega) hm.1
        hcd.nonempty_E hJ hcd.radial hins₂
      exact ⟨T₃, d₃, h, hh⟩
  have hvA : ({v} : Set S) ∈ Γ₁.A := Or.inl (Or.inl ⟨v, hv₁, rfl⟩)
  refine theorem_7_5_case_2 hS hθ hT hK heq hr hvr hvK hK₁ hdual hM₁ hd₁ hm hr₂ hvr₂ ?_ ?_ hJ
    (fun _ _ _ _ => rfl) hcd hM₃ hd₃
  · intro a ha b hb
    have := hi a ha b hb
    rw [heq₁ a ha.1 b hb.1]
    omega
  · intro a ha
    have := hii a ha
    rw [heq₁ a ha.1 {v} hvA]
    omega

/-- **(7.5)** of Graph Minors XII (page 263). -/
theorem theorem_7_5_proof : Theorem75Statement.{u} := by
  intro S _ _ _ hS Γ θ T d r hθ hd hr
  obtain ⟨Γ₀, T₀, d₀, r₀, -, hd₀, hr₀, hrr₀, hno, hlift⟩ :=
    exists_theorem_7_5_disc_reduction hS hθ hd hr
  obtain ⟨Γ', T', d', r', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ :=
    theorem_7_5_case_2_chain hS hθ hd₀ hr₀ hno
  exact ⟨Γ', T', d', r', hlift Γ' T' d' r' h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉⟩

end GraphMinor.GM12

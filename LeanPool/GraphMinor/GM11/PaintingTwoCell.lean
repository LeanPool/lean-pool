/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.PaintingFacts
public import LeanPool.GraphMinor.GM11.RadialTwoCell

/-!
# A radial drawing of a painting is 2-cell

Graph Minors XI, Section 3 (page 75): "$\Gamma'$ is 2-cell", for a 2-cell painting `Γ`.

Let `D` be the drawing of the boundaries of the cells, and `G` a radial drawing of `D` made from
`Γ'` by
adding a star in each cell. Let `s` be a region of `Γ'`, and let `e` be the cell in `s`. Each edge
`a` of
`D` in `e` has two regions of `D ∪ G` beside it. One lies inside the cell. Call the other one `f a`,
and
it lies outside the cell (`exists_inner_outer`). Now `s` is the interior of `e`, with each `a` and
each
`f a` added. We add them one at a time with `glue_open_discs`.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval Metric

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

omit [ConnectedSpace S] in
/-- Beside a point of an edge, the two regions and the edge fill an open set. -/
theorem exists_open_sides (hS : IsClosedSurface S) {F : Drawing S} {a u f : Set S} (ha : a ∈ F.E)
    (hu : u ∈ F.R) (hf : f ∈ F.R) (hne : u ≠ f) (hau : a ⊆ closure u) (haf : a ⊆ closure f) :
    ∃ y ∈ a, ∃ O, IsOpen O ∧ y ∈ O ∧ O ⊆ u ∪ f ∪ a := by
  obtain ⟨γ, hγ, h0, h1, hinj, hγe⟩ := exists_edge_param F ha
  let t₀ : I := ⟨1 / 2, by norm_num, by norm_num⟩
  have ht₀ : t₀ ∈ Ioo (0 : I) 1 := ⟨show (0 : ℝ) < 1 / 2 by norm_num, show
    (1 / 2 : ℝ) < 1 by norm_num⟩
  obtain ⟨G, c₁, c₂, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉, g₁₀, g₁₁⟩ :=
    exists_edge_chart hS F ha hγ h0 h1 hinj hγe ht₀ ht₀.1 ht₀.2
  have c : IsEdgeChart F γ t₀ G c₁ c₂ := ⟨g₁, g₂, g₄, g₅, g₇, g₈, g₉, g₁₀, g₁₁⟩
  have hy : γ t₀ ∈ a := hγe ▸ mem_image_of_mem γ ht₀
  have hsub : γ '' Ioo c₁ c₂ ⊆ a := by
    rw [← hγe]
    refine image_mono fun t ht => ⟨?_, ?_⟩
    · exact g₃.trans ht.1
    · exact ht.2.trans g₆
  have hsd : G '' IsEdgeChart.lower ⊆ u ∪ f ∧ G '' IsEdgeChart.upper ⊆ u ∪ f := by
    rcases c.sides hS hu hf hne (hau hy) (haf hy) with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact ⟨h₁.trans subset_union_left, h₂.trans subset_union_right⟩
    · exact ⟨h₁.trans subset_union_right, h₂.trans subset_union_left⟩
  refine ⟨γ t₀, hy, G '' ball 0 1, c.isOpen_image_ball hS, ⟨0, by simp, g₇⟩, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  rcases IsEdgeChart.cases_of_closedBall (ball_subset_closedBall hz) with h | h | h
  · exact Or.inl (hsd.1 ⟨z, h, rfl⟩)
  · exact Or.inr (hsub (g₉ ▸ mem_image_of_mem G ⟨hz, h⟩))
  · exact Or.inl (hsd.2 ⟨z, h, rfl⟩)

omit [ConnectedSpace S] in
/-- Let `a` be an edge of `F` in the boundary of a closed disc `N`, and let `u, f` be the regions
beside
`a`. If each of `u, f` lies in the interior of `N` or misses `N`, then one of them does each. -/
theorem exists_inner_outer (hS : IsClosedSurface S) {F : Drawing S} {a u f N : Set S} (ha : a ∈ F.E)
    (hu : u ∈ F.R) (hf : f ∈ F.R) (hne : u ≠ f) (hau : a ⊆ closure u) (haf : a ⊆ closure f)
    (hN : IsClosedDisc N) (haN : a ⊆ discBd N) (hcu : u ⊆ discInt N ∨ Disjoint u N)
    (hcf : f ⊆ discInt N ∨ Disjoint f N) :
    (u ⊆ discInt N ∧ Disjoint f N) ∨ (f ⊆ discInt N ∧ Disjoint u N) := by
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  obtain ⟨y, hy, O, hO, hyO, hsub⟩ := exists_open_sides hS ha hu hf hne hau haf
  rcases hcu with h₁ | h₁ <;> rcases hcf with h₂ | h₂
  · have hsN : O ⊆ N := hsub.trans (union_subset (union_subset (h₁.trans sdiff_subset)
      (h₂.trans sdiff_subset)) (haN.trans (discBd_subset N)))
    have hin : y ∈ interior N := mem_interior.mpr ⟨O, hsN, hO, hyO⟩
    rw [interior_eq_sdiff_discBd hS hN] at hin
    exact (hin.2 (haN hy)).elim
  · exact Or.inl ⟨h₁, h₂⟩
  · exact Or.inr ⟨h₂, h₁⟩
  · have hcl : y ∈ closure (discInt N) := hN.subset_closure_discInt (discBd_subset N (haN hy))
    obtain ⟨x, hxO, hxN⟩ := mem_closure_iff.mp hcl O hO hyO
    rcases hsub hxO with (h | h) | h
    · exact (disjoint_left.mp h₁ h hxN.1).elim
    · exact (disjoint_left.mp h₂ h hxN.1).elim
    · exact (hxN.2 (haN h)).elim

variable {Γ : Painting S} {Γ' : Drawing S}

/-- If a 2-cell painting has a cell with no vertex, each region of its radial drawing is an open
disc.
In this case the cell and a closed disc in the region fill the surface, so the surface is a sphere,
and
`Γ'` is one point. -/
theorem region_isOpenDisc_of_free_cell (hS : IsClosedSurface S)
    (hrad : PreRad (PaintingOrDrawing.painting Γ) Γ') {e : Set S} (he : e ∈ Γ.E)
    (hfree : closure e ∩ Γ.V = ∅) {s : Set S} (hs : s ∈ Γ'.R) : IsOpenDisc s := by
  classical
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hP : ∀ r ∈ Γ.R, IsOpenDisc r := hrad.1.2
  obtain ⟨hV, hE⟩ := free_cell hS hP he hfree
  have hEΓ' : Γ'.E = ∅ := by
    refine eq_empty_of_forall_notMem fun f hf => ?_
    obtain ⟨v, hv, -⟩ := hrad.2.2.2.2.2.1 f hf
    have hv' : v ∈ Γ.V := hv
    rw [hV] at hv'
    exact hv'
  have hU'V : Γ'.U = Γ'.V := by
    rw [Γ'.U_eq, hEΓ']
    simp
  have hN : IsClosedDisc (closure e) := Cell.isClosedDisc_closure he
  have hUΓ : closure e ⊆ Γ.U := closure_subset_cell_U hrad he
  have hNV' : Disjoint (closure e) Γ'.V := by
    refine disjoint_left.mpr fun x hx hxV => ?_
    have h₁ : x ∈ Γ.U ∩ Γ'.U := ⟨hUΓ hx, Γ'.V_subset_U hxV⟩
    have h₂ : Γ.U ∩ Γ'.U = Γ.V := hrad.2.1
    have h₃ := h₂ ▸ h₁
    rw [hV] at h₃
    exact h₃
  have hW : IsOpen Γ'.Vᶜ := Γ'.finite_V.isClosed.isOpen_compl
  obtain ⟨D, hD, hND, hDsub⟩ := exists_disc_around hman hN (fun x _ => hS.2.2 x) hW
    (fun x hx h => disjoint_left.mp hNV' (discBd_subset _ hx) h)
  have hDV : Disjoint D Γ'.V := by
    refine disjoint_left.mpr fun x hx hxV => ?_
    rcases hDsub hx with h | h
    · exact disjoint_left.mp hNV' h hxV
    · exact h hxV
  have hF := hD.isOArc_discBd
  have hUe : Γ.U ⊆ closure e := by
    intro x hx
    rcases Cell.mem_V_or_cell Γ hx with h | ⟨f, hf, hxf⟩
    · rw [hV] at h
      exact h.elim
    · have hf' : f ∈ Γ.E := hf
      rw [hE] at hf'
      exact subset_closure (hf' ▸ hxf)
  have hbU : Disjoint (discBd D) Γ.U := by
    refine disjoint_left.mpr fun x hx hxU => ?_
    exact (hND (hUe hxU)).2 hx
  have hbne : (discBd D).Nonempty := by
    obtain ⟨φ⟩ := hF
    exact ⟨_, (φ 1).2⟩
  obtain ⟨y, hy⟩ := hbne
  have hUclosed : IsClosed Γ.U := cell_isClosed_U hrad
  obtain ⟨r, hr, hyr⟩ : ∃ r ∈ Γ.R, y ∈ r := by
    have hy' : y ∈ univ \ Γ.U := ⟨trivial, disjoint_left.mp hbU hy⟩
    exact ⟨_, ⟨y, hy', rfl⟩, mem_connectedComponentIn hy'⟩
  have hrU : Disjoint r Γ.U := by
    obtain ⟨z, hz, rfl⟩ := hr
    exact disjoint_left.mpr fun x hx h => (connectedComponentIn_subset _ _ hx).2 h
  have hbconn : IsPreconnected (discBd D) := by
    obtain ⟨φ⟩ := id hF
    have : discBd D = range fun z => (φ z).1 := by
      ext y
      exact ⟨fun hy => ⟨φ.symm ⟨y, hy⟩, by simp⟩, by rintro ⟨z, rfl⟩; exact (φ z).2⟩
    rw [this]
    exact isPreconnected_range (by fun_prop)
  have hbr : discBd D ⊆ r := by
    obtain ⟨z, hz, rfl⟩ := hr
    rw [connectedComponentIn_eq hyr]
    exact hbconn.subset_connectedComponentIn hy fun x hx => ⟨trivial, disjoint_left.mp hbU hx⟩
  obtain ⟨Δ, hΔr, hΔ, hb⟩ := exists_disc_in_openDisc (hP r hr) hF hbr
  have hne : D ≠ Δ := by
    rintro rfl
    obtain ⟨x, hx⟩ := he.1
    exact disjoint_left.mp hrU (hΔr (hND (subset_closure hx)).1) (hUΓ (subset_closure hx))
  have hcov := cover_of_discBd_eq hS hD hΔ hb.symm hne
  have hsph : IsSphere S := by
    by_contra hsph
    exact hne (eq_of_discBd_eq (IsClosedSurface.isSurface hS) hsph hD hΔ hb.symm)
  -- All vertices of `Γ'` are the vertex of `r`.
  obtain ⟨c, ⟨hc, hcV⟩, -⟩ := hrad.2.2.2.1 r hr
  have hc' : c ∈ r := hc
  have hcV' : c ∈ Γ'.V := hcV
  have hall : ∀ w ∈ Γ'.V, w = c := by
    intro w hw
    have hwr : w ∈ r := by
      rcases (hcov ▸ mem_univ w : w ∈ D ∪ Δ) with h | h
      · exact (disjoint_left.mp hDV h hw).elim
      · exact hΔr h
    exact (hrad.2.2.2.1 r hr).unique ⟨hwr, hw⟩ ⟨hc', hcV'⟩
  have hcs : c ∉ s := fun h => region_subset hs h (Γ'.V_subset_U hcV')
  have hdisc := open_disc S s hS inferInstance
    ⟨region_nonempty hs, region_isPreconnected hs⟩ (region_isOpen hs) ?_
  · rcases hdisc with ⟨-, h⟩ | h
    · exact (hcs (h ▸ mem_univ c)).elim
    · exact h
  intro F hFs hFO
  obtain ⟨Δ₁, Δ₂, -, h₁, h₂, hb₁, hb₂, hc₁, hc₂, -, -⟩ := sphere_disc S hsph F hFO
  have hcF : c ∉ F := fun h => region_subset hs (hFs h) (Γ'.V_subset_U hcV')
  have key : ∀ A : Set S, IsClosedDisc A → discBd A = F → c ∉ A →
      ∃ Δ : Set S, Δ ⊆ s ∧ IsClosedDisc Δ ∧ discBd Δ = F := by
    intro A hA hbA hcA
    obtain ⟨z, hz⟩ : F.Nonempty := by
      obtain ⟨φ⟩ := hFO
      exact ⟨_, (φ 1).2⟩
    have hconn : IsPreconnected A := by
      obtain ⟨h, g, c'⟩ := hA.exists_isChart
      rw [← c'.g_closedBall]
      exact (convex_closedBall _ _).isPreconnected.image _ c'.gc
    have hdis : Disjoint A Γ'.U := by
      rw [hU'V]
      exact disjoint_left.mpr fun x hx hxV => hcA (hall x hxV ▸ hx)
    exact ⟨A, subset_region hs hconn hdis (discBd_subset A (hbA.symm.subset hz)) (hFs hz), hA, hbA⟩
  by_cases hc₁' : c ∈ Δ₁
  · refine key Δ₂ h₂ hb₂ fun hc₂' => hcF ?_
    exact hc₂ ▸ (⟨hc₁', hc₂'⟩ : c ∈ Δ₁ ∩ Δ₂)
  · exact key Δ₁ h₁ hb₁ hc₁'

private theorem adjacent_regions_of_cell_edge (hS : IsClosedSurface S)
    (hrad : PreRad (PaintingOrDrawing.painting Γ) Γ') {D G : Drawing S}
    (hU : IsClosed Γ.U) (hDU : D.U = Γ.V ∪ ⋃ e ∈ Γ.E, discBd (closure e))
    (hDV : D.V = Γ.V) (hDR : D.R = Γ.R ∪ cellInt '' Γ.E)
    (hrG : PreRad (PaintingOrDrawing.drawing D) G)
    (hmG : RadMax (PaintingOrDrawing.drawing D) G) {e : Set S} (he : e ∈ Γ.E) :
    let F := radialUnion hrG
    ∀ a ∈ D.E, a ⊆ e → ∃ u ∈ F.R, ∃ f ∈ F.R, u ≠ f ∧ a ⊆ closure u ∧ a ⊆ closure f ∧
      u ⊆ cellInt e ∧ Disjoint f (closure e) ∧ ∀ p ∈ G.R, a ⊆ p → p = u ∪ f ∪ a := by
  intro F
  have hFE : ∀ {a}, a ∈ D.E → a ∈ F.E := fun {a} ha => by
    change a ∈ (radialUnion hrG).E
    rw [radialUnion_E]
    exact Or.inl ha
  have hN : IsClosedDisc (closure e) := Cell.isClosedDisc_closure he
  have hNU : closure e ⊆ Γ.U := closure_subset_cell_U hrad he
  intro a ha hae
  have hadis : Disjoint a G.U := edge_disjoint hrG ha
  obtain ⟨y, hy⟩ := ha.1
  obtain ⟨p, hp, hyp⟩ := exists_region_of_notMem (disjoint_left.mp hadis hy)
  have hap : a ⊆ p := subset_region hp ha.2.2.1.isConnected.isPreconnected hadis hy hyp
  have hDE : D.E.Nonempty := ⟨a, ha⟩
  obtain ⟨u, hu, f, hf, hne, hau, haf, hpeq⟩ := region_eq_two_faces hrG hS hmG hDE hp ha hap
  have haN : a ⊆ discBd (closure e) := by
    intro x hx
    have hxU := (ha.2.1 hx).1
    rw [hDU] at hxU
    rcases hxU with h | h
    · exact ((ha.2.1 hx).2 (hDV.symm.subset h)).elim
    · obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp h
      have hxV : x ∉ Γ.V := fun h' => (ha.2.1 hx).2 (hDV.symm.subset h')
      have hxg' : x ∈ g := Cell.closure_sdiff_V hS hU hg ▸
        (⟨discBd_subset _ hxg, hxV⟩ : x ∈ closure g \ Γ.V)
      rwa [arcComponent_eq hg he hxg' (hae hx)] at hxg
  have hclass : ∀ w ∈ F.R, a ⊆ closure w → w ⊆ discInt (closure e) ∨ Disjoint w (closure e) := by
    intro w hw haw
    obtain ⟨r, hr, hwr⟩ := exists_region_of_sub hrG hw
    have hr' : r ∈ D.R := hr
    rw [hDR] at hr'
    rcases hr' with h | ⟨g, hg, rfl⟩
    · refine Or.inr (disjoint_left.mpr fun x hx hxe => ?_)
      obtain ⟨z, hz, rfl⟩ := h
      exact (connectedComponentIn_subset _ _ (hwr hx)).2 (hNU hxe)
    · have hyg : y ∈ closure g :=
        closure_minimal (hwr.trans sdiff_subset) isClosed_closure (haw hy)
      have hyV : y ∉ Γ.V := fun h' => (ha.2.1 hy).2 (hDV.symm.subset h')
      have hyg' : y ∈ g := Cell.closure_sdiff_V hS hU hg ▸ (⟨hyg, hyV⟩ : y ∈ closure g \ Γ.V)
      obtain rfl := arcComponent_eq hg he hyg' (hae hy)
      exact Or.inl hwr
  rcases exists_inner_outer hS (hFE ha) hu hf hne hau haf hN haN (hclass u hu hau)
    (hclass f hf haf) with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · refine ⟨u, hu, f, hf, hne, hau, haf, h₁, h₂, fun p' hp' hap' => ?_⟩
    obtain rfl := region_eq_of_mem hp' hp (hap' hy) hyp
    exact hpeq
  · refine ⟨f, hf, u, hu, hne.symm, haf, hau, h₁, h₂, fun p' hp' hap' => ?_⟩
    obtain rfl := region_eq_of_mem hp' hp (hap' hy) hyp
    rw [hpeq, union_comm u f]

/-- **Each region of a radial drawing of a 2-cell painting is an open disc.** -/
theorem painting_region_isOpenDisc (hS : IsClosedSurface S)
    (hrad : PreRad (PaintingOrDrawing.painting Γ) Γ') (hmax : RadMax (PaintingOrDrawing.painting Γ)
      Γ')
    {s : Set S} (hs : s ∈ Γ'.R) : IsOpenDisc s := by
  classical
  by_cases hfree : ∃ e ∈ Γ.E, closure e ∩ Γ.V = ∅
  · obtain ⟨e, he, hf⟩ := hfree
    exact region_isOpenDisc_of_free_cell hS hrad he hf hs
  have hv : ∀ e ∈ Γ.E, (closure e ∩ Γ.V).Nonempty := fun e he => by
    by_contra h
    exact hfree ⟨e, he, not_nonempty_iff_eq_empty.mp h⟩
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hneS : Nonempty S := ⟨(region_nonempty hs).some⟩
  have hU : IsClosed Γ.U := cell_isClosed_U hrad
  obtain ⟨c, K, hst⟩ := exists_cellStars (Γ := Γ)
  obtain ⟨G, hG⟩ := exists_star_drawing hrad hst hS
  have hbd : ∀ e ∈ Γ.E, Γ.V ∩ closure e ⊆ discBd (closure e) := fun e he x hx =>
    Cell.closure_inter_V_subset hS he ⟨hx.2, hx.1⟩
  obtain ⟨D, hDU, hDV⟩ := exists_boundary_drawing hS hU Γ.finite_V Subset.rfl fun e he => by
    obtain ⟨x, hx, hxV⟩ := hv e he
    exact ⟨x, hxV, hbd e he ⟨hxV, hx⟩⟩
  have hDR : D.R = Γ.R ∪ cellInt '' Γ.E :=
    boundary_R hS hrad.1.2 Subset.rfl Γ.V_subset_U hbd hDU
  have hGrad := radial_of_stars hrad hst hS hG hDU hDV hv hmax hDR
  have hrG : PreRad (PaintingOrDrawing.drawing D) G := ⟨hGrad.1, hGrad.2.1⟩
  have hmG := hGrad.2.2
  by_cases hE : (PaintingOrDrawing.painting Γ).E.Nonempty
  swap
  · -- With no cell, `G` is `Γ'`.
    have hE₀ : Γ.E = ∅ := not_nonempty_iff_eq_empty.mp hE
    have hUU : G.U = Γ'.U := by
      rw [hG.U]
      have : cellPairs Γ = ∅ := by
        refine eq_empty_of_forall_notMem fun t ht => ?_
        have h := ht.1
        rw [hE₀] at h
        exact h
      simp [this]
    have hsG : s ∈ G.R := by
      change s ∈ componentsIn (univ \ G.U)
      rw [hUU]
      exact hs
    exact radial_region_isOpenDisc hrG hS hmG hsG
  obtain ⟨hex, huniq, -⟩ := regionFacts_of_painting hrad hmax hS hE
  obtain ⟨e, he, hes⟩ := hex s hs
  have he' : e ∈ Γ.E := he
  have hhuniq : ∀ f ∈ Γ.E, f ⊆ s → f = e := fun f hf hfs => huniq s hs f hf e he hfs hes
  have hedge : ∀ x ∈ D.U, x ∉ D.V → ∃ a ∈ D.E, x ∈ a := fun x hx hn =>
    exists_mem_arcComponent ⟨hx, hn⟩
  have hDUsub : D.U ⊆ Γ.U := D_U_subset hrad hDU
  have hUU' : Γ.U ∩ Γ'.U = Γ.V := hrad.2.1
  have hcellV : ∀ e ∈ Γ.E, Disjoint e Γ.V := fun e he =>
    disjoint_left.mpr fun x hx h => (he.2.1 hx).2 h
  have hcell : ∀ a ∈ D.E, ∃ e ∈ Γ.E, a ⊆ e := by
    intro a ha
    have hsub : a ⊆ Γ.U \ Γ.V := fun x hx => by
      have h := ha.2.1 hx
      exact ⟨hDUsub h.1, fun hV => h.2 (hDV.symm.subset hV)⟩
    obtain ⟨x, hx⟩ := ha.1
    obtain ⟨e, he, hxe⟩ := exists_mem_arcComponent (hsub hx)
    refine ⟨e, he, ?_⟩
    have hu : IsPathConnected (e ∪ a) := he.2.2.1.union ha.2.2.1 ⟨x, hxe, hx⟩
    have := he.2.2.2 _ (union_subset he.2.1 hsub) hu subset_union_left
    exact this ▸ subset_union_right
  have hcellU' : ∀ e ∈ Γ.E, Disjoint e Γ'.U := fun e he =>
    disjoint_left.mpr fun x hx h => disjoint_left.mp (hcellV e he) hx
      (hUU'.subset ⟨(he.2.1 hx).1, h⟩)
  have hG_U : Γ'.U ⊆ G.U := fun x hx => hG.U ▸ Or.inl hx
  have hstarU : G.U ⊆ Γ'.U ∪ Γ.U := by
    rw [hG.U]
    refine union_subset_union_right _ (iUnion₂_subset fun t ht => ?_)
    have hb := Cell.closure_inter_V_subset hS ht.1 ⟨ht.2.2, ht.2.1⟩
    exact (star_subset_closure hst ht.1 hb).trans (closure_subset_cell_U hrad ht.1)
  let F : Drawing S := radialUnion hrG
  have hFU : F.U = D.U ∪ G.U := rfl
  have hFE : ∀ {a}, a ∈ D.E → a ∈ F.E := fun {a} ha => by
    change a ∈ (radialUnion hrG).E
    rw [radialUnion_E]
    exact Or.inl ha
  have hFdis : ∀ {p}, p ∈ F.R → Disjoint p G.U := fun {p} hp =>
    disjoint_left.mpr fun x hx h => region_subset hp hx (Or.inr h)
  have hN : IsClosedDisc (closure e) := Cell.isClosedDisc_closure he'
  have hNU : closure e ⊆ Γ.U := closure_subset_cell_U hrad he'
  have hDint : Disjoint (cellInt e) D.U := cellInt_disjoint_D hrad hS hDU he'
  have hside := adjacent_regions_of_cell_edge hS hrad hU hDU hDV hDR hrG hmG he'
  choose! u hu f hf hne hcu hcf hui hfo hpe using hside
  let M : Set (Set S) → Set S := fun A => cellInt e ∪ ⋃ a ∈ A, (a ∪ f a)
  let Aall : Set (Set S) := {a | a ∈ D.E ∧ a ⊆ e}
  have hAll : Aall.Finite := D.finite_edges.subset fun _ h => h.1
  have hfdis : ∀ a ∈ Aall, ∀ b ∈ Aall, a ≠ b → Disjoint (f a) (f b) := by
    intro a ha b hb hab
    refine disjoint_left.mpr fun x hxa hxb => hab ?_
    have hff := region_eq_of_mem (hf a ha.1 ha.2) (hf b hb.1 hb.2) hxa hxb
    obtain ⟨e₀, -, -, hun, -⟩ := face_edge hrG hS hmG ⟨a, ha.1⟩ (hf a ha.1 ha.2)
    exact (hun a ha.1 (hcf a ha.1 ha.2)).trans (hun b hb.1 (hff ▸ hcf b hb.1 hb.2)).symm
  have hregU : ∀ {r b}, r ∈ F.R → b ∈ D.E → Disjoint r (closure b) := fun {r b} hr hb =>
    disjoint_left.mpr fun x hx h => region_subset hr hx (Or.inl (D.closure_subset_U hb h))
  have key : ∀ A : Set (Set S), A.Finite → A ⊆ Aall → IsOpenDisc (M A) := by
    intro A hA
    induction A, hA using Set.Finite.induction_on with
    | empty =>
      intro _
      have h₀ : M ∅ = cellInt e := by simp [M]
      rw [h₀]
      exact isOpenDisc_interior hS hN
    | @insert b A hbA hfin ih =>
      intro hsub
      have hA' : A ⊆ Aall := fun x hx => hsub (mem_insert_of_mem _ hx)
      have hb : b ∈ Aall := hsub (mem_insert _ _)
      have hih := ih hA'
      have heq : M (insert b A) = M A ∪ f b ∪ b := by
        ext x
        simp only [M, biUnion_insert, mem_union]
        tauto
      rw [heq]
      have hdisM : Disjoint (M A) (f b) := by
        refine disjoint_left.mpr ?_
        rintro x (hx | hx) hxb
        · exact disjoint_left.mp (hfo b hb.1 hb.2) hxb hx.1
        · obtain ⟨a, ha, hx⟩ := mem_iUnion₂.mp hx
          rcases hx with hx | hx
          · exact region_subset (hf b hb.1 hb.2) hxb (Or.inl ((hA' ha).1.2.1 hx).1)
          · exact disjoint_left.mp (hfdis a (hA' ha) b hb (fun h => hbA (h ▸ ha))) hx hxb
      have hdiscl : Disjoint (M A) (closure b) := by
        refine disjoint_left.mpr ?_
        rintro x (hx | hx) hxb
        · exact disjoint_left.mp hDint hx (D.closure_subset_U hb.1 hxb)
        · obtain ⟨a, ha, hx⟩ := mem_iUnion₂.mp hx
          rcases hx with hx | hx
          · have hab : a ≠ b := fun h => hbA (h ▸ ha)
            have hxV : x ∉ D.V := ((hA' ha).1.2.1 hx).2
            have hxb' : x ∈ b := D.closure_diff_V hb.1 ▸ (⟨hxb, hxV⟩ : x ∈ closure b \ D.V)
            exact hab (D.edge_eq_of_mem (hA' ha).1 hb.1 hx hxb')
          · exact disjoint_left.mp (hregU (hf a (hA' ha).1 (hA' ha).2) hb.1) hx hxb
      exact glue_open_discs hS (hFE hb.1) (hu b hb.1 hb.2) (hf b hb.1 hb.2) (hne b hb.1 hb.2)
        (hcu b hb.1 hb.2) (hcf b hb.1 hb.2) ((hui b hb.1 hb.2).trans subset_union_left) Subset.rfl
        hih (face_isOpenDisc hrG hS hmG (hf b hb.1 hb.2)) hdisM hdiscl
        (hregU (hf b hb.1 hb.2) hb.1)
  have heq : s = M Aall := by
    have hes' : cellInt e ⊆ e := fun x hx => by
      have hxV : x ∉ Γ.V := disjoint_left.mp (cellInt_disjoint_V hS he') hx
      exact Cell.closure_sdiff_V hS hU he' ▸ (⟨hx.1, hxV⟩ : x ∈ closure e \ Γ.V)
    have hbdpart : ∀ x ∈ e, x ∈ M Aall := by
      intro x hx
      by_cases hxb : x ∈ discBd (closure e)
      · have hxV : x ∉ Γ.V := disjoint_left.mp (hcellV e he') hx
        have hxD : x ∈ D.U := by
          rw [hDU]
          exact Or.inr (mem_iUnion₂.mpr ⟨e, he', hxb⟩)
        obtain ⟨b, hb, hxb'⟩ := hedge x hxD (hDV ▸ hxV)
        obtain ⟨e', he'', hbe'⟩ := hcell b hb
        obtain rfl : e' = e := arcComponent_eq he'' he' (hbe' hxb') hx
        exact Or.inr (mem_iUnion₂.mpr ⟨b, ⟨hb, hbe'⟩, Or.inl hxb'⟩)
      · exact Or.inl ⟨subset_closure hx, hxb⟩
    apply subset_antisymm
    · intro x hx
      have hxU' : x ∉ Γ'.U := region_subset hs hx
      by_cases hxU : x ∈ Γ.U
      · rcases Cell.mem_V_or_cell Γ hxU with h | ⟨g, hg, hxg⟩
        · exact (hxU' (Γ'.V_subset_U (hrad.2.2.1 h))).elim
        · have hgs : g ⊆ s :=
            subset_region hs hg.2.2.1.isConnected.isPreconnected (hcellU' g hg) hxg hx
          exact hbdpart x (hhuniq g hg hgs ▸ hxg)
      · have hxG : x ∉ G.U := fun h => (hstarU h).elim hxU' hxU
        obtain ⟨p, hp, hxp⟩ := exists_region_of_notMem hxG
        have hps : p ⊆ s := subset_region hs (region_isPreconnected hp)
          (disjoint_left.mpr fun y hy h => region_subset hp hy (hG_U h)) hxp hx
        have hDE : D.E.Nonempty := by
          obtain ⟨e₀, he₀⟩ := hE
          have hinf := infinite_of_isOArc (Cell.isClosedDisc_closure he₀).isOArc_discBd
          obtain ⟨y, hy, hn⟩ := hinf.exists_notMem_finite Γ.finite_V
          have hyD : y ∈ D.U := by
            rw [hDU]
            exact Or.inr (mem_iUnion₂.mpr ⟨e₀, he₀, hy⟩)
          obtain ⟨a, ha, -⟩ := hedge y hyD (hDV ▸ hn)
          exact ⟨a, ha⟩
        obtain ⟨hf₁, -, -⟩ := regionFacts_of_radial hrG hS hmG hDE
        obtain ⟨a, ha, hap⟩ := hf₁ p hp
        have ha' : a ∈ D.E := ha
        obtain ⟨g, hg, hag⟩ := hcell a ha'
        obtain ⟨z, hz⟩ := ha'.1
        have hgs : g ⊆ s := subset_region hs hg.2.2.1.isConnected.isPreconnected (hcellU' g hg)
          (hag hz) (hps (hap hz))
        obtain rfl := hhuniq g hg hgs
        have hmem : x ∈ u a ∪ f a ∪ a := hpe a ha' hag p hp hap ▸ hxp
        rcases hmem with (h | h) | h
        · exact Or.inl (hui a ha' hag h)
        · exact Or.inr (mem_iUnion₂.mpr ⟨a, ⟨ha', hag⟩, Or.inr h⟩)
        · exact Or.inr (mem_iUnion₂.mpr ⟨a, ⟨ha', hag⟩, Or.inl h⟩)
    · refine union_subset (hes'.trans hes) (iUnion₂_subset fun a ha => union_subset
      (ha.2.trans hes) ?_)
      obtain ⟨y, hy⟩ := (show a ∈ D.E from ha.1).1
      have hmeet : (f a ∩ s).Nonempty := by
        obtain ⟨z, hzs, hzf⟩ := mem_closure_iff.mp (hcf a ha.1 ha.2 hy) s (region_isOpen hs) (hes
          (ha.2 hy))
        exact ⟨z, hzf, hzs⟩
      obtain ⟨z, hzf, hzs⟩ := hmeet
      exact subset_region hs (region_isPreconnected (hf a ha.1 ha.2))
        (disjoint_left.mpr fun y hy h => disjoint_left.mp (hFdis (hf a ha.1 ha.2)) hy
          (hG_U h)) hzf hzs
  exact heq ▸ key Aall hAll Subset.rfl

/-- **A radial drawing of a 2-cell painting or drawing is 2-cell.** Graph Minors XI, Section 3
(page 75). -/
theorem radial_isTwoCell (hS : IsClosedSurface S) {Γ : PaintingOrDrawing S} {Γ' : Drawing S}
    (h : Γ.IsRadialDrawing Γ') : (PaintingOrDrawing.drawing Γ').IsTwoCell := by
  refine ⟨inferInstance, fun s hs => ?_⟩
  have hs' : s ∈ Γ'.R := hs
  cases Γ with
  | painting Γ => exact painting_region_isOpenDisc hS ⟨h.1, h.2.1⟩ h.2.2 hs'
  | drawing Γ => exact radial_region_isOpenDisc ⟨h.1, h.2.1⟩ hS h.2.2 hs'

end GraphMinor.GM11

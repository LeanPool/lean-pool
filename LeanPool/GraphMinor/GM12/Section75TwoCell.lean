/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2FreeSectorChord
public import LeanPool.GraphMinor.GM12.Section2SectorSpoke
public import LeanPool.GraphMinor.GM12.Section2SpokePaths
public import LeanPool.GraphMinor.GM12.Section74BaseCellularity
import LeanPool.GraphMinor.GM12.Section74CornerEdges
import LeanPool.GraphMinor.GM12.Section74FiniteGluing
import LeanPool.GraphMinor.GM12.Section74LeafTwoCell
import LeanPool.GraphMinor.GM12.Section74VertexWalk
import LeanPool.GraphMinor.GM12.Section78
import LeanPool.GraphMinor.GM11.Section4b
import LeanPool.GraphMinor.GM11.RadialCorners

/-!
# Two-cellularity of `Γ₁ \ r*` in Case 2 of XII (7.5)

In Case 2 of Graph Minors XII (7.5) (page 265), after the selected-disc reduction of Case 1,
`no_parallel_spokes_at_region_hub` ensures that the hub `v = r* ∈ V(Γ₁)` of `r ∈ R(Γ)` in the common
radial drawing `K` of `Γ` and its dual `Γ₁` has at most one spoke in `K` to each vertex `c ∈ V(Γ)`
(the hub in `K` of a region of `Γ₁`).

By radial maximality of `K` as a radial drawing of `Γ₁`, each sector `Q k` of `Γ₁` at `v` is entered
by a spoke of `K` at `v` whose other end is the hub `c ∈ ρ k ∩ V(K)`. Uniqueness of spokes at `v`
therefore implies that `ρ` is injective at `v`, and the sector-gluing argument of
`Section74BaseCellularity.lean` yields that `Γ₂ = deleteVertices Γ₁ {v}` is a 2-cell drawing.
-/

@[expose] public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM10 GM14 unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- Every sector `Q k` at a vertex `v ∈ V(Γ)` of a 2-cell drawing `Γ` with radial drawing `K` is
entered by a spoke of `K` at `v` whose other end is the hub `c ∈ ρ k ∩ V(K)`. -/
theorem exists_sector_spoke_of_radial (hS : IsClosedSurface S)
    {Γ K : Drawing S} (hrad : PreRad (.drawing Γ) K)
    (hmax : RadMax (.drawing Γ) K) (hE : Γ.E.Nonempty)
    {γ η : Set S → I → S} (hη : EdgePar K η) {v : S} (hv : v ∈ Γ.V)
    {next : halfEdges Γ γ v → halfEdges Γ γ v}
    {ρ P Q : halfEdges Γ γ v → Set S} {W : Set S}
    {τ : halfEdges Γ γ v → I}
    (hsec : IsSectors Γ γ v next ρ P W Q τ) (k : halfEdges Γ γ v)
    {c : S} (hc : c ∈ ρ k) (hcV : c ∈ K.V) :
    ∃ (i : halfEdges K η v) (ε : I), 0 < ε ∧
      closure i.val.1 ∩ K.V = {v, c} ∧
      ∀ t, 0 < t → t ≤ ε → spoke η i.val t ∈ Q k \ discBd (Q k) := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hr : ρ k ∈ Γ.R := hsec.corners.region k
  have hcover : W \ Γ.U ⊆ ⋃ j, Q j := fun x hx => by
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hsec.cover hx)
    exact mem_iUnion.mpr ⟨j, hsec.subQ j hj⟩
  have hoff : ∀ i : halfEdges K η v, ∀ t : I, 0 < t → spoke η i.val t ∉ Γ.U := by
    intro i t ht hΓ
    have he : spoke η i.val t ∈ i.val.1 := spoke_mem_edge hη i.property.1 ht
    have hKV : spoke η i.val t ∈ K.V := radial_V hrad
      (radial_inter hrad ▸ ⟨hΓ, K.closure_subset_U i.property.1 (subset_closure he)⟩)
    exact edge_notMem_V i.property.1 he hKV
  have hregion : (Q k \ discBd (Q k)) ∩ W ⊆ ρ k := by
    rintro z ⟨⟨hzQ, hzbd⟩, hzW⟩
    exact hsec.sub k (hsec.inside k ⟨⟨hzW, hzQ⟩, hzbd⟩)
  rcases sector_spoke_or_free_neighbourhood hη hv (radial_V hrad hv) hsec hcover hoff k with
    ⟨i, ε, hε, hεQ⟩ | ⟨O, hO, hvO, hfree⟩
  · have hgi : Continuous (spoke η i.val) :=
      (hη.cont i.val.1 i.property.1).comp (continuous_halfPar i.val.2)
    have hgi0 : spoke η i.val 0 = v := by rw [spoke_zero]; exact i.property.2
    obtain ⟨δ, hδ, hδε, hδW⟩ := exists_pos_le hgi hsec.isOpen (hgi0.symm ▸ hsec.mem) hε
    have hδr : spoke η i.val δ ∈ ρ k := hregion ⟨hεQ δ hδ hδε, hδW δ le_rfl⟩
    have hcap := spoke_ends_of_halfEdge_point hS hrad hη hv i hr hc hcV hδ hδr
    exact ⟨i, δ, hδ, hcap, fun t ht htδ => hεQ t ht (htδ.trans hδε)⟩
  · exfalso
    obtain ⟨e, he, hcap, u, hu, hui, hu0, _, _, ⟨N, hN, hvN, hNgerm⟩, Δ, hΔ, hΔr, hbd⟩ :=
      exists_parallel_spoke_at_free_sector hS hrad hmax hE hv hsec k hc hcV hO hvO hfree
    have hb : discBd Δ = closure e ∪ range u :=
      (IsClosedDisc.frontier_eq_discBd hS hΔ).symm.trans ((subBd_eq_frontier Δ).symm.trans hbd)
    have hve : v ∈ closure e := (hcap.superset (Or.inl rfl)).1
    have hvb : v ∈ discBd Δ := hb ▸ Or.inl hve
    have hΔfree : Disjoint (Δ \ discBd Δ) Γ.U := by
      refine disjoint_left.mpr fun y hy hyU => ?_
      rcases hΔr hy.1 with hyr | hyv
      · exact region_subset hr hyr hyU
      · exact hy.2 (hyv.symm ▸ hvb)
    have hWN : IsOpen (W ∩ N) := hsec.isOpen.inter hN
    obtain ⟨A, W₀, hW₀, hvW₀, hAc, hAΔ, hAb, hAX, -, hclA⟩ :=
      exists_half_nbhd hΔ hWN.isClosed_compl hvb (fun h' => h' ⟨hsec.mem, hvN⟩)
    have hAW : ∀ y ∈ A, y ∈ W ∩ N := fun y hy => by
      by_contra hn
      exact disjoint_left.mp hAX hy hn
    have hAU : ∀ y ∈ A, y ∉ Γ.U := fun y hy hyU =>
      disjoint_left.mp hΔfree ⟨hAΔ hy, disjoint_left.mp hAb hy⟩ hyU
    have hQd := hsec.disc k
    have hAfr : Disjoint A (frontier (Q k)) := by
      rw [IsClosedDisc.frontier_eq_discBd hS hQd]
      exact disjoint_left.mpr fun y hy hyb => hAU y hy (hsec.bdU k ⟨(hAW y hy).1, hyb⟩)
    obtain ⟨t, ht, hutW⟩ := exists_pos_mem hu (hW₀.inter hN) (by rw [hu0]; exact ⟨hvW₀, hvN⟩)
    have hzcl : u t ∈ closure A := hclA ⟨hutW.1, hb ▸ Or.inr ⟨t, rfl⟩⟩
    obtain ⟨hzQ, hzb⟩ := hNgerm t ht hutW.2
    have hzint : u t ∈ interior (Q k) := by
      have hnf : u t ∉ frontier (Q k) := by
        rwa [IsClosedDisc.frontier_eq_discBd hS hQd]
      by_contra hni
      exact hnf ⟨subset_closure hzQ, hni⟩
    have hAQ : A ⊆ Q k := by
      rcases subset_or_disjoint_of_frontier hQd.isClosed hAc hAfr with h' | h'
      · exact h'
      · obtain ⟨y, hyI, hyA⟩ := mem_closure_iff.mp hzcl _ isOpen_interior hzint
        exact (disjoint_left.mp h' hyA (interior_subset hyI)).elim
    have hclQ : closure A ⊆ Q k := closure_minimal hAQ hQd.isClosed
    obtain ⟨b, hbv⟩ := exists_end_eq hη he (radial_V hrad hv) hve
    let i : halfEdges K η v := ⟨(e, b), he, hbv⟩
    have hgi : Continuous (spoke η i.val) :=
      (hη.cont i.val.1 i.property.1).comp (continuous_halfPar i.val.2)
    have hgi0 : spoke η i.val 0 = v := by rw [spoke_zero]; exact hbv
    obtain ⟨s', hs', hsW⟩ := exists_pos_mem hgi (hW₀.inter hO) (by rw [hgi0]; exact ⟨hvW₀, hvO⟩)
    have hmem : spoke η i.val s' ∈ closure e := subset_closure (spoke_mem_edge hη i.property.1 hs')
    have hsQ : spoke η i.val s' ∈ Q k := hclQ (hclA ⟨hsW.1, hb ▸ Or.inl hmem⟩)
    have hsK : spoke η i.val s' ∈ K.U := K.closure_subset_U he hmem
    exact disjoint_left.mp hfree ⟨⟨hsW.2, hsQ⟩, hoff i s' hs'⟩ hsK

/-- If `K` is a radial drawing of `Γ` and has at most one spoke between `v ∈ V(Γ)` and any hub
`c ∈ V(K)`, then the corner-region map `ρ` of any sector system of `Γ` at `v` is injective. -/
theorem corner_regions_injective_of_unique_spokes (hS : IsClosedSurface S)
    {Γ K : Drawing S} (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    (hE : Γ.E.Nonempty) {v : S} (hv : v ∈ Γ.V)
    (hunique : ∀ g ∈ K.E, ∀ h ∈ K.E, ∀ c : S, c ∈ K.V →
      closure g ∩ K.V = {v, c} → closure h ∩ K.V = {v, c} → g = h)
    {γ : Set S → I → S}
    {next : halfEdges Γ γ v → halfEdges Γ γ v}
    {ρ P Q : halfEdges Γ γ v → Set S} {W : Set S} {τ : halfEdges Γ γ v → I}
    (hsec : IsSectors Γ γ v next ρ P W Q τ) : Function.Injective ρ := by
  intro k k' hρ
  by_contra hkk
  have : Nonempty S := ⟨v⟩
  obtain ⟨η, hη⟩ := exists_edgePar K
  have hrad : PreRad (.drawing Γ) K := ⟨hK.1, hK.2.1⟩
  have hmax : RadMax (.drawing Γ) K := hK.2.2
  have hr : ρ k ∈ Γ.R := hsec.corners.region k
  obtain ⟨c, ⟨hc, hcV⟩, -⟩ := hrad.2.2.2.1 (ρ k) hr
  obtain ⟨i, ε, hε, hcap, hεQ⟩ :=
    exists_sector_spoke_of_radial hS hrad hmax hE hη hv hsec k hc hcV
  obtain ⟨i', ε', hε', hcap', hε'Q⟩ :=
    exists_sector_spoke_of_radial hS hrad hmax hE hη hv hsec k' (hρ ▸ hc) hcV
  have heq_edge : i.val.1 = i'.val.1 :=
    hunique i.val.1 i.property.1 i'.val.1 i'.property.1 c hcV hcap hcap'
  have hvc : c ≠ v := fun h => region_subset hr (h ▸ hc) (Γ.V_subset_U hv)
  have hcap_cv : closure i.val.1 ∩ K.V = {c, v} := hcap.trans (pair_comm v c)
  have hii' : i = i' :=
    (halfedge_eq_of_same_nonloop_edge hη i i' hvc hcap_cv heq_edge.symm).symm
  subst hii'
  let t : I := min ε ε'
  have ht : 0 < t := lt_min hε hε'
  have htQ : spoke η i.val t ∈ Q k := (hεQ t ht (min_le_left _ _)).1
  have htQ' : spoke η i.val t ∈ Q k' := (hε'Q t ht (min_le_right _ _)).1
  have htΓ : spoke η i.val t ∈ Γ.U := hsec.inter k k' hkk ⟨htQ, htQ'⟩
  have he : spoke η i.val t ∈ i.val.1 := spoke_mem_edge hη i.property.1 ht
  have hKV : spoke η i.val t ∈ K.V := radial_V hrad
    (radial_inter hrad ▸ ⟨htΓ, K.closure_subset_U i.property.1 (subset_closure he)⟩)
  exact edge_notMem_V i.property.1 he hKV

/-- If `Γ` is a 2-cell drawing with radial drawing `K`, `v ∈ V(Γ)` is not the only vertex of `Γ`,
and `K` has at most one spoke from `v` to each hub `c ∈ V(K)`, then `deleteVertices Γ {v}` is a
2-cell drawing. -/
theorem isTwoCell_delete_vertex_of_unique_spokes (hS : IsClosedSurface S)
    {Γ K : Drawing S} (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {v : S} (hv : v ∈ Γ.V) (hother : ∃ w ∈ Γ.V, w ≠ v)
    (hunique : ∀ g ∈ K.E, ∀ h ∈ K.E, ∀ c : S, c ∈ K.V →
      closure g ∩ K.V = {v, c} → closure h ∩ K.V = {v, c} → g = h) :
    (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsTwoCell := by
  obtain ⟨w, hw, hwv⟩ := hother
  classical
  have hpre : IsPreconnected Γ.U := isPreconnected_U_of_isTwoCell hS hK.1
  obtain ⟨W⟩ := exists_walk_of_isPreconnected_U hpre hv hw
  obtain ⟨P, hP, _, _⟩ := GraphWalk.exists_isSimple W
  have hex : ∃ (e : Set S) (u : S), e ∈ Γ.E ∧ u ∈ Γ.V ∧ u ≠ v ∧
      closure e ∩ Γ.V = {u, v} ∧ IsLineWithEnds (closure e) u v := by
    cases P with
    | nil _ => exact (hwv rfl).elim
    | @cons _ u _ e hl R =>
      have hvu : v ≠ u := by
        intro heq
        exact (List.nodup_cons.mp hP).1
          ((congrArg (fun x => x ∈ R.support) heq.symm).mp R.start_mem_support)
      exact ⟨e, u, hl.1, hl.2.2.1, hvu.symm, hl.2.2.2.trans (pair_comm v u),
        Surface.IsLineWithEnds.symm (isLine_closure hl.1 hvu hl.2.2.2)⟩
  obtain ⟨e, u, he, _, huv, hcap, hLine⟩ := hex
  have hE : Γ.E.Nonempty := ⟨e, he⟩
  let : Nonempty S := ⟨v⟩
  obtain ⟨γ, hγ⟩ := exists_edgePar Γ
  have hvCap : v ∈ closure e ∩ Γ.V := hcap.symm ▸ (Or.inr rfl : v ∈ ({u, v} : Set S))
  obtain ⟨b, hb⟩ := exists_end_eq hγ he hv hvCap.1
  let keep : halfEdges Γ γ v := ⟨(e, b), he, hb⟩
  have hkeep : ∀ k : halfEdges Γ γ v, k.1.1 = keep.1.1 → k = keep :=
    fun k hk => halfedge_eq_of_same_nonloop_edge hγ keep k huv hcap hk
  by_cases h2 : 2 ≤ Nat.card (halfEdges Γ γ v)
  · obtain ⟨next, ρ, P, W, Q, τ, hsec⟩ := exists_sectors hS Γ hγ hv h2
    have hρ := corner_regions_injective_of_unique_spokes hS hK hE hv hunique hsec
    have hEdges := corner_edges_injective_of_single_fibre hsec.corners hρ keep hkeep
    exact isTwoCell_delete_vertex_of_corner_data hS hK.1 hγ hv hsec.corners hρ hEdges keep huv hcap
      hLine
  · let α := halfEdges Γ γ v
    let : Finite α := (finite_halfEdges Γ γ v).to_subtype
    let : Nonempty α := ⟨keep⟩
    have hpos : 0 < Nat.card α := Nat.card_pos
    have hOne : Nat.card α = 1 := by change ¬ 2 ≤ Nat.card α at h2; omega
    let : Subsingleton α := (Nat.card_eq_one_iff_unique.mp hOne).1
    have hleaf : ∀ f ∈ Γ.E, f ≠ e → v ∉ closure f := by
      intro f hf hfe hvf
      obtain ⟨c, hc⟩ := exists_end_eq hγ hf hv hvf
      let k : α := ⟨(f, c), hf, hc⟩
      have hk : k = keep := Subsingleton.elim _ _
      exact hfe (congrArg (fun j : α => j.1.1) hk)
    exact isTwoCell_delete_leaf hS hK.1 he huv hcap hLine hleaf

end GraphMinor.GM12

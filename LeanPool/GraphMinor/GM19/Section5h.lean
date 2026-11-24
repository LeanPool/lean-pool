/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section5g

/-!
# Graph Minors XIX, proof of (5.4): from the edges of `Γ₁` back to the edges of `Γ`

Here we match the edges of the painting `Γ₁ = ψ⁻¹(Γ) ∩ Σ₁` with the edges of `Γ`. A lifted edge has
this form by
definition. A border edge of `Γ₁` over `bd(Σ)` maps onto a border edge of `Γ`, and it is the whole
of the preimage
of this edge in `Σ₁`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

variable {S S₁ : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace S₁] [T2Space S₁]


variable {Γ : Painting S} {K : Drawing S} {ψ : S₁ → S}

namespace PullData

variable (d : PullData Γ K ψ)
include d

omit [T2Space S] [T2Space S₁] in
/-- `U(K) ∩ bd(Σ) ⊆ V(K)`, because `bd(Σ) ⊆ U(Γ)`. -/
theorem K_bd : K.U ∩ bd S ⊆ K.V := fun _ hx ↦ (d.inter ⟨Γ.bd_subset hx.2, hx.1⟩).2

omit [T2Space S] [T2Space S₁] in
/-- An arc of `bd(Σ₁) \ V₁` that has a point over `bd(Σ)` lies over `bd(Σ)`: its image is connected
in
`bd(Σ) ∪ U(K)`, and it misses `V(K)`, which holds `U(K) ∩ bd(Σ)`. -/
theorem image_arc_subset_bd {R : Set S₁} (hR : R ∈ arcComponentsIn (bd S₁ \ pullV Γ K ψ)) {x : S₁}
  (hxR : x ∈ R)
    (hb : ψ x ∈ bd S) : ψ '' R ⊆ bd S := by
  have hc := d.frag.continuous_ψ
  have hbc : IsClosed (bd S) := (cuff_statement S d.surface).1
  have hIc : IsPreconnected (ψ '' R) := hR.2.2.1.isConnected.isPreconnected.image _ hc.continuousOn
  have hoff : ∀ {w}, w ∈ R → ψ w ∉ K.V := fun hw hv ↦ (hR.2.1 hw).2 (Or.inr hv)
  have hcov : ψ '' R ⊆ (bd S) ∪ K.U := by
    rintro _ ⟨w, hw, rfl⟩
    exact d.frag.maps_bd (mem_image_of_mem ψ (hR.2.1 hw).1)
  by_contra hn
  obtain ⟨_, ⟨z, hRz, rfl⟩, hzn⟩ := not_subset.mp hn
  have hzK : ψ z ∈ K.U := (hcov (mem_image_of_mem ψ hRz)).resolve_left hzn
  obtain ⟨_, ⟨w, hw, rfl⟩, hw₁, hw₂⟩ := isPreconnected_closed_iff.mp hIc
    (bd S) K.U hbc K.isClosed_U hcov
    ⟨ψ x, mem_image_of_mem ψ hxR, hb⟩ ⟨ψ z, mem_image_of_mem ψ hRz, hzK⟩
  exact hoff hw (d.K_bd ⟨hw₂, hw₁⟩)

omit [T2Space S] in
/-- Near a point of an arc of `bd(Σ₁) \ V₁`, the boundary is the arc. -/
theorem exists_nhds_arc {R : Set S₁} (hR : R ∈ arcComponentsIn (bd S₁ \ pullV Γ K ψ)) {x : S₁}
  (hxR : x ∈ R) :
    ∃ W ∈ 𝓝 x, ∀ z ∈ W, z ∈ bd S₁ → z ∈ R := by
  have hS₁ := d.frag.isSurface
  obtain ⟨W, hW, hWs⟩ := exists_nhds_arcs hS₁ d.finite_pullV d.two x
  refine ⟨W, hW, fun z hz hzb ↦ ?_⟩
  rcases hWs z hz hzb with rfl | ⟨R', hR', hzR', hxc⟩
  · exact hxR
  · have hx' := mem_of_mem_closure_arc hS₁ d.finite_pullV d.two hR' hxc (hR.2.1 hxR).2
    exact arcComp_eq_of_mem hR hR' hxR hx' ▸ hzR'

omit [T2Space S] in
/-- A point of `bd(Σ₁)` off `V₁`, over `bd(Σ)`: the boundary near it maps into `bd(Σ)`. -/
theorem exists_nhds_bd {x : S₁} (hx : x ∈ bd S₁ \ pullV Γ K ψ) (hb : ψ x ∈ bd S) :
    ∃ W ∈ 𝓝 x, ∀ z ∈ W, z ∈ bd S₁ → ψ z ∈ bd S ∧ z ∉ pullV Γ K ψ := by
  obtain ⟨R, hR, hsub⟩ := exists_arcComp_superset (isPathConnected_singleton x)
    (singleton_subset_iff.mpr hx)
  have hxR : x ∈ R := hsub rfl
  obtain ⟨W, hW, hWs⟩ := d.exists_nhds_arc hR hxR
  refine ⟨W, hW, fun z hz hzb ↦ ?_⟩
  have hRz := hWs z hz hzb
  exact ⟨d.image_arc_subset_bd hR hxR hb (mem_image_of_mem ψ hRz), (hR.2.1 hRz).2⟩

/-- `ψ` is one-to-one on the points of `bd(Σ₁)` off `V₁` over `bd(Σ)`. -/
theorem eq_of_image_eq_bd {x x' : S₁} (hx : x ∈ bd S₁ \ pullV Γ K ψ) (hx' : x' ∈ bd S₁ \ pullV Γ K
  ψ)
    (hb : ψ x ∈ bd S) (heq : ψ x = ψ x') : x = x' := by
  obtain ⟨W, hW, hWs⟩ := d.exists_nhds_bd hx hb
  obtain ⟨W', hW', hWs'⟩ := d.exists_nhds_bd hx' (heq ▸ hb)
  exact d.frag.eq_of_image_eq d.surface hx.1 hx'.1 hb hW hW' (fun z hz hzb ↦ (hWs z hz hzb).1)
    (fun z hz hzb ↦ (hWs' z hz hzb).1) heq

/-- A border edge of `Γ₁` over `bd(Σ)` maps onto an edge of `Γ`, and it is the whole of the preimage
of this edge. -/
theorem image_border_edge {e₁ : Set S₁} (he₁ : e₁ ∈ arcComponentsIn (bd S₁ \ pullV Γ K ψ))
    {x₀ : S₁} (hx₀ : x₀ ∈ e₁) (hb₀ : ψ x₀ ∈ bd S) :
    ψ '' e₁ ∈ Γ.E ∧ ψ ⁻¹' (ψ '' e₁) = e₁ := by
  have hS₁ := d.frag.isSurface
  have hS := d.surface
  have hman := hS.2.2
  have hc := d.frag.continuous_ψ
  have hcl := d.frag.isClosedMap
  have : CompactSpace S₁ := hS₁.1
  have hbc : IsClosed (bd S) := (cuff_statement S hS).1
  have hbd := d.image_arc_subset_bd he₁ hx₀ hb₀
  have hsubU : ψ '' e₁ ⊆ Γ.U \ Γ.V := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨Γ.bd_subset (hbd (mem_image_of_mem ψ hx)), fun hv ↦ (he₁.2.1 hx).2 (Or.inl hv)⟩
  obtain ⟨e, he, hsub⟩ := exists_arcComp_superset (he₁.2.2.1.image hc) hsubU
  have heb : e ⊆ bd S := (Γ.border_edge e he ⟨ψ x₀, hsub (mem_image_of_mem ψ hx₀),
    hbd (mem_image_of_mem ψ hx₀)⟩).2
  have heK : ∀ {z}, z ∈ e → z ∉ K.U := fun hz hK ↦
    Γ.disjoint_V he hz (d.inter ⟨he.2.1 hz |>.1, hK⟩).1
  have hpre : ∀ {x}, ψ x ∈ e → x ∈ bd S₁ \ pullV Γ K ψ := by
    intro x hx
    refine ⟨d.mem_bd_of_notMem_R (Or.inl (heb hx)), ?_⟩
    rintro (hv | hv)
    · exact Γ.disjoint_V he hx hv
    · exact heK hx (K.V_subset_U hv)
  -- `ψ(e₁)` is open in `e`
  have hopen : ∀ x ∈ e₁, ∃ O, IsOpen O ∧ ψ x ∈ O ∧ O ∩ e ⊆ ψ '' e₁ := by
    intro x hx
    obtain ⟨W, hW, hWs⟩ := d.exists_nhds_arc he₁ hx
    obtain ⟨W', hW', hsubW⟩ := d.exists_nhds_bd (he₁.2.1 hx) (hbd (mem_image_of_mem ψ hx))
    obtain ⟨A, hA, hAs, hf⟩ := d.frag.exists_nhds_fibre x (Filter.inter_mem hW hW')
    obtain ⟨C, hC, hCc, hCs⟩ := exists_mem_nhds_isClosed_subset hA
    obtain ⟨N, hN, hs⟩ := d.frag.local_fill hS (he₁.2.1 hx).1 (hbd (mem_image_of_mem ψ hx)) hC
      (fun z hz ↦ (hsubW z (hAs (hCs hz)).2 · |>.1)) (fun z hz ↦ hf z (hCs hz))
    refine ⟨interior N, isOpen_interior, mem_interior_iff_mem_nhds.mpr hN, ?_⟩
    rintro z ⟨hzN, hze⟩
    have hzcl := (isConnectedNear_compl_bd (hman z) (heb hze)).2
    have hzcl' := isOpen_interior.inter_closure ⟨hzN, hzcl⟩
    have hsub' : interior N ∩ (bd S)ᶜ ⊆ ψ '' C := fun y hy ↦ by
      obtain ⟨c, hc', rfl⟩ := hs ⟨hy.2, interior_subset hy.1⟩
      exact mem_image_of_mem ψ hc'.1
    have hz' := closure_minimal hsub' (hcl _ hCc) hzcl'
    obtain ⟨c, hcC, rfl⟩ := hz'
    exact mem_image_of_mem ψ (hWs c (hAs (hCs hcC)).1 (hpre hze).1)
  -- `ψ(e₁)` is closed in `e`
  have hclosed : closure (ψ '' e₁) ∩ e ⊆ ψ '' e₁ := by
    rintro z ⟨hz, hze⟩
    rw [hcl.closure_image_eq_of_continuous hc] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact mem_image_of_mem ψ (mem_of_mem_closure_arc hS₁ d.finite_pullV d.two he₁ hx (hpre hze).2)
  have hesub : e ⊆ ψ '' e₁ := by
    choose! O hOo hOm hOs using hopen
    intro z hz
    by_contra hzn
    obtain ⟨w, hwe, hwO, hwc⟩ := he.2.2.1.isConnected.isPreconnected (⋃ x ∈ e₁, O x)
      (closure (ψ '' e₁))ᶜ (isOpen_biUnion hOo) isClosed_closure.isOpen_compl
      (fun w hw ↦ by
        by_cases hwc : w ∈ closure (ψ '' e₁)
        · obtain ⟨x, hx, rfl⟩ := hclosed ⟨hwc, hw⟩
          exact Or.inl (mem_biUnion hx (hOm x hx))
        · exact Or.inr hwc)
      ⟨ψ x₀, hsub (mem_image_of_mem ψ hx₀), mem_biUnion hx₀ (hOm x₀ hx₀)⟩
      ⟨z, hz, fun hzc ↦ hzn (hclosed ⟨hzc, hz⟩)⟩
    obtain ⟨x, hx, hwx⟩ := mem_iUnion₂.mp hwO
    exact hwc (subset_closure (hOs x hx ⟨hwx, hwe⟩))
  have heq : ψ '' e₁ = e := Subset.antisymm hsub hesub
  refine ⟨heq ▸ he, ?_⟩
  ext x
  constructor
  · rintro ⟨x', hx', hxx⟩
    rw [d.eq_of_image_eq_bd (hpre (heq ▸ ⟨x', hx', hxx⟩)) (he₁.2.1 hx') (by
      rw [← hxx]; exact hbd (mem_image_of_mem ψ hx')) hxx.symm]
    exact hx'
  · exact fun hx ↦ ⟨x, hx, rfl⟩

/-- The preimage of a border edge of `Γ` that meets `Σ₁` is a border edge of `Γ₁`. -/
theorem preimage_border_edge {e : Set S} (he : e ∈ Γ.E) (hb : e ⊆ bd S) {x : S₁} (hx : ψ x ∈ e) :
    ψ ⁻¹' e ∈ arcComponentsIn (bd S₁ \ pullV Γ K ψ) ∧ ψ '' (ψ ⁻¹' e) = e := by
  have hxm : x ∈ bd S₁ \ pullV Γ K ψ := by
    refine ⟨d.mem_bd_of_notMem_R (Or.inl (hb hx)), ?_⟩
    rintro (hv | hv)
    · exact Γ.disjoint_V he hx hv
    · exact Γ.disjoint_V he hx (d.inter ⟨he.2.1 hx |>.1, K.V_subset_U hv⟩).1
  obtain ⟨R, hR, hsub⟩ := exists_arcComp_superset (isPathConnected_singleton x)
    (singleton_subset_iff.mpr hxm)
  have hxR : x ∈ R := hsub rfl
  obtain ⟨hRE, hRpre⟩ := d.image_border_edge hR hxR (hb hx)
  have hRe : ψ '' R = e := arcComp_eq_of_mem hRE he (mem_image_of_mem ψ hxR) hx
  rw [← hRe, hRpre]
  exact ⟨hR, rfl⟩

end PullData

end GraphMinor.GM19

/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section12g
public import LeanPool.GraphMinor.GM11.RadialBasics
public import LeanPool.GraphMinor.Surface.AddCrosscap

/-!
# Graph Minors XIX, Section 12: circuits in a wheel

`Γ*` has no two edges with the same ends (`no_parallel`): such edges bound a disc in a region of
`Γ`, by internal
3-connectivity, or since a cuff bounds a disc, and the last condition on a radial drawing forbids
this disc. So at a vertex
of `R*` a circuit of `Γ*` has two different neighbours, and the second condition in the definition
of a wheel applies.
This gives `IsWheelHubOfRadius.ins_subset_of_vertices`: a short circuit with its vertices of `Γ` in
a wheel has its
inside in the wheel. The proof of (12.4) uses this as "this subwalk remains within `W_x`".
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

namespace TangleDatum

/-- `Γ*` has no two edges with the same ends. -/
theorem no_parallel (D : TangleDatum cap χ) {g₁ g₂ : Set Shat} (hg₁ : g₁ ∈ D.rad.G.E)
  (hg₂ : g₂ ∈ D.rad.G.E)
    (hne : g₁ ≠ g₂) {v t : Shat} (hc₁ : closure g₁ ∩ D.rad.G.V = {v, t})
      (hc₂ : closure g₂ ∩ D.rad.G.V = {v, t})
    (hv : v ∈ D.P.Γ.hatV cap) : False := by
  classical
  have hT := cap.isClosedSurface
  have hS := χ.isSurface
  have : ConnectedSpace Shat := cap.connected
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  set G := D.rad.G with hG
  have ht : t ∈ D.rad.Rstar := other_end_mem_Rstar D hg₁ hc₁ hv
  have hvt : v ≠ t := fun h ↦ ht.2 (h ▸ hv)
  have hline : ∀ {g : Set Shat}, g ∈ G.E → closure g ∩ G.V = {v, t} → IsLineWithEnds
    (closure g) v t := by
    intro g hg hc
    rcases G.edge_cond g hg with ⟨a, b, -, hab, hL⟩ | ⟨u, hu, -⟩
    · rw [hc] at hab
      have hv' : v ∈ ({a, b} : Set Shat) := hab ▸ mem_insert _ _
      have ht' : t ∈ ({a, b} : Set Shat) := hab ▸ mem_insert_of_mem _ rfl
      rcases hv' with rfl | rfl
      · rcases ht' with rfl | rfl
        · exact absurd rfl hvt
        · exact hL
      · rcases ht' with rfl | rfl
        · exact GraphMinor.GM11.IsLineWithEnds.symm hL
        · exact absurd rfl hvt
    · rw [hc] at hu
      have hv' : v ∈ ({u} : Set Shat) := hu ▸ mem_insert _ _
      have ht' : t ∈ ({u} : Set Shat) := hu ▸ mem_insert_of_mem _ rfl
      exact absurd (hv'.trans ht'.symm) hvt
  have hL₁ := hline hg₁ hc₁
  have hL₂ := hline hg₂ hc₂
  have hsplit : ∀ {g : Set Shat} {x : Shat}, g ∈ G.E → closure g ∩ G.V = {v, t} → x ∈ closure g
    → x ∈ g ∨ x = v ∨ x = t := by
    intro g x hg hc hx
    rcases closure_edge_subset hg hx with h | h
    · exact .inl h
    · have : x ∈ closure g ∩ G.V := ⟨hx, h⟩
      rw [hc] at this
      exact .inr this
  have hcap : closure g₁ ∩ closure g₂ ⊆ {v, t} := by
    rintro x ⟨h₁, h₂⟩
    rcases hsplit hg₁ hc₁ h₁ with h | h
    · rcases hsplit hg₂ hc₂ h₂ with h' | h'
      · exact absurd (G.edge_eq_of_mem hg₁ hg₂ h h') hne
      · exact h'
    · exact h
  have hO : IsOArc (closure g₁ ∪ closure g₂) := GM11.isOArc_union hL₁ hL₂ hcap
  set F₀ := closure g₁ ∪ closure g₂ with hF₀
  set r := D.rad.regionOf t with hr
  have hrm : r ∈ D.P.Γ.hatRegions cap := (D.rad.regionOf_mem ht).1
  have htr : t ∈ r := (D.rad.regionOf_mem ht).2
  have hmem : ∀ {g : Set Shat}, g ∈ G.E → closure g ∩ G.V = {v, t} → g ⊆ r := fun {g} hg hc ↦ by
    have : t ∈ closure g ∩ G.V := by
      rw [hc]
      exact .inr rfl
    exact edge_subset_regionOf D ht hg this.1
  have hF₀r : F₀ ⊆ r ∪ {v} := by
    rintro x (h | h)
    · rcases hsplit hg₁ hc₁ h with h' | rfl | rfl
      · exact .inl (hmem hg₁ hc₁ h')
      · exact .inr rfl
      · exact .inl htr
    · rcases hsplit hg₂ hc₂ h with h' | rfl | rfl
      · exact .inl (hmem hg₂ hc₂ h')
      · exact .inr rfl
      · exact .inl htr
  have hclosed : ∃ Δ, IsClosedDisc Δ ∧ Δ ⊆ r ∪ {v} ∧ discBd Δ = F₀ := by
    rcases hatRegion_cases cap D.P.Γ hrm with hsub | ⟨Θ, hΘ, hreq⟩
    · -- the region lies in `Σ`
      obtain ⟨b, hb, rfl⟩ := hv
      have hrU : Disjoint r (D.P.Γ.hatU cap) := by
        rw [disjoint_left]
        exact fun x hx ↦ connectedComponentIn_subset _ _ hx
      have hF₀range : F₀ ⊆ range cap.emb := fun x hx ↦ by
        rcases hF₀r hx with h | rfl
        · exact hsub h
        · exact mem_range_self b
      let F₁ : Set S := cap.emb ⁻¹' F₀
      have hF₁im : cap.emb '' F₁ = F₀ := image_preimage_eq_iff.mpr hF₀range
      have hF₁O : IsOArc F₁ := isOArc_of_image cap.isEmbedding (hF₁im ▸ hO)
      have hF₁U : ∀ {x}, x ∈ F₁ → x ∈ D.P.Γ.U → x = b := fun {x} hx hxU ↦ by
        rcases hF₀r hx with h | h
        · exact absurd (mem_image_of_mem _ hxU) (disjoint_left.mp hrU h)
        · exact cap.isEmbedding.injective h
      have hbsub : F₁ ∩ bd S ⊆ {b} := fun x hx ↦ hF₁U hx.1 (D.P.Γ.bd_subset hx.2)
      have hVsub : F₁ ∩ D.P.Γ.V ⊆ {b} := fun x hx ↦ hF₁U hx.1 (D.P.Γ.V_subset hx.2)
      have hn₁ := ncard_le_ncard hbsub (toFinite _)
      have hn₂ := ncard_le_ncard hVsub (toFinite _)
      rw [ncard_singleton] at hn₁ hn₂
      obtain ⟨Δ₁, hΔ₁, hΔ₁b, hΔ₁V⟩ := D.P.fits.internally_three_connected.2 F₁ hF₁O
        (fun x hx ↦ (hF₁U hx.1 hx.2) ▸ hb) ((finite_singleton b).subset hbsub) (by omega)
      obtain ⟨hE, hEb⟩ := isClosedDisc_image hΔ₁ cap.isEmbedding
      have hEb' : discBd (cap.emb '' Δ₁) = F₀ := by rw [hEb, hΔ₁b, hF₁im]
      obtain ⟨Sk, hSk⟩ := exists_isSkHat hS cap D.P.Γ
      have hintU : Disjoint (discInt (cap.emb '' Δ₁)) (D.P.Γ.hatU cap) := by
        rw [disjoint_left]
        rintro _ ⟨⟨x, hxΔ, rfl⟩, hxb⟩ ⟨x', hx', hxx⟩
        obtain rfl := cap.isEmbedding.injective hxx
        rw [hEb'] at hxb
        have hxF : x' ∉ F₁ := hxb
        have hxV : x' ∉ D.P.Γ.V := fun h ↦ hxF (hΔ₁V ⟨hxΔ, h⟩)
        obtain ⟨c, hc, hxc⟩ := exists_arcComp_superset (F := D.P.Γ.U \ D.P.Γ.V)
          (isPathConnected_singleton x') (singleton_subset_iff.2 ⟨hx', hxV⟩)
        have hxc' : x' ∈ c := hxc rfl
        have hcdis : Disjoint (cap.emb '' c) (discBd (cap.emb '' Δ₁)) := by
          rw [hEb', disjoint_left]
          rintro _ ⟨y, hy, rfl⟩ hyF
          have := hF₁U (x := y) hyF (hc.2.1 hy).1
          exact (hc.2.1 hy).2 (this ▸ hb)
        have hin : cap.emb '' c ⊆ discInt (cap.emb '' Δ₁) := by
          rcases hE.side hman (hc.2.2.1.image
            cap.isEmbedding.continuous).isConnected.isPreconnected hcdis with h | h
          · exact h
          · exact absurd (mem_image_of_mem _ hxΔ) (disjoint_left.mp h (mem_image_of_mem _ hxc'))
        have htil : tilde c ⊆ {b} := by
          intro a ha
          have hcl : cap.emb a ∈ closure (cap.emb '' c) :=
            image_closure_subset_closure_image cap.isEmbedding.continuous (mem_image_of_mem _ ha.1)
          obtain ⟨a', ha', haa⟩ := closure_minimal (hin.trans sdiff_subset) hE.isClosed hcl
          obtain rfl := cap.isEmbedding.injective haa
          exact hF₁U (hΔ₁V ⟨ha', D.P.Γ.tilde_subset_V hc ha⟩) (D.P.Γ.V_subset
            (D.P.Γ.tilde_subset_V hc ha))
        have hn := ncard_le_ncard htil (toFinite _)
        rw [ncard_singleton] at hn
        rcases D.P.Γ.size_cases hc with h | h <;> omega
      obtain ⟨p, hp⟩ := hg₁.1
      have hpr := hmem hg₁ hc₁ hp
      have hpb : p ∈ discBd (cap.emb '' Δ₁) := by
        rw [hEb']
        exact .inl (subset_closure hp)
      have hpcl := hE.subset_closure_discInt (Surface.discBd_subset _ hpb)
      obtain ⟨y, hy₁, hy₂⟩ := mem_closure_iff.mp hpcl _ (isOpen_regionOf D ht) hpr
      have hRr := hSk.hatRegion_mem_R hrm
      have hdis : Disjoint (discInt (cap.emb '' Δ₁)) Sk.U := by
        rw [disjoint_left]
        intro z hz hzU
        rw [hSk.hU] at hzU
        exact disjoint_left.mp hintU hz (image_mono D.P.Γ.skU_subset hzU)
      have hsubr : discInt (cap.emb '' Δ₁) ⊆ r := subset_region hRr hE.isPreconnected_discInt hdis
        hy₂ hy₁
      refine ⟨cap.emb '' Δ₁, hE, fun x hx ↦ ?_, hEb'⟩
      by_cases hxF : x ∈ F₀
      · exact hF₀r hxF
      · exact .inl (hsubr ⟨hx, by rwa [hEb']⟩)
    · -- the region is a pasted disc
      have hcd := cap.cuffDisc_closedDisc Θ hΘ
      have hsubc : F₀ ⊆ closure (cap.cuffDisc Θ) := by
        rw [← hreq]
        refine hF₀r.trans (union_subset subset_closure ?_)
        rw [singleton_subset_iff]
        have : v ∈ closure g₁ ∩ G.V := by
          rw [hc₁]
          exact .inl rfl
        exact closure_mono (hmem hg₁ hc₁) this.1
      obtain ⟨Δ, ⟨h₁, h₂, h₃, -, h₄, -⟩, -⟩ := disc_oArc _ F₀ hcd hsubc hO
      refine ⟨Δ, h₂, fun x hx ↦ ?_, h₃⟩
      by_cases hxF : x ∈ F₀
      · exact hF₀r hxF
      · have hxb : x ∉ discBd (closure (cap.cuffDisc Θ)) := disjoint_left.mp h₄ ⟨hx, hxF⟩
        have hxc := h₁ hx
        rw [cap.closure_cuffDisc hΘ] at hxc
        rcases hxc with h | h
        · exact .inl (hreq ▸ h)
        · exact absurd (by rw [cap.cuffDisc_bd Θ hΘ]; exact h) hxb
  obtain ⟨Δ, hΔ, hΔr, hΔb⟩ := hclosed
  refine D.rad.isPreRadial.2.2.2.2.2 g₁ hg₁ g₂ hg₂ hne v hv r hrm t ⟨htr, ht.1⟩ hc₁ hc₂ ⟨Δ, hΔ,
    hΔr, ?_⟩
  rw [← subBd_eq_frontier', IsClosedDisc.frontier_eq_discBd hT hΔ, hΔb]

variable {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ}

omit [T2Space S] in
/-- An edge of `Γ*` lies in a wheel or misses it. -/
theorem IsWheelHubOfRadius.edge_side (h : D.IsWheelHubOfRadius W H ρ) {g : Set Shat}
  (hg : g ∈ D.rad.G.E) :
    g ⊆ W ∨ Disjoint g W := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  obtain ⟨F, hFc, hFs, hFU⟩ := exists_circuit_of_oArc h.is_disc.isOArc_discBd h.bd_sub
  by_cases hgF : g ∈ F.E
  · refine .inl (subset_closure.trans fun x hx ↦ Surface.discBd_subset W ?_)
    rw [← hFU, F.U_eq]
    exact .inr (mem_iUnion₂.mpr ⟨g, hgF, hx⟩)
  have hdis : Disjoint g (discBd W) := by
    rw [← hFU, disjoint_left]
    intro x hx hxF
    have hxV : x ∉ F.V := fun h' ↦ (hg.2.1 hx).2 (hFs.1 h')
    obtain ⟨f, hf, hxf⟩ := F.exists_edge_of_mem hxF hxV
    exact hgF (D.rad.G.edge_eq_of_mem hg (hFs.2 hf) hx hxf ▸ hf)
  rcases h.is_disc.side hman hg.2.2.1.isConnected.isPreconnected hdis with h' | h'
  · exact .inl (h'.trans sdiff_subset)
  · exact .inr h'

omit [T2Space S] in
omit [T2Space Shat] in
/-- A point of a wheel in the closure of an edge of `Γ*` that misses the wheel lies on the boundary
of the wheel. -/
theorem IsWheelHubOfRadius.mem_bd_of_closure (h : D.IsWheelHubOfRadius W H ρ) {g : Set Shat}
  (hdis : Disjoint g W)
    {p : Shat} (hpg : p ∈ closure g) (hpW : p ∈ W) : p ∈ discBd W := by
  have hT := cap.isClosedSurface
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  by_contra hn
  obtain ⟨y, hy₁, hy₂⟩ := mem_closure_iff.mp hpg _ (h.is_disc.isOpen_discInt hman) ⟨hpW, hn⟩
  exact disjoint_left.mp hdis hy₂ hy₁.1

omit [T2Space S] [T2Space Shat] in
/-- An end of an edge of `Γ*` that is not a vertex of `Γ` has a vertex of `Γ` as its other end. -/
theorem hatV_of_not_hatV (D : TangleDatum cap χ) {g : Set Shat} (hg : g ∈ D.rad.G.E) {p q : Shat}
    (hcap : closure g ∩ D.rad.G.V = {p, q}) (hp : p ∉ D.P.Γ.hatV cap) : q ∈ D.P.Γ.hatV cap := by
  obtain ⟨a, ha, t, ht, hcap'⟩ := D.rad.isPreRadial.2.2.2.2.1 g hg
  have : a ∈ closure g ∩ D.rad.G.V := by
    rw [hcap']
    exact .inl rfl
  rw [hcap] at this
  rcases this with rfl | rfl
  · exact absurd ha hp
  · exact ha

/-- A circuit of `Γ*` with its vertices of `Γ` in a wheel lies in the wheel. -/
theorem IsWheelHubOfRadius.U_subset_of_vertices (h : D.IsWheelHubOfRadius W H ρ) {C : Drawing Shat}
    (hC : Drawing.IsCircuitOf C D.rad.G) (hV : ∀ x ∈ C.V, x ∈ D.P.Γ.hatV cap → x ∈ W) : C.U ⊆ W
      := by
  classical
  have hS := χ.isSurface
  have hVall : ∀ x ∈ C.V, x ∈ W := by
    intro t ht
    by_cases hth : t ∈ D.P.Γ.hatV cap
    · exact hV t ht hth
    by_contra htW
    have htG := hC.1.1 ht
    -- another vertex of the circuit
    obtain ⟨b, hb, hbt⟩ : ∃ b ∈ C.V, b ≠ t := by
      obtain ⟨u, W₀, -, hpos, hCV, -⟩ := id hC.2
      cases W₀ with
      | nil h' => simp [GraphWalk.length] at hpos
      | @cons _ x _ e hl r =>
        have huC : u ∈ C.V := by rw [hCV]; exact .head _
        have hxC : x ∈ C.V := by
          rw [hCV]
          exact .tail _ r.start_mem_support
        have hlG : D.rad.G.toGraph.IsLink e u x :=
          ⟨hC.1.2 hl.1, hC.1.1 hl.2.1, hC.1.1 hl.2.2.1, by rw [← hC.1.closure_inter_V hl.1]; exact
            hl.2.2.2⟩
        by_cases hu : u = t
        · refine ⟨x, hxC, fun hxt ↦ ?_⟩
          have hq := hatV_of_not_hatV D hlG.1 hlG.2.2.2 (by rw [hu]; exact hth)
          exact hth (hxt ▸ hq)
        · exact ⟨u, huC, hu⟩
    obtain ⟨P, Q, hP, hQ, hPs, hQs, -, -, -, hdisj, -⟩ := hC.2.exists_two_paths ht hb hbt.symm
    obtain ⟨g₁, hg₁, w₁, hw₁, -, hc₁, -⟩ := first_step (hPs.trans hC.1) hbt.symm hP
    obtain ⟨g₂, hg₂, w₂, hw₂, -, hc₂, -⟩ := first_step (hQs.trans hC.1) hbt.symm hQ
    have hgne : g₁ ≠ g₂ := fun e ↦ disjoint_left.mp hdisj hg₁ (e ▸ hg₂)
    have hg₁G := hC.1.2 (hPs.2 hg₁)
    have hg₂G := hC.1.2 (hQs.2 hg₂)
    have hh₁ := hatV_of_not_hatV D hg₁G hc₁ hth
    have hh₂ := hatV_of_not_hatV D hg₂G hc₂ hth
    have hc₁' : closure g₁ ∩ D.rad.G.V = {w₁, t} := by rw [hc₁, pair_comm]
    have hc₂' : closure g₂ ∩ D.rad.G.V = {w₂, t} := by rw [hc₂, pair_comm]
    have hne : w₁ ≠ w₂ := fun e ↦ no_parallel D hg₁G hg₂G hgne hc₁' (e ▸ hc₂') hh₁
    have hW₁ := hV w₁ (hPs.1 hw₁) hh₁
    have hW₂ := hV w₂ (hQs.1 hw₂) hh₂
    have hend : ∀ {g w}, g ∈ D.rad.G.E → closure g ∩ D.rad.G.V = {t, w} → w ∈ W → w ∈ discBd W := by
      intro g w hg hc hwW
      have hm₁ : t ∈ closure g ∩ D.rad.G.V := by
        rw [hc]
        exact .inl rfl
      have hm₂ : w ∈ closure g ∩ D.rad.G.V := by
        rw [hc]
        exact .inr rfl
      rcases h.edge_side hg with h' | h'
      · exact absurd (closure_minimal h' h.is_disc.isClosed hm₁.1) htW
      · exact h.mem_bd_of_closure h' hm₂.1 hwW
    exact htW (h.two_nbrs_in_W t htG w₁ ⟨hh₁, hend hg₁G hc₁ hW₁⟩ w₂ ⟨hh₂, hend hg₂G hc₂ hW₂⟩ hne
      ⟨g₁, hg₁G, (closure_inter_V_eq_tilde hg₁G).symm.trans hc₁⟩ ⟨g₂, hg₂G,
        (closure_inter_V_eq_tilde hg₂G).symm.trans hc₂⟩)
  intro x hx
  by_cases hxV : x ∈ C.V
  · exact hVall x hxV
  obtain ⟨g, hg, hxg⟩ := C.exists_edge_of_mem hx hxV
  have hgG := hC.1.2 hg
  rcases h.edge_side hgG with h' | h'
  · exact h' hxg
  exfalso
  have hsub : tilde g ⊆ discBd W := by
    intro y hy
    have hyV : y ∈ closure g ∩ D.rad.G.V := closure_inter_V_eq_tilde hgG ▸ hy
    have hyC : y ∈ closure g ∩ C.V := (hC.1.closure_inter_V hg).symm ▸ hyV
    exact h.mem_bd_of_closure h' hyV.1 (hVall y hyC.2)
  exact disjoint_left.mp h' hxg (h.chord_in_W g hgG hsub hxg)

/-- A short circuit of `Γ*` with its vertices of `Γ` in a wheel has its inside in the wheel. -/
theorem IsWheelHubOfRadius.ins_subset_of_vertices (h : D.IsWheelHubOfRadius W H ρ) {C : Drawing
  Shat}
    (hC : Drawing.IsCircuitOf C D.rad.G) (hle : C.E.ncard ≤ 4 * ρ + 4)
      (hV : ∀ x ∈ C.V, x ∈ D.P.Γ.hatV cap → x ∈ W) :
    D.ins C ⊆ W :=
  h.ins_sub C hC hle (h.U_subset_of_vertices hC hV)

end TangleDatum

end GraphMinor.GM19

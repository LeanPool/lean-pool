/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section15k
public import LeanPool.GraphMinor.GM19.DiscTouch
public import LeanPool.GraphMinor.GM19.Section15h

/-!
# Graph Minors XIX, (15.2): the discs of (3.2)

Theorem (3.2) of Graph Minors XII takes a family of disjoint closed discs in `Σ̂`, each of which
meets `sk(Γ)` only in vertices on its boundary. The proof of (15.2) uses one disc for each cuff and
one disc for each internal edge `β(e)`.
It does not say what the discs are. Here we build them.

The disc of a cuff lies in the closed disc pasted onto the cuff, and it touches the cuff in `N(r*)`
(`exists_cuff_disc`). The disc of an edge of size 3 lies in the closed disc of the edge, and it
touches the boundary in the three ends
(`exists_three_disc`). The disc of an edge of size 2 lies on one side of the edge in a thin disc
around it (`exists_two_disc`). In each case the regions of `sk(Γ)` that meet the disc have an edge
of the right kind on their boundary, which is
what we need to bound distances. `IsAnchoredDisc` collects what we use.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 GraphMinor.GM14 Hypergraph

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {Γ : Painting S} {H : Drawing Shat}

/-- A closed disc of `Σ̂` that meets `sk(Γ)` only in vertices `N` on its boundary, such that every
region of `sk(Γ)` that meets the disc has `N` in its closure, and has on its boundary a side of the
edge `a`. -/
structure IsAnchoredDisc (cap : IsCappedSurface S Shat) (Γ : Painting S) (H : Drawing Shat)
  (Δ N : Set Shat) (a : Set S) : Prop where
  disc : IsClosedDisc Δ
  inter : H.U ∩ Δ = N
  sub_V : N ⊆ H.V
  sub_bd : N ⊆ discBd Δ
  anchor : ∀ r ∈ H.R, (r ∩ Δ).Nonempty → N ⊆ closure r ∧ ∃ f, Γ.IsSkEdgeIn f a
    ∧ cap.emb '' f ⊆ closure r

omit [T2Space S] in
/-- A cuff lies in `sk(Γ)`. -/
theorem Painting.subset_skU_of_mem_bd (Γ : Painting S) {y : S} (hy : y ∈ bd S) : y ∈ Γ.skU := by
  by_cases hyV : y ∈ Γ.V
  · exact .inl (.inl hyV)
  obtain ⟨c, hc, hyc⟩ := exists_arcComp_superset (F := Γ.U \ Γ.V) (isPathConnected_singleton y)
    (singleton_subset_iff.2 ⟨Γ.bd_subset hy, hyV⟩)
  have hyc' : y ∈ c := hyc rfl
  exact .inl (.inr (mem_iUnion₂.mpr ⟨c, ⟨hc, (Γ.border_edge c hc ⟨y, hyc', hy⟩).1⟩, hyc'⟩))

omit [T2Space S] in
/-- **The disc of a cuff.** -/
theorem exists_cuff_disc (hH : IsSkHat cap Γ H) {Θ : Set S}
  (hΘ : Θ ∈ cuffs S) {N₀ : Set S} (hN : N₀ ⊆ Θ ∩ Γ.V) (hfin : N₀.Finite)
    (hne : N₀.Nonempty) {a : Set S} (ha : a ∈ Γ.E)
    (haΘ : a ⊆ Θ) : ∃ Δ, Δ ⊆ closure (cap.cuffDisc Θ) ∧ IsAnchoredDisc cap Γ H Δ (cap.emb '' N₀) a
      := by
  classical
  have hT := cap.isClosedSurface
  have hman : ∀ x : Shat, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  have hinj := cap.isEmbedding.injective
  have hd := cap.cuffDisc_closedDisc Θ hΘ
  have hb := cap.cuffDisc_bd Θ hΘ
  have hNb : cap.emb '' N₀ ⊆ discBd (closure (cap.cuffDisc Θ)) := hb ▸ image_mono fun x hx =>
    (hN hx).1
  obtain ⟨Δ, hΔ, hsub, hcap, hbd⟩ := GM19.IsClosedDisc.exists_touching hd hNb (hfin.image _)
    (hne.image _)
  have hUc : ∀ x ∈ H.U, x ∈ closure (cap.cuffDisc Θ) → x ∈ cap.emb '' Θ := fun x hx hxc => by
    rw [cap.closure_cuffDisc hΘ] at hxc
    rcases hxc with h | h
    · rw [hH.hU] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact absurd (mem_range_self y) (cap.notMem_range hΘ h)
    · exact h
  have hΘU : cap.emb '' Θ ⊆ H.U := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hH.hU]
    exact mem_image_of_mem _ (Γ.subset_skU_of_mem_bd (cuff_subset_bd ⟨Θ, hΘ⟩ hy))
  have hdint : Disjoint (cap.cuffDisc Θ) H.U := disjoint_left.mpr fun x hx hxU => by
    have := hUc x hxU (subset_closure hx)
    obtain ⟨y, -, rfl⟩ := this
    exact cap.notMem_range hΘ hx (mem_range_self y)
  have hconn : IsPreconnected (cap.cuffDisc Θ) := by
    rw [cap.cuffDisc_eq_discInt hΘ]
    exact hd.isPreconnected_discInt
  have hinter : H.U ∩ Δ = cap.emb '' N₀ := by
    ext x
    constructor
    · rintro ⟨hxU, hxΔ⟩
      rw [← hcap]
      exact ⟨hxΔ, hb ▸ hUc x hxU (hsub hxΔ)⟩
    · intro hx
      refine ⟨?_, (Surface.discBd_subset _ (hbd hx))⟩
      exact hΘU (image_mono (fun z hz => (hN hz).1) hx)
  refine ⟨Δ, hsub, hΔ, hinter, ?_, hbd, ?_⟩
  · rw [hH.hV]
    exact image_mono fun x hx => (hN hx).2
  · rintro r hr ⟨z, hzr, hzΔ⟩
    have hzU : z ∉ H.U := region_subset hr hzr
    have hzc : z ∈ cap.cuffDisc Θ := by
      have := hsub hzΔ
      rw [cap.closure_cuffDisc hΘ] at this
      exact this.resolve_right fun h => hzU (hΘU h)
    have hsubr : cap.cuffDisc Θ ⊆ r := subset_region hr hconn hdint hzc hzr
    have hcl : closure (cap.cuffDisc Θ) ⊆ closure r := closure_mono hsubr
    have hΘr : cap.emb '' Θ ⊆ closure r := fun x hx => hcl (Surface.discBd_subset _ (hb.symm ▸ hx))
    obtain ⟨y, hy⟩ := ha.1
    exact ⟨(image_mono fun x hx => (hN hx).1).trans hΘr, a, ⟨ha, .inl ⟨(Γ.border_edge a ha ⟨y,
      hy, cuff_subset_bd ⟨Θ, hΘ⟩ (haΘ hy)⟩).1, rfl⟩⟩, (image_mono haΘ).trans hΘr⟩

/-- **A disc beside an edge of a drawing.** In a thin disc around the edge we take an arc on one
side with the same ends. The edge and the arc bound a disc, and a smaller disc touches its boundary
in the two ends. -/
theorem Drawing.exists_disc_beside_edge {T : Type} [TopologicalSpace T] [T2Space T]
  (hT : IsClosedSurface T) (G : Drawing T) {e : Set T} (he : e ∈ G.E) {a b : T}
    (hL : IsLineWithEnds (closure e) a b) (hab : a ≠ b)
    (hV : closure e ∩ G.V = {a, b}) {U : Set T} (hUo : IsOpen U) (hsub : closure e ⊆ U) :
    ∃ Δ, IsClosedDisc Δ ∧ Δ ⊆ U ∧ G.U ∩ Δ = {a, b} ∧ ({a, b} : Set T) ⊆ discBd Δ ∧ ∀ r ∈ G.R,
      (r ∩ Δ).Nonempty → closure e ⊆ closure r := by
  classical
  have ha : a ∈ closure e ∩ G.V := hV ▸ .inl rfl
  have hb : b ∈ closure e ∩ G.V := hV ▸ .inr rfl
  let Z : Set T := G.V ∪ (⋃ f ∈ G.E \ {e}, closure f) ∪ Uᶜ
  have hZ : IsClosed Z := (G.finite_V.isClosed.union ((G.finite_edges.subset
    sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure)).union hUo.isClosed_compl
  have heV : Disjoint e G.V := disjoint_left.mpr fun x hx => (he.2.1 hx).2
  have hcl : closure e ⊆ e ∪ {a, b} := fun x hx => by
    by_cases hxV : x ∈ G.V
    · exact .inr (hV ▸ ⟨hx, hxV⟩)
    · exact .inl ((G.closure_diff_V he).subset ⟨hx, hxV⟩)
  have hLZ : closure e ∩ Z ⊆ {a, b} := by
    rintro x ⟨hx, (hxV | hxf) | hxU⟩
    · exact hV ▸ ⟨hx, hxV⟩
    · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hxf
      by_contra hn
      have hxe : x ∈ e := (hcl hx).resolve_right hn
      have hxV : x ∉ G.V := disjoint_left.mp heV hxe
      have hxf' : x ∈ f := (G.closure_diff_V hf.1).subset ⟨hxf, hxV⟩
      exact hf.2 (G.edge_eq_of_mem hf.1 he hxf' hxe)
    · exact absurd (hsub hx) hxU
  have hUZ : G.U ⊆ Z ∪ e := fun x hx => by
    by_cases hxV : x ∈ G.V
    · exact .inl (.inl (.inl hxV))
    obtain ⟨f, hf, hxf⟩ := G.exists_edge_of_mem hx hxV
    by_cases hfe : f = e
    · exact .inr (hfe ▸ hxf)
    · exact .inl (.inl (.inr (mem_iUnion₂.mpr ⟨f, ⟨hf, hfe⟩, subset_closure hxf⟩)))
  have hLU : closure e ⊆ G.U := G.closure_subset_U he
  obtain ⟨D, A, B, hD, hLD, hDZ, -, -, -, hDe, hAc, hBc, -, -, hAL, hBL, hLA, hLB, ⟨p, hpD, hp₀⟩,
    -⟩ := exists_edge_lens hT hL hab hZ hLZ
  obtain ⟨g, hgc, hgi, hg0, hg1, hgr⟩ := exists_arc_of_path (γ := p) p.continuous
    (by simpa using hab)
  rw [p.source] at hg0
  rw [p.target] at hg1
  have hI : IsLineWithEnds (range g) a b := by
    have := IsArcMap.isLineWithEnds (⟨hgc, hgi⟩ : IsArcMap g)
    rwa [hg0, hg1] at this
  have hcapL : closure e ∩ range g ⊆ {a, b} := by
    rintro x ⟨hxL, hxI⟩
    obtain ⟨t, rfl⟩ := hgr hxI
    by_cases h₀ : t = 0
    · exact .inl (by rw [h₀, p.source])
    by_cases h₁ : t = 1
    · exact .inr (mem_singleton_iff.mpr (by rw [h₁, p.target]))
    exact absurd hxL (disjoint_left.mp hAL (hp₀ t (unitInterval.pos_iff_ne_zero.mpr h₀)
      (unitInterval.lt_one_iff_ne_one.mpr h₁)))
  have hFo : IsOArc (closure e ∪ range g) := GM11.isOArc_union hL hI hcapL
  have hFD : closure e ∪ range g ⊆ D := union_subset hLD (hgr.trans hpD)
  obtain ⟨E, ⟨hEsub, hEd, hEb, -⟩, -⟩ := disc_oArc D _ hD hFD hFo
  have hNb : ({a, b} : Set T) ⊆ discBd E := by
    rw [hEb]
    rintro x (rfl | hx)
    · exact .inl ha.1
    · rw [mem_singleton_iff.mp hx]
      exact .inl hb.1
  obtain ⟨Δ, hΔ, hsubE, hcap, hbd⟩ := GM19.IsClosedDisc.exists_touching hEd hNb (toFinite _)
    (insert_nonempty _ _)
  have hΔD : Δ ⊆ D := hsubE.trans hEsub
  have hmem : ∀ x ∈ ({a, b} : Set T), x ∈ closure e := by
    rintro x (rfl | hx)
    · exact ha.1
    · rw [mem_singleton_iff.mp hx]
      exact hb.1
  have hoff : ∀ X : Set T, X ⊆ D → Disjoint X (closure e) → Disjoint X G.U := fun X hXD hX
    => disjoint_left.mpr fun x hx hxU => by
    rcases hUZ hxU with hxZ | hxe
    · exact disjoint_left.mp hX hx (hmem x (hDZ ⟨hXD hx, hxZ⟩))
    · exact disjoint_left.mp hX hx (subset_closure hxe)
  refine ⟨Δ, hΔ, fun x hx => ?_, ?_, hbd, ?_⟩
  · by_contra hxU
    exact hxU (hsub (hmem x (hDZ ⟨hΔD hx, .inr hxU⟩)))
  · ext x
    constructor
    · rintro ⟨hxU, hxΔ⟩
      rcases hUZ hxU with hxZ | hxe
      · exact hDZ ⟨hΔD hxΔ, hxZ⟩
      · rw [← hcap]
        exact ⟨hxΔ, hEb ▸ .inl (subset_closure hxe)⟩
    · intro hx
      exact ⟨hLU (hmem x hx), Surface.discBd_subset _ (hbd hx)⟩
  · rintro r hr ⟨z, hzr, hzΔ⟩
    have hzU : z ∉ G.U := region_subset hr hzr
    have hAB : z ∈ A ∨ z ∈ B := by
      have hzD := hΔD hzΔ
      rw [hDe] at hzD
      rcases hzD with (h | h) | h
      · exact .inl h
      · exact .inr h
      · exact absurd (hLU h) hzU
    rcases hAB with hzA | hzB
    · have hAD : A ⊆ D := by
        rw [hDe]
        exact fun x hx => .inl (.inl hx)
      exact hLA.trans (closure_mono (subset_region hr hAc (hoff A hAD hAL) hzA hzr))
    · have hBD : B ⊆ D := by
        rw [hDe]
        exact fun x hx => .inl (.inr hx)
      exact hLB.trans (closure_mono (subset_region hr hBc (hoff B hBD hBL) hzB hzr))

/-- **The disc of an edge of size 3.** -/
theorem exists_three_disc (hH : IsSkHat cap Γ H) {c : Set S} (hc : c ∈ Γ.E) (h3 : (tilde c).ncard
  = 3) :
    ∃ Δ, Δ ⊆ cap.emb '' closure c ∧ IsAnchoredDisc cap Γ H Δ (cap.emb '' tilde c) c := by
  classical
  have : ConnectedSpace Shat := cap.connected
  have hinj := cap.isEmbedding.injective
  obtain ⟨hdisc, htb, htf⟩ := Γ.isDisc_of_three hc h3
  obtain ⟨hd, hb⟩ := isClosedDisc_image hdisc cap.isEmbedding
  have htne : (tilde c).Nonempty := nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨Δ, hΔ, hsub, hcap, hbd⟩ := GM19.IsClosedDisc.exists_touching hd (hb ▸ image_mono htb)
    (htf.image _) (htne.image _)
  have hbU : discBd (closure c) ⊆ Γ.skU := fun x hx => .inr (mem_iUnion₂.mpr ⟨c, ⟨hc, h3⟩, hx⟩)
  have hUbd : ∀ y ∈ Γ.skU, y ∈ closure c → y ∈ discBd (closure c) := fun y hy hyc => by
    by_cases hyt : y ∈ tilde c
    · exact htb hyt
    have hyc' : y ∈ c := by
      by_contra hn
      exact hyt ⟨hyc, hn⟩
    rcases hy with (hyV | hy) | hy
    · exact absurd hyV (Γ.disjoint_V hc hyc')
    · obtain ⟨e, ⟨he, h2⟩, hye⟩ := mem_iUnion₂.mp hy
      obtain rfl := GM11.arcComponent_eq he hc hye hyc'
      omega
    · obtain ⟨e, ⟨he, h3e⟩, hye⟩ := mem_iUnion₂.mp hy
      have hdE := (Γ.isDisc_of_three he h3e).1
      have hyE : y ∈ closure e := Surface.discBd_subset _ hye
      have hyn : y ∈ e := by
        by_contra hn
        exact Γ.disjoint_V hc hyc' (Γ.tilde_subset_V he ⟨hyE, hn⟩)
      obtain rfl := GM11.arcComponent_eq he hc hyn hyc'
      exact hye
  have hdint : Disjoint (discInt (cap.emb '' closure c)) H.U := disjoint_left.mpr fun x hx hxU => by
    rw [hH.hU] at hxU
    obtain ⟨y, hy, rfl⟩ := hxU
    obtain ⟨y', hy', e⟩ := id hx.1
    obtain rfl := hinj e
    exact hx.2 (hb ▸ mem_image_of_mem _ (hUbd y' hy hy'))
  have hinter : H.U ∩ Δ = cap.emb '' tilde c := by
    ext x
    constructor
    · rintro ⟨hxU, hxΔ⟩
      rw [← hcap]
      refine ⟨hxΔ, ?_⟩
      rw [hH.hU] at hxU
      obtain ⟨y, hy, rfl⟩ := hxU
      obtain ⟨y', hy', e⟩ := hsub hxΔ
      obtain rfl := hinj e
      exact hb ▸ mem_image_of_mem _ (hUbd y' hy hy')
    · intro hx
      refine ⟨?_, Surface.discBd_subset _ (hbd hx)⟩
      rw [hH.hU]
      exact image_mono (fun y hy => hbU (htb hy)) hx
  refine ⟨Δ, hsub, hΔ, hinter, ?_, hbd, ?_⟩
  · rw [hH.hV]
    exact image_mono (Γ.tilde_subset_V hc)
  · rintro r hr ⟨z, hzr, hzΔ⟩
    have hzU : z ∉ H.U := region_subset hr hzr
    have hzint : z ∈ discInt (cap.emb '' closure c) := by
      refine ⟨hsub hzΔ, fun hzb => hzU ?_⟩
      rw [hb] at hzb
      rw [hH.hU]
      exact image_mono hbU hzb
    have hsubr := subset_region hr hd.isPreconnected_discInt hdint hzint hzr
    have hcl : cap.emb '' closure c ⊆ closure r := by
      have := closure_mono hsubr
      rwa [closure_discInt hd] at this
    obtain ⟨f, hf⟩ := Γ.exists_sk_in hc
    exact ⟨(image_mono (fun y hy => Surface.discBd_subset _ (htb hy))).trans hcl, f, hf,
      (image_mono hf.subset_closure).trans hcl⟩

/-- **The disc of an edge of size 2.** -/
theorem exists_two_disc (hS : IsSurface S) (hH : IsSkHat cap Γ H) {c : Set S} (hc : c ∈ Γ.E) (h2 :
  (tilde c).ncard = 2) {U : Set Shat} (hUo : IsOpen U) (hU : cap.emb '' closure c ⊆ U) :
    ∃ Δ, Δ ⊆ U ∧ IsAnchoredDisc cap Γ H Δ (cap.emb '' tilde c) c := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hinj := cap.isEmbedding.injective
  have hsk := Γ.two_mem_sk hc h2
  obtain ⟨u, v, huv, ht, htV, hL⟩ := Γ.sk_line hsk
  have hE : cap.emb '' c ∈ H.E := hH.edge_iff.2 ⟨c, hsk, rfl⟩
  have hcl : closure (cap.emb '' c) = cap.emb '' closure c := (cap.isClosedEmbedding
    hS).closure_image_eq c
  have hne : cap.emb u ≠ cap.emb v := fun h => huv (hinj h)
  have hV : closure (cap.emb '' c) ∩ H.V = {cap.emb u, cap.emb v} := by
    rw [hcl, hH.hV, ← image_inter hinj]
    have e : closure c ∩ Γ.V = {u, v} := by
      rw [← ht]
      ext y
      exact ⟨fun h => ⟨h.1, fun hy => Γ.disjoint_V hc hy h.2⟩, fun h => ⟨h.1, htV h⟩⟩
    rw [e, image_pair]
  obtain ⟨Δ, hΔ, hsub, hcap, hbd, hr⟩ := H.exists_disc_beside_edge hT hE
    (hcl ▸ hL.map_of_embedding cap.isEmbedding) hne hV hUo (hcl ▸ hU)
  have hN : cap.emb '' tilde c = {cap.emb u, cap.emb v} := by rw [ht, image_pair]
  refine ⟨Δ, hsub, hΔ, by rwa [hN], hN ▸ (hV ▸ inter_subset_right),
    by rwa [hN], fun r hr' hz => ?_⟩
  have hcr := hr r hr' hz
  have hsubc : cap.emb '' tilde c ⊆ closure (cap.emb '' c) := by
    rw [hcl]
    exact image_mono fun y hy => hy.1
  exact ⟨hsubc.trans hcr, c, ⟨hc, .inl ⟨h2, rfl⟩⟩, subset_closure.trans hcr⟩

end GraphMinor.GM19

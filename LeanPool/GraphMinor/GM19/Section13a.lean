/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section12l

/-!
# Graph Minors XIX, Section 13: (13.1)

(13.1) says that no vertex of `R*` on the boundary of a wheel is within `ρ - 1` steps of the hub.
The paper looks at the
edge `e` of `sk(Γ)` outside `W` next to `r*`. We take instead the region `q` of `Γ*` outside `W`
next to `r*`, and the edge
`c` of `Γ` in `q`. The two ends of the side of `c` on `rBar` lie on `bd(W)`. If `|cTilde| = 3`, the
fifth condition of "fit" says
that they are the only vertices of `Γ` in `rBar`. If `|cTilde| = 2`, then all of the frontier of `q`
lies on `bd(W)`, so `q` is
the whole of the complement of `W`, against `three_le_ncard_bd`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

/-- A connected set off the vertices of a drawing that meets an edge lies in this edge. -/
theorem Drawing.subset_edge_of_preconnected {T : Type} [TopologicalSpace T] [T2Space T] {G :
  Drawing T} {g : Set T}
    (hg : g ∈ G.E) {X : Set T} (hX : IsPreconnected X) (hXU : X ⊆ G.U) (hXV : Disjoint X G.V) (hm :
      (X ∩ g).Nonempty) :
    X ⊆ g := by
  classical
  have hcl : ∀ {f}, f ∈ G.E → closure f ⊆ f ∪ G.V := fun hf ↦ closure_edge_subset hf
  have hsub : X ⊆ closure g ∪ ⋃ f ∈ G.E \ {g}, closure f := by
    intro x hx
    obtain ⟨f, hf, hxf⟩ := G.exists_edge_of_mem (hXU hx) (disjoint_left.mp hXV hx)
    by_cases hfg : f = g
    · exact .inl (subset_closure (hfg ▸ hxf))
    · exact .inr (mem_iUnion₂.mpr ⟨f, ⟨hf, hfg⟩, subset_closure hxf⟩)
  have hfin : (G.E \ {g}).Finite := G.finite_edges.subset sdiff_subset
  have hclosed : IsClosed (⋃ f ∈ G.E \ {g}, closure f) := hfin.isClosed_biUnion fun _ _ ↦
    isClosed_closure
  by_contra hn
  obtain ⟨z, hzX, hzg⟩ := not_subset.mp hn
  have hzg' : (X ∩ ⋃ f ∈ G.E \ {g}, closure f).Nonempty := by
    rcases hsub hzX with h | h
    · rcases hcl hg h with h' | h'
      · exact absurd h' hzg
      · exact absurd h' (disjoint_left.mp hXV hzX)
    · exact ⟨z, hzX, h⟩
  obtain ⟨y, hyX, hy₁, hy₂⟩ := isPreconnected_closed_iff.mp hX _ _ isClosed_closure hclosed hsub
    (hm.mono (inter_subset_inter_right _ subset_closure)) hzg'
  obtain ⟨f, ⟨hf, hfg⟩, hyf⟩ := mem_iUnion₂.mp hy₂
  rcases hcl hg hy₁ with h | h
  · rcases hcl hf hyf with h' | h'
    · exact hfg (G.edge_eq_of_mem hf hg h' h)
    · exact disjoint_left.mp hXV hyX h'
  · exact disjoint_left.mp hXV hyX h

namespace TangleDatum

/-- A side of an edge of size 3 has two different ends, among the ends of the edge. -/
theorem exists_side_ends (D : TangleDatum cap χ) {e f : Set S} (hf : D.P.Γ.IsSkEdgeIn f e) (h3 :
  (tilde e).ncard = 3) :
    ∃ a b, a ≠ b ∧ a ∈ closure f ∧ b ∈ closure f ∧ a ∈ tilde e ∧ b ∈ tilde e ∧
      closure f ⊆ f ∪ {a, b} := by
  classical
  have hS := χ.isSurface
  have he := hf.1
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨Sk, hSk⟩ := exists_isSkHat hS cap D.P.Γ
  have hfE : cap.emb '' f ∈ Sk.E := (hSk.edge_iff hS).mpr ⟨f, hf.mem, rfl⟩
  have hc3 := D.P.Γ.isDisc_of_three he h3
  obtain ⟨hC, hCbd⟩ := isClosedDisc_image hc3.1 cap.isEmbedding
  have hcl : IsClosedEmbedding cap.emb := cap.isClosedEmbedding hS
  have hfb : closure (cap.emb '' f) ⊆ cap.emb '' discBd (closure e) := by
    have hclosed : IsClosed (cap.emb '' discBd (closure e)) := by
      rw [← hCbd]
      exact hC.isOArc_discBd.isCompact.isClosed
    refine closure_minimal ?_ hclosed
    rintro _ ⟨z, hz, rfl⟩
    rcases hf.2 with ⟨h, -⟩ | ⟨-, h⟩
    · omega
    · exact mem_image_of_mem _ (h.2.1 hz).1
  obtain ⟨a, b, hab, hcap⟩ : ∃ a b, a ≠ b ∧ closure (cap.emb '' f) ∩ Sk.V = {a, b} := by
    rcases Sk.edge_cond _ hfE with ⟨a, b, hab, hcap, -⟩ | ⟨u, hcap, hO⟩
    · exact ⟨a, b, hab, hcap⟩
    · exfalso
      have heq' : closure (cap.emb '' f) = discBd (cap.emb '' closure e) :=
        eq_of_oArc_subset hO hC.isOArc_discBd (hCbd ▸ hfb)
      have hsub : cap.emb '' tilde e ⊆ {u} := by
        rintro _ ⟨t, ht, rfl⟩
        rw [← hcap]
        refine ⟨heq' ▸ hCbd ▸ mem_image_of_mem _ (hc3.2.1 ht), ?_⟩
        rw [hSk.hV]
        exact mem_image_of_mem _ (D.P.Γ.tilde_subset_V he ht)
      have := ncard_le_ncard hsub (toFinite _)
      rw [ncard_image_of_injective _ cap.isEmbedding.injective, h3, ncard_singleton] at this
      omega
  have hend : ∀ {t}, t ∈ closure (cap.emb '' f) ∩ Sk.V → ∃ z ∈ closure f, z ∈ tilde e ∧ cap.emb z
    = t := by
    rintro t ⟨ht, htV⟩
    rw [hcl.closure_image_eq] at ht
    obtain ⟨z, hz, rfl⟩ := ht
    rw [hSk.hV] at htV
    obtain ⟨z', hz', hzz⟩ := htV
    obtain rfl := cap.isEmbedding.injective hzz
    exact ⟨z', hz, ⟨closure_mono hf.subset hz, fun h ↦ D.P.Γ.disjoint_V he h hz'⟩, rfl⟩
  obtain ⟨a', ha'f, ha't, rfl⟩ := (hend (t := a) (hcap ▸ mem_insert _ _))
  obtain ⟨b', hb'f, hb't, rfl⟩ := (hend (t := b) (hcap ▸ mem_insert_of_mem _ rfl))
  refine ⟨a', b', fun h ↦ hab (by rw [h]), ha'f, hb'f, ha't, hb't, fun t ht ↦ ?_⟩
  have htcl : cap.emb t ∈ closure (cap.emb '' f) :=
    image_closure_subset_closure_image cap.isEmbedding.continuous (mem_image_of_mem _ ht)
  rcases closure_edge_subset hfE htcl with ⟨t', ht', htt⟩ | htV
  · exact .inl (cap.isEmbedding.injective htt ▸ ht')
  · have hm : cap.emb t ∈ closure (cap.emb '' f) ∩ Sk.V := ⟨htcl, htV⟩
    rw [hcap] at hm
    rcases hm with hm | hm
    · exact .inr (.inl (cap.isEmbedding.injective hm))
    · exact .inr (.inr (cap.isEmbedding.injective hm))

/-- **The fifth condition, for a side.** Let `f` be a side, off `bd(Σ)`, of an edge `e` of size 3,
on the boundary of a
region `r` of `Γ`. If `x, y` are the two ends of `f`, then they are the only vertices of `Γ` in
`rBar`. This differs from
`vertex_mem_of_side` in that the third end of `e` may lie on `bd(Σ)`. -/
theorem vertex_mem_of_side_off (D : TangleDatum cap χ) {e f : Set S} {r : Set Shat}
  (hf : D.P.Γ.IsSkEdgeIn f e)
    (h3 : (tilde e).ncard = 3) (hoff : closure f ∩ bd S = ∅) (hr : r ∈ D.P.Γ.hatRegions cap)
    (hfr : cap.emb '' f ⊆ closure r) {x y v : S} (hxy : x ≠ y) (hxf : x ∈ closure f)
      (hyf : y ∈ closure f)
    (hxV : x ∈ D.P.Γ.V) (hyV : y ∈ D.P.Γ.V) (hv : v ∈ D.P.Γ.V) (hvr : cap.emb v ∈ closure r) : v
      = x ∨ v = y := by
  classical
  have hS := χ.isSurface
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  have hc := cap.isClosedEmbedding hS
  obtain ⟨p, hp⟩ := hf.mem.1
  have hpe := hf.subset hp
  have hpr : cap.emb p ∈ closure r := hfr (mem_image_of_mem _ hp)
  rcases hatRegion_cases hS cap D.P.Γ hr with hsub | ⟨Θ, hΘ, rfl⟩
  · obtain ⟨r₀, hr₀, rfl⟩ := Painting.exists_region_of_hat hr hsub
    have hcl : ∀ {z : S}, cap.emb z ∈ closure (cap.emb '' r₀) → z ∈ closure r₀ := fun {z} hz ↦ by
      rw [hc.closure_image_eq] at hz
      obtain ⟨z', hz', hzz⟩ := hz
      exact cap.isEmbedding.injective hzz ▸ hz'
    by_contra hne
    push Not at hne
    have hcard : 3 ≤ (closure r₀ ∩ D.P.Γ.V).ncard := by
      have hsub' : ({x, y, v} : Set S) ⊆ closure r₀ ∩ D.P.Γ.V := by
        have hfcl : closure f ⊆ closure r₀ := closure_minimal
          (fun z hz ↦ hcl (hfr (mem_image_of_mem _ hz))) isClosed_closure
        rintro z (rfl | rfl | rfl)
        · exact ⟨hfcl hxf, hxV⟩
        · exact ⟨hfcl hyf, hyV⟩
        · exact ⟨hcl hvr, hv⟩
      have h₃ : ({x, y, v} : Set S).ncard = 3 := by
        rw [ncard_eq_three]
        exact ⟨x, y, v, hxy, hne.1.symm, hne.2.symm, rfl⟩
      rw [← h₃]
      exact ncard_le_ncard hsub' (D.P.Γ.finite_V.subset inter_subset_right)
    have hmem : p ∈ e ∩ closure r₀ := ⟨hpe, hcl hpr⟩
    obtain ⟨z, hz, hzb⟩ := D.P.fits.size_three_region e hf.1 h3 r₀ hr₀ hcard
      (connectedComponentIn (e ∩ closure r₀) p) ⟨p, hmem, rfl⟩
    -- the component lies in `f`
    obtain ⟨Sk, hSk⟩ := exists_isSkHat hS cap D.P.Γ
    have hfE : cap.emb '' f ∈ Sk.E := (hSk.edge_iff hS).mpr ⟨f, hf.mem, rfl⟩
    set T := connectedComponentIn (e ∩ closure r₀) p with hTdef
    have hTc : IsPreconnected (cap.emb '' T) :=
      isPreconnected_connectedComponentIn.image _ cap.isEmbedding.continuous.continuousOn
    have hTsub : T ⊆ e ∩ closure r₀ := connectedComponentIn_subset _ _
    have hTU : cap.emb '' T ⊆ Sk.U := by
      rintro _ ⟨t, ht, rfl⟩
      rw [hSk.hU]
      refine mem_image_of_mem _ (.inr (mem_iUnion₂.2 ⟨e, ⟨hf.1, h3⟩, ?_⟩))
      by_contra hn
      obtain ⟨hdisc, -⟩ := D.P.Γ.isDisc_of_three hf.1 h3
      obtain ⟨hC, hCbd⟩ := isClosedDisc_image hdisc cap.isEmbedding
      have hint : cap.emb t ∈ discInt (cap.emb '' closure e) := by
        refine ⟨mem_image_of_mem _ (subset_closure (hTsub ht).1), fun h ↦ ?_⟩
        rw [hCbd] at h
        obtain ⟨z', hz', hzz⟩ := h
        exact hn (cap.isEmbedding.injective hzz ▸ hz')
      have htcl : cap.emb t ∈ closure (cap.emb '' r₀) := by
        rw [hc.closure_image_eq]
        exact mem_image_of_mem _ (hTsub ht).2
      obtain ⟨y, hyO, hyρ⟩ := mem_closure_iff.mp htcl _ (hC.isOpen_discInt hman) hint
      obtain ⟨y', hy', rfl⟩ := hyO.1
      have hrU : Disjoint (cap.emb '' r₀) (D.P.Γ.hatU cap) := by
        obtain ⟨x₀, -, hx₀⟩ := hr
        rw [← hx₀, disjoint_left]
        exact fun _ hx ↦ connectedComponentIn_subset _ _ hx
      exact disjoint_left.mp hrU hyρ (mem_image_of_mem _ (D.P.Γ.closure_subset_U hf.1 hy'))
    have hTV : Disjoint (cap.emb '' T) Sk.V := by
      rw [disjoint_left, hSk.hV]
      rintro _ ⟨z', hz', rfl⟩ ⟨z'', hz'', hzz⟩
      obtain rfl := cap.isEmbedding.injective hzz
      exact D.P.Γ.disjoint_V hf.1 (hTsub hz').1 hz''
    have hsubf := Drawing.subset_edge_of_preconnected hfE hTc hTU hTV
      ⟨cap.emb p, mem_image_of_mem _ (mem_connectedComponentIn hmem), mem_image_of_mem _ hp⟩
    have hTf : T ⊆ f := fun t ht ↦ by
      obtain ⟨t', ht', htt⟩ := hsubf (mem_image_of_mem _ ht)
      exact cap.isEmbedding.injective htt ▸ ht'
    have hzf : z ∈ closure f ∩ bd S := ⟨closure_mono hTf hz, hzb⟩
    rw [hoff] at hzf
    exact hzf.elim
  · exfalso
    have hpΘ : p ∈ Θ := cap.mem_of_emb_mem hS hΘ hpr
    have : p ∈ closure f ∩ bd S := ⟨subset_closure hp, cuff_subset_bd ⟨Θ, hΘ⟩ hpΘ⟩
    rw [hoff] at this
    exact this.elim

variable {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ}

omit [T2Space S] in
/-- A region of `Γ*` lies inside a wheel or misses it. -/
theorem IsWheelHubOfRadius.region_side (h : D.IsWheelHubOfRadius W H ρ) {q : Set Shat}
  (hq : q ∈ D.rad.G.R) :
    q ⊆ W \ discBd W ∨ Disjoint q W := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  have hdis : Disjoint q (discBd W) := by
    rw [disjoint_left]
    exact fun x hx hxb ↦ region_subset hq hx (h.bd_sub hxb)
  exact h.is_disc.side hman (region_isPreconnected hq) hdis

omit [T2Space S] in
/-- The complement of a wheel is connected. -/
theorem IsWheelHubOfRadius.isConnected_compl (h : D.IsWheelHubOfRadius W H ρ) : IsConnected Wᶜ := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hnice : IsGammaNice D.rad.G W := by
    refine ⟨{a ∈ D.rad.G.A | a ⊆ W}, fun a ha ↦ ha.1, Subset.antisymm (fun p hp ↦ ?_)
      (sUnion_subset fun a ha ↦ ha.2)⟩
    by_cases hpU : p ∈ D.rad.G.U
    · by_cases hpV : p ∈ D.rad.G.V
      · exact ⟨{p}, ⟨.inl (.inl ⟨p, hpV, rfl⟩), by simpa using hp⟩, rfl⟩
      · obtain ⟨g, hg, hpg⟩ := D.rad.G.exists_edge_of_mem hpU hpV
        rcases h.edge_side hg with h' | h'
        · exact ⟨g, ⟨.inl (.inr hg), h'⟩, hpg⟩
        · exact absurd hp (disjoint_left.mp h' hpg)
    · obtain ⟨q, hq, hpq⟩ := exists_region_of_notMem hpU
      rcases h.region_side hq with h' | h'
      · exact ⟨q, ⟨.inr hq, h'.trans sdiff_subset⟩, hpq⟩
      · exact absurd hp (disjoint_left.mp h' hpq)
  have hne : W.Nonempty := by
    obtain ⟨p, -, -, hp, -⟩ := h.is_disc.isOArc_discBd.exists_three
    exact ⟨p, Surface.discBd_subset _ hp⟩
  have hu : W ≠ univ := by
    intro he
    obtain ⟨p, -, -, hp, -⟩ := h.is_disc.isOArc_discBd.exists_three
    rw [← IsClosedDisc.frontier_eq_discBd hT h.is_disc, he, frontier_univ] at hp
    exact hp
  exact GraphMinor.GM11.isConnected_compl hT h.is_disc.isClosed hnice
    (IsClosedDisc.isSimplyConnectedSet h.is_disc) hne hu

omit [T2Space S] in
/-- A region of `Γ*` outside a wheel with its frontier in the wheel has the boundary of the wheel in
its closure. -/
theorem IsWheelHubOfRadius.bd_subset_of_frontier (h : D.IsWheelHubOfRadius W H ρ) {q : Set Shat}
  (hq : q ∈ D.rad.G.R)
    (hdis : Disjoint q W) (hfr : frontier q ⊆ W) : discBd W ⊆ closure q := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hlc : LocallyConnectedSpace Shat := IsClosedSurface.locallyConnectedSpace hT
  have hqo : IsOpen q := region_isOpen hq
  obtain ⟨y, hy₀, hye⟩ := id hq
  have hy : y ∈ q := hye ▸ mem_connectedComponentIn hy₀
  have hsub : Wᶜ ⊆ q := by
    refine h.isConnected_compl.isPreconnected.subset_left_of_subset_union hqo
      isClosed_closure.isOpen_compl
      (disjoint_left.mpr fun x hx hn ↦ hn (subset_closure hx)) (fun x hx ↦ ?_) ⟨y, disjoint_left.mp
        hdis hy, hy⟩
    by_cases hxc : x ∈ closure q
    · refine .inl ?_
      by_contra hn
      exact hx (hfr ⟨hxc, by rwa [hqo.interior_eq]⟩)
    · exact .inr hxc
  intro p hp
  rw [← IsClosedDisc.frontier_eq_discBd hT h.is_disc] at hp
  rw [frontier_eq_closure_inter_closure] at hp
  exact closure_mono hsub hp.2

/-- **Graph Minors XIX, (13.1)** (page 366): "There is no path in $\Gamma^*$ from $R^* \cap bd(W)$
to $V(H)$ with $\le \rho - 1$ edges."
The paper's "fourth condition" is the condition that `W` contains the vertices of `Γ` near `H`. -/
theorem theorem_13_1_proof (h : D.IsWheelHubOfRadius W H ρ) (hbd : discBd W ⊆ cap.emb ''
  (univ \ bd S))
    (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty) {r : Shat} (hr : r ∈ D.rad.Rstar)
      (hrb : r ∈ discBd W) :
    ¬ ∃ P : Drawing Shat, ∃ z ∈ H.V, P.IsPathOf D.rad.G r z ∧ P.E.ncard + 1 ≤ ρ := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hS := χ.isSurface
  have h3t := D.P.fits.internally_three_connected
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  have hlc : LocallyConnectedSpace Shat := IsClosedSurface.locallyConnectedSpace hT
  rintro ⟨P, z, hz, hP, hle⟩
  obtain ⟨K, hK⟩ := GraphMinor.GM19.Drawing.IsPathOf.exists_walk hP
  have hH := h.H_sub
  have hNr : D.IsNear H (ρ - 1) r := ⟨z, hz, K, by omega⟩
  set ρr := D.rad.regionOf r with hρr
  have hρm := D.rad.regionOf_mem hr
  -- the vertices of `Γ` around `r` lie in `W`
  have hnbr : ∀ {v : S}, v ∈ D.P.Γ.V → cap.emb v ∈ closure ρr → cap.emb v ∈ W := by
    intro v hv hcl
    have hN := hNr.of_closure_region hr hv hcl
    exact h.close_in_W _ (mem_image_of_mem _ hv) (isNear_iff_exists_path.mp (hN.mono (by omega)))
  -- the region of `Γ*` outside `W` beside an edge of `bd(W)` at `r`
  obtain ⟨F, hFc, hFs, hFU⟩ := exists_circuit_of_oArc h.is_disc.isOArc_discBd h.bd_sub
  have hFG : Drawing.IsCircuitOf F D.rad.G := ⟨hFs, hFc⟩
  have hrF : r ∈ F.V := mem_V_of_mem_U hFs (hFU ▸ hrb) hr.1
  obtain ⟨e₁, he₁, v₁, -, -, hcap₁⟩ := exists_edge_at_Rstar hFG hrF hr.2
  have he₁G := hFs.2 he₁
  obtain ⟨p, hp⟩ := he₁G.2.2.1.nonempty
  have hpb : p ∈ discBd W := by
    rw [← hFU, F.U_eq]
    exact .inr (mem_iUnion₂.mpr ⟨e₁, he₁, subset_closure hp⟩)
  have hrcl : r ∈ closure e₁ ∩ D.rad.G.V := by
    rw [hcap₁]
    exact .inl rfl
  have hpρ : p ∈ ρr := edge_subset_regionOf D hr he₁G hrcl.1 hp
  have hpo : p ∈ closure Wᶜ := by
    have := hpb
    rw [← IsClosedDisc.frontier_eq_discBd hT h.is_disc, frontier_eq_closure_inter_closure] at this
    exact this.2
  obtain ⟨q, hq, hpq, y, hyq, hyW⟩ := exists_region_near hT D.rad.G h.is_disc.isClosed.isOpen_compl
    hpo
  have hdis : Disjoint q W := by
    rcases h.region_side hq with h' | h'
    · exact absurd (h' hyq).1 hyW
    · exact h'
  have hnotint : ∀ {x}, x ∈ closure q → x ∈ W → x ∈ discBd W := by
    intro x hx hxW
    by_contra hn
    obtain ⟨t, ht₁, ht₂⟩ := mem_closure_iff.mp hx _ (h.is_disc.isOpen_discInt hman) ⟨hxW, hn⟩
    exact disjoint_left.mp hdis ht₂ ht₁.1
  obtain ⟨c, hc, hcq⟩ := (D.rad.region_facts hS h3t).1 q hq
  have hm : (q ∩ ρr).Nonempty := by
    obtain ⟨t, ht₁, ht₂⟩ := mem_closure_iff.mp hpq _ (isOpen_regionOf D hr) hpρ
    exact ⟨t, ht₂, ht₁⟩
  obtain ⟨f, hf, hfρ⟩ := exists_side_of_meet D hq hc hcq hr hm
  have hcl_q : ∀ {t : S}, t ∈ closure c → cap.emb t ∈ closure q := fun {t} ht ↦
    closure_mono hcq (image_closure_subset_closure_image cap.isEmbedding.continuous
      (mem_image_of_mem _ ht))
  have hcl_ρ : ∀ {t : S}, t ∈ closure f → cap.emb t ∈ closure ρr := fun {t} ht ↦
    closure_minimal hfρ isClosed_closure
      (image_closure_subset_closure_image cap.isEmbedding.continuous (mem_image_of_mem _ ht))
  have hsideb : ∀ {t : S}, t ∈ closure f → t ∈ tilde c → cap.emb t ∈ discBd W := fun {t} ht htc ↦
    hnotint (hcl_q htc.1) (hnbr (D.P.Γ.tilde_subset_V hc htc) (hcl_ρ ht))
  -- the first step of the path
  have hzne : r ≠ z := fun e ↦ (h.H_in_int (H.V_subset_U hz)).2 (e ▸ hrb)
  obtain ⟨n, hnV, hncl, hnN⟩ : ∃ n ∈ D.P.Γ.V, cap.emb n ∈ closure ρr ∧ D.IsNear H (ρ - 2)
    (cap.emb n) := by
    cases K with
    | nil _ => exact absurd rfl hzne
    | @cons _ n₀ _ g hl rest =>
      rw [GraphWalk.length_cons] at hK
      obtain ⟨n, hn, rfl⟩ := hatV_of_not_hatV D hl.1 hl.2.2.2 hr.2
      have hrg : r ∈ closure g ∩ D.rad.G.V := by
        rw [hl.2.2.2]
        exact .inl rfl
      have hng : cap.emb n ∈ closure g ∩ D.rad.G.V := by
        rw [hl.2.2.2]
        exact .inr rfl
      exact ⟨n, hn, closure_mono (edge_subset_regionOf D hr hl.1 hrg.1) hng.1, z, hz, rest,
        by omega⟩
  have hρ2 : ∀ {m : Shat}, m ∈ cap.emb '' D.Γ.V → m ∈ discBd W → D.IsNear H (ρ - 2) m → 2 ≤ ρ
    → False := by
    intro m hm hmb hN h2
    obtain ⟨Q, t, ht, hQ, hQl⟩ := isNear_iff_exists_path.mp hN
    exact (h.bd_dist m ⟨hm, hmb⟩).2 ⟨Q, t, ht, hQ, by omega⟩
  have h2ρ : 2 ≤ ρ := by
    have hne : 1 ≤ K.length := by
      by_contra h0
      have : K.length = 0 := by omega
      exact hzne (GraphWalk.eq_of_length_eq_zero this)
    omega
  rcases D.P.Γ.size_cases hc with h2 | h3
  · have hfe : f = c := by
      rcases hf.2 with ⟨-, h'⟩ | ⟨h', -⟩
      · exact h'
      · omega
    subst hfe
    obtain ⟨x, y, hxy, htil⟩ := ncard_eq_two.mp h2
    have hx : x ∈ tilde f := htil ▸ mem_insert _ _
    have hy : y ∈ tilde f := htil ▸ mem_insert_of_mem _ rfl
    have hbx := hsideb hx.1 hx
    have hby := hsideb hy.1 hy
    have hVx := D.P.Γ.tilde_subset_V hc hx
    have hVy := D.P.Γ.tilde_subset_V hc hy
    -- a vertex of `R*` on the closure of `q` lies on `bd(W)`
    have hRq : ∀ {w : Shat}, w ∈ D.rad.Rstar → w ∈ closure q → w ∈ discBd W := by
      intro w hw hwq
      have hmw : (q ∩ D.rad.regionOf w).Nonempty := by
        obtain ⟨t, ht₁, ht₂⟩ := mem_closure_iff.mp hwq _ (isOpen_regionOf D hw)
          (D.rad.regionOf_mem hw).2
        exact ⟨t, ht₂, ht₁⟩
      obtain ⟨f', hf', hf'w⟩ := exists_side_of_meet D hq hc hcq hw hmw
      have hff : f' = f := by
        rcases hf'.2 with ⟨-, h'⟩ | ⟨h', -⟩
        · exact h'
        · omega
      subst hff
      have hclw : ∀ {t : S}, t ∈ closure f' → cap.emb t ∈ closure (D.rad.regionOf w) := fun {t} ht ↦
        closure_minimal hf'w isClosed_closure
          (image_closure_subset_closure_image cap.isEmbedding.continuous (mem_image_of_mem _ ht))
      obtain ⟨g₁, hg₁, hc₁⟩ := D.rad.exists_spoke hS (h3t.hatRegions_isOpenDisc hS cap) h3t.1 hw
        hVx (hclw hx.1)
      obtain ⟨g₂, hg₂, hc₂⟩ := D.rad.exists_spoke hS (h3t.hatRegions_isOpenDisc hS cap) h3t.1 hw
        hVy (hclw hy.1)
      refine hnotint hwq (h.two_nbrs_in_W w hw.1 _ ⟨mem_image_of_mem _ hVx,
        hbx⟩ _ ⟨mem_image_of_mem _ hVy, hby⟩
        (fun e ↦ hxy (cap.isEmbedding.injective e)) ⟨g₁, hg₁, ?_⟩ ⟨g₂, hg₂, ?_⟩)
      · rw [← closure_inter_V_eq_tilde hg₁, hc₁, pair_comm]
      · rw [← closure_inter_V_eq_tilde hg₂, hc₂, pair_comm]
    -- a vertex of `Γ` in the closure of `q` is an end of `c`
    have hVq : ∀ {v : S}, v ∈ D.P.Γ.V → cap.emb v ∈ closure q → v ∈ tilde f := fun {v} hv hcl ↦
      ⟨(D.rad.region_facts hS h3t).2.2 q hq f hc hcq v hv hcl, fun h' ↦ D.P.Γ.disjoint_V hc h' hv⟩
    have hVb : ∀ {v : S}, v ∈ tilde f → cap.emb v ∈ discBd W := fun {v} hv ↦ by
      have : v ∈ ({x, y} : Set S) := htil ▸ hv
      rcases this with rfl | rfl
      · exact hbx
      · exact hby
    have hGq : ∀ {t : Shat}, t ∈ D.rad.G.V → t ∈ closure q → t ∈ discBd W := by
      intro t ht hcl
      by_cases hth : t ∈ D.P.Γ.hatV cap
      · obtain ⟨v, hv, rfl⟩ := hth
        exact hVb (hVq hv hcl)
      · exact hRq ⟨ht, hth⟩ hcl
    have hfr : frontier q ⊆ W := by
      intro t ht
      have hcl := frontier_subset_closure ht
      have htq : t ∉ q := fun h' ↦ by
        rw [(region_isOpen hq).frontier_eq] at ht
        exact ht.2 h'
      have htU : t ∈ D.rad.G.U := (closure_region_subset hq hcl).resolve_left htq
      by_cases htV : t ∈ D.rad.G.V
      · exact Surface.discBd_subset _ (hGq htV hcl)
      · obtain ⟨g, hg, htg⟩ := D.rad.G.exists_edge_of_mem htU htV
        have hgq : g ⊆ closure q := edge_subset_closure_of_incident hT hg hq ⟨t, htg, hcl⟩
        have hsub : tilde g ⊆ discBd W := by
          intro u hu
          have hu' : u ∈ closure g ∩ D.rad.G.V := closure_inter_V_eq_tilde hg ▸ hu
          exact hGq hu'.2 (closure_minimal hgq isClosed_closure hu'.1)
        exact h.chord_in_W g hg hsub htg
    have hbq := h.bd_subset_of_frontier hq hdis hfr
    have h3b := three_le_ncard_bd h hbd hin
    have hsub : discBd W ∩ D.P.Γ.hatV cap ⊆ cap.emb '' tilde f := by
      rintro _ ⟨hb, v, hv, rfl⟩
      exact mem_image_of_mem _ (hVq hv (hbq hb))
    have := ncard_le_ncard hsub (((D.P.Γ.finite_V.subset (D.P.Γ.tilde_subset_V hc))).image _)
    have h₂ := ncard_image_le (f := cap.emb) (D.P.Γ.finite_V.subset (D.P.Γ.tilde_subset_V hc))
    omega
  · obtain ⟨a, b, hab, haf, hbf, hat, hbt, hclf⟩ := D.exists_side_ends hf h3
    have hba := hsideb haf hat
    have hbb := hsideb hbf hbt
    have hnotbd : ∀ {t : S}, cap.emb t ∈ discBd W → t ∉ bd S := fun {t} ht hb ↦ by
      obtain ⟨t', ht', hee⟩ := hbd ht
      obtain rfl := cap.isEmbedding.injective hee
      exact ht'.2 hb
    have hoff : closure f ∩ bd S = ∅ := by
      refine eq_empty_of_forall_notMem ?_
      rintro t ⟨ht, htb⟩
      rcases hclf ht with h' | rfl | rfl
      · have := (D.P.Γ.border_edge c hc ⟨t, hf.subset h', htb⟩).1
        omega
      · exact hnotbd hba htb
      · exact hnotbd hbb htb
    rcases D.vertex_mem_of_side_off hf h3 hoff hρm.1 hfρ hab haf hbf (D.P.Γ.tilde_subset_V hc hat)
      (D.P.Γ.tilde_subset_V hc hbt) hnV hncl with rfl | rfl
    · exact hρ2 (mem_image_of_mem _ hnV) hba hnN h2ρ
    · exact hρ2 (mem_image_of_mem _ hnV) hbb hnN h2ρ

end TangleDatum

end GraphMinor.GM19

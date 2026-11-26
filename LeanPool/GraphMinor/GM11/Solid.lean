/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Corners
public import LeanPool.GraphMinor.GM11.LeafNbhd
public import LeanPool.GraphMinor.GM11.ForestRegions
public import LeanPool.GraphMinor.GM11.NiceSets
public import LeanPool.GraphMinor.GM11.DrawingOps
public import LeanPool.GraphMinor.GM11.Section5b
public import LeanPool.GraphMinor.Surface.ArcInPath

/-!
# Closed nice sets are solid

Graph Minors XI, Section 7 (page 93), applies Graph Minors VII, (11.10), to nice sets, and so it
needs them
to be solid. The paper does not say why they are. This file proves it (`isSolid_of_nice`).

We show that a closed nice set `X` is connected in the small at each point `x`: points of `X` near
`x` are
joined to `x` by a path in `X` near `x` (`LocJoin`). It is enough to do this for the closure of each
vertex,
edge and region, since `X` is a finite union of these. The closure of an edge is a curve. At a
vertex of
degree at least two, the sectors of `exists_sectors` give straight paths into a region. At a vertex
of
degree at most one, a whole neighbourhood lies in the closure of the one region there. A point in an
edge
becomes a vertex after we add it, and this does not change the regions.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

/-- A closed surface is locally path-connected, because it is a quotient of a union of open discs.
-/
theorem IsClosedSurface.locallyPathConnectedSpace (hS : IsClosedSurface S) :
    LocallyPathConnectedSpace S := by
  choose V hV hxV h using hS.2.2
  have hball : LocallyPathConnectedSpace OpenUnitDisc :=
    IsOpen.locallyPathConnectedSpace Metric.isOpen_ball
  have hlp : ∀ x, LocallyPathConnectedSpace (V x) := fun x => by
    obtain ⟨e⟩ := h x
    exact e.symm.locallyPathConnectedSpace
  let f : (Σ x, V x) → S := fun p => p.2.1
  have hf : Continuous f := continuous_sigma fun _ => continuous_subtype_val
  have ho : IsOpenMap f := isOpenMap_sigma.mpr fun i => (hV i).isOpenEmbedding_subtypeVal.isOpenMap
  exact (ho.isQuotientMap hf fun x => ⟨⟨x, x, hxV x⟩, rfl⟩).locallyPathConnectedSpace

/-- Points of `Y` near `x` are joined to `x` by paths in `Y` near `x`. -/
def LocJoin (Y : Set S) (x : S) : Prop :=
  ∀ A : Set S, IsOpen A → x ∈ A → ∃ N : Set S, IsOpen N ∧ x ∈ N ∧ ∀ y ∈ Y ∩ N, JoinedIn (Y ∩ A) x y

/-- A curve is connected in the small. -/
theorem locJoin_range [T2Space S] {f : I → S} (hf : Continuous f) {x : S} (hx : x ∈ range f) :
    LocJoin (range f) x := by
  have hlp : LocallyPathConnectedSpace I :=
    (IsQuotientMap.of_inverse continuous_subtype_val continuous_projIcc
      (projIcc_val (zero_le_one' ℝ))).locallyPathConnectedSpace
  intro A hA hxA
  have hO : IsOpen (f ⁻¹' A) := hA.preimage hf
  let T : Set I := ⋃ s ∈ f ⁻¹' {x}, pathComponentIn (f ⁻¹' A) s
  have hT : IsOpen T := isOpen_biUnion fun s _ => hO.pathComponentIn s
  have hK : IsClosed (f '' Tᶜ) := (hT.isClosed_compl.isCompact.image hf).isClosed
  have hx' : x ∉ f '' Tᶜ := by
    rintro ⟨t, ht, rfl⟩
    exact ht (mem_biUnion rfl (mem_pathComponentIn_self hxA))
  refine ⟨_, hK.isOpen_compl, hx', ?_⟩
  rintro y ⟨⟨t, rfl⟩, hy⟩
  have htT : t ∈ T := by
    by_contra h
    exact hy (mem_image_of_mem f h)
  obtain ⟨s, hs, hst⟩ := mem_iUnion₂.mp htT
  obtain rfl : f s = x := hs
  have hj : JoinedIn (f ⁻¹' A) s t := hst
  exact ⟨(hj.somePath).map hf, fun u => ⟨mem_range_self _, hj.somePath_mem u⟩⟩

/-- Connected in the small at every point gives locally arc-connected. -/
theorem isLocallyArcConnected_of_locJoin [T2Space S] {X : Set S} (h : ∀ x ∈ X, LocJoin X x) :
    IsLocallyArcConnected X := by
  intro x hx A hA hxA
  let C := pathComponentIn (X ∩ A) x
  have hC : C ⊆ X ∩ A := pathComponentIn_subset
  have hxC : x ∈ C := mem_pathComponentIn_self ⟨hx, hxA⟩
  choose! N hNo hNm hNj using fun c (hc : c ∈ C) => h c (hC hc).1 A hA (hC hc).2
  refine ⟨(⋃ c ∈ C, N c) ∩ A, inter_subset_right, ⟨mem_biUnion hxC (hNm x hxC), hxA⟩,
    (isOpen_biUnion hNo).inter hA, ?_⟩
  have heq : X ∩ ((⋃ c ∈ C, N c) ∩ A) = C := by
    apply subset_antisymm
    · rintro y ⟨hyX, hyN, -⟩
      obtain ⟨c, hc, hyc⟩ := mem_iUnion₂.mp hyN
      have h₁ : JoinedIn (X ∩ A) x c := hc
      exact h₁.trans (hNj c hc y ⟨hyX, hyc⟩)
    · intro y hy
      obtain ⟨c, hc⟩ : ∃ c, y = c := ⟨y, rfl⟩
      exact ⟨(hC hy).1, mem_biUnion hy (hNm y hy), (hC hy).2⟩
  rw [heq]
  intro a ha b hb hab
  have hpc : IsPathConnected C := isPathConnected_pathComponentIn ⟨hx, hxA⟩
  have hj := hpc.joinedIn a ha b hb
  obtain ⟨e, hec, hei, he0, he1, hsub⟩ := exists_arc_of_path (γ := hj.somePath)
    hj.somePath.continuous
    (by simpa using hab)
  have hc : CompactSpace (range e) := isCompact_iff_compactSpace.mp (isCompact_range hec)
  refine ⟨range e, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    obtain ⟨u, hu⟩ := hsub (mem_range_self t)
    exact hu ▸ hj.somePath_mem u
  · have hjb : Function.Bijective (rangeFactorization e) :=
      ⟨fun x y hxy => hei (congrArg Subtype.val hxy), rangeFactorization_surjective⟩
    refine ⟨(Continuous.subtype_mk hec _).homeoOfEquivCompactToT2
      (f := Equiv.ofBijective _ hjb), ?_, ?_⟩
    · exact he0.trans (by simp)
    · exact he1.trans (by simp)

/-- A point `x` on the boundary of a closed disc `Q` is reached from each interior point of `Q` near
`x`
by a straight path, in the chart of `Q`, that stays in the interior of `Q` and near `x`. -/
theorem exists_disc_approach {Q : Set S} (hQ : IsClosedDisc Q) {x : S}
  (hx : x ∈ discBd Q) {O : Set S}
    (hO : IsOpen O) (hxO : x ∈ O) :
    ∃ N : Set S, IsOpen N ∧ x ∈ N ∧ ∀ y ∈ N ∩ Q, y ∉ discBd Q →
      ∃ p : Path x y, ∀ t, p t = x ∨ p t ∈ (O ∩ Q) \ discBd Q := by
  obtain ⟨φ⟩ := id hQ
  have hbd := disc_boundary Q φ
  rw [hbd] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  let G : ClosedUnitDisc → S := fun z => (φ z).1
  have hG : Continuous G := continuous_subtype_val.comp φ.continuous
  have hGi : Function.Injective G := fun a b h => φ.injective (Subtype.ext h)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (hO.preimage hG) c hxO
  have hopen : IsOpen (φ '' Metric.ball c δ) := φ.isOpenMap _ Metric.isOpen_ball
  obtain ⟨N, hN, hNeq⟩ := isOpen_induced_iff.mp hopen
  have hcN : G c ∈ N := by
    have : φ c ∈ Subtype.val ⁻¹' N := hNeq ▸ mem_image_of_mem φ (Metric.mem_ball_self hδ)
    exact this
  refine ⟨N, hN, hcN, ?_⟩
  rintro y ⟨hyN, hyQ⟩ hyb
  have hmem : (⟨y, hyQ⟩ : Q) ∈ φ '' Metric.ball c δ := hNeq ▸ hyN
  obtain ⟨p, hp, hpy⟩ := hmem
  have hpy' : G p = y := congrArg Subtype.val hpy
  have hc1 : ‖c.1‖ = 1 := by simpa [UnitCircle] using hc
  have hp1 : ‖p.1‖ < 1 := by
    have hle : ‖p.1‖ ≤ 1 := by simpa [ClosedUnitDisc] using p.2
    refine lt_of_le_of_ne hle fun h => hyb ?_
    rw [hbd]
    exact ⟨p, by simpa [UnitCircle] using h, hpy'⟩
  have hnorm : ∀ t : I, ‖(1 - t.1) • c.1 + t.1 • p.1‖ ≤ (1 - t.1) + t.1 * ‖p.1‖ := by
    intro t
    have h₁ : 0 ≤ 1 - t.1 := by linarith [t.2.2]
    calc ‖(1 - t.1) • c.1 + t.1 • p.1‖ ≤ ‖(1 - t.1) • c.1‖ + ‖t.1 • p.1‖ := norm_add_le _ _
      _ = (1 - t.1) + t.1 * ‖p.1‖ := by
        rw [norm_smul, norm_smul, hc1, Real.norm_of_nonneg h₁, Real.norm_of_nonneg t.2.1, mul_one]
  let seg : I → ClosedUnitDisc := fun t => ⟨(1 - t.1) • c.1 + t.1 • p.1, by
    have h₂ := hnorm t
    have h₃ : t.1 * ‖p.1‖ ≤ t.1 := by nlinarith [t.2.1, t.2.2]
    have : ‖(1 - t.1) • c.1 + t.1 • p.1‖ ≤ 1 := by linarith
    simpa [ClosedUnitDisc] using this⟩
  have hseg : Continuous seg := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  have hs0 : seg 0 = c := Subtype.ext (by simp [seg])
  have hs1 : seg 1 = p := Subtype.ext (by simp [seg])
  have hdist : ∀ t, seg t ∈ Metric.ball c δ := by
    intro t
    have hp' : dist p c < δ := hp
    rw [Metric.mem_ball, Subtype.dist_eq]
    have heq : (seg t).1 - c.1 = t.1 • (p.1 - c.1) := by
      change (1 - t.1) • c.1 + t.1 • p.1 - c.1 = _
      rw [smul_sub, sub_smul, one_smul]
      abel
    rw [dist_eq_norm, heq, norm_smul, Real.norm_of_nonneg t.2.1, ← dist_eq_norm, ← Subtype.dist_eq]
    nlinarith [t.2.1, t.2.2, dist_nonneg (x := p) (y := c)]
  subst hpy'
  let P : Path (G c) (G p) := ⟨⟨fun t => G (seg t), hG.comp hseg⟩, by simp [hs0], by simp [hs1]⟩
  refine ⟨P, fun t => ?_⟩
  by_cases ht : t = 0
  · left
    subst ht
    exact P.source
  right
  refine ⟨⟨hball (hdist t), (φ (seg t)).2⟩, fun hin => ?_⟩
  rw [hbd] at hin
  obtain ⟨z, hz, hzs⟩ := hin
  have hzeq : z = seg t := hGi hzs
  have hz1 : ‖(seg t).1‖ = 1 := by
    rw [← hzeq]
    simpa [UnitCircle] using hz
  have htpos : 0 < t.1 := lt_of_le_of_ne t.2.1 fun h => ht (Subtype.ext h.symm)
  have h₄ := hnorm t
  have h₅ : ‖(seg t).1‖ = ‖(1 - t.1) • c.1 + t.1 • p.1‖ := rfl
  nlinarith

variable [T2Space S] [ConnectedSpace S]

omit [ConnectedSpace S] in
/-- The closure of an edge is connected in the small. -/
theorem locJoin_edge {Γ : Drawing S} {e : Set S} (he : e ∈ Γ.E) {γ : Set S → I → S}
  (hγ : EdgePar Γ γ)
    {x : S} (hx : x ∈ closure e) : LocJoin (closure e) x := by
  have hcl : closure e = range (γ e) := by
    apply subset_antisymm
    · refine closure_minimal ?_ (isCompact_range (hγ.cont e he)).isClosed
      intro y hy
      obtain ⟨t, -, rfl⟩ := (hγ.image e he).superset hy
      exact mem_range_self t
    · rintro _ ⟨t, rfl⟩
      have ht : t ∈ closure (Ioo (0 : I) 1) := by
        rw [closure_Ioo (zero_ne_one' I)]
        exact ⟨t.2.1, t.2.2⟩
      have := image_closure_subset_closure_image (hγ.cont e he) (mem_image_of_mem _ ht)
      rwa [hγ.image e he] at this
  rw [hcl] at hx ⊢
  exact locJoin_range (hγ.cont e he) hx

omit [ConnectedSpace S] in
/-- At a vertex with at most one half-edge, a whole neighbourhood lies in the closure of each region
that has the vertex in its closure. -/
theorem exists_nbhd_of_few (hS : IsClosedSurface S) {Γ : Drawing S} {γ : Set S → I → S}
    (hγ : EdgePar Γ γ) {x : S} (hxV : x ∈ Γ.V) (h2 : ¬ 2 ≤ Nat.card (halfEdges Γ γ x)) {r : Set S}
    (hr : r ∈ Γ.R) (hxr : x ∈ closure r) : ∃ Z : Set S, IsOpen Z ∧ x ∈ Z ∧ Z ⊆ closure r := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hfin : Finite (halfEdges Γ γ x) := (finite_halfEdges Γ γ x).to_subtype
  have hss : Subsingleton (halfEdges Γ γ x) :=
    Finite.card_le_one_iff_subsingleton.mp (by omega)
  have key : ∃ Z : Set S, IsOpen Z ∧ x ∈ Z ∧ ∀ a ∈ Z, a ∉ Γ.U → ∀ b ∈ Z, b ∉ Γ.U →
      ∃ A : Set S, IsPreconnected A ∧ Disjoint A Γ.U ∧ a ∈ A ∧ b ∈ A := by
    rcases isEmpty_or_nonempty (halfEdges Γ γ x) with h0 | ⟨⟨k⟩⟩
    · have hno : ∀ g ∈ Γ.E, x ∉ closure g := by
        intro g hg hxg
        obtain ⟨b, hb⟩ := exists_end_eq hγ hg hxV hxg
        exact h0.false ⟨(g, b), hg, hb⟩
      have hop : IsOpen (Γ.U \ {x})ᶜ := by
        have hcl : IsClosed (Γ.U \ {x}) := by
          have heq : Γ.U \ {x} = (Γ.V \ {x}) ∪ ⋃ g ∈ Γ.E, closure g := by
            ext y
            rw [Γ.U_eq]
            constructor
            · rintro ⟨hy | hy, hyx⟩
              · exact Or.inl ⟨hy, hyx⟩
              · exact Or.inr hy
            · rintro (⟨hy, hyx⟩ | hy)
              · exact ⟨Or.inl hy, hyx⟩
              · refine ⟨Or.inr hy, fun h => ?_⟩
                obtain ⟨g, hg, hyg⟩ := mem_iUnion₂.mp hy
                exact hno g hg (mem_singleton_iff.mp h ▸ hyg)
          rw [heq]
          exact (Γ.finite_V.subset sdiff_subset).isClosed.union
            (Γ.finite_edges.isClosed_biUnion fun _ _ => isClosed_closure)
        exact hcl.isOpen_compl
      obtain ⟨Z, hZ, hxZ, hZO, hconn, -⟩ := exists_punctured_nbhd hS hop (by
        rintro ⟨-, h⟩
        exact h rfl)
      have hoff : Disjoint (Z \ {x}) Γ.U := disjoint_left.mpr fun y hy hyU =>
        hZO hy.1 ⟨hyU, hy.2⟩
      refine ⟨Z, hZ, hxZ, fun a ha hau b hb hbu => ⟨Z \ {x}, hconn, hoff, ⟨ha, ?_⟩, ⟨hb, ?_⟩⟩⟩
      · exact fun h => hau (mem_singleton_iff.mp h ▸ Γ.V_subset_U hxV)
      · exact fun h => hbu (mem_singleton_iff.mp h ▸ Γ.V_subset_U hxV)
    · obtain ⟨Z, hZ, hxZ, h⟩ := exists_single_nbhd hS hγ k fun l => Subsingleton.elim l k
      refine ⟨Z, hZ, hxZ, fun a ha hau b hb hbu => ?_⟩
      obtain ⟨A, h₁, h₂, h₃, h₄, -⟩ := h a ha hau b hb hbu
      exact ⟨A, h₁, h₂, h₃, h₄⟩
  obtain ⟨Z, hZ, hxZ, hsame⟩ := key
  refine ⟨Z, hZ, hxZ, fun y hy => mem_closure_iff.mpr fun O hO hyO => ?_⟩
  obtain ⟨z, hzZ, hzr⟩ := mem_closure_iff.mp hxr Z hZ hxZ
  have hzU := region_subset hr hzr
  obtain ⟨w, ⟨hwO, hwZ⟩, hwU⟩ := exists_notMem_U (Γ := Γ) hS (hO.inter hZ)
    ⟨y, hyO, hy⟩
  obtain ⟨A, h₁, h₂, h₃, h₄⟩ := hsame z hzZ hzU w hwZ hwU
  exact ⟨w, hwO, subset_region hr h₁ h₂ h₃ hzr h₄⟩

/-- The closure of a region is connected in the small at a vertex. -/
theorem locJoin_region_vertex (hS : IsClosedSurface S) {Γ : Drawing S} {r : Set S} (hr : r ∈ Γ.R)
    {x : S} (hxV : x ∈ Γ.V) (hxr : x ∈ closure r) : LocJoin (closure r) x := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hlp : LocallyPathConnectedSpace S := IsClosedSurface.locallyPathConnectedSpace hS
  intro A hA hxA
  obtain ⟨γ, hγ⟩ := exists_edgePar Γ
  -- The points of the drawing near `x`.
  have hA' : ∀ g ∈ {g | g ∈ Γ.E ∧ x ∈ closure g}, ∃ N : Set S, IsOpen N ∧ x ∈ N ∧
      ∀ y ∈ closure g ∩ N, JoinedIn (closure g ∩ A) x y := fun g hg =>
    locJoin_edge hg.1 hγ hg.2 A hA hxA
  choose! Ng hNo hNm hNj using hA'
  have hfin₁ : {g | g ∈ Γ.E ∧ x ∈ closure g}.Finite := Γ.finite_edges.subset fun _ h => h.1
  have hfin₂ : {g | g ∈ Γ.E ∧ x ∉ closure g}.Finite := Γ.finite_edges.subset fun _ h => h.1
  let N₁ : Set S := (⋂ g ∈ {g | g ∈ Γ.E ∧ x ∈ closure g}, Ng g) ∩
    (⋂ g ∈ {g | g ∈ Γ.E ∧ x ∉ closure g}, (closure g)ᶜ) ∩ (Γ.V \ {x})ᶜ
  have hN₁ : IsOpen N₁ :=
    ((hfin₁.isOpen_biInter hNo).inter (hfin₂.isOpen_biInter fun _ _ =>
      isClosed_closure.isOpen_compl)).inter
      (Γ.finite_V.subset sdiff_subset).isClosed.isOpen_compl
  have hxN₁ : x ∈ N₁ :=
    ⟨⟨mem_iInter₂.mpr hNm, mem_iInter₂.mpr fun g hg => hg.2⟩, fun h => h.2 rfl⟩
  have hjx : JoinedIn (closure r ∩ A) x x := JoinedIn.refl ⟨hxr, hxA⟩
  have hstep₁ : ∀ y ∈ closure r ∩ N₁, y ∈ Γ.U → JoinedIn (closure r ∩ A) x y := by
    rintro y ⟨hyr, ⟨hy₁, hy₂⟩, hy₃⟩ hyU
    by_cases hyx : y = x
    · exact hyx ▸ hjx
    have hyV : y ∉ Γ.V := fun h => hy₃ ⟨h, hyx⟩
    rw [Γ.U_eq] at hyU
    obtain ⟨g, hg, hyg⟩ := mem_iUnion₂.mp (hyU.resolve_left hyV)
    have hyge : y ∈ g := (Γ.closure_diff_V hg).subset ⟨hyg, hyV⟩
    have hgsub := edge_subset_closure_of_incident hS hg hr ⟨y, hyge, hyr⟩
    have hcl : closure g ⊆ closure r := closure_minimal hgsub isClosed_closure
    have hxg : x ∈ closure g := by
      by_contra h
      exact mem_iInter₂.mp hy₂ g ⟨hg, h⟩ hyg
    refine (hNj g ⟨hg, hxg⟩ y ⟨hyg, mem_iInter₂.mp hy₁ g ⟨hg, hxg⟩⟩).mono ?_
    exact inter_subset_inter_left _ hcl
  -- The points of `r` near `x`.
  have hstep₂ : ∃ N₂ : Set S, IsOpen N₂ ∧ x ∈ N₂ ∧ ∀ y ∈ r ∩ N₂, JoinedIn (closure r ∩ A) x y := by
    by_cases h2 : 2 ≤ Nat.card (halfEdges Γ γ x)
    · obtain ⟨next, ρ, P, W, Q, τ, hs⟩ := exists_sectors hS Γ hγ hxV h2
      have hfin : Finite (halfEdges Γ γ x) := (finite_halfEdges Γ γ x).to_subtype
      have hWA : IsOpen (W ∩ A) := (IsSectors.isOpen hs).inter hA
      have hxWA : x ∈ W ∩ A := ⟨IsSectors.mem hs, hxA⟩
      choose N hNo' hNm' hNp using fun k =>
        exists_disc_approach (IsSectors.disc hs k) (IsSectors.bd hs k) hWA hxWA
      refine ⟨(W ∩ A) ∩ ⋂ k, N k, hWA.inter (isOpen_iInter_of_finite hNo'),
        ⟨hxWA, mem_iInter.mpr hNm'⟩, ?_⟩
      rintro y ⟨hyr, hyW, hyN⟩
      obtain ⟨k, hk⟩ := mem_iUnion.mp (IsSectors.cover hs ⟨hyW.1, region_subset hr hyr⟩)
      have hrk : r = ρ k := region_eq_of_mem hr ((IsSectors.corners hs).region k) hyr
        (IsSectors.sub hs k hk)
      have hyb : y ∉ discBd (Q k) := fun h =>
        region_subset hr hyr (IsSectors.bdU hs k ⟨hyW.1, h⟩)
      obtain ⟨p, hp⟩ := hNp k y ⟨mem_iInter.mp hyN k, IsSectors.subQ hs k hk⟩ hyb
      refine ⟨p, fun t => ?_⟩
      rcases hp t with h | h
      · rw [h]
        exact ⟨hxr, hxA⟩
      · have hin : p t ∈ P k := IsSectors.inside hs k ⟨⟨h.1.1.1, h.1.2⟩, h.2⟩
        have hρ : p t ∈ r := hrk ▸ IsSectors.sub hs k hin
        exact ⟨subset_closure hρ, h.1.1.2⟩
    · obtain ⟨Z, hZ, hxZ, hZr⟩ := exists_nbhd_of_few hS hγ hxV h2 hr hxr
      refine ⟨pathComponentIn (Z ∩ A) x, (hZ.inter hA).pathComponentIn x,
        mem_pathComponentIn_self ⟨hxZ, hxA⟩, ?_⟩
      rintro y ⟨-, hy⟩
      have hj : JoinedIn (Z ∩ A) x y := hy
      exact hj.mono (inter_subset_inter_left _ hZr)
  obtain ⟨N₂, hN₂, hxN₂, h₂⟩ := hstep₂
  refine ⟨N₁ ∩ N₂, hN₁.inter hN₂, ⟨hxN₁, hxN₂⟩, ?_⟩
  rintro y ⟨hyr, hy₁, hy₂⟩
  by_cases hyU : y ∈ Γ.U
  · exact hstep₁ y ⟨hyr, hy₁⟩ hyU
  · exact h₂ y ⟨(closure_region_subset hr hyr).resolve_right hyU, hy₂⟩

/-- The closure of a region is connected in the small. -/
theorem locJoin_region (hS : IsClosedSurface S) {Γ : Drawing S} {r : Set S} (hr : r ∈ Γ.R) {x : S}
    (hxr : x ∈ closure r) : LocJoin (closure r) x := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hlp : LocallyPathConnectedSpace S := IsClosedSurface.locallyPathConnectedSpace hS
  by_cases hxU : x ∈ Γ.U
  · by_cases hxV : x ∈ Γ.V
    · exact locJoin_region_vertex hS hr hxV hxr
    classical
    have hxU' := hxU
    rw [Γ.U_eq] at hxU'
    obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp (hxU'.resolve_left hxV)
    have hxee : x ∈ e := (Γ.closure_diff_V he).subset ⟨hxe, hxV⟩
    choose! c hc using fun g (hg : g ∈ Γ.E) => (hg.1 : g.Nonempty)
    let m : Set S → S := fun g => if g = e then x else c g
    have hm : ∀ g ∈ Γ.E, m g ∈ g := by
      intro g hg
      by_cases h : g = e
      · simp only [m, h, ite_true]
        exact hxee
      · simp only [m, h, ite_false]
        exact hc g hg
    obtain ⟨D, hDU, hDV⟩ := exists_added_vertices Γ hm
    have hxD : x ∈ D.V := by
      rw [hDV]
      refine Or.inr ⟨e, he, ?_⟩
      simp [m]
    have hrD : r ∈ D.R := (mem_R_iff D).mpr (by
      rw [hDU]
      exact (mem_R_iff Γ).mp hr)
    exact locJoin_region_vertex hS hrD hxD hxr
  · have hxr' : x ∈ r := (closure_region_subset hr hxr).resolve_right hxU
    intro A hA hxA
    refine ⟨pathComponentIn (r ∩ A) x, ((region_isOpen hr).inter hA).pathComponentIn x,
      mem_pathComponentIn_self ⟨hxr', hxA⟩, ?_⟩
    rintro y ⟨-, hy⟩
    have hj : JoinedIn (r ∩ A) x y := hy
    exact hj.mono (inter_subset_inter_left _ subset_closure)

/-- **A closed nice set is solid.** -/
theorem isSolid_of_nice (hS : IsClosedSurface S) {Γ : Drawing S} {X : Set S} (hc : IsClosed X)
    (hn : IsGammaNice Γ X) : IsSolid X := by
  refine ⟨isLocallyArcConnected_of_locJoin ?_, hc⟩
  obtain ⟨𝒜, h𝒜, hX⟩ := hn
  have hfin : Γ.A.Finite :=
    ((Γ.finite_V.image _).union Γ.finite_edges).union (finite_R hS Γ)
  have hfin𝒜 := hfin.subset h𝒜
  have hsub : ∀ a ∈ 𝒜, closure a ⊆ X := fun a ha =>
    closure_minimal (fun y hy => hX ▸ mem_sUnion.mpr ⟨a, ha, hy⟩) hc
  have hatom : ∀ a ∈ 𝒜, ∀ x ∈ closure a, LocJoin (closure a) x := by
    obtain ⟨γ, hγ⟩ := exists_edgePar Γ
    intro a ha x hx
    rcases h𝒜 ha with (⟨v, -, rfl⟩ | he) | hr
    · intro A _ hxA
      refine ⟨univ, isOpen_univ, mem_univ _, ?_⟩
      rintro y ⟨hy, -⟩
      have h₁ : x = v := by simpa using hx
      have h₂ : y = v := by simpa using hy
      subst h₁
      subst h₂
      exact JoinedIn.refl ⟨hx, hxA⟩
    · exact locJoin_edge he hγ hx
    · exact locJoin_region hS hr hx
  intro x hx A hA hxA
  have hA' : ∀ a ∈ {a | a ∈ 𝒜 ∧ x ∈ closure a}, ∃ N : Set S, IsOpen N ∧ x ∈ N ∧
      ∀ y ∈ closure a ∩ N, JoinedIn (closure a ∩ A) x y := fun a ha =>
    hatom a ha.1 x ha.2 A hA hxA
  choose! N hNo hNm hNj using hA'
  have hfin₁ : {a | a ∈ 𝒜 ∧ x ∈ closure a}.Finite := hfin𝒜.subset fun _ h => h.1
  have hfin₂ : {a | a ∈ 𝒜 ∧ x ∉ closure a}.Finite := hfin𝒜.subset fun _ h => h.1
  refine ⟨_, (hfin₁.isOpen_biInter hNo).inter
    (hfin₂.isOpen_biInter fun _ _ => isClosed_closure.isOpen_compl),
    ⟨mem_iInter₂.mpr hNm, mem_iInter₂.mpr fun a ha => ha.2⟩, ?_⟩
  rintro y ⟨hyX, hy₁, hy₂⟩
  obtain ⟨a, ha, hya⟩ := mem_sUnion.mp (hX ▸ hyX : y ∈ ⋃₀ 𝒜)
  have hxa : x ∈ closure a := by
    by_contra h
    exact mem_iInter₂.mp hy₂ a ⟨ha, h⟩ (subset_closure hya)
  have hmem : a ∈ {a | a ∈ 𝒜 ∧ x ∈ closure a} := ⟨ha, hxa⟩
  exact (hNj a hmem y ⟨subset_closure hya, mem_iInter₂.mp hy₁ a hmem⟩).mono
    (inter_subset_inter_left _ (hsub a ha))

end GraphMinor.GM11

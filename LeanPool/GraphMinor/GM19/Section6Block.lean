/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section6Hub
public import LeanPool.GraphMinor.GM19.Section6Comp
public import LeanPool.GraphMinor.GM19.Section6Region

/-!
# Graph Minors XIX, (6.7): `sk(Γ)` is a block

Let `Γ` be an internally 3-connected painting. The paper's proof, page 342, shows that the closed
curve
tracing the perimeter of a region has no repeated vertices, and then finds that a vertex that cuts
`sk(Γ)` would have to cut such a curve.

A repeated vertex would give two spokes to the hub of the region with the same ends, and these bound
a
disc that misses `sk(Γ)` except at the vertex, which condition (iv) of a radial drawing forbids
(`spoke_once`). For a region of `Γ` in `Σ̂` the disc is `pinch`, which is where internal
3-connectivity is used, and for the inside of an edge of size 3 it comes from `pinch_of_cell`. So
each
region has a perimeter as in `exists_perimeter`. A set of vertices closed under adjacency off a
vertex
`v` that meets the closure of a region holds all vertices other than `v` in that closure
(`sk_region_part`), and since `Σ̂ \ v` is connected this gives all vertices other than `v`
(`conn_of_regions`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11

section Generic

variable {T : Type} [TopologicalSpace T]

/-- Two spokes with the same ends, in a region in which each `O`-arc through the vertex bounds a
disc
that misses the drawing, are equal. The proof is that of `spoke_unique`. -/
theorem spoke_once (hT : IsClosedSurface T) {D G₃ : Drawing T}
    (hrad : PreRad (PaintingOrDrawing.drawing D) G₃) {e₁ e₂ r : Set T} (he₁ : e₁ ∈ G₃.E)
    (he₂ : e₂ ∈ G₃.E) (hrD : r ∈ D.R) (h₁r : e₁ ⊆ r) (h₂r : e₂ ⊆ r) {v : T} (hv : v ∈ D.V) {w : T}
    (hw : w ∈ r) (hwG : w ∈ G₃.V) (h₁ : closure e₁ ∩ G₃.V = {v, w})
    (h₂ : closure e₂ ∩ G₃.V = {v, w})
    (hpinch : ∀ F : Set T, IsOArc F → v ∈ F → v ∈ closure (F \ {v}) → F \ {v} ⊆ r →
      ∃ Δ, IsClosedDisc Δ ∧ discBd Δ = F ∧ Δ ∩ D.U ⊆ {v}) : e₁ = e₂ := by
  by_contra hne
  have : T2Space T := hT.2.1
  have hman : ∀ x : T, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  have hlc : LocallyConnectedSpace T := IsClosedSurface.locallyConnectedSpace hT
  have hdis : Disjoint r D.U := by
    refine disjoint_left.mpr fun x hx hxU ↦ region_subset hrD hx hxU
  have hvne : v ≠ w := fun h ↦ disjoint_left.mp hdis hw
    (D.V_subset_U (h ▸ hv))
  have hL₁ : IsLineWithEnds (closure e₁) (v) w := isLine_closure he₁ hvne h₁
  have hL₂ : IsLineWithEnds (closure e₂) (v) w := isLine_closure he₂ hvne h₂
  have hcl : ∀ {e}, e ∈ G₃.E → closure e ∩ G₃.V = {v, w} → closure e ⊆ e ∪ {v, w} := by
    intro e he hset x hx
    rcases closure_edge_subset he hx with h | h
    · exact Or.inl h
    · exact Or.inr (hset ▸ ⟨hx, h⟩)
  have hcap : closure e₁ ∩ closure e₂ ⊆ {v, w} := by
    rintro x ⟨hx₁, hx₂⟩
    rcases hcl he₁ h₁ hx₁ with h | h
    · rcases hcl he₂ h₂ hx₂ with h' | h'
      · exact absurd (arcComp_eq_of_mem he₁ he₂ h h') hne
      · exact h'
    · exact h
  have hO := isOArc_union hL₁ hL₂ hcap
  have hsubr : (closure e₁ ∪ closure e₂) \ {v} ⊆ r := by
    have hc : ∀ {e}, e ∈ G₃.E → e ⊆ r → closure e ∩ G₃.V = {v, w} →
        closure e \ {v} ⊆ r := by
      intro e he her hset x hx
      rcases hcl he hset hx.1 with h | h | h
      · exact her h
      · exact absurd h hx.2
      · exact h ▸ hw
    rintro x ⟨hx | hx, hxn⟩
    · exact hc he₁ h₁r h₁ ⟨hx, hxn⟩
    · exact hc he₂ h₂r h₂ ⟨hx, hxn⟩
  have hvm : v ∈ closure e₁ := by
    have : v ∈ closure e₁ ∩ G₃.V := by rw [h₁]; exact Or.inl rfl
    exact this.1
  have hclv : v ∈ closure ((closure e₁ ∪ closure e₂) \ {v}) := by
    have : e₁ ⊆ (closure e₁ ∪ closure e₂) \ {v} := fun x hx ↦
      ⟨Or.inl (subset_closure hx), fun h ↦ hdis.le_bot ⟨h₁r hx, D.V_subset_U (by
        rw [mem_singleton_iff.mp h]
        exact hv)⟩⟩
    exact closure_mono this hvm
  obtain ⟨Δ, hΔ, hbd, hΔU⟩ := hpinch _ hO (Or.inl hvm) hclv hsubr
  have hsubΔ : Δ ⊆ r ∪ {v} := by
    have hopen := hΔ.isOpen_discInt hman
    obtain ⟨x, hx⟩ := he₁.1
    have hxb : x ∈ discBd Δ := by rw [hbd]; exact Or.inl (subset_closure hx)
    have hxΔ : x ∈ closure (discInt Δ) := hΔ.subset_closure_discInt (Surface.discBd_subset _ hxb)
    obtain ⟨y, hyr, hyi⟩ := mem_closure_iff.mp hxΔ r (region_isOpen hrD) (h₁r hx)
    have hdI : Disjoint (discInt Δ) D.U := by
      refine disjoint_left.mpr fun z hz hzU ↦ ?_
      have hzv : z = v := hΔU ⟨hz.1, hzU⟩
      apply hz.2
      rw [hbd, hzv]
      exact Or.inl hvm
    have hIr := subset_region hrD hΔ.isPreconnected_discInt hdI hyi hyr
    intro z hz
    by_cases hzb : z ∈ discBd Δ
    · rw [hbd] at hzb
      by_cases hzv : z = v
      · exact Or.inr hzv
      · exact Or.inl (hsubr ⟨hzb, hzv⟩)
    · exact Or.inl (hIr ⟨hz, hzb⟩)
  refine hrad.2.2.2.2.2.2 e₁ he₁ e₂ he₂ hne (v) ?_ r hrD w ⟨hw, hwG⟩ h₁ h₂
    ⟨Δ, hΔ, hsubΔ, ?_⟩
  · exact hv
  · rw [← hbd, ← subBd_eq_frontier', IsClosedDisc.frontier_eq_discBd hT hΔ]


/-- A closed nonempty family: the closures of the regions cover the surface. -/
theorem exists_region_closure (hT : IsClosedSurface T) [ConnectedSpace T] (D : Drawing T) (x : T) :
    ∃ r ∈ D.R, x ∈ closure r := by
  have hlc : LocallyConnectedSpace T := IsClosedSurface.locallyConnectedSpace hT
  have : T2Space T := hT.2.1
  have hx : x ∈ closure (⋃ r ∈ D.R, r) := by
    rw [mem_closure_iff]
    intro O hO hxO
    obtain ⟨y, hyO, hyU⟩ := exists_notMem_U (Γ := D) hT hO ⟨x, hxO⟩
    obtain ⟨r, hr, hyr⟩ := exists_region_of_notMem hyU
    exact ⟨y, hyO, mem_biUnion hr hyr⟩
  rw [(finite_R hT D).closure_biUnion] at hx
  obtain ⟨r, hr, h⟩ := mem_iUnion₂.mp hx
  exact ⟨r, hr, h⟩

theorem regions_eq_R (D : Drawing T) : D.regions = D.R := by
  rw [Drawing.regions, Surface.Drawing.R, compl_eq_univ_sdiff]

/-- **From regions to the whole drawing.** Let `X` be a set of at most one point. If a set of
vertices
off `X` closed under adjacency off `X` holds, with one vertex in the closure of a region, every
vertex
off `X` in that closure, then the vertices off `X` are connected. The reason is that `T \ X` is
connected, and it would otherwise be split by two closed unions of closures of regions. -/
theorem conn_of_regions (hT : IsClosedSurface T) [ConnectedSpace T] (D : Drawing T)
  (hl : LoopFree D)
    {X : Set T} (hX : X.Subsingleton)
    (hreg : ∀ r ∈ D.R, ∀ Y ⊆ D.V \ X, (∀ a ∈ Y, ∀ b ∈ D.V \ X, D.adj.Adj a b → b ∈ Y) →
      ∀ x ∈ Y, x ∈ closure r → ∀ y ∈ D.V \ X, y ∈ closure r → y ∈ Y) : ConnIn D (D.V \ X) := by
  classical
  have hlc : LocallyConnectedSpace T := IsClosedSurface.locallyConnectedSpace hT
  have : T2Space T := hT.2.1
  intro Y hY hne hc
  by_contra hn
  obtain ⟨w, hw, hwY⟩ : ∃ w ∈ D.V \ X, w ∉ Y := by
    by_contra h
    push Not at h
    exact hn (Subset.antisymm hY h)
  obtain ⟨y, hy⟩ := hne
  have hRfin := finite_R hT D
  let 𝓐 : Set (Set T) := {r | r ∈ D.R ∧ (Y ∩ closure r).Nonempty}
  let 𝓑 : Set (Set T) := {r | r ∈ D.R ∧ ¬ (Y ∩ closure r).Nonempty}
  let Z₁ : Set T := ⋃ r ∈ 𝓐, closure r
  let Z₂ : Set T := ⋃ r ∈ 𝓑, closure r
  have hfin₁ : 𝓐.Finite := hRfin.subset fun _ h => h.1
  have hfin₂ : 𝓑.Finite := hRfin.subset fun _ h => h.1
  have hZ₁ : IsClosed Z₁ := hfin₁.isClosed_biUnion fun _ _ => isClosed_closure
  have hZ₂ : IsClosed Z₂ := hfin₂.isClosed_biUnion fun _ _ => isClosed_closure
  have hcov : Xᶜ ⊆ Z₁ ∪ Z₂ := fun x _ ↦ by
    obtain ⟨r, hr, hxr⟩ := exists_region_closure hT D x
    by_cases h : (Y ∩ closure r).Nonempty
    · exact Or.inl (mem_biUnion (x := r) ⟨hr, h⟩ hxr)
    · exact Or.inr (mem_biUnion (x := r) ⟨hr, h⟩ hxr)
  have hne₁ : (Xᶜ ∩ Z₁).Nonempty := by
    obtain ⟨r, hr, hxr⟩ := exists_region_closure hT D y
    exact ⟨y, (hY hy).2, mem_biUnion (x := r) ⟨hr, y, hy, hxr⟩ hxr⟩
  have hne₂ : (Xᶜ ∩ Z₂).Nonempty := by
    obtain ⟨r, hr, hxr⟩ := exists_region_closure hT D w
    refine ⟨w, hw.2, mem_biUnion (x := r) ⟨hr, ?_⟩ hxr⟩
    rintro ⟨z, hzY, hzr⟩
    exact hwY (hreg r hr Y hY hc z hzY hzr w hw hxr)
  have hconn : IsPreconnected Xᶜ := by
    have hfin : X.Finite := hX.finite
    exact Surface.isPreconnected_compl_finite hT hfin
  obtain ⟨z, hzX, hz₁, hz₂⟩ := isPreconnected_closed_iff.mp hconn Z₁ Z₂ hZ₁ hZ₂ hcov hne₁ hne₂
  obtain ⟨r, ⟨hr, v, hvY, hvr⟩, hzr⟩ := mem_iUnion₂.mp hz₁
  obtain ⟨r', ⟨hr', hnr'⟩, hzr'⟩ := mem_iUnion₂.mp hz₂
  have hrg : r ∈ D.regions := by rw [regions_eq_R]; exact hr
  have hrg' : r' ∈ D.regions := by rw [regions_eq_R]; exact hr'
  -- A vertex off `X` in both closures is a contradiction.
  have hvert : ∀ u ∈ D.V \ X, u ∈ closure r → u ∈ closure r' → False := fun u hu h₁ h₂ ↦
    hnr' ⟨u, hreg r hr Y hY hc v hvY hvr u hu h₁, h₂⟩
  have hneq : r ≠ r' := by
    rintro rfl
    exact hnr' ⟨v, hvY, hvr⟩
  have hzU : z ∈ D.U := by
    by_contra hzU
    obtain ⟨-, -, -, -, -, h₁⟩ := region_props D hrg
    obtain ⟨-, -, -, -, -, h₂⟩ := region_props D hrg'
    have hzr₁ : z ∈ r := by_contra fun h ↦ hzU (h₁ ⟨hzr, h⟩)
    obtain ⟨p, hpo, hpr⟩ := mem_closure_iff.mp hzr' r (region_props D hrg).1 hzr₁
    exact hneq (region_eq_of_mem hr hr' hpo hpr)
  by_cases hzV : z ∈ D.V
  · exact hvert z ⟨hzV, hzX⟩ hzr hzr'
  obtain ⟨e, he, hze⟩ := exists_edge_of_mem D hzU hzV
  have h₁ := edge_subset_closure hT D hl he hrg ⟨z, hze, hzr⟩
  have h₂ := edge_subset_closure hT D hl he hrg' ⟨z, hze, hzr'⟩
  obtain ⟨a, b, hab, -, -, hset⟩ := exists_end D hl he
  have hcl : ∀ {q}, e ⊆ closure q → closure e ⊆ closure q := fun h ↦ closure_minimal h
    isClosed_closure
  have ha : a ∈ closure e ∩ D.V := by rw [hset]; exact Or.inl rfl
  have hb : b ∈ closure e ∩ D.V := by rw [hset]; exact Or.inr rfl
  by_cases haX : a ∈ X
  · have hbX : b ∉ X := fun h ↦ hab (hX haX h)
    exact hvert b ⟨hb.2, hbX⟩ (hcl h₁ hb.1) (hcl h₂ hb.1)
  · exact hvert a ⟨ha.2, haX⟩ (hcl h₁ ha.1) (hcl h₂ ha.1)

end Generic

section Sk

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {Γ : Painting S} {D G₃ : Drawing Shat}

omit [T2Space S] [T2Space Shat] in
/-- The inside of the disc of an edge `c` of size 3 holds a region `r` of `sk(Γ)`, with `sk(Γ)` in
the
disc only on its boundary. -/
theorem cell_facts (hD : IsSkHat cap Γ D) {r c : Set Shat} {c₀ : Set S}
    (hr : r ∈ D.R) (hc₀ : c₀ ∈ Γ.E) (h3 : (tilde c₀).ncard = 3) (hc : c = cap.emb '' closure c₀)
    (hrs : r ⊆ c) : IsClosedDisc c ∧ r ⊆ discInt c ∧ c ∩ D.U ⊆ discBd c := by
  subst hc
  obtain ⟨hdisc, hT', -⟩ := Γ.isDisc_of_three hc₀ h3
  obtain ⟨hΔ, hbd⟩ := isClosedDisc_image hdisc cap.isEmbedding
  have hbdsk : discBd (closure c₀) ⊆ Γ.skU := fun x hx ↦
    Or.inr (mem_iUnion₂.2 ⟨c₀, ⟨hc₀, h3⟩, hx⟩)
  refine ⟨hΔ, fun x hx ↦ ⟨hrs hx, fun hb ↦ ?_⟩, ?_⟩
  · rw [hbd] at hb
    refine region_subset hr hx ?_
    rw [hD.hU]
    exact image_mono hbdsk hb
  · rintro _ ⟨⟨x, hx, rfl⟩, hxU⟩
    rw [hD.hU] at hxU
    obtain ⟨z, hz, hzx⟩ := hxU
    obtain rfl := cap.isEmbedding.injective hzx
    rw [hbd]
    refine mem_image_of_mem _ ?_
    by_contra hnb
    have hzc : z ∈ c₀ := by
      by_contra hn
      exact hnb (hT' ⟨hx, hn⟩)
    have hzV : z ∉ Γ.V := Γ.disjoint_V hc₀ hzc
    rcases hz with (hz | hz) | hz
    · exact hzV hz
    · obtain ⟨e, ⟨he, h2⟩, hze⟩ := mem_iUnion₂.mp hz
      have := arcComp_eq_of_mem he hc₀ hze hzc
      rw [this, h3] at h2
      omega
    · obtain ⟨e, ⟨he, h2⟩, hze⟩ := mem_iUnion₂.mp hz
      have hze' : z ∈ e := by
        by_contra hn
        exact hzV (Γ.tilde_subset_V he ⟨Surface.discBd_subset _ hze, hn⟩)
      have := arcComp_eq_of_mem he hc₀ hze' hzc
      exact hnb (this ▸ hze)

/-- Each vertex has one spoke into each region of `sk(Γ)`, for a radial drawing of `sk(Γ)`. -/
theorem sk_spoke_once (hS : IsSurface S) (hD : IsSkHat cap Γ D)
    (h3 : Γ.IsInternallyThreeConnected) (hrad : PreRad (PaintingOrDrawing.drawing D) G₃)
    {r : Set Shat} (hr : r ∈ D.R) : ∀ e₁ ∈ G₃.E, ∀ e₂ ∈ G₃.E, e₁ ⊆ r → e₂ ⊆ r → ∀ v ∈ D.V, ∀ c ∈ r,
      c ∈ G₃.V → closure e₁ ∩ G₃.V = {v, c} → closure e₂ ∩ G₃.V = {v, c} → e₁ = e₂ := by
  intro e₁ he₁ e₂ he₂ h₁r h₂r v hv c hc hcV h₁ h₂
  have hT := cap.isClosedSurface
  refine spoke_once hT hrad he₁ he₂ hr h₁r h₂r hv hc hcV h₁ h₂ fun F hF hvF hcl hsub ↦ ?_
  rcases hD.region_cases hr with hh | ⟨c₀, hc₀, h3c, hrs⟩
  · rw [hD.hV] at hv
    obtain ⟨v₀, hv₀, rfl⟩ := hv
    exact pinch hS hD h3 hh hv₀ hF hvF hcl hsub
  · obtain ⟨hΔ, hint, hU⟩ := cell_facts hD hr hc₀ h3c rfl hrs
    have hrΔ : closure r ⊆ cap.emb '' closure c₀ := closure_minimal hrs hΔ.isClosed
    refine pinch_of_cell hT hΔ hF (fun x hx ↦ ?_) (fun x hx ↦ hint (hsub hx)) hU
    by_cases hxv : x = v
    · exact hrΔ (closure_mono hsub (hxv ▸ hcl))
    · exact (hint (hsub ⟨hx, hxv⟩)).1

/-- **Two vertices on the perimeter of a region.** A set of vertices off a point of `X`, closed
under
adjacency off `X`, that holds a vertex in the closure of `r` holds all vertices off `X` in that
closure. -/
theorem sk_region_part [ConnectedSpace Shat] (hS : IsSurface S) (hD : IsSkHat cap Γ D)
    (h3 : Γ.IsInternallyThreeConnected) (hrad : PreRad (PaintingOrDrawing.drawing D) G₃)
    (hmax : RadMax (PaintingOrDrawing.drawing D) G₃) {X : Set Shat} (hX : X.Subsingleton)
    {r : Set Shat} (hr : r ∈ D.R) {Y : Set Shat} (hY : Y ⊆ D.V \ X)
    (hc : ∀ a ∈ Y, ∀ b ∈ D.V \ X, D.adj.Adj a b → b ∈ Y) {x : Shat} (hx : x ∈ Y)
    (hxr : x ∈ closure r) {y : Shat} (hy : y ∈ D.V \ X) (hyr : y ∈ closure r) : y ∈ Y := by
  have hT := cap.isClosedSurface
  obtain ⟨κ, _, next, A, hA, -, hrange, hedge, hreach⟩ := exists_perimeter hT hrad hmax
    (hD.E_nonempty h3.1) (hD.no_loops hS) hr (sk_spoke_once hS hD h3 hrad hr)
  have hAV : ∀ k, A k ∈ D.V := fun k ↦ (hrange.subset ⟨k, rfl⟩).1
  obtain ⟨k, rfl⟩ : x ∈ range A := by
    rw [hrange]
    exact ⟨(hY hx).1, hxr⟩
  obtain ⟨j, rfl⟩ : y ∈ range A := by
    rw [hrange]
    exact ⟨hy.1, hyr⟩
  have hadj : ∀ a, A a ∉ X → A (next a) ∉ X → (A a ∈ Y ↔ A (next a) ∈ Y) := by
    intro a h₁ h₂
    by_cases he : A a = A (next a)
    · rw [← he]
    obtain ⟨e, heE, hset⟩ := hedge a
    have hm : ∀ {z}, z ∈ ({A a, A (next a)} : Set Shat) → z ∈ tilde e := fun {z} hz ↦ by
      rw [tilde_eq_inter_V D heE, hset]
      exact hz
    have hAd : D.adj.Adj (A a) (A (next a)) := ⟨he, hAV a, hAV _, e, heE, hm (Or.inl rfl), hm
      (Or.inr rfl)⟩
    exact ⟨fun h ↦ hc _ h _ ⟨hAV _, h₂⟩ hAd, fun h ↦ hc _ h _ ⟨hAV _, h₁⟩ hAd.symm⟩
  by_cases hb : ∃ b, A b ∈ X
  · obtain ⟨b, hbX⟩ := hb
    have hnb : ∀ a, a ≠ b → A a ∉ X := fun a hab h ↦ hab (hA (hX h hbX))
    refine cycle_avoid (Y := A ⁻¹' Y) hreach b ⟨k, hx⟩ (fun h ↦ (hY h).2 hbX) ?_ ?_ j ?_
    · intro a ha hn
      exact (hadj a (fun h ↦ (hY ha).2 h) (hnb _ hn)).mp ha
    · intro a ha hn
      exact (hadj a (hnb _ hn) (fun h ↦ (hY ha).2 h)).mpr ha
    · rintro rfl
      exact hy.2 hbX
  · push Not at hb
    have key : ∀ i, Relation.ReflTransGen (fun x y => y = next x) k i → A i ∈ Y := by
      intro i h
      induction h with
      | refl => exact hx
      | tail _ hs ih =>
        subst hs
        exact (hadj _ (hb _) (hb _)).mp ih
    exact key j (hreach k j)

/-- **Graph Minors XIX, (6.7), first statement** (page 342): `sk(Γ)` is a block. -/
theorem sk_isBlock [ConnectedSpace Shat] (hS : IsSurface S) (hD : IsSkHat cap Γ D)
    (h3 : Γ.IsInternallyThreeConnected) (hl : LoopFree D)
    (hrad : PreRad (PaintingOrDrawing.drawing D) G₃)
    (hmax : RadMax (PaintingOrDrawing.drawing D) G₃) : D.IsBlock := by
  have hT := cap.isClosedSurface
  have hconn : ∀ {X : Set Shat}, X.Subsingleton → ConnIn D (D.V \ X) := fun hX ↦
    conn_of_regions hT D hl hX fun r hr Y hY hc x hx hxr y hy hyr ↦
      sk_region_part hS hD h3 hrad hmax hX hr hY hc hx hxr hy hyr
  obtain ⟨e, he⟩ := hD.E_nonempty h3.1
  obtain ⟨a, b, -, -, -, hset⟩ := exists_end D hl he
  refine ⟨⟨a, (show a ∈ closure e ∩ D.V by rw [hset]; exact Or.inl rfl).2⟩, ?_, fun v _ ↦ ?_⟩
  · have := hconn (X := ∅) subsingleton_empty
    rw [sdiff_empty] at this
    exact (preconnected_iff_connIn D _).mpr this
  · exact (preconnected_iff_connIn D _).mpr (hconn subsingleton_singleton)

end Sk

end GraphMinor.GM19

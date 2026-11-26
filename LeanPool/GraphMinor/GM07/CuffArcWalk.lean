/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CuffArc
public import LeanPool.GraphMinor.GM07.SideDisc
public import LeanPool.GraphMinor.GM12.Section3OneDiscComplement
public import LeanPool.GraphMinor.GM11.PerimeterPull

/-!
# The path of `G` from `C` to `A`, in (6.1)

Graph Minors VII, (6.1), page 238: "if $V(G) \cap C \ne \emptyset$ there is a path of $G$ between
$C$ and $a_1$ not using $a_2$. (If $V(G) \cap C \ne \emptyset$ there is such a path, because $G$ is
boundary-linked.)"

We fill in the reason. Suppose the vertices that a walk from the vertex of `C` can reach strictly
inside `A` have no neighbour on `A`. Then we chart a neighbourhood of the disc into the sphere, and
grow a disc from the pasted disc over these vertices with
`exists_disc_of_side`. Its boundary is an `O`-arc that surrounds `C` and misses `G`, against
boundary-linkage.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function GraphMinor.Surface GraphMinor.GM11

universe u

/-- Carry a drawing by a map that is an embedding on a compact set holding it. -/
theorem exists_transport {S R : Type*} [TopologicalSpace S] [TopologicalSpace R] [T2Space S]
  [T2Space R] {K : Set S} (hK : IsCompact K) (hne : K.Nonempty) {κ : S → R} (hc : ContinuousOn κ K)
    (hi : InjOn κ K) (G : Drawing S) (hU : G.U ⊆ K) :
    ∃ Γ : Drawing R, Γ.U = κ '' G.U ∧ Γ.V = κ '' G.V ∧ Γ.E = image κ '' G.E := by
  classical
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : Nonempty K := hne.to_subtype
  have hv : IsClosedEmbedding ((↑) : K → S) := hK.isClosed.isClosedEmbedding_subtypeVal
  obtain ⟨P, hPU, hPV, hm⟩ := exists_pull_drawing hv G (by rwa [Subtype.range_coe])
  have hlc : Continuous (K.domRestrict κ) := hc.domRestrict
  have hli : Injective (K.domRestrict κ) := fun a b h => Subtype.ext (hi a.2 b.2 h)
  obtain ⟨Γ, hΓ⟩ := exists_image_matched (hlc.isClosedEmbedding hli) P
  have hsub : ∀ {A : Set S}, A ⊆ K → K.domRestrict κ '' ((↑) ⁻¹' A) = κ '' A := fun {A} hA => by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.1, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hA hy⟩, hy, rfl⟩
  refine ⟨Γ, ?_, ?_, ?_⟩
  · rw [← hΓ.image_U, sdiff_empty, hPU, hsub hU]
  · rw [← hΓ.image_V, sdiff_empty, hPV, hsub (G.V_subset_U.trans hU)]
  · rw [hΓ.image_E, hm.image_E]
    ext f
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨(↑) '' e, ⟨e, he, rfl⟩, by rw [image_image]; rfl⟩
    · rintro ⟨_, ⟨e, he, rfl⟩, rfl⟩
      exact ⟨e, he, by rw [image_image]; rfl⟩

/-- A chart of the plane into a sphere. -/
theorem exists_sphere_chart : ∃ (R : Type) (_ : TopologicalSpace R) (ι : ℂ → R), T2Space R
  ∧ IsClosedSurface R ∧ IsSphere R ∧ Continuous ι ∧ Injective ι := by
  have hT2 : T2Space (OnePoint EuclideanPlane) := inferInstance
  have hTs : IsClosedSurface (OnePoint EuclideanPlane) := (GM11.IsSphere.isClosedSurface
    ⟨Homeomorph.refl _⟩).1
  refine ⟨OnePoint EuclideanPlane, inferInstance, fun z => ((Complex.orthonormalBasisOneI.repr z :
    EuclideanPlane) : OnePoint EuclideanPlane), hT2, hTs, ⟨Homeomorph.refl _⟩, ?_, ?_⟩
  · exact OnePoint.continuous_coe.comp Complex.orthonormalBasisOneI.repr.continuous
  · exact fun a b h => Complex.orthonormalBasisOneI.repr.injective (OnePoint.coe_injective h)

section Cap

variable {S : Type u} [TopologicalSpace S] {T : Type u} [TopologicalSpace T] {C : Set S} {j : S
  → T} {D : Set T}

/-- An edge with an end strictly inside a disc, whose boundary it misses, lies strictly inside. -/
theorem edge_inside [T2Space T] (hman : ∀ x : T, IsManifoldPoint x) {G : Drawing S}
  (hj : Continuous j) {Δ : Set T} (hΔ : IsClosedDisc Δ) (hn : G.IsNormal
    (j ⁻¹' discBd Δ)) {e : Set S} (he : e ∈ G.E) {x : S} (hx : x ∈ closure e)
      (hxi : j x ∈ discInt Δ) : j '' e ⊆ discInt Δ := by
  have hpc : IsPreconnected (j '' e) := he.2.2.1.isConnected.isPreconnected.image _ hj.continuousOn
  have hdb : Disjoint (j '' e) (discBd Δ) := by
    rw [disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ hzb
    have hzU := he.2.1 hz
    exact hzU.2 (hn ⟨hzb, hzU.1⟩)
  rcases inside_or_off hpc hΔ.isClosed (hdb.mono_right (frontier_disc_subset hman hΔ)) with h | h
  · exact fun z hz => ⟨interior_subset (h hz), disjoint_left.mp hdb hz⟩
  · exfalso
    have h1 : j x ∈ closure (j '' e) := image_closure_subset_closure_image hj
      (mem_image_of_mem j hx)
    obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp h1 _ (hΔ.isOpen_discInt hman) hxi
    exact h hz2 hz1.1

private theorem spanned_vertices_inside_disc
    {S : Type u}
    [TopologicalSpace S]
    [T1Space S]
    {T : Type u}
    [TopologicalSpace T]
    {j : S → T}
    (hcj : IsClosedEmbedding j)
    {G : Drawing S}
    {Δ : Set T}
    (hΔ : IsClosedDisc Δ)
    [T2Space T] :
    let Gi : Drawing S := G.span (j ⁻¹' Δ) {e | j '' e ⊆ Δ}
    Gi.V ⊆ G.V ∩ j ⁻¹' Δ := by
  intro Gi
  rintro x (hx | hx)
  · exact ⟨hx.2, hx.1⟩
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
    refine ⟨hxe.2, ?_⟩
    have h1 : closure e ⊆ j ⁻¹' Δ := closure_minimal (fun z hz => he.1 (mem_image_of_mem j hz))
      (hΔ.isClosed.preimage hcj.continuous)
    exact h1 hxe.1

private theorem spanned_drawing_inside_disc
    {S : Type u}
    [TopologicalSpace S]
    [T1Space S]
    {T : Type u}
    [TopologicalSpace T]
    {j : S → T}
    (hcj : IsClosedEmbedding j)
    {G : Drawing S}
    {Δ : Set T}
    (hΔ : IsClosedDisc Δ)
    [T2Space T] :
    let Gi : Drawing S := G.span (j ⁻¹' Δ) {e | j '' e ⊆ Δ}
    (Gi.V ⊆ G.V ∩ j ⁻¹' Δ) →
    Gi.U ⊆ j ⁻¹' Δ := by
  intro Gi hGiV
  rintro x (hx | hx)
  · exact (hGiV hx).2
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
    have h1 : closure e ⊆ j ⁻¹' Δ := closure_minimal (fun z hz => he.1 (mem_image_of_mem j hz))
      (hΔ.isClosed.preimage hcj.continuous)
    exact h1 hxe

private theorem chart_image_edge_closure
    {S : Type u}
    [TopologicalSpace S]
    {T : Type u}
    {j : S → T}
    [CompactSpace S]
    (E : Set T)
    (R : Type)
    [TopologicalSpace R]
    [T2Space R]
    (τ : T → R)
    (Gi : Drawing S)
    (hκc : ContinuousOn (τ ∘ j) (j ⁻¹' E))
    (hGiK : Gi.U ⊆ j ⁻¹' E) :
    let κ : S → R := τ ∘ j
    ∀ (e : Set S),
    (e ∈ Gi.E) →
    closure (κ '' e) = κ '' closure e := by
  intro κ e he
  have hcl : closure e ⊆ j ⁻¹' E := (Gi.closure_subset_U he).trans hGiK
  apply subset_antisymm
  · exact closure_minimal (image_mono subset_closure)
      ((isClosed_closure.isCompact.image_of_continuousOn (hκc.mono hcl)).isClosed)
  · exact (hκc.mono hcl).image_closure

private theorem transport_cuff_reachability_to_chart
    {S : Type u}
    [TopologicalSpace S]
    {T : Type u}
    [TopologicalSpace T]
    {C : Set S}
    {j : S → T}
    {D : Set T}
    (hc : IsCappedCuff C T j D)
    (hcj : IsClosedEmbedding j)
    {G : Drawing S}
    {Δ : Set T}
    (hΔ : IsClosedDisc Δ)
    (hn : G.IsNormal (j ⁻¹' discBd Δ))
    {K : Set S}
    (hKi : ∀ u ∈ K, j u ∈ discInt Δ)
    {ρ : S → ℕ}
    (hreach : ∀ u ∈ K, u ∉ C → ∃ e ∈ G.E, ∃ w ∈ K, w ≠ u ∧ u ∈ closure e ∧ w ∈ closure e ∧ ρ w < ρ
      u)
    [T2Space T]
    (hman : ∀ (x : T), IsManifoldPoint x)
    (E : Set T)
    (R : Type)
    [TopologicalSpace R]
    (τ : T → R)
    (Gi : Drawing S)
    (hGiE : Gi.E = {e | j '' e ⊆ Δ} ∩ G.E)
    (hEs : j ⁻¹' Δ ⊆ j ⁻¹' E)
    (hκi : InjOn (τ ∘ j) (j ⁻¹' E))
    (Γ : Drawing R)
    (hΓE : Γ.E = image (τ ∘ j) '' Gi.E) :
    let κ : S → R := τ ∘ j
    (∀ e ∈ Gi.E, closure (κ '' e) = κ '' closure e) →
    (discBd (τ '' D) = τ '' discBd D) →
    ∀ (ρR : R → ℕ),
    (∀ {x : S}, x ∈ j ⁻¹' E → ρR (κ x) = ρ x) →
    ∀ u ∈ κ '' K, u ∉ discBd (τ '' D) → ∃ e ∈ Γ.E, ∃ w ∈ κ '' K, w ≠ u ∧ u ∈ closure e ∧ w ∈
      closure e ∧ (w ∉ discBd (τ '' D) → ρR w < ρR u) := by
  intro κ hclos hB₀b ρR hρR
  rintro _ ⟨u', hu', rfl⟩ hnb
  have huE := hEs (hKi u' hu').1
  have huC : u' ∉ C := fun h => hnb (by
    rw [hB₀b]
    refine ⟨j u', ?_, rfl⟩
    rw [hc.discBd_eq]
    exact mem_image_of_mem j h)
  obtain ⟨e, he, w, hw, hne', h1, h2, h3⟩ := hreach u' hu' huC
  have hei : e ∈ Gi.E := by
    rw [hGiE]
    exact ⟨(edge_inside hman hcj.continuous hΔ hn he h1 (hKi u' hu')).trans sdiff_subset, he⟩
  have hwE := hEs (hKi w hw).1
  refine ⟨κ '' e, by rw [hΓE]; exact ⟨e, hei, rfl⟩, κ w, ⟨w, hw, rfl⟩,
    fun h => hne' (hκi hwE huE h), ?_, ?_, fun _ => ?_⟩
  · rw [hclos e hei]
    exact mem_image_of_mem κ h1
  · rw [hclos e hei]
    exact mem_image_of_mem κ h2
  · rw [hρR hwE, hρR huE]
    exact h3

/-- **An `O`-arc off `G` around the cuff.** Let `K` be a set of vertices strictly inside `Δ`, with
all vertices of `C`, closed under neighbours, and such that each vertex of `K` off `C` has a
neighbour in `K` that is closer to `C`, as `ρ` measures.
Then a disc around `D` has a boundary that misses `G`. -/
theorem exists_free_disc [T2Space S] [CompactSpace S] [Nonempty S] (hc : IsCappedCuff C T j D)
  (hcj : IsClosedEmbedding j) {G : Drawing S} (hG : G.IsProper) (hCsub : C ⊆ bd S) {Δ : Set T}
    (hΔ : IsClosedDisc Δ) (hDΔ : D ⊆ Δ) (hn : G.IsNormal (j ⁻¹' discBd Δ))
      (hint : ∀ x ∈ discBd Δ, IsInteriorPoint x)
    {K : Set S} (hKV : K ⊆ G.V) (hKi : ∀ u ∈ K, j u ∈ discInt Δ) (hCK : G.V ∩ C ⊆ K)
      (hedge : ∀ e ∈ G.E, ∀ u ∈ K, u ∈ closure e → ∀ w ∈ G.V, w ∈ closure e → w ∈ K) {ρ : S → ℕ}
    (hreach : ∀ u ∈ K, u ∉ C → ∃ e ∈ G.E, ∃ w ∈ K, w ≠ u ∧ u ∈ closure e ∧ w ∈ closure e
      ∧ ρ w < ρ u) : ∃ B, IsClosedDisc B ∧ D ⊆ B ∧ Disjoint (discBd B) (j '' G.U) := by
  classical
  have hT := hc.isSurface
  have : T2Space T := hT.2.1
  have : CompactSpace T := hT.1
  have hman := hT.2.2
  have hii := hcj.injective
  -- a slightly larger disc that touches `Δ` only on `G`
  have hZc : IsClosed (j '' G.U) := hcj.isClosedMap _ G.isClosed_U
  obtain ⟨E, hE, hΔE, -⟩ := exists_disc_around hman hΔ hint isOpen_univ (subset_univ _)
  obtain ⟨Δp, hΔp, hsp, hpE, hoffZ, hb1, hb2, hb3⟩ := exists_disc_push_off hΔ hE hΔE hZc
  have hDp : D ⊆ Δp := hDΔ.trans hsp
  obtain ⟨p⟩ := hΔp.isOArc_discBd
  obtain ⟨c, c', hcc, hcc', hm, hm', hl, hr, hcE, hcb, -⟩ := exists_disc_collar hΔp hE hpE p
  obtain ⟨R, tR, ι, hR2, hRc, hRs, hιc, hιi⟩ := exists_sphere_chart
  let τ : T → R := ι ∘ c'
  have hτc : ContinuousOn τ E := hιc.comp_continuousOn hcc'
  have hτi : InjOn τ E := fun x hx y hy h => by
    have h1 : c' x = c' y := hιi h
    rw [← hr hx, ← hr hy, h1]
  -- the part of `G` in `Δ`
  let Gi : Drawing S := G.span (j ⁻¹' Δ) {e | j '' e ⊆ Δ}
  have hGiE : Gi.E = {e | j '' e ⊆ Δ} ∩ G.E := G.span_E _ _
  have hGiV : Gi.V ⊆ G.V ∩ j ⁻¹' Δ := by
    exact spanned_vertices_inside_disc (S := S) (T := T) (j := j) hcj (G := G) (Δ := Δ) hΔ
  have hGiU : Gi.U ⊆ j ⁻¹' Δ := by
    exact spanned_drawing_inside_disc (S := S) (T := T) (j := j) hcj (G := G) (Δ := Δ) hΔ hGiV
  have hEs : j ⁻¹' Δ ⊆ j ⁻¹' E := preimage_mono fun x hx => (hΔE hx).1
  have hmap : ∀ {x : S}, x ∈ j ⁻¹' E → j x ∈ E := fun h => h
  have hKc : IsCompact (j ⁻¹' E) := (hE.isClosed.preimage hcj.continuous).isCompact
  have hκc : ContinuousOn (τ ∘ j) (j ⁻¹' E) := hτc.comp hcj.continuous.continuousOn fun x hx => hx
  have hκi : InjOn (τ ∘ j) (j ⁻¹' E) := fun x hx y hy h => hii (hτi hx hy h)
  have hne : (j ⁻¹' E).Nonempty := by
    obtain ⟨z, hz⟩ := (isConnected_of_isOArc hc.isClosedDisc.isOArc_discBd).nonempty
    have hz' := hz
    rw [hc.discBd_eq] at hz'
    obtain ⟨y, -, rfl⟩ := hz'
    exact ⟨y, (hΔE (hDΔ (Surface.discBd_subset D hz))).1⟩
  have hGiK : Gi.U ⊆ j ⁻¹' E := hGiU.trans hEs
  obtain ⟨Γ, hΓU, hΓV, hΓE⟩ := exists_transport hKc hne hκc hκi Gi hGiK
  let κ : S → R := τ ∘ j
  -- closures of carried edges
  have hclos : ∀ e ∈ Gi.E, closure (κ '' e) = κ '' closure e := fun e he => by
    exact chart_image_edge_closure (S := S) (T := T) (j := j) E R τ Gi hκc hGiK e he
  have hGiUU : Gi.U ⊆ G.U := by
    rintro x (hx | hx)
    · exact G.V_subset_U (hGiV hx).1
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      exact G.closure_subset_U he.2 hxe
  have hinV : ∀ y ∈ G.V, j y ∈ Δ → y ∈ Gi.V := fun y hy h => .inl ⟨h, hy⟩
  have hDE : D ⊆ E := fun x hx => (hΔE (hDΔ hx)).1
  have hpE' : Δp ⊆ E := fun x hx => (hpE hx).1
  obtain ⟨hB₀, hB₀b⟩ := isClosedDisc_image hc.isClosedDisc (hτc.mono hDE) (hτi.mono hDE)
  obtain ⟨hΛ, hΛb⟩ := isClosedDisc_image hΔp (hτc.mono hpE') (hτi.mono hpE')
  obtain ⟨hE₀, hE₀b⟩ := GM12.isClosedDisc_closure_compl_of_sphere hRc hRs hΛ
  have hRman : ∀ x : R, IsManifoldPoint x := fun x => (hRc.2.2 x).isManifoldPoint
  have hE₀cl : ∀ {z}, z ∈ Δp → τ z ∈ closure (univ \ τ '' Δp) → z ∈ discBd Δp := fun {z} hz h => by
    by_contra hnb
    have hi : τ z ∈ discInt (τ '' Δp) := ⟨mem_image_of_mem τ hz, fun hb => by
      rw [hΛb] at hb
      obtain ⟨w, hw, he⟩ := hb
      exact hnb (hτi (hpE' hz) (hpE' (Surface.discBd_subset Δp hw)) he.symm ▸ hw)⟩
    obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.mp h _ (hΛ.isOpen_discInt hRman) hi
    exact hw2.2 hw1.1
  have hGiEs : ∀ {e}, e ∈ Gi.E → e ∈ G.E := fun {e} he => by
    rw [hGiE] at he
    exact he.2
  have hzC : ∀ {z : T} {y : S}, z ∈ discBd D → z = j y → y ∈ C := fun {z y} hz h => by
    rw [hc.discBd_eq] at hz
    obtain ⟨w, hw, he⟩ := hz
    rw [← hii (he.trans h)]
    exact hw
  have hBb : ∀ {y : S}, j y ∈ E → κ y ∈ discBd (τ '' D) → y ∈ C := fun {y} hy h => by
    rw [hB₀b] at h
    obtain ⟨z, hz, he⟩ := h
    exact hzC hz (hτi (hDE (Surface.discBd_subset D hz)) hy he)
  have hd : Disjoint (τ '' D) (closure (univ \ τ '' Δp)) := by
    rw [disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ h
    have h1 := hE₀cl (hDp hz) h
    have h2 := hb1 ⟨h1, hDΔ hz⟩
    have h3 := hb3 ⟨h1, h2⟩
    obtain ⟨y, hy, rfl⟩ := h2
    have h4 : j y ∈ range j ∩ D := ⟨mem_range_self y, hz⟩
    rw [hc.inter_eq] at h4
    obtain ⟨w, hw, he⟩ := h4
    have hyC : y ∈ C := hii he ▸ hw
    exact (hKi y (hCK ⟨hG ⟨hCsub hyC, hy⟩, hyC⟩)).2 h3
  have hbd' : Γ.U ∩ discBd (τ '' D) ⊆ Γ.V := by
    rintro _ ⟨hx, hb⟩
    rw [hΓU] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hyC := hBb (hGiK hy) hb
    rw [hΓV]
    exact ⟨y, hinV y (hG ⟨hCsub hyC, hGiUU hy⟩) (hGiU hy), rfl⟩
  have hint' : Disjoint Γ.U (discInt (τ '' D)) := by
    rw [disjoint_left]
    intro x hx hi
    rw [hΓU] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨⟨z, hz, he⟩, hnb⟩ := hi
    have hzy : z = j y := hτi (hDE hz) (hGiK hy) he
    refine not_mem_discInt_cap hc y ⟨hzy ▸ hz, fun hb => hnb ?_⟩
    rw [hB₀b]
    exact ⟨j y, hb, rfl⟩
  have hΛm : ∀ y ∈ Gi.U, κ y ∈ τ '' Δp := fun y hy => mem_image_of_mem τ (hsp (hGiU hy))
  have hEU : Γ.U ∩ closure (univ \ τ '' Δp) ⊆ Γ.V := by
    rintro _ ⟨hx, hb⟩
    rw [hΓU] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h1 := hE₀cl (hsp (hGiU hy)) hb
    have h2 := hb3 ⟨h1, mem_image_of_mem j (hGiUU hy)⟩
    rw [hΓV]
    exact ⟨y, hinV y (hn ⟨h2, hGiUU hy⟩) (hGiU hy), rfl⟩
  have hEint : Disjoint Γ.U (discInt (closure (univ \ τ '' Δp))) := by
    rw [disjoint_left]
    intro x hx hi
    rw [hΓU] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h1 := hE₀cl (hsp (hGiU hy)) hi.1
    refine hi.2 ?_
    rw [hE₀b, hΛb]
    exact mem_image_of_mem τ h1
  have hKV' : κ '' K ⊆ Γ.V := by
    rw [hΓV]
    exact image_mono fun u hu => hinV u (hKV hu) (hKi u hu).1
  have hcuff : Γ.V ∩ discBd (τ '' D) ⊆ κ '' K ∪ ∅ := by
    rintro _ ⟨hx, hb⟩
    rw [hΓV] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hyC := hBb (hGiK (Gi.V_subset_U hy)) hb
    exact .inl ⟨y, hCK ⟨(hGiV hy).1, hyC⟩, rfl⟩
  have hKE : Disjoint (κ '' K) (closure (univ \ τ '' Δp)) := by
    rw [disjoint_left]
    rintro _ ⟨u, hu, rfl⟩ h
    have h1 := hE₀cl (hsp (hKi u hu).1) h
    have h2 := hb1 ⟨h1, (hKi u hu).1⟩
    exact (hKi u hu).2 (hb3 ⟨h1, h2⟩)
  have hmemcl : ∀ {e a}, e ∈ Gi.E → a ∈ j ⁻¹' E → κ a ∈ closure (κ '' e) → a ∈ closure e
    := fun {e a} he ha h => by
    rw [hclos e he] at h
    obtain ⟨b, hb, hab⟩ := h
    exact hκi ((hGiK (Gi.closure_subset_U he hb))) ha hab ▸ hb
  have hedge' : ∀ e ∈ Γ.E, ∀ u ∈ κ '' K, u ∈ closure e → ∀ w ∈ Γ.V, w ∈ closure e → w ∈ κ '' K ∪ ∅
    := by
    intro e he u hu huc w hw hwc
    rw [hΓE] at he
    obtain ⟨e', he', rfl⟩ := he
    obtain ⟨u', hu', rfl⟩ := hu
    rw [hΓV] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    have h1 := hmemcl he' (hEs (hKi u' hu').1) huc
    have h2 := hmemcl he' (hGiK (Gi.V_subset_U hw')) hwc
    exact .inl ⟨w', hedge e' (hGiEs he') u' hu' h1 w' (hGiV hw').1 h2, rfl⟩
  let ρR : R → ℕ := fun x => ρ (invFunOn κ (j ⁻¹' E) x)
  have hρR : ∀ {x}, x ∈ j ⁻¹' E → ρR (κ x) = ρ x := fun {x} hx => by
    change ρ (invFunOn κ (j ⁻¹' E) (κ x)) = ρ x
    rw [hκi.leftInvOn_invFunOn hx]
  have hreach' : ∀ u ∈ κ '' K, u ∉ discBd (τ '' D) → ∃ e ∈ Γ.E, ∃ w ∈ κ '' K, w ≠ u ∧ u ∈ closure e
    ∧ w ∈ closure e ∧ (w ∉ discBd (τ '' D) → ρR w < ρR u) := by
    exact transport_cuff_reachability_to_chart (S := S) (T := T) (C := C) (j := j) (D := D) hc hcj
      (G := G) (Δ := Δ) hΔ hn (K := K) hKi (ρ := ρ) hreach hman E R τ Gi hGiE hEs hκi Γ hΓE
      hclos hB₀b ρR hρR
  obtain ⟨B, hB, hB₀B, hBE, hBU⟩ := exists_disc_of_side hRc hRs Γ (X := ∅) hB₀ hE₀ hd hbd' hint'
    hEU hEint hKV' (empty_subset _) (empty_disjoint _) hcuff hKE hedge' hreach'
  have hBΛ : B ⊆ τ '' Δp := fun x hx => by
    by_contra hn'
    refine disjoint_left.mp hBE ⟨subset_closure ⟨mem_univ x, hn'⟩, fun hb => hn' ?_⟩ hx
    rw [hE₀b] at hb
    exact Surface.discBd_subset _ hb
  have : Nonempty T := ⟨j (Classical.arbitrary S)⟩
  obtain ⟨ρ', hρc, hρl⟩ := exists_inv_of_compactOn hE.isClosed.isCompact hτc hτi
  have hρcB : ContinuousOn ρ' B := hρc.mono (hBΛ.trans (image_mono hpE'))
  have hρiB : InjOn ρ' B := fun x hx y hy h => by
    obtain ⟨a, ha, rfl⟩ := hBΛ hx
    obtain ⟨b, hb, rfl⟩ := hBΛ hy
    rw [hρl (hpE' ha), hρl (hpE' hb)] at h
    rw [h]
  obtain ⟨hB', hbB'⟩ := isClosedDisc_image hB hρcB hρiB
  refine ⟨ρ' '' B, hB', fun z hz => ⟨τ z, hB₀B (mem_image_of_mem τ hz), hρl (hDE hz)⟩, ?_⟩
  rw [hbB', disjoint_left]
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hyU, he⟩
  obtain ⟨w, hw, rfl⟩ := hBΛ (Surface.discBd_subset B hx)
  rw [hρl (hpE' hw)] at he
  subst he
  have hjΔ : j y ∈ Δ := by
    by_contra hnΔ
    exact disjoint_left.mp hoffZ ⟨hw, hnΔ⟩ (mem_image_of_mem j hyU)
  have hyi : y ∈ Gi.U := by
    by_cases hyV : y ∈ G.V
    · exact Gi.V_subset_U (hinV y hyV hjΔ)
    · obtain ⟨e, he, hye⟩ := G.exists_edge_of_mem hyU hyV
      have hi : j y ∈ discInt Δ := ⟨hjΔ, fun hb => hyV (hn ⟨hb, hyU⟩)⟩
      have h1 := (edge_inside hman hcj.continuous hΔ hn he (subset_closure hye) hi).trans
        sdiff_subset
      exact .inr (mem_iUnion₂.mpr ⟨e, ⟨h1, he⟩, subset_closure hye⟩)
  have h5 : τ (j y) ∈ Γ.U := by
    rw [hΓU]
    exact ⟨y, hyi, rfl⟩
  exact hBU ⟨hx, h5⟩

/-- Two distinct vertices on the closure of an edge are its ends. -/
theorem isLink_of_mem_closure {G : Drawing S} {e : Set S} (he : e ∈ G.E) {u w : S} (hne : u ≠ w)
  (hu : u ∈ closure e ∩ G.V) (hw : w ∈ closure e ∩ G.V) : G.toGraph.IsLink e u w := by
  refine ⟨he, hu.2, hw.2, ?_⟩
  rcases G.edge_cond e he with ⟨p, q, -, hcap, -⟩ | ⟨p, hcap, -⟩
  · rw [hcap] at hu hw ⊢
    rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
    · exact absurd rfl hne
    · rfl
    · exact pair_comm _ _
    · exact absurd rfl hne
  · rw [hcap] at hu hw
    exact absurd (hu.trans hw.symm) hne

theorem walk_edges_inside [T2Space T] (hman : ∀ x : T, IsManifoldPoint x) {G : Drawing S}
  (hj : Continuous j) {Δ : Set T} (hΔ : IsClosedDisc Δ) (hn : G.IsNormal
    (j ⁻¹' discBd Δ)) {x y : S} (W : GraphWalk G.toGraph x y)
    (hs : ∀ v ∈ W.support, j v ∈ discInt Δ) : ∀ e ∈ W.edges, j '' e ⊆ discInt Δ := by
  induction W with
  | nil _ => simp [GraphWalk.edges]
  | cons hl rest ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · refine edge_inside hman hj hΔ hn hl.1 ?_ (hs _ (List.mem_cons_self))
      have h1 : _ ∈ closure _ ∩ G.V := hl.2.2.2 ▸ mem_insert _ _
      exact h1.1
    · exact ih (fun v hv => hs v (List.mem_cons_of_mem _ hv)) e he

/-- **The path of `G` from `C` to `A`.** If `C` has one vertex `c₀`, then a simple walk of `G` goes
from a vertex `a₁` of the boundary of `Δ` to `c₀`, strictly inside `Δ` after its start. -/
theorem exists_walk_to_arc (hS : IsSurface S) [ConnectedSpace S] (hC : C ∈ cuffs S)
  (hc : IsCappedCuff C T j D) (hns : ¬ IsSphere T) {G : Drawing S} (hbl : IsBoundaryLinked G) {Δ :
    Set T} (hΔ : IsClosedDisc Δ) (hDΔ : D ⊆ Δ) (hn : G.IsNormal (j ⁻¹' discBd Δ))
    (hint : ∀ x ∈ discBd Δ, IsInteriorPoint x) {c₀ : S} (hone : G.V ∩ C = {c₀}) :
    ∃ a₁ ∈ G.V, j a₁ ∈ discBd Δ ∧ ∃ W : GraphWalk G.toGraph a₁ c₀, W.IsSimple ∧
      (∀ v ∈ W.support, v ≠ a₁ → j v ∈ discInt Δ) ∧ ∀ e ∈ W.edges, j '' e ⊆ discInt Δ := by
  classical
  have hT := hc.isSurface
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have : T2Space T := hT.2.1
  have hman := hT.2.2
  have hcj : IsClosedEmbedding j := hc.isEmbedding.continuous.isClosedEmbedding
    hc.isEmbedding.injective
  have hG := hbl.1
  have hc₀ : c₀ ∈ G.V ∩ C := by
    rw [hone]
    exact rfl
  have hc₀Δ : j c₀ ∈ Δ := hDΔ (Surface.discBd_subset D (by
    rw [hc.discBd_eq]
    exact mem_image_of_mem j hc₀.2))
  have hnil : c₀ ∈ G.toGraph.vertexSet := hc₀.1
  by_cases hc₀b : j c₀ ∈ discBd Δ
  · exact ⟨c₀, hc₀.1, hc₀b, .nil hnil, by simp [GraphWalk.IsSimple, GraphWalk.support],
      by simp [GraphWalk.support], by simp [GraphWalk.edges]⟩
  let Q : ∀ {u : S}, GraphWalk G.toGraph u c₀ → Prop := fun W => ∀ v ∈ W.support, j v ∈ discInt Δ
  let K : Set S := {u | ∃ W : GraphWalk G.toGraph u c₀, Q W}
  have hc₀K : c₀ ∈ K := ⟨.nil hnil, fun v hv => by
    simp only [GraphWalk.support, List.mem_singleton] at hv
    subst hv
    exact ⟨hc₀Δ, hc₀b⟩⟩
  have hstart : ∀ {u : S} (W : GraphWalk G.toGraph u c₀), u ∈ W.support := fun W
    => W.start_mem_support
  by_cases hit : ∃ u ∈ K, ∃ a ∈ G.V, j a ∈ discBd Δ ∧ ∃ e, G.toGraph.IsLink e a u
  · obtain ⟨u, ⟨W, hW⟩, a, haV, hab, e, hl⟩ := hit
    obtain ⟨W', hs, hsup, hed⟩ := GM09.exists_isSimple_subwalk (GraphWalk.cons hl W)
    have hin : ∀ v ∈ W'.support, v ≠ a → j v ∈ discInt Δ := fun v hv hne => by
      rcases List.mem_cons.mp (hsup v hv) with rfl | h
      · exact absurd rfl hne
      · exact hW v h
    refine ⟨a, haV, hab, W', hs, hin, ?_⟩
    clear hsup hed
    revert hs hin
    cases W' with
    | nil _ => simp [GraphWalk.edges]
    | @cons _ v₁ _ f hl' rest =>
      intro hs hin
      have hrest : ∀ v ∈ rest.support, j v ∈ discInt Δ := fun v hv => hin v
        (List.mem_cons_of_mem _ hv) (fun h => (List.nodup_cons.mp hs).1 (h ▸ hv))
      intro e' he'
      rcases List.mem_cons.mp he' with h | he'
      · rw [h]
        refine edge_inside hman hcj.continuous hΔ hn hl'.1 ?_ (hrest _ rest.start_mem_support)
        have h1 : v₁ ∈ closure f ∩ G.V := by
          rw [hl'.2.2.2]
          exact mem_insert_of_mem _ rfl
        exact h1.1
      · exact walk_edges_inside hman hcj.continuous hΔ hn rest hrest e' he'
  exfalso
  push Not at hit
  let ρ : S → ℕ := fun u => sInf {n | ∃ W : GraphWalk G.toGraph u c₀, Q W ∧ W.length = n}
  have hρle : ∀ {u : S} (W : GraphWalk G.toGraph u c₀), Q W → ρ u ≤ W.length := fun W h
    => Nat.sInf_le ⟨W, h, rfl⟩
  have hρex : ∀ u ∈ K, ∃ W : GraphWalk G.toGraph u c₀, Q W ∧ W.length = ρ u := fun u ⟨W, h⟩
    => Nat.sInf_mem (s := {n | ∃ W : GraphWalk G.toGraph u c₀, Q W ∧ W.length = n}) ⟨_, W, h, rfl⟩
  have hKV : K ⊆ G.V := fun u ⟨W, _⟩ => by
    cases W with
    | nil hv => exact hv
    | cons hl _ => exact hl.2.1
  have hKi : ∀ u ∈ K, j u ∈ discInt Δ := fun u ⟨W, h⟩ => h u (hstart W)
  have hCK : G.V ∩ C ⊆ K := by
    rw [hone]
    rintro _ rfl
    exact hc₀K
  have hedge : ∀ e ∈ G.E, ∀ u ∈ K, u ∈ closure e → ∀ w ∈ G.V, w ∈ closure e → w ∈ K := by
    intro e he u hu huc w hw hwc
    by_cases huw : u = w
    · exact huw ▸ hu
    have hl : G.toGraph.IsLink e w u := isLink_of_mem_closure he (Ne.symm huw) ⟨hwc, hw⟩ ⟨huc, hKV
      hu⟩
    obtain ⟨W, hW⟩ := id hu
    refine ⟨.cons hl W, fun v hv => ?_⟩
    rcases List.mem_cons.mp hv with rfl | hv
    · have hin := edge_inside hman hcj.continuous hΔ hn he huc (hKi u hu)
      have h1 : j v ∈ Δ := by
        have h2 : closure e ⊆ j ⁻¹' Δ := closure_minimal (fun z hz => (hin
          (mem_image_of_mem j hz)).1) (hΔ.isClosed.preimage hcj.continuous)
        exact h2 hwc
      exact ⟨h1, fun hb => hit u hu v hw hb e hl⟩
    · exact hW v hv
  have hreach : ∀ u ∈ K, u ∉ C → ∃ e ∈ G.E, ∃ w ∈ K, w ≠ u ∧ u ∈ closure e ∧ w ∈ closure e
    ∧ ρ w < ρ u := by
    intro u hu huC
    obtain ⟨W, hW, hlen⟩ := hρex u hu
    have hne : u ≠ c₀ := fun h => huC (h ▸ hc₀.2)
    cases W with
    | nil _ => exact absurd rfl hne
    | @cons _ v _ e hl rest =>
      have hrestQ : Q rest := fun v hv => hW v (List.mem_cons_of_mem _ hv)
      have hlen' : rest.length + 1 = ρ u := by simpa [GraphWalk.length] using hlen
      have h1 : ρ v ≤ rest.length := hρle rest hrestQ
      have hmem : u ∈ closure e ∩ G.V ∧ v ∈ closure e ∩ G.V := by
        have h2 := hl.2.2.2
        exact ⟨h2 ▸ mem_insert _ _, h2 ▸ mem_insert_of_mem _ rfl⟩
      refine ⟨e, hl.1, v, ⟨rest, hrestQ⟩, fun h => ?_, hmem.1.1, hmem.2.1, by omega⟩
      subst h
      have := hρle rest hrestQ
      omega
  have : Nonempty S := ⟨c₀⟩
  obtain ⟨B, hB, hDB, hoff⟩ := exists_free_disc hc hcj hG (connectedComponentIn_subset_of_cuff hC)
    hΔ hDΔ hn hint hKV hKi hCK hedge hreach
  have hF := isOArc_preimage_bd hc hB hDB
  have hnF : G.IsNormal (j ⁻¹' discBd B) := fun y hy => absurd (mem_image_of_mem j hy.2)
    (disjoint_left.mp hoff hy.1)
  have h1 := hbl.2 C hC _ hnF hF (surrounds_of_disc hS hC hc hns hB hDB)
  have h2 : G.V ∩ j ⁻¹' discBd B = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro y hy
    exact disjoint_left.mp hoff hy.2 (mem_image_of_mem j (G.V_subset_U hy.1))
  rw [hone, h2] at h1
  simp at h1

end Cap

end GraphMinor.GM07

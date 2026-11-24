/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.CutFragment
public import LeanPool.GraphMinor.GM19.PullPainting
public import LeanPool.GraphMinor.GM19.Section5a
public import LeanPool.GraphMinor.GM19.Section5c
public import LeanPool.GraphMinor.GM19.CutDrawing3
public import LeanPool.GraphMinor.GM11.OArcCircuit
public import LeanPool.GraphMinor.GM11.Ties
public import LeanPool.GraphMinor.Surface.CutIArc
public import LeanPool.GraphMinor.Surface.CutOArc

/-!
# Each cuff of a fragment has two vertices

The pull-back of a painting needs that each cuff of the fragment has two points of `ψ⁻¹(V(Γ) ∪
V(K))`
(`PullData.two`). Take a cuff with at most one such point. Off that point `ψ` is one to one, and it
maps the
rest of the cuff into one open edge of `K` or into `bd(Σ)`. So `ψ` embeds the cuff in a line, which
cannot be,
or onto a cuff of `Σ`, which has two vertices of `Γ`. The cut along `K` is `exists_cut_drawing`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

variable {S Y : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Y] [T2Space Y]
  {ψ : Y → S} {F : Set S}

/-- Over one edge of `K`, a compact connected set of the cut surface lies on one sheet. -/
def HasSheets (ψ : Y → S) (K : Drawing S) : Prop :=
  ∀ e ∈ arcComponentsIn (K.U \ K.V), ∀ J : Set Y, IsCompact J → IsPreconnected J → ψ '' J ⊆ e
    → InjOn ψ J

/-- An `O`-arc with one point off a closed set lies in that closed set. -/
theorem subset_of_sdiff_singleton {Z B : Set S} (hZ : IsOArc Z) (hB : IsClosed B) {w : S}
  (h : Z \ {w} ⊆ B) :
    Z ⊆ B := by
  intro x hx
  by_contra hxB
  obtain rfl : x = w := by
    by_contra hne
    exact hxB (h ⟨hx, hne⟩)
  obtain ⟨y, hy, hyx⟩ := hZ.exists_ne x
  obtain ⟨z, -, hz₁, hz₂⟩ := isPreconnected_closed_iff.mp hZ.isPreconnected B {x} hB
    isClosed_singleton
    (fun u hu ↦ by
      by_cases hux : u = x
      · exact Or.inr hux
      · exact Or.inl (h ⟨hu, hux⟩))
    ⟨y, hy, h ⟨hy, hyx⟩⟩ ⟨x, hx, rfl⟩
  exact hxB (show x ∈ B from (show z = x from hz₂) ▸ hz₁)

theorem isPathConnected_of_line {T : Type*} [TopologicalSpace T] {L : Set T} {u v : T}
    (h : IsLineWithEnds L u v) : IsPathConnected L := by
  obtain ⟨a, ha, rfl, -, -⟩ := h.exists_arc
  exact isPathConnected_range ha.1

/-- **Two vertices on each cuff.** Let `ψ` be one to one off `U(K)`, map the boundary into `bd(Σ) ∪
U(K)` and
have sheets over the edges of `K`. If each cuff of `Σ` has two points of `A`, and `A` holds `V(K)`
and
`U(K) ∩ bd(Σ)`, then each cuff of `S₁` has two points over `A`. -/
theorem two_of_sheets {S₁ : Type} [TopologicalSpace S₁] [T2Space S₁] {ψ : S₁
  → S} {K : Drawing S} {A : Set S}
    (hS : IsSurface S) (hS₁ : IsSurface S₁) (hc : Continuous ψ) (hinj : InjOn ψ (ψ ⁻¹' K.Uᶜ))
    (hmaps : ψ '' bd S₁ ⊆ bd S ∪ K.U) (hsheet : HasSheets ψ K)
    (hlines : ∀ e ∈ arcComponentsIn (K.U \ K.V), ∃ u v, IsLineWithEnds (closure e) u v)
      (hKbd : K.U ∩ bd S ⊆ K.V) (hKA : K.V ⊆ A)
    (hA : ∀ C : cuffs S, ∃ p ∈ A ∩ C.1, ∃ q ∈ A ∩ C.1, p ≠ q) (C : cuffs S₁) :
    ∃ p ∈ ψ ⁻¹' A ∩ C.1, ∃ q ∈ ψ ⁻¹' A ∩ C.1, p ≠ q := by
  classical
  by_contra hnc
  have hno : ∀ p, ψ p ∈ A → p ∈ C.1 → ∀ q, ψ q ∈ A → q ∈ C.1 → p ≠ q → False :=
    fun p hp hpC q hq hqC hne ↦ hnc ⟨p, ⟨hp, hpC⟩, q, ⟨hq, hqC⟩, hne⟩
  have hOC : IsOArc C.1 := (cuff_statement S₁ hS₁).2.2 C.1 C.2
  have : Nonempty S₁ := by
    obtain ⟨a, -, -, -, -, -, -, -, -⟩ := hOC.exists_three
    exact ⟨a⟩
  have hCb : C.1 ⊆ bd S₁ := cuff_subset_bd C
  have hbd : IsClosed (bd S) := (cuff_statement S hS).1
  let O : Set S₁ := C.1 \ ψ ⁻¹' A
  have hO : ∀ x ∈ O, ψ x ∈ (bd S ∪ K.U) \ A := fun x hx ↦ ⟨hmaps (mem_image_of_mem ψ
    (hCb hx.1)), hx.2⟩
  -- any two points of `O` lie on a path in `O`
  have hJ : ∀ x ∈ O, ∀ y ∈ O, ∃ J ⊆ O, x ∈ J ∧ y ∈ J ∧ IsCompact J ∧ IsPathConnected J := by
    intro x hx y hy
    by_cases hxy : x = y
    · subst hxy
      exact ⟨{x}, singleton_subset_iff.mpr hx, rfl, rfl, isCompact_singleton,
        isPathConnected_singleton x⟩
    obtain ⟨L₁, L₂, h₁, h₂, hun, hin⟩ := hOC.lines hx.1 hy.1 hxy
    have hsubC₁ : L₁ ⊆ C.1 := hun ▸ subset_union_left
    have hsubC₂ : L₂ ⊆ C.1 := hun ▸ subset_union_right
    by_cases hL : L₁ ⊆ O
    · exact ⟨L₁, hL, h₁.left_mem, h₁.right_mem, h₁.isCompact, isPathConnected_of_line h₁⟩
    obtain ⟨p, hp₁, hpO⟩ := not_subset.mp hL
    have hpA : p ∈ ψ ⁻¹' A ∩ C.1 := by
      by_contra hn
      exact hpO ⟨hsubC₁ hp₁, fun hpa ↦ hn ⟨hpa, hsubC₁ hp₁⟩⟩
    refine ⟨L₂, ?_, h₂.left_mem, h₂.right_mem, h₂.isCompact, isPathConnected_of_line h₂⟩
    intro q hq
    refine ⟨hsubC₂ hq, fun hqA ↦ ?_⟩
    have hpq : p = q := by
      by_contra hne
      exact hno p hpA.1 hpA.2 q hqA (hsubC₂ hq) hne
    subst hpq
    have : p ∈ L₁ ∩ L₂ := ⟨hp₁, hq⟩
    rw [hin] at this
    rcases this with rfl | rfl
    · exact hx.2 hqA
    · exact hy.2 hqA
  -- a path in `O` stays on `bd(Σ)` or stays on one edge of `K`
  have hside : ∀ J ⊆ O, IsPathConnected J → ψ '' J ⊆ bd S ∨ ∃ e ∈ arcComponentsIn
    (K.U \ K.V), ψ '' J ⊆ e := by
    intro J hJO hJc
    have hIc : IsPathConnected (ψ '' J) := hJc.image hc
    obtain ⟨_, w, hw, rfl⟩ := hIc.nonempty
    have hcov : ψ '' J ⊆ bd S ∪ K.U := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hO x (hJO hx)).1
    by_cases hb : ψ '' J ⊆ bd S
    · exact Or.inl hb
    have hKsub : ψ '' J ⊆ K.U := by
      obtain ⟨_, ⟨u, hu, rfl⟩, hub⟩ := not_subset.mp hb
      by_contra hk
      obtain ⟨_, ⟨v, hv, rfl⟩, hvk⟩ := not_subset.mp hk
      obtain ⟨z, ⟨x, hx, rfl⟩, hz₁, hz₂⟩ := isPreconnected_closed_iff.mp
        hIc.isConnected.isPreconnected
        (bd S) K.U hbd K.isClosed_U hcov
        ⟨ψ v, mem_image_of_mem ψ hv, (hcov (mem_image_of_mem ψ hv)).resolve_right hvk⟩
        ⟨ψ u, mem_image_of_mem ψ hu, (hcov (mem_image_of_mem ψ hu)).resolve_left hub⟩
      exact (hO x (hJO hx)).2 (hKA (hKbd ⟨hz₂, hz₁⟩))
    refine Or.inr ?_
    obtain ⟨e, he, hsub⟩ := exists_arcComp_superset hIc (F := K.U \ K.V) (by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨hKsub (mem_image_of_mem ψ hx), fun hv ↦ (hO x (hJO hx)).2 (hKA hv)⟩)
    exact ⟨e, he, hsub⟩
  have hinjO : InjOn ψ O := by
    intro x hx y hy he
    obtain ⟨J, hJO, hxJ, hyJ, hJc, hJp⟩ := hJ x hx y hy
    rcases hside J hJO hJp with hb | ⟨e, he', hsub⟩
    · have hoff : ∀ {z}, z ∈ J → z ∈ ψ ⁻¹' K.Uᶜ := fun {z} hz hk ↦
        (hO z (hJO hz)).2 (hKA (hKbd ⟨hk, hb (mem_image_of_mem ψ hz)⟩))
      exact hinj (hoff hxJ) (hoff hyJ) he
    · exact hsheet e he' J hJc hJp.isConnected.isPreconnected hsub hxJ hyJ he
  have hinjC : InjOn ψ C.1 := by
    intro x hx y hy he
    by_cases hxA : ψ x ∈ A
    · by_contra hne
      exact hno x hxA hx y (he ▸ hxA) hy hne
    · exact hinjO ⟨hx, hxA⟩ ⟨hy, fun h ↦ hxA (he ▸ h)⟩ he
  obtain ⟨ρ, hρ, hl⟩ := exists_inv_of_compactOn hOC.isCompact hc.continuousOn hinjC
  have hZ : IsOArc (ψ '' C.1) := hOC.image hc.continuousOn hρ fun x hx ↦ hl hx
  -- the part of `C` off `A` misses at most one point
  obtain ⟨x₀, hx₀⟩ : O.Nonempty := by
    obtain ⟨a, b, d, ha, hb, hd, hab, had, hbd'⟩ := hOC.exists_three
    by_contra hemp
    have hall : ∀ {z}, z ∈ C.1 → ψ z ∈ A := fun {z} hz ↦ by
      by_contra hn
      exact hemp ⟨z, hz, hn⟩
    exact hno a (hall ha) ha b (hall hb) hb hab
  have hmiss : ∃ w, ψ '' C.1 \ {w} ⊆ ψ '' O := by
    by_cases hP : ∃ p ∈ C.1, ψ p ∈ A
    · obtain ⟨p, hp, hpA⟩ := hP
      refine ⟨ψ p, ?_⟩
      rintro _ ⟨⟨x, hx, rfl⟩, hne⟩
      refine ⟨x, ⟨hx, fun hxA ↦ hne ?_⟩, rfl⟩
      have : x = p := by
        by_contra hn
        exact hno x hxA hx p hpA hp hn
      rw [this]
      rfl
    · push Not at hP
      refine ⟨ψ x₀, ?_⟩
      rintro _ ⟨⟨x, hx, rfl⟩, -⟩
      exact ⟨x, ⟨hx, hP x hx⟩, rfl⟩
  obtain ⟨w, hw⟩ := hmiss
  -- all of `O` is on one side
  have hallside : ψ '' O ⊆ bd S ∨ ∃ e ∈ arcComponentsIn (K.U \ K.V), ψ '' O ⊆ e := by
    by_cases hb0 : ψ x₀ ∈ bd S
    · refine Or.inl ?_
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨J, hJO, hxJ, hyJ, -, hJp⟩ := hJ x₀ hx₀ y hy
      rcases hside J hJO hJp with hb | ⟨e, he, hsub⟩
      · exact hb (mem_image_of_mem ψ hyJ)
      · exact absurd (hKbd ⟨he.2.1 (hsub (mem_image_of_mem ψ hxJ)) |>.1, hb0⟩)
          (he.2.1 (hsub (mem_image_of_mem ψ hxJ))).2
    · have hK0 : ψ x₀ ∈ K.U \ K.V :=
        ⟨(hO x₀ hx₀).1.resolve_left hb0, fun hv ↦ (hO x₀ hx₀).2 (hKA hv)⟩
      obtain ⟨e, he, hxe⟩ : ∃ e ∈ arcComponentsIn (K.U \ K.V), ψ x₀ ∈ e :=
        ⟨_, GM20.mem_arcComponentsIn_pathComponentIn hK0, mem_pathComponentIn_self hK0⟩
      refine Or.inr ⟨e, he, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨J, hJO, hxJ, hyJ, -, hJp⟩ := hJ x₀ hx₀ y hy
      rcases hside J hJO hJp with hb | ⟨e', he', hsub⟩
      · exact absurd (hb (mem_image_of_mem ψ hxJ)) hb0
      · obtain rfl : e = e' := arcComp_eq_of_mem he he' hxe (hsub (mem_image_of_mem ψ hxJ))
        exact hsub (mem_image_of_mem ψ hyJ)
  rcases hallside with hb | ⟨e, he, hsub⟩
  · have hZb : ψ '' C.1 ⊆ bd S := subset_of_sdiff_singleton hZ hbd (hw.trans hb)
    have hZc : IsPreconnected (ψ '' C.1) := hZ.isPreconnected
    obtain ⟨z, hz⟩ : (ψ '' C.1).Nonempty := ⟨ψ x₀, mem_image_of_mem ψ hx₀.1⟩
    let Θ : cuffs S := ⟨connectedComponentIn (bd S) z, z, hZb hz, rfl⟩
    have hsubΘ : ψ '' C.1 ⊆ Θ.1 := hZc.subset_connectedComponentIn hz hZb
    have hΘ : ψ '' C.1 = Θ.1 := GM11.eq_of_oArc_subset hZ ((cuff_statement S hS).2.2 Θ.1 Θ.2) hsubΘ
    obtain ⟨p, hp, q, hq, hpq⟩ := hA Θ
    obtain ⟨p', hp', rfl⟩ : p ∈ ψ '' C.1 := hΘ ▸ hp.2
    obtain ⟨q', hq', rfl⟩ : q ∈ ψ '' C.1 := hΘ ▸ hq.2
    exact hno p' hp.1 hp' q' hq.1 hq' fun h ↦ hpq (h ▸ rfl)
  · obtain ⟨u, v, hL⟩ := hlines e he
    have hZL : ψ '' C.1 ⊆ closure e :=
      subset_of_sdiff_singleton hZ isClosed_closure (hw.trans (hsub.trans subset_closure))
    exact GM11.not_isOArc_of_subset_line ⟨hL.choose⟩ hZ hZL

/-- Each cuff of `Σ` has two vertices of a frame: a side lies on the cuff, and it has two ends. -/
theorem Frame.two_on_cuff (hS : IsSurface S) (Φ : Frame S) (C : cuffs S) :
    ∃ p ∈ Φ.V ∩ C.1, ∃ q ∈ Φ.V ∩ C.1, p ≠ q := by
  have hbd : IsClosed (bd S) := (cuff_statement S hS).1
  obtain ⟨e, he, heC⟩ := exists_side_on_cuff hbd Φ C (cuffPar hS C)
  have htV : tilde e ⊆ Φ.V := (Φ.toPainting hbd).tilde_subset_V he
  have htC : tilde e ⊆ C.1 := fun x hx ↦ closure_minimal heC (isClosed_cuff hS C) hx.1
  obtain ⟨p, q, hpq, heq⟩ := Set.ncard_eq_two.mp (Φ.side_shape e he).1
  have hp : p ∈ tilde e := heq ▸ mem_insert _ _
  have hq : q ∈ tilde e := heq ▸ mem_insert_of_mem _ rfl
  exact ⟨p, ⟨htV hp, htC hp⟩, q, ⟨htV hq, htC hq⟩, hpq⟩

/-- An edge of a drawing with two ends is its closure without the ends. -/
theorem closure_sdiff_subset {K : Drawing S} {e : Set S} (he : e ∈ arcComponentsIn
  (K.U \ K.V)) {u v : S}
    (hcap : closure e ∩ K.V = {u, v}) (hL : IsLineWithEnds (closure e) u v) : closure e \ K.V ⊆ e
      := by
  have hsubU : closure e ⊆ K.U := closure_minimal (he.2.1.trans sdiff_subset) K.isClosed_U
  have hoff : closure e \ {u, v} ⊆ K.U \ K.V := fun x hx ↦
    ⟨hsubU hx.1, fun hv ↦ hx.2 (hcap ▸ ⟨hx.1, hv⟩)⟩
  have hsub : e ⊆ closure e \ {u, v} := fun x hx ↦ ⟨subset_closure hx, fun hxc ↦
    (he.2.1 hx).2 ((hcap ▸ hxc : x ∈ closure e ∩ K.V).2)⟩
  have heq : closure e \ {u, v} = e := he.2.2.2 _ hoff (GM20.line_facts hL).2.1 hsub
  rintro x ⟨hx, hxV⟩
  rw [← heq]
  exact ⟨hx, fun hxc ↦ hxV ((hcap ▸ hxc : x ∈ closure e ∩ K.V).2)⟩

/-- **Cutting along a drawing.** The edges of `K` are lines, the drawing meets the boundary only in
vertices,
and no vertex is isolated. The sets `𝓐`, `𝓛` say how `K` and the cuffs are built from `O`-arcs and
lines. -/
theorem exists_cut_drawing (hS : IsSurface S) [ConnectedSpace S] {K : Drawing S} {𝓐 𝓛 : Set (Set S)}
    (hlines : ∀ e ∈ arcComponentsIn (K.U \ K.V), ∃ u v, u ≠ v ∧ closure e ∩ K.V = {u, v} ∧
      IsLineWithEnds (closure e) u v)
    (hKbd : K.U ∩ bd S ⊆ K.V) (hKne : K.V ⊆ ⋃ e ∈ arcComponentsIn (K.U \ K.V), closure e)
    (hF : IsCutFrame S 𝓐 𝓛) (hc : bd S ∪ K.U = ⋃₀ 𝓐 ∪ ⋃₀ 𝓛) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : T2Space Y) (ψ : Y → S), IsSurface Y ∧ IsCutMap ψ K.U
      ∧
      HasSheets ψ K := by
  classical
  let 𝓔 : Set (Set S) := closure '' arcComponentsIn (K.U \ K.V)
  have hsubU : ∀ e ∈ arcComponentsIn (K.U \ K.V), closure e ⊆ K.U := fun e he ↦
    closure_minimal (he.2.1.trans sdiff_subset) K.isClosed_U
  have hUeq : ⋃₀ 𝓔 = K.U := by
    apply subset_antisymm
    · rintro x ⟨_, ⟨e, he, rfl⟩, hx⟩
      exact hsubU e he hx
    · intro x hx
      by_cases hxV : x ∈ K.V
      · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp (hKne hxV)
        exact ⟨_, ⟨e, he, rfl⟩, hxe⟩
      · have hm : x ∈ K.U \ K.V := ⟨hx, hxV⟩
        exact ⟨_, ⟨_, GM20.mem_arcComponentsIn_pathComponentIn hm, rfl⟩,
          subset_closure (mem_pathComponentIn_self hm)⟩
  have hNs : K.V ⊆ ⋃₀ 𝓔 := hUeq ▸ K.V_subset_U
  obtain ⟨Y, tY, t2, ψ, h1, h2, h3, h4, h5, h6, hlift⟩ := exists_cut_lines hS K.finite_V
    (K.finite_edges.image _)
    (by
      rintro _ ⟨e, he, rfl⟩
      obtain ⟨u, v, huv, hcap, hL⟩ := hlines e he
      exact ⟨u, v, huv, hL, hcap⟩)
    (by
      rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩ hne x ⟨hx, hx'⟩
      by_contra hxV
      obtain ⟨u, v, -, hcap, hL⟩ := hlines e he
      obtain ⟨u', v', -, hcap', hL'⟩ := hlines e' he'
      have h₁ := closure_sdiff_subset he hcap hL ⟨hx, hxV⟩
      have h₂ := closure_sdiff_subset he' hcap' hL' ⟨hx', hxV⟩
      exact hne (congrArg closure (arcComp_eq_of_mem he he' h₁ h₂)))
    (by
      rintro _ ⟨e, he, rfl⟩ x ⟨hx, hb⟩
      exact hKbd ⟨hsubU e he hx, hb⟩)
    hNs hF (by rw [hUeq]; exact hc)
  rw [hUeq] at h4 h6
  have : CompactSpace Y := h1.1
  refine ⟨Y, tY, t2, ψ, h1, ⟨h2, h3, h4, h5, h6⟩, ?_⟩
  intro e he J hJc hJp hsub
  obtain ⟨u, v, -, hcap, hL⟩ := hlines e he
  have hQ : ψ '' J ⊆ closure e \ K.V := fun x hx ↦
    ⟨subset_closure (hsub hx), fun hv ↦ (he.2.1 (hsub hx)).2 hv⟩
  obtain ⟨L', -, hQL, -, -, X, X', x0, x1, y0, y1, hX, hX', hdis, hun, hbX, hbX', -⟩ :=
    hlift _ ⟨e, he, rfl⟩ _ hQ (hJc.image h2)
  have hJsub : J ⊆ X ∪ X' := fun z hz ↦ hun ▸ hQL (mem_image_of_mem ψ hz)
  by_cases hJX : J ⊆ X
  · exact hbX.injOn.mono hJX
  by_cases hJX' : J ⊆ X'
  · exact hbX'.injOn.mono hJX'
  exfalso
  obtain ⟨a, ha, haX⟩ := not_subset.mp hJX
  obtain ⟨b, hb, hbX''⟩ := not_subset.mp hJX'
  obtain ⟨z, -, hz₁, hz₂⟩ := isPreconnected_closed_iff.mp hJp X X' hX.isCompact.isClosed
    hX'.isCompact.isClosed
    hJsub ⟨b, hb, (hJsub hb).resolve_right hbX''⟩ ⟨a, ha, (hJsub ha).resolve_left haX⟩
  exact disjoint_left.mp hdis hz₁ hz₂

/-- On each cuff of a fragment of a cut, two points lie over `A`, if `A` holds `V(K)` and two points
of each cuff of
`Σ`. -/
theorem two_of_cut (hS : IsSurface S) {Y : Type} [TopologicalSpace Y] [T2Space Y] {ψ : Y
  → S} {K : Drawing S}
    {A : Set S} (hY : IsSurface Y) (hψ : IsCutMap ψ K.U) (hsheet : HasSheets ψ K)
    (hlines : ∀ e ∈ arcComponentsIn (K.U \ K.V), ∃ u v, u ≠ v ∧ closure e ∩ K.V = {u, v} ∧
      IsLineWithEnds (closure e) u v)
    (hKbd : K.U ∩ bd S ⊆ K.V) (hKA : K.V ⊆ A) (hA : ∀ C : cuffs S, ∃ p ∈ A ∩ C.1, ∃ q ∈ A ∩ C.1, p
      ≠ q) (y : Y)
    (C : cuffs (connectedComponent y)) :
    ∃ p ∈ (fun x : connectedComponent y ↦ ψ x.1) ⁻¹' A ∩ C.1,
      ∃ q ∈ (fun x : connectedComponent y ↦ ψ x.1) ⁻¹' A ∩ C.1, p ≠ q := by
  have hfrag := isCuttingFragment_of_cut hS hY hψ (K := K) rfl y
  refine two_of_sheets hS hfrag.isSurface hfrag.continuous_ψ ?_ hfrag.maps_bd ?_ ?_ hKbd hKA hA C
  · intro a ha b hb hab
    exact Subtype.ext (hψ.2.2.1 ha hb hab)
  · intro e he J hJc hJp hsub a ha b hb hab
    refine Subtype.ext (hsheet e he (Subtype.val '' J) (hJc.image continuous_subtype_val)
      (hJp.image _ continuous_subtype_val.continuousOn) ?_ (mem_image_of_mem _ ha)
        (mem_image_of_mem _ hb) hab)
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact hsub (mem_image_of_mem _ hx)
  · intro e he
    obtain ⟨u, v, -, -, hL⟩ := hlines e he
    exact ⟨u, v, hL⟩

/-- **`PullData` at a cut.** Cut a connected surface along a drawing `K` that meets `Γ` only in
common
vertices. Each component of the cut surface carries the data for the pull-back of `Γ`. The condition
`two`
holds by `two_of_sheets`, and the cuffs of `Σ` have two vertices of `Γ` because `Γ` fits a frame. -/
theorem exists_pullData (hS : IsSurface S) [ConnectedSpace S] {Φ : Frame S} {Γ : Painting S}
  (hfit : Γ.Fits Φ)
    {K : Drawing S} {𝓐 𝓛 : Set (Set S)} (hinter : Γ.U ∩ K.U ⊆ Γ.V ∩ K.V)
    (hlines : ∀ e ∈ arcComponentsIn (K.U \ K.V), ∃ u v, u ≠ v ∧ closure e ∩ K.V = {u, v} ∧
      IsLineWithEnds (closure e) u v)
    (hKne : K.V ⊆ ⋃ e ∈ arcComponentsIn (K.U \ K.V), closure e) (hF : IsCutFrame S 𝓐 𝓛)
    (hc : bd S ∪ K.U = ⋃₀ 𝓐 ∪ ⋃₀ 𝓛) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : T2Space Y) (ψ : Y → S), IsSurface Y ∧ IsCutMap ψ K.U
      ∧
      HasSheets ψ K ∧ ∀ y : Y, PullData Γ K (fun x : connectedComponent y ↦ ψ x.1) := by
  have hKbd : K.U ∩ bd S ⊆ K.V := fun x hx ↦ (hinter ⟨Γ.bd_subset hx.2, hx.1⟩).2
  obtain ⟨Y, tY, t2, ψ, hY, hψ, hsheet⟩ := exists_cut_drawing hS hlines hKbd hKne hF hc
  refine ⟨Y, tY, t2, ψ, hY, hψ, hsheet, fun y ↦ ?_⟩
  have hfrag := isCuttingFragment_of_cut hS hY hψ (K := K) rfl y
  refine ⟨hS, hfrag, hinter, fun C ↦ ?_⟩
  refine two_of_cut hS hY hψ hsheet hlines hKbd subset_union_right ?_ y C
  intro C'
  obtain ⟨p, hp, q, hq, hpq⟩ := Frame.two_on_cuff hS Φ C'
  exact ⟨p, ⟨Or.inl (hfit.V_subset hp.1), hp.2⟩, q, ⟨Or.inl (hfit.V_subset hq.1), hq.2⟩, hpq⟩

omit [T2Space S] in
/-- The cuffs, some `O`-arcs, and lines with ends on these, make a frame for a cut. An `O`-arc may
touch a
cuff, or another `O`-arc. -/
theorem isCutFrame_of (hS : IsSurface S) {𝓞 𝓛 : Set (Set S)} (h𝓞 : 𝓞.Finite) (h𝓛 : 𝓛.Finite)
    (hO : ∀ C ∈ 𝓞, IsOArc C)
    (hL : ∀ L ∈ 𝓛, ∃ s t, s ≠ t ∧ IsLineWithEnds L s t ∧ s ∈ bd S ∪ ⋃₀ 𝓞 ∧ t ∈ bd S ∪ ⋃₀ 𝓞) :
    IsCutFrame S (cuffs S ∪ 𝓞) 𝓛 := by
  have hc := cuff_statement S hS
  refine ⟨hc.2.1.union h𝓞, h𝓛, ?_, subset_union_left, ?_⟩
  · rintro C (hC | hC)
    · exact hc.2.2 C hC
    · exact hO C hC
  · intro L hLm
    rw [sUnion_union, sUnion_cuffs]
    exact hL L hLm

/-- `exists_pullData` when `K` is a union of `O`-arcs and of lines with ends on these or on the
cuffs. This
covers each cut of XIX, for instance one `O`-arc that meets a cuff in one point. -/
theorem exists_pullData_of_shape (hS : IsSurface S) [ConnectedSpace S] {Φ : Frame S} {Γ : Painting
  S}
    (hfit : Γ.Fits Φ) {K : Drawing S} {𝓞 𝓛 : Set (Set S)} (hinter : Γ.U ∩ K.U ⊆ Γ.V ∩ K.V)
    (hlines : ∀ e ∈ arcComponentsIn (K.U \ K.V), ∃ u v, u ≠ v ∧ closure e ∩ K.V = {u, v} ∧
      IsLineWithEnds (closure e) u v)
    (hKne : K.V ⊆ ⋃ e ∈ arcComponentsIn (K.U \ K.V), closure e) (h𝓞 : 𝓞.Finite) (h𝓛 : 𝓛.Finite)
    (hO : ∀ C ∈ 𝓞, IsOArc C)
    (hL : ∀ L ∈ 𝓛, ∃ s t, s ≠ t ∧ IsLineWithEnds L s t ∧ s ∈ bd S ∪ ⋃₀ 𝓞 ∧ t ∈ bd S ∪ ⋃₀ 𝓞)
    (hU : K.U = ⋃₀ 𝓞 ∪ ⋃₀ 𝓛) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : T2Space Y) (ψ : Y → S), IsSurface Y ∧ IsCutMap ψ K.U
      ∧
      HasSheets ψ K ∧ ∀ y : Y, PullData Γ K (fun x : connectedComponent y ↦ ψ x.1) :=
  exists_pullData hS hfit hinter hlines hKne (isCutFrame_of hS h𝓞 h𝓛 hO hL) (by
    rw [hU, sUnion_union, sUnion_cuffs, union_assoc])

end GraphMinor.GM19

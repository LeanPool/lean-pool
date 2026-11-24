/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FrameMove

/-!
# The topology in the proof of Graph Minors XIX, (2.1)

Here we prove `Theorem21TopologyStatement`, for surfaces in `Type`. The frame is `stdFrame`. For a
painting `Γ`,
the homeomorphism `h` of `exists_move` puts an edge on each short side. Then `thinP` makes the image
of `Γ`
narrow, with border edges directed along the sides of the frame.
The deductions that use later proofs are in `ThinningProved`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

universe w

variable {S : Type} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
theorem symm_image_image' (h : S ≃ₜ S) (e : Set S) : h.symm '' (h '' e) = e := by
  rw [← image_comp]
  simp

/-- The image of a painting under a homeomorphism of the surface. -/
noncomputable def Painting.push (h : S ≃ₜ S) (Γ : Painting S) : Painting S where
  U := h '' Γ.U
  V := h '' Γ.V
  γ e := (Γ.γ (h.symm '' e)).map h
  isClosed_U := h.isClosed_image.mpr Γ.isClosed_U
  V_subset := image_mono Γ.V_subset
  finite_V := Γ.finite_V.image _
  bd_subset := by
    rw [← image_bd h]
    exact image_mono Γ.bd_subset
  finite_edges := by
    rw [← image_sdiff h.injective, GM20.image_arcComponentsIn]
    exact Γ.finite_edges.image _
  edge_shape := by
    rw [← image_sdiff h.injective, GM20.image_arcComponentsIn]
    rintro _ ⟨c, hc, rfl⟩
    simp only
    rw [GM20.image_tilde, ncard_image_of_injective _ h.injective, ← h.image_closure]
    rcases Γ.edge_shape c hc with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩
    · refine Or.inl ⟨h₁, h₂.image _, GM20.image_isLine h h₃, ?_⟩
      rw [GM20.image_lineEnds, h₄]
    · refine Or.inr ⟨h₁, h₂.image _, GM20.image_isClosedDisc h h₃, ?_⟩
      rw [GM20.image_discBd]
      exact image_mono h₄
  γ_nodup := by
    rw [← image_sdiff h.injective, GM20.image_arcComponentsIn]
    rintro _ ⟨c, hc, rfl⟩
    simp only
    rw [symm_image_image' h]
    exact (Γ.γ_nodup c hc).map h.injective
  γ_set := by
    rw [← image_sdiff h.injective, GM20.image_arcComponentsIn]
    rintro _ ⟨c, hc, rfl⟩
    simp only
    rw [symm_image_image' h, GM20.image_tilde, ← Γ.γ_set c hc]
    ext x
    simp
  border_edge := by
    rw [← image_sdiff h.injective, GM20.image_arcComponentsIn]
    rintro _ ⟨c, hc, rfl⟩ hb
    simp only at hb ⊢
    have hb' : Painting.IsBorder c := (isBorder_image h).mp hb
    obtain ⟨h₁, h₂⟩ := Γ.border_edge c hc hb'
    refine ⟨by rw [GM20.image_tilde, ncard_image_of_injective _ h.injective, h₁], ?_⟩
    rw [← image_bd h]
    exact image_mono h₂

section Push

variable (h : S ≃ₜ S) (Γ : Painting S)

omit [T2Space S] in
theorem push_E : (Γ.push h).E = (fun c ↦ h '' c) '' Γ.E := by
  change arcComponentsIn (h '' Γ.U \ h '' Γ.V) = _
  rw [← image_sdiff h.injective, GM20.image_arcComponentsIn]
  rfl

omit [T2Space S] in
theorem push_mem {e : Set S} (he : e ∈ Γ.E) : h '' e ∈ (Γ.push h).E := by
  rw [push_E]
  exact ⟨e, he, rfl⟩

omit [T2Space S] in
theorem push_γ (e : Set S) : (Γ.push h).γ (h '' e) = (Γ.γ e).map h := by
  change (Γ.γ (h.symm '' (h '' e))).map h = _
  rw [symm_image_image' h]

omit [T2Space S] in
theorem push_internally (hΓ : Γ.IsInternallyThreeConnected) :
    (Γ.push h).IsInternallyThreeConnected := by
  refine ⟨?_, ?_⟩
  · obtain ⟨e, he⟩ := hΓ.1
    exact ⟨_, push_mem h Γ he⟩
  · intro F hF hFU hfin hcard
    change F ∩ h '' Γ.U ⊆ h '' Γ.V at hFU
    change (F ∩ h '' Γ.V).ncard + _ ≤ 2 at hcard
    have himg : ∀ A : Set S, h.symm '' (F ∩ h '' A) = (h.symm '' F) ∩ A := fun A ↦ by
      rw [image_inter h.symm.injective, symm_image_image' h]
    have hbd : h.symm '' (F ∩ bd S) = (h.symm '' F) ∩ bd S := by
      rw [image_inter h.symm.injective, image_bd h.symm]
    obtain ⟨D, h₁, h₂, h₃⟩ := hΓ.2 (h.symm '' F) (GM20.image_isOArc h.symm hF)
      (by
        rw [← himg]
        rintro _ ⟨y, hy, rfl⟩
        obtain ⟨v, hv, rfl⟩ := hFU hy
        simpa using hv)
      (by rw [← hbd]; exact hfin.image _)
      (by
        rw [← himg, ← hbd, ncard_image_of_injective _ h.symm.injective,
          ncard_image_of_injective _ h.symm.injective]
        exact hcard)
    refine ⟨h '' D, GM20.image_isClosedDisc h h₁, ?_, ?_⟩
    · rw [GM20.image_discBd, h₂, ← image_comp]
      simp
    · rintro _ ⟨⟨y, hy, rfl⟩, ⟨v, hv, he⟩⟩
      have hyv : y = v := h.injective he.symm
      subst hyv
      obtain ⟨z, hz, hzy⟩ := h₃ ⟨hy, hv⟩
      have : h y = z := by rw [← hzy]; simp
      rw [this]
      exact hz

end Push

omit [T2Space S] in
theorem list_two (Γ : Painting S) {e : Set S} (he : e ∈ Γ.E) (h2 : (tilde e).ncard = 2) :
    ∃ x y, Γ.γ e = [x, y] ∧ x ≠ y := by
  classical
  have h1 : ((Γ.γ e).toFinset : Set S) = tilde e := by
    rw [← Γ.γ_set e he]
    ext x
    simp
  have hl : (Γ.γ e).length = 2 := by
    rw [← List.toFinset_card_of_nodup (Γ.γ_nodup e he), ← Set.ncard_coe_finset, h1, h2]
  obtain ⟨x, y, hxy⟩ := List.length_eq_two.mp hl
  refine ⟨x, y, hxy, ?_⟩
  have := Γ.γ_nodup e he
  rw [hxy] at this
  simpa using this

/-- **The topology in the proof of Graph Minors XIX, (2.1).** -/
theorem theorem21Topology : Theorem21TopologyStatement.{0} := by
  classical
  intro S _ hS _
  have : T2Space S := hS.2.1
  have hpar : ∀ C : cuffs S, Nonempty (Circle ≃ₜ C.1) := fun C ↦ (cuff_statement S hS).2.2 C.1 C.2
  let par : ∀ C : cuffs S, Circle ≃ₜ C.1 := fun C ↦ (hpar C).some
  let Φ := stdFrame par hS
  refine ⟨Φ, fun Γ hΓ ↦ ?_⟩
  obtain ⟨h, hm, hedge⟩ := exists_move par hS Γ
  let Γ₁ := Γ.push h
  obtain ⟨Δ, L, R, hl⟩ := exists_isLensed Γ₁
  have hΔ := hl.isCore
  let g : Set S → List S := fun e ↦
    if Painting.IsBorder e ∧ ¬ ∀ s ∈ Φ.sides, e ⊆ s → DirAgrees s (Φ.γ s) e (Γ₁.γ e)
    then (Γ₁.γ e).reverse else Γ₁.γ e
  have hg : ∀ e ∈ Γ₁.E, (tilde e).ncard = 2 → g e = Γ₁.γ e ∨ g e = (Γ₁.γ e).reverse := by
    intro e _ _
    by_cases hc : Painting.IsBorder e ∧ ¬ ∀ s ∈ Φ.sides, e ⊆ s → DirAgrees s (Φ.γ s) e (Γ₁.γ e)
    · exact Or.inr (ite_eq_left hc)
    · exact Or.inl (ite_eq_right hc)
  let Γ' := thinP hΔ g hg
  have hE' : Γ'.E = pieces Γ₁ Δ := pieces_eq hΔ
  have hint₁ := push_internally h Γ hΓ
  have hbcase : ∀ e' ∈ Γ'.E, Painting.IsBorder e' → e' ∈ Γ₁.E ∧ (tilde e').ncard = 2 := by
    intro e' he' hb
    rw [hE'] at he'
    obtain ⟨x, hxe, hxb⟩ := id hb
    rcases he' with he' | ⟨c, hc, rfl⟩
    · rcases Γ₁.sk_cases he' with h' | ⟨c, hc, h3, hsub, -⟩
      · exact h'
      · have := size_two_of_border Γ₁ hc ⟨x, hsub hxe, hxb⟩
        omega
    · have := size_two_of_border Γ₁ hc.1 ⟨x, hΔ.core_subset hc.1 hc.2 hxe, hxb⟩
      have := hc.2
      omega
  have hthree : ∀ e ∈ Γ.E, (tilde e).ncard = 3 → h '' e ∈ Γ₁.E ∧ (tilde (h '' e)).ncard = 3 := by
    intro e he h3
    exact ⟨push_mem h Γ he, by rw [ncard_tilde_image, h3]⟩
  have htwo : ∀ e ∈ Γ.E, (tilde e).ncard = 2 → h '' e ∈ Γ₁.E ∧ (tilde (h '' e)).ncard = 2 := by
    intro e he h2
    exact ⟨push_mem h Γ he, by rw [ncard_tilde_image, h2]⟩
  refine ⟨h, Γ', fun e ↦ core Δ (h '' e), ?_⟩
  refine
    { null := hasNullSignature_of_moves hm
      null_symm := hasNullSignature_of_moves fun C ↦ (hm C).symm
      V_eq := rfl
      fits := ?_
      three := ?_
      three_inj := ?_
      three_surj := ?_
      two := ?_
      internal_γ := ?_
      border_γ := ?_
      rest := ?_
      short := ?_ }
  · refine
      { V_subset := ?_
        short_sides := ?_
        border_dir := ?_
        internally_three_connected := thin_internally hS hint₁ hl g hg
        size_three_region := thin_region hS hl g hg }
    · refine iUnion_subset fun C x hx ↦ ?_
      obtain ⟨e, he, -, -, heq⟩ := hedge C
      have hxt : x ∈ tilde (upSide par C) := by
        rw [tilde_up]
        exact hx
      rw [← heq, tilde_image_homeo] at hxt
      exact image_mono (Γ.tilde_subset_V he) hxt
    · intro t ht
      obtain ⟨C, rfl⟩ := stdFrame_short par hS ht
      obtain ⟨e, he, -, h2, heq⟩ := hedge C
      rw [hE', ← heq]
      exact Or.inl (Γ₁.two_mem_sk (htwo e he h2).1 (htwo e he h2).2)
    · intro e' he' hb s hs hes
      obtain ⟨h₁, h₂⟩ := hbcase e' he' hb
      change DirAgrees s (Φ.γ s) e' (thinγ Γ₁ Δ g e')
      rw [thinγ_two hΔ g h₁ h₂]
      by_cases hall : ∀ s ∈ Φ.sides, e' ⊆ s → DirAgrees s (Φ.γ s) e' (Γ₁.γ e')
      · have hgq : g e' = Γ₁.γ e' := ite_eq_right fun hc ↦ hc.2 hall
        rw [hgq]
        exact hall s hs hes
      · have hgq : g e' = (Γ₁.γ e').reverse := ite_eq_left ⟨hb, hall⟩
        rw [hgq]
        push Not at hall
        obtain ⟨s', hs', hes', hn⟩ := hall
        obtain ⟨z, hz⟩ := h₁.1
        have hss : s' = s := arcComp_eq_of_mem hs' hs (hes' hz) (hes hz)
        subst hss
        obtain ⟨x, y, hγ, hxy⟩ := list_two Γ₁ h₁ h₂
        have hset := Γ₁.γ_set e' h₁
        rw [hγ] at hset
        have hxt : x ∈ tilde e' := hset ▸ (by simp)
        have hyt : y ∈ tilde e' := hset ▸ (by simp)
        have hcl : closure e' ⊆ closure s' := closure_mono hes
        rw [hγ] at hn ⊢
        rcases dirAgrees_or par hS hs hxy hes (hcl hxt.1) (hcl hyt.1) with h' | h'
        · exact absurd h' hn
        · simpa using h'
  · intro e he h3
    obtain ⟨h₁, h₂⟩ := hthree e he h3
    refine ⟨?_, ?_, ?_⟩
    · rw [hE']
      exact Or.inr ⟨_, ⟨h₁, h₂⟩, rfl⟩
    · rw [hΔ.tilde_core h₁ h₂, tilde_image_homeo]
    · change thinγ Γ₁ Δ g _ = _
      rw [thinγ_core hΔ g h₁ h₂, push_γ]
  · intro e he e' he' heq
    have := core_injOn hΔ ⟨(hthree e he.1 he.2).1, (hthree e he.1 he.2).2⟩
      ⟨(hthree e' he'.1 he'.2).1, (hthree e' he'.1 he'.2).2⟩ heq
    exact h.injective.image_injective this
  · intro e' he' h3
    rw [hE'] at he'
    rcases he' with he' | ⟨c, hc, rfl⟩
    · have := (Γ₁.sk_size he').1
      omega
    · obtain ⟨e, he, rfl⟩ := (push_E h Γ) ▸ hc.1
      have h3' := hc.2
      simp only [] at h3'
      rw [ncard_tilde_image] at h3'
      exact ⟨e, he, h3', rfl⟩
  · intro e he h2
    rw [hE']
    exact Or.inl (Γ₁.two_mem_sk (htwo e he h2).1 (htwo e he h2).2)
  · intro e he h2 hi
    change thinγ Γ₁ Δ g _ = _
    rw [thinγ_two hΔ g (htwo e he h2).1 (htwo e he h2).2]
    have hnb : ¬ Painting.IsBorder (h '' e) := fun hb ↦
      (isInternal_iff_not_border.mp hi) ((isBorder_image h).mp hb)
    change (if _ then _ else _) = _
    rw [ite_eq_right (fun hc ↦ hnb hc.1), push_γ]
  · intro e he hb
    have h2 := size_two_of_border Γ he hb
    change thinγ Γ₁ Δ g _ = _ ∨ thinγ Γ₁ Δ g _ = _
    rw [thinγ_two hΔ g (htwo e he h2).1 (htwo e he h2).2, ← push_γ h Γ e]
    exact hg _ (htwo e he h2).1 (htwo e he h2).2
  · intro e' he' h2
    rw [hE'] at he'
    rcases he' with he' | ⟨c, hc, rfl⟩
    · rcases Γ₁.sk_cases he' with ⟨h₁, -⟩ | ⟨c, hc, h3, hsub, -⟩
      · obtain ⟨e, he, rfl⟩ := (push_E h Γ) ▸ h₁
        refine Or.inl ⟨e, he, ?_, rfl⟩
        rw [← ncard_tilde_image h]
        exact h2
      · obtain ⟨e, he, rfl⟩ := (push_E h Γ) ▸ hc
        have h3' : (tilde e).ncard = 3 := by
          rw [← ncard_tilde_image h]
          exact h3
        right
        refine ⟨?_, e, he, h3', ?_⟩
        · exact (internal_of_three Γ₁ hc h3).mono_left hsub
        · obtain ⟨u, v, -, -, hV, -⟩ := Γ₁.sk_line he'
          rw [← tilde_image_homeo, ← Γ₁.closure_inter_V hc]
          exact fun x hx ↦ ⟨closure_mono hsub hx.1, hV hx⟩
    · have := hc.2
      rw [hΔ.tilde_core hc.1 hc.2] at h2
      omega
  · intro t ht
    obtain ⟨C, rfl⟩ := stdFrame_short par hS ht
    obtain ⟨e, he, -, -, heq⟩ := hedge C
    exact ⟨e, he, heq⟩


end GraphMinor.GM19

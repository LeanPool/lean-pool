/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.LineCut
public import LeanPool.GraphMinor.GM19.Section10g

import LeanPool.GraphMinor.GM19.FragmentOrient

/-!
# The refinement in the proof of (10.5)

Let `Σ'` be a fragment on which `ψ` is one to one. Suppose `Φ` has more vertices in the part that is
cut off than the cut has vertices,
and suppose each long side keeps at most one piece. Then the colour scheme of the fragment is a
refinement of `χ`.

To count we use that a frame has as many sides as vertices (`Frame.ncard_sides`), which holds cuff
by cuff by `arcs_of_oArc`. So the
short sides are the vertices less the long sides, and it suffices that each long side keeps a piece
and that the fragment has fewer
vertices than `Φ`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe w

variable {S : Type} [TopologicalSpace S] [T2Space S]

/-- **A frame has as many sides as vertices.** -/
theorem Frame.ncard_sides (hS : IsSurface S) (Φ : Frame S) : Φ.sides.ncard = Φ.V.ncard := by
  classical
  have hfc : (cuffs S).Finite := (cuff_statement S hS).2.1
  have key : ∀ 𝓒 : Set (Set S), 𝓒.Finite → 𝓒 ⊆ cuffs S →
      (arcComponentsIn (⋃₀ 𝓒 \ Φ.V)).Finite ∧ (arcComponentsIn (⋃₀ 𝓒 \ Φ.V)).ncard =
        (Φ.V ∩ ⋃₀ 𝓒).ncard := by
    intro 𝓒 hf
    induction 𝓒, hf using Set.Finite.induction_on with
    | empty =>
      intro _
      have : arcComponentsIn (⋃₀ (∅ : Set (Set S)) \ Φ.V) = ∅ := by
        ext e
        simp only [sUnion_empty, empty_sdiff, mem_empty_iff_false, iff_false]
        rintro ⟨⟨x, hx⟩, h, -⟩
        exact h hx
      rw [this]
      simp
    | @insert C 𝓒 hC hf ih =>
      intro hsub
      have hCc : C ∈ cuffs S := hsub (mem_insert _ _)
      obtain ⟨h₁, h₂⟩ := ih fun _ h ↦ hsub (mem_insert_of_mem _ h)
      let C' : cuffs S := ⟨C, hCc⟩
      have hO : IsOArc C := ⟨cuffPar hS C'⟩
      have hcC : IsClosed C := isClosed_cuff hS C'
      have hcU : IsClosed (⋃₀ 𝓒) := hf.isClosed_sUnion fun D hD ↦ isClosed_cuff hS ⟨D, hsub
        (mem_insert_of_mem _ hD)⟩
      have hdis : Disjoint C (⋃₀ 𝓒) := disjoint_left.2 fun x hx ⟨D, hD, hxD⟩ ↦
        hC ((cuffs_eq_of_mem hCc (hsub (mem_insert_of_mem _ hD)) hx hxD) ▸ hD)
      have hint : C ∩ ⋃₀ 𝓒 ⊆ Φ.V := by
        rw [disjoint_iff_inter_eq_empty.1 hdis]
        exact empty_subset _
      have h2 : 2 ≤ (Φ.V ∩ C).ncard := by
        obtain ⟨p, hp, q, hq, hne⟩ := Frame.two_on_cuff hS Φ C'
        exact (one_lt_ncard (Φ.finite_V.subset inter_subset_left)).2 ⟨p, hp, q, hq, hne⟩
      obtain ⟨f₃, n₃, -⟩ := arcs_of_oArc (Φ.finite_V.subset inter_subset_left) hO
        inter_subset_right h2
      have hs : C \ (Φ.V ∩ C) = C \ Φ.V := by
        ext z
        simp only [mem_sdiff, mem_inter_iff, not_and]
        exact ⟨fun h ↦ ⟨h.1, fun hz ↦ h.2 hz h.1⟩, fun h ↦ ⟨h.1, fun hz ↦ absurd hz h.2⟩⟩
      rw [hs] at f₃ n₃
      have hA : arcComponentsIn (⋃₀ insert C 𝓒 \ Φ.V) = arcComponentsIn (C \ Φ.V) ∪ arcComponentsIn
        (⋃₀ 𝓒 \ Φ.V) := by
        rw [sUnion_insert]
        exact arcComponentsIn_union_sdiff hcC hcU hint
      have hdisj : Disjoint (arcComponentsIn (C \ Φ.V)) (arcComponentsIn (⋃₀ 𝓒 \ Φ.V))
        := disjoint_left.2 fun e he₁ he₂ ↦ by
        obtain ⟨z, hz⟩ := he₁.1
        exact disjoint_left.1 hdis (he₁.2.1 hz).1 (he₂.2.1 hz).1
      rw [hA]
      refine ⟨f₃.union h₁, ?_⟩
      have hdisjV : Disjoint (Φ.V ∩ C) (Φ.V ∩ ⋃₀ 𝓒) :=
        disjoint_left.2 fun x hx hx' => disjoint_left.1 hdis hx.2 hx'.2
      rw [ncard_union_eq hdisj f₃ h₁, n₃, h₂, sUnion_insert, inter_union_distrib_left,
        ncard_union_eq hdisjV (Φ.finite_V.subset inter_subset_left)
          (Φ.finite_V.subset inter_subset_left)]
  obtain ⟨-, h⟩ := key (cuffs S) hfc Subset.rfl
  rw [sUnion_cuffs, inter_eq_left.2 Φ.V_subset] at h
  exact h

/-- A side of a frame lies on one cuff, and it has two ends there, both vertices of the frame. -/
theorem Frame.side_on_cuff (hS : IsSurface S) (Φ : Frame S) {s : Set S} (hs : s ∈ Φ.sides) :
    ∃ Θ ∈ cuffs S, s ⊆ Θ ∧ IsMarkedArc (Φ.V ∩ Θ) s := by
  classical
  have hs' : s ∈ arcComponentsIn (bd S \ Φ.V) := hs
  obtain ⟨⟨x, hx⟩, hsub, hpc, hmax⟩ := hs'
  have hxb : x ∈ bd S := (hsub hx).1
  let Θ := connectedComponentIn (bd S) x
  have hΘ : Θ ∈ cuffs S := ⟨x, hxb, rfl⟩
  have hsΘ : s ⊆ Θ := hpc.isConnected.isPreconnected.subset_connectedComponentIn hx fun y hy ↦
    (hsub hy).1
  let C' : cuffs S := ⟨Θ, hΘ⟩
  have hO : IsOArc Θ := ⟨cuffPar hS C'⟩
  have h2 : 2 ≤ (Φ.V ∩ Θ).ncard := by
    obtain ⟨p, hp, q, hq, hne⟩ := Frame.two_on_cuff hS Φ C'
    exact (one_lt_ncard (Φ.finite_V.subset inter_subset_left)).2 ⟨p, hp, q, hq, hne⟩
  obtain ⟨-, -, hm⟩ := arcs_of_oArc (Φ.finite_V.subset inter_subset_left) hO inter_subset_right h2
  refine ⟨Θ, hΘ, hsΘ, (hm s ?_).1⟩
  refine ⟨⟨x, hx⟩, fun y hy ↦ ⟨hsΘ hy, fun h ↦ (hsub hy).2 h.1⟩, hpc,
    fun T hT hTp hsT ↦ hmax T (fun y hy ↦ ?_) hTp hsT⟩
  exact ⟨cuff_subset_bd C' (hT hy).1, fun h ↦ (hT hy).2 ⟨h, (hT hy).1⟩⟩


variable {S₁ : Type} [TopologicalSpace S₁] [T2Space S₁] [Nonempty S₁] {β : Type w} {χ :
  ColourScheme S β} {K : Drawing S} {ψ : S₁ → S}
  {Γ : Painting S}

theorem QuasiOrder.isSubIdeal_refl (Ω : QuasiOrder β) : Ω.IsSubIdeal Ω
  := ⟨Subset.rfl, fun _ _ _ h _ ↦ h, fun _ _ _ _ ↦ Iff.rfl⟩

omit [Nonempty S₁] in
omit [T2Space S₁] in
/-- Two sides of the frame of a fragment over a path-connected set of `bd(Σ)` without vertices are
equal, if `ψ` is one to one. -/
theorem FrameData.side_eq_of_isPathConnected {Φ : Frame S} (D : FrameData Φ Γ K ψ)
  (hinj : Function.Injective ψ) {B : Set S}
    (hB : IsPathConnected B) (hBr : B ⊆ range ψ) (hBb : B ⊆ bd S) (hBV : Disjoint B
      (Φ.V ∪ K.V)) {R₁ R₂ : Set S₁}
    (h₁ : R₁ ∈ arcComponentsIn (bd S₁ \ pullFrameV Φ K ψ)) (h₂ : R₂ ∈ arcComponentsIn
      (bd S₁ \ pullFrameV Φ K ψ)) (hs₁ : ψ '' R₁ ⊆ B)
    (hs₂ : ψ '' R₂ ⊆ B) : R₁ = R₂ := by
  have : CompactSpace S₁ := D.pull.frag.isSurface.1
  have he : IsClosedEmbedding ψ := D.pull.frag.continuous_ψ.isClosedEmbedding hinj
  have hX : IsPathConnected (ψ ⁻¹' B) := by
    rw [he.isInducing.isPathConnected_iff, image_preimage_eq_of_subset hBr]
    exact hB
  have hsub : ψ ⁻¹' B ⊆ bd S₁ \ pullFrameV Φ K ψ := fun x hx ↦
    ⟨D.pull.mem_bd_of_notMem_R (Or.inl (hBb hx)), fun hv ↦ disjoint_left.1 hBV hx hv⟩
  have e₁ := h₁.2.2.2 _ hsub hX (image_subset_iff.1 hs₁)
  have e₂ := h₂.2.2.2 _ hsub hX (image_subset_iff.1 hs₂)
  exact e₁.symm.trans e₂

open Classical in
omit [Nonempty S₁] in
/-- **The colour scheme of the fragment is a refinement of `χ`.** -/
theorem fragScheme_isRefinement (D : FrameData χ.Φ Γ K ψ) (hF : IsFeature χ.Φ K) (flip : Set S₁
  → Bool) (a₀ : β)
    (hhom : Nonempty (S₁ ≃ₜ S)) (hinj : Function.Injective ψ)
    (hconn : ∀ s ∈ χ.Φ.longSides, (s ∩ range ψ) \ K.U = ∅ ∨ IsPathConnected ((s ∩ range ψ) \ K.U))
    (hcount : (∃ s ∈ χ.Φ.longSides, s ∩ range ψ ⊆ K.U) ∨ K.V.ncard < (χ.Φ.V ∩
      ((range ψ)ᶜ ∪ K.U)).ncard) :
    (fragScheme χ a₀ D hF flip).IsRefinement χ := by
  have hS := D.pull.surface
  have hS₁ := D.pull.frag.isSurface
  set Φ' := D.frame hF flip with hΦ'
  have hlongs : ∀ R, R ∈ Φ'.longSides ↔ R ∈ arcComponentsIn (bd S₁ \ pullFrameV χ.Φ K ψ)
    ∧ ∃ s ∈ χ.Φ.longSides, ψ '' R ⊆ s :=
    fun R ↦ Iff.rfl
  let f : Set S₁ → Set S := fun R ↦ if h : ∃ s ∈ χ.Φ.longSides, ψ '' R ⊆ s then h.choose else ∅
  have hf : ∀ {R}, (∃ s ∈ χ.Φ.longSides, ψ '' R ⊆ s) → f R ∈ χ.Φ.longSides ∧ ψ '' R ⊆ f R
    := fun {R} h ↦ by
    simp only [f, dite_eq_left h]
    exact h.choose_spec
  have hoffK : ∀ {R s}, R ∈ arcComponentsIn (bd S₁ \ pullFrameV χ.Φ K ψ) → s ∈ χ.Φ.longSides
    → ψ '' R ⊆ s → ψ '' R ⊆ (s ∩ range ψ) \ K.U := by
    rintro R s hR hs hsub _ ⟨x, hx, rfl⟩
    refine ⟨⟨hsub (mem_image_of_mem _ hx), mem_range_self x⟩, fun hk ↦ ?_⟩
    have hb : ψ x ∈ bd S := (hs.1.2.1 (hsub (mem_image_of_mem _ hx))).1
    exact (hR.2.1 hx).2 (Or.inr (D.K_bd ⟨hk, hb⟩))
  have huniq : ∀ {R₁ R₂}, R₁ ∈ Φ'.longSides → R₂ ∈ Φ'.longSides → f R₁ = f R₂ → R₁ = R₂ := by
    intro R₁ R₂ h₁ h₂ he
    obtain ⟨h₁s, h₁l⟩ := (hlongs R₁).1 h₁
    obtain ⟨h₂s, h₂l⟩ := (hlongs R₂).1 h₂
    obtain ⟨m₁, s₁⟩ := hf h₁l
    obtain ⟨m₂, s₂⟩ := hf h₂l
    rw [← he] at m₂ s₂
    have b₁ := hoffK h₁s m₁ s₁
    have b₂ := hoffK h₁s m₁ s₁
    have b₂' := hoffK h₂s m₁ s₂
    obtain ⟨x, hx⟩ := h₁s.1
    have hne : ((f R₁ ∩ range ψ) \ K.U).Nonempty := ⟨_, b₁ (mem_image_of_mem _ hx)⟩
    rcases hconn _ m₁ with h₀ | hp
    · exact absurd hne (by rw [h₀]; exact not_nonempty_empty)
    · refine D.side_eq_of_isPathConnected hinj hp (fun z hz ↦ hz.1.2) (fun z hz ↦
        (m₁.1.2.1 hz.1.1).1) ?_ h₁s h₂s b₁ b₂'
      refine disjoint_left.2 fun z hz hv ↦ ?_
      rcases hv with hv | hv
      · exact (m₁.1.2.1 hz.1.1).2 hv
      · exact hz.2 (K.V_subset_U hv)
  refine ⟨hhom, rfl, rfl, f, fun R hR ↦ (hf ((hlongs R).1 hR).2).1, fun R hR ↦ ?_,
    fun R₁ h₁ R₂ h₂ hne he ↦ absurd (huniq h₁ h₂ he) hne, ?_⟩
  · obtain ⟨hRs, hl⟩ := (hlongs R).1 hR
    obtain ⟨m, sub⟩ := hf hl
    have : (fragScheme χ a₀ D hF flip).ΩS R = χ.ΩS (f R) := fragScheme_ΩS hRs.1 m.1 sub
    rw [this]
    exact QuasiOrder.isSubIdeal_refl _
  · intro hall
    have hcard : K.V.ncard < (χ.Φ.V ∩ ((range ψ)ᶜ ∪ K.U)).ncard := by
      rcases hcount with ⟨s, hs, hsub⟩ | h
      · exfalso
        obtain ⟨R, hR, hsf, -⟩ := hall s hs
        obtain ⟨hRs, hl⟩ := (hlongs R).1 hR
        obtain ⟨m, sub⟩ := hf hl
        obtain ⟨x, hx⟩ := hRs.1
        have := hoffK hRs m sub (mem_image_of_mem _ hx)
        exact this.2 (hsub ⟨hsf ▸ this.1.1, this.1.2⟩)
      · exact h
    have hfΦ : χ.Φ.sides.Finite := χ.Φ.finite_sides
    have hfΦ' : Φ'.sides.Finite := Φ'.finite_sides
    have hsΦ := Frame.ncard_sides hS χ.Φ
    have hsΦ' := Frame.ncard_sides hS₁ Φ'
    have hsplit : ∀ {T : Type} [TopologicalSpace T] (X : Frame T), X.longSides.ncard +
      X.shortSides.ncard = X.sides.ncard := by
      intro T _ X
      have hd : Disjoint X.longSides X.shortSides := disjoint_left.2 fun _ h h' ↦ h'.2 h.2
      have hu : X.longSides ∪ X.shortSides = X.sides := by
        ext e
        constructor
        · rintro (h | h)
          · exact h.1
          · exact h.1
        · intro h
          by_cases hl : X.isLong e
          · exact Or.inl ⟨h, hl⟩
          · exact Or.inr ⟨h, hl⟩
      rw [← hu, ncard_union_eq hd (X.finite_sides.subset fun _ h ↦ h.1)
        (X.finite_sides.subset fun _ h ↦ h.1)]
    have hL : χ.Φ.longSides.ncard ≤ Φ'.longSides.ncard := by
      have hsub : χ.Φ.longSides ⊆ f '' Φ'.longSides := fun s hs ↦ by
        obtain ⟨R, hR, h, -⟩ := hall s hs
        exact ⟨R, hR, h⟩
      have hfin : Φ'.longSides.Finite := hfΦ'.subset fun _ h => h.1
      exact (ncard_le_ncard hsub (hfin.image _)).trans (ncard_image_le hfin)
    have hP := χ.Φ.finite_V
    set P := χ.Φ.V ∩ ((range ψ)ᶜ ∪ K.U) with hPdef
    have hVsub : ψ '' Φ'.V ⊆ (χ.Φ.V \ P) ∪ K.V := by
      rintro _ ⟨x, hx, rfl⟩
      rcases hx with h | h
      · by_cases hk : ψ x ∈ K.U
        · exact Or.inr (D.K_bd ⟨hk, χ.Φ.V_subset h⟩)
        · exact Or.inl ⟨h, fun hp ↦ hp.2.elim (fun h' ↦ h' (mem_range_self x)) hk⟩
      · exact Or.inr h
    have hle : Φ'.V.ncard ≤ (χ.Φ.V \ P).ncard + K.V.ncard := by
      rw [← ncard_image_of_injective _ hinj]
      exact (ncard_le_ncard hVsub ((hP.subset sdiff_subset).union K.finite_V)).trans
        (ncard_union_le _ _)
    have hdiff : (χ.Φ.V \ P).ncard + P.ncard = χ.Φ.V.ncard := ncard_sdiff_add_ncard_of_subset
      inter_subset_left hP
    have h₁ := hsplit χ.Φ
    have h₂ := hsplit Φ'
    change Φ'.shortSides.ncard < χ.Φ.shortSides.ncard
    omega

/-- The places of one fragment are well-behaved by `S₄`, if the fragment is a copy of `Σ` and the
count of `fragScheme_isRefinement`
holds. -/
theorem wellBehaved_S4 (hS : IsSurface S) {K : Drawing S} (hF : IsFeature χ.Φ K) {𝒮 : Set
  (ColouredPainting χ)}
    (hcl : IsPaintingClass χ 𝒮)
    (hlines : ∀ e ∈ arcComponentsIn (K.U \ K.V), ∃ u v, u ≠ v ∧ closure e ∩ K.V = {u, v}
      ∧ IsLineWithEnds (closure e) u v)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] {ψ : Y → S} (hY : IsSurface Y)
      (hψ : IsCutMap ψ K.U) (hsheet : HasSheets ψ K)
    (y : Y) (l : List S) (m : ℕ) (a₀ : β) (hS4 : ConditionS4 χ) (hhom : Nonempty
      (connectedComponent y ≃ₜ S))
    (hinj : InjOn ψ (connectedComponent y))
    (hconn : ∀ s ∈ χ.Φ.longSides, (s ∩ (ψ '' connectedComponent y)) \ K.U = ∅ ∨ IsPathConnected
      ((s ∩ (ψ '' connectedComponent y)) \ K.U))
    (hcount : (∃ s ∈ χ.Φ.longSides, s ∩ (ψ '' connectedComponent y) ⊆ K.U) ∨
      K.V.ncard < (χ.Φ.V ∩ ((ψ '' connectedComponent y)ᶜ ∪ K.U)).ncard)
    (hO : IsOrientableSurface (connectedComponent y) → IsOrientableSurface S) :
    IsWellBehavedPlaces {X | IsCutPlace χ K (fun x : connectedComponent y ↦ ψ x.1) l m X ∧ X.P ∈ 𝒮}
      := by
  have : Nonempty (connectedComponent y) := ⟨⟨y, mem_connectedComponent⟩⟩
  have hr : range (fun x : connectedComponent y ↦ ψ x.1) = ψ '' connectedComponent y := by
    ext z
    simp
  apply wellBehaved_of_fragment (fun x : connectedComponent y ↦ ψ x.1) hF l m a₀
    (fun a b hab hoff ↦ Subtype.ext (hψ.2.2.1 hoff (fun h ↦ hoff (hab ▸ h)) hab))
    (fun X hX ↦ frameData_of_cut hS X.P.fits hX.inter hlines hY hψ hsheet y)
  intro seq hq h flip hflip
  set D := fun i ↦ frameData_of_cut hS (seq i).P.fits (h i).inter hlines hY hψ hsheet y with hDdef
  have hnb := hS4 _ (fragScheme χ a₀ (D 0) hF flip) (fragScheme_isRefinement (D 0) hF flip a₀ hhom
    (fun a b hab ↦ Subtype.ext (hinj a.2 b.2 hab)) (by rw [hr]; exact hconn)
      (by rw [hr]; exact hcount))
  have hsim := frag_similarly hcl hS hF a₀ (D 0) (fun i ↦ (seq i).P) hq D (fun i ↦
    (h i).anchored) flip hO
  by_contra hno
  push Not at hno
  exact hnb ⟨_, fun i j hij ⟨σv, σe, hσ⟩ ↦ hno i j hij σv σe hσ, hsim⟩

end GraphMinor.GM19

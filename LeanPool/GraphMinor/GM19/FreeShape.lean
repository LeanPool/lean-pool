/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FreeTopology
public import LeanPool.GraphMinor.GM19.Section10j
public import LeanPool.GraphMinor.GM19.FragmentOrient

/-!
# The fragment outside a freedom flaw

`IsFreeShape cap Φ K Z` says what the proof of (10.5) needs of the closed disc `Z` around a flaw. If
the fragment outside `Z` has fewer
cuffs than `Σ` we use `S₃`. Otherwise it is a copy of `Σ` on which `ψ` is one to one
(`free_fragment`), and we use `S₄`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]


/-- What the count needs: each long side keeps at most one piece outside `In`, and `In` holds a long
side or more vertices of the frame
than `K` has. -/
def FreeFacts (Φ : Frame S) (K : Drawing S) (In : Set S) : Prop :=
  (∀ s ∈ Φ.longSides, s \ In = ∅ ∨ IsPathConnected (s \ In)) ∧ ((∃ s ∈ Φ.longSides, s ⊆ In)
    ∨ K.V.ncard < (Φ.V ∩ In).ncard)

/-- The closed disc `Z` around a freedom flaw. -/
structure IsFreeShape (cap : IsCappedSurface S Shat) (Φ : Frame S) (K : Drawing S)
  (Z : Set Shat) : Prop where
  disc : IsClosedDisc Z
  sub : cap.emb '' K.U ⊆ discBd Z
  rest : discBd Z ⊆ cap.discs ∪ cap.emb '' K.U
  touch : ∀ Θ ∈ cuffs S, ¬ closure (cap.cuffDisc Θ) ⊆ Z → (closure (cap.cuffDisc Θ) ∩
    Z).Subsingleton
  inner : ∃ Θ ∈ cuffs S, closure (cap.cuffDisc Θ) ⊆ Z
  facts : (∀ Θ ∈ cuffs S, closure (cap.cuffDisc Θ) ⊆ Z ∨ Disjoint (closure (cap.cuffDisc Θ)) Z) →
    FreeFacts Φ K (cap.emb ⁻¹' discInt Z ∪ K.U)

/-- What makes a fragment good for (10.5). -/
def FreeGood {Y : Type} [TopologicalSpace Y] (Φ : Frame S) (K : Drawing S)
  (Shat : Type) [TopologicalSpace Shat] (ψ : Y → S) (c : Set Y) : Prop :=
  (∀ (Shat₁ : Type) [TopologicalSpace Shat₁], IsCappedSurface c Shat₁ → Nonempty (Shat₁ ≃ₜ Shat)) ∧
    (IsOrientableSurface c → IsOrientableSurface S) ∧
    (numCuffs c < numCuffs S ∨ (Nonempty (c ≃ₜ S) ∧ InjOn ψ c ∧
      (∀ s ∈ Φ.longSides, (s ∩ (ψ '' c)) \ K.U = ∅ ∨ IsPathConnected ((s ∩ (ψ '' c)) \ K.U)) ∧
      ((∃ s ∈ Φ.longSides, s ∩ (ψ '' c) ⊆ K.U) ∨ K.V.ncard < (Φ.V ∩ ((ψ '' c)ᶜ ∪ K.U)).ncard)))

/-- **The fragment outside `Z`.** -/
theorem free_fragment {Y : Type} [TopologicalSpace Y] [T2Space Y] [ConnectedSpace S]
  (hS : IsSurface S) (cap : IsCappedSurface S Shat)
    {Φ : Frame S} {K : Drawing S} {Z : Set Shat} (h : IsFreeShape cap Φ K Z) {ψ : Y → S}
      (hY : IsSurface Y) (hψ : IsCutMap ψ K.U) :
    ∃ y : Y, ψ '' connectedComponent y = (cap.emb ⁻¹' discInt Z)ᶜ ∧ FreeGood Φ K Shat ψ
      (connectedComponent y) := by
  classical
  have hT := cap.isClosedSurface
  have hman : ∀ x : Shat, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  have hD := h.disc
  have : ConnectedSpace Shat := cap.connected
  have hfc : (cuffs S).Finite := (cuff_statement S hS).2.1
  have hbd : Z \ discInt Z ⊆ discBd Z := by
    rintro x ⟨hx, hn⟩
    by_contra hb
    exact hn ⟨hx, hb⟩
  obtain ⟨y, hy, hcap, hnum, T', _, e, P, hT', ⟨hom⟩, hP, hs, ht⟩ := exists_outer_fragment_core hS
    cap hY hψ hD.isClosed
    (hD.isOpen_discInt hman) (discInt_subset Z) (fun c hc ↦ isCell_disc hT
      (isClosedDisc_image_injOn hD c.continuous.continuousOn hc).1)
    (h.sub.trans (Surface.discBd_subset Z)) (hbd.trans h.rest) (hbd.trans
      (discBd_subset_closure_compl hT hD)) h.touch
  have hy' : ψ '' connectedComponent y = (cap.emb ⁻¹' discInt Z)ᶜ := by rw [hy, preimage_compl]
  refine ⟨y, hy', hcap, fun ⟨ω⟩ ↦ ?_, ?_⟩
  · have : T2Space T' := hT'.2.1
    have : ConnectedSpace Shat := cap.connected
    have : ConnectedSpace T' := hom.symm.surjective.connectedSpace hom.symm.continuous
    have h₁ := isOrientable_of_inside hT' hP e hs ht (ω.isPartial _)
    exact isOrientable_of_embedding cap.isEmbedding (isOrientable_of_embedding hom.symm.isEmbedding
      h₁)
  by_cases hlt : numCuffs (connectedComponent y) < numCuffs S
  · exact Or.inl hlt
  right
  have hall : ∀ Θ ∈ cuffs S, closure (cap.cuffDisc Θ) ⊆ Z ∨ Disjoint (closure (cap.cuffDisc Θ)) Z
    := by
    by_contra hno
    push Not at hno
    obtain ⟨Θ₀, hΘ₀, hn₁, hn₂⟩ := hno
    obtain ⟨Θ₁, hΘ₁, hin⟩ := h.inner
    have hne' : Θ₀ ≠ Θ₁ := by
      rintro rfl
      exact hn₁ hin
    have hE₁ : (closure (cap.cuffDisc Θ₁)).Nonempty := (cap.cuffDisc_closedDisc _
      hΘ₁).nonempty_discInt.mono (discInt_subset _)
    have hsub : {Θ ∈ cuffs S | Disjoint (closure (cap.cuffDisc Θ)) Z} ⊆ cuffs S \ {Θ₀, Θ₁} := by
      rintro Θ ⟨hΘ, hd⟩
      refine ⟨hΘ, ?_⟩
      rintro (rfl | h')
      · exact hn₂ hd
      · rw [mem_singleton_iff.1 h'] at hd
        obtain ⟨x, hx⟩ := hE₁
        exact disjoint_left.1 hd hx (hin hx)
    have h₁ := ncard_le_ncard hsub (hfc.subset sdiff_subset)
    have h₂ : (cuffs S \ {Θ₀, Θ₁}).ncard + ({Θ₀, Θ₁} : Set (Set S)).ncard = (cuffs S).ncard :=
      ncard_sdiff_add_ncard_of_subset (by
        rintro _ (rfl | h')
        · exact hΘ₀
        · exact (mem_singleton_iff.1 h') ▸ hΘ₁) hfc
    rw [ncard_pair hne'] at h₂
    change ¬ numCuffs (connectedComponent y) < (cuffs S).ncard at hlt
    omega
  have hfrag := isCuttingFragment_of_cut hS hY hψ (K := K) rfl y
  have hconn := hfrag.connected
  obtain ⟨Shat₁, _, ⟨cap₁⟩⟩ := exists_cappedSurface _ (connectedComponent y) hfrag.isSurface hconn
    rfl
  have hle : numCuffs S ≤ numCuffs (connectedComponent y) := not_lt.1 hlt
  have hcard : numCuffs (connectedComponent y) = numCuffs S := by
    refine le_antisymm ?_ hle
    obtain ⟨Θ₁, hΘ₁, hin⟩ := h.inner
    have hE₁ : (closure (cap.cuffDisc Θ₁)).Nonempty := (cap.cuffDisc_closedDisc _
      hΘ₁).nonempty_discInt.mono (discInt_subset _)
    have hsub : {Θ ∈ cuffs S | Disjoint (closure (cap.cuffDisc Θ)) Z} ⊆ cuffs S \ {Θ₁} := by
      rintro Θ ⟨hΘ, hd⟩
      refine ⟨hΘ, ?_⟩
      intro h'
      rw [mem_singleton_iff.1 h'] at hd
      obtain ⟨x, hx⟩ := hE₁
      exact disjoint_left.1 hd hx (hin hx)
    have h₁ := ncard_le_ncard hsub (hfc.subset sdiff_subset)
    have h₂ : (cuffs S \ {Θ₁}).ncard + ({Θ₁} : Set (Set S)).ncard = (cuffs S).ncard :=
      ncard_sdiff_add_ncard_of_subset (singleton_subset_iff.2 hΘ₁) hfc
    rw [ncard_singleton] at h₂
    change _ ≤ (cuffs S).ncard
    omega
  obtain ⟨hf₁, hf₂⟩ := h.facts hall
  have hset : ∀ s : Set S, (s ∩ (ψ '' connectedComponent y)) \ K.U = s \
    (cap.emb ⁻¹' discInt Z ∪ K.U) := fun s ↦ by
    rw [hy']
    ext x
    simp only [mem_sdiff, mem_inter_iff, mem_compl_iff, mem_union, not_or]
    tauto
  have hcompl : (ψ '' connectedComponent y)ᶜ ∪ K.U = cap.emb ⁻¹' discInt Z ∪ K.U := by
    rw [hy', compl_compl]
  refine ⟨nonempty_homeomorph_of_cap hfrag.isSurface hconn hS ‹_› cap₁ cap (hcap _ cap₁) hcard,
    ?_, ?_, ?_⟩
  · refine injOn_of_outside hS cap hY hψ y hD h.sub h.rest hall ?_
    rw [hy']
  · intro s hs'
    rw [hset]
    exact hf₁ s hs'
  · rw [hcompl]
    refine hf₂.imp ?_ id
    rintro ⟨s, hs', hsub⟩
    refine ⟨s, hs', fun x hx ↦ ?_⟩
    by_contra hk
    have : x ∈ (s ∩ (ψ '' connectedComponent y)) \ K.U := ⟨hx, hk⟩
    rw [hset] at this
    exact this.2 (hsub this.1)

omit [T2Space S] [T2Space Shat] in
/-- The shape moves to the cap twisted by a homeomorphism that keeps the frame. -/
theorem IsFreeShape.ofHomeo {cap : IsCappedSurface S Shat} {Φ : Frame S} {K K' :
  Drawing S} {Z : Set Shat}
    (h : IsFreeShape cap Φ K' Z) (f : S ≃ₜ S) (hf : IsFramePreservingHomeo Φ f) (hU : f '' K.U
      = K'.U) (hV : f '' K.V = K'.V) :
    IsFreeShape (cap.ofHomeo f) Φ K Z := by
  have him : ∀ A : Set S, (cap.ofHomeo f).emb '' A = cap.emb '' (f '' A) := fun A ↦ by
    rw [image_image]
    rfl
  have hsym : ∀ A : Set S, f '' (f.symm '' A) = A := fun A ↦ by
    rw [image_image]
    simp
  have hc : ∀ {Θ}, Θ ∈ cuffs S → f '' Θ ∈ cuffs S ∧ (cap.ofHomeo f).cuffDisc Θ = cap.cuffDisc
    (f '' Θ) := fun {Θ} hΘ ↦
    ⟨by rw [cuffs_eq_image f]; exact mem_image_of_mem _ hΘ, rfl⟩
  have hc' : ∀ {Θ}, Θ ∈ cuffs S → f.symm '' Θ ∈ cuffs S ∧ (cap.ofHomeo f).cuffDisc (f.symm '' Θ)
    = cap.cuffDisc Θ := fun {Θ} hΘ ↦ by
    refine ⟨?_, ?_⟩
    · rw [cuffs_eq_image f.symm]
      exact mem_image_of_mem _ hΘ
    · change cap.cuffDisc (f '' (f.symm '' Θ)) = _
      rw [hsym]
  have hdiscs : (cap.ofHomeo f).discs = cap.discs := by
    ext x
    simp only [IsCappedSurface.discs, mem_iUnion₂]
    constructor
    · rintro ⟨Θ, hΘ, hx⟩
      rw [(hc hΘ).2] at hx
      exact ⟨_, (hc hΘ).1, hx⟩
    · rintro ⟨Θ, hΘ, hx⟩
      rw [← (hc' hΘ).2] at hx
      exact ⟨_, (hc' hΘ).1, hx⟩
  have hKU : (cap.ofHomeo f).emb '' K.U = cap.emb '' K'.U := by rw [him, hU]
  refine ⟨h.disc, by rw [hKU]; exact h.sub, by rw [hKU, hdiscs]; exact h.rest, ?_, ?_, ?_⟩
  · intro Θ hΘ hn
    rw [(hc hΘ).2] at hn ⊢
    exact h.touch _ (hc hΘ).1 hn
  · obtain ⟨Θ, hΘ, hin⟩ := h.inner
    exact ⟨_, (hc' hΘ).1, by rw [(hc' hΘ).2]; exact hin⟩
  · intro hall
    obtain ⟨hf₁, hf₂⟩ := h.facts fun Θ hΘ ↦ by
      have := hall _ (hc' hΘ).1
      rwa [(hc' hΘ).2] at this
    set In' := cap.emb ⁻¹' discInt Z ∪ K'.U with hIn'
    have hmem : ∀ x, x ∈ (cap.ofHomeo f).emb ⁻¹' discInt Z ∪ K.U ↔ f x ∈ In' := fun x ↦ by
      refine or_congr Iff.rfl ?_
      rw [← hU]
      exact (f.injective.mem_set_image).symm
    have hside : ∀ s ∈ Φ.longSides, ∀ x, f x ∈ s ↔ x ∈ s := fun s hs x ↦ by
      have := hf.preserve_sides s hs.1
      constructor
      · intro hx
        rw [← this] at hx
        obtain ⟨y, hy, he⟩ := hx
        exact f.injective he ▸ hy
      · intro hx
        rw [← this]
        exact mem_image_of_mem _ hx
    constructor
    · intro s hs
      have heq : s \ ((cap.ofHomeo f).emb ⁻¹' discInt Z ∪ K.U) = f.symm '' (s \ In') := by
        ext x
        simp only [mem_sdiff, hmem]
        constructor
        · rintro ⟨h₁, h₂⟩
          exact ⟨f x, ⟨(hside s hs x).2 h₁, h₂⟩, f.symm_apply_apply x⟩
        · rintro ⟨y, ⟨h₁, h₂⟩, rfl⟩
          refine ⟨?_, by rwa [f.apply_symm_apply]⟩
          rw [← hside s hs, f.apply_symm_apply]
          exact h₁
      rw [heq]
      rcases hf₁ s hs with h' | h'
      · left
        rw [h', image_empty]
      · exact Or.inr (h'.image f.symm.continuous)
    · refine hf₂.imp ?_ ?_
      · rintro ⟨s, hs, hsub⟩
        refine ⟨s, hs, fun x hx ↦ (hmem x).2 (hsub ((hside s hs x).2 hx))⟩
      · intro hlt
        have h₁ : K.V.ncard = K'.V.ncard := by
          rw [← hV, ncard_image_of_injective _ f.injective]
        have h₂ : Φ.V ∩ ((cap.ofHomeo f).emb ⁻¹' discInt Z ∪ K.U) = Φ.V ∩ In' := by
          ext x
          simp only [mem_inter_iff]
          refine and_congr_right fun hx ↦ ?_
          rw [hmem, hf.fix_V x hx]
        rw [h₁, h₂]
        exact hlt

omit [T2Space Shat] in
/-- **The count holds on the cuff `Θ`.** Off `Θ` the frame lies outside `Z`. On `Θ` the part `A` is
what stays outside. -/
theorem freeFacts_of_cuff (hS : IsSurface S) (Φ : Frame S) {K : Drawing S}
  (cap : IsCappedSurface S Shat) {Z : Set Shat} {Θ A : Set S} (hΘ : Θ ∈ cuffs S)
    {In : Set S} (hInZ : In ⊆ cap.emb ⁻¹' Z) (hoth : ∀ Θ' ∈ cuffs S, Θ' ≠ Θ → Disjoint (closure
      (cap.cuffDisc Θ')) Z) (hApc : IsPreconnected A)
    (hAΘ : A ⊆ Θ) (hiff : ∀ x ∈ Θ, x ∈ In ↔ x ∉ A) (hcl : IsClosed (Θ \ A))
    (hcount : (∃ s ∈ Φ.longSides, s ⊆ In) ∨ K.V.ncard < (Φ.V ∩ In).ncard) : FreeFacts Φ K In := by
  classical
  have hO : IsOArc Θ := ⟨cuffPar hS ⟨Θ, hΘ⟩⟩
  have hoff : ∀ {Θ' x}, Θ' ∈ cuffs S → Θ' ≠ Θ → x ∈ Θ' → x ∉ In := fun {Θ' x} hΘ' hne hx hxI ↦
    disjoint_left.1 (hoth Θ' hΘ' hne) (cap.mem_closure_emb hS hΘ' hx) (hInZ hxI)
  have hcuff : ∀ {x}, x ∈ bd S → x ∈ In → x ∈ Θ := fun {x} hx hxI ↦ by
    by_contra hn
    have hΘ' : connectedComponentIn (bd S) x ∈ cuffs S := ⟨x, hx, rfl⟩
    have hm : x ∈ connectedComponentIn (bd S) x := mem_connectedComponentIn hx
    exact hoff hΘ' (fun h ↦ hn (h ▸ hm)) hm hxI
  obtain ⟨w, hwV, hwΘ, hwA⟩ : ∃ w ∈ Φ.V, w ∈ Θ ∧ w ∉ A := by
    rcases hcount with ⟨s, hs, hsub⟩ | hlt
    · obtain ⟨Θ', hΘ', hsΘ, u, v, huv, hset, -⟩ := Frame.side_on_cuff hS Φ hs.1
      obtain ⟨x, hx⟩ : s.Nonempty := hs.1.1
      have hxb : x ∈ bd S := cuff_subset_bd ⟨Θ', hΘ'⟩ (hsΘ hx)
      have hxΘ := hcuff hxb (hsub hx)
      have hsame : Θ' = Θ := cuffs_eq_of_mem hΘ' hΘ (hsΘ hx) hxΘ
      subst hsame
      have hsA : s ⊆ Θ' \ A := fun y hy ↦ ⟨hsΘ hy, (hiff y (hsΘ hy)).1 (hsub hy)⟩
      have hu : u ∈ closure s ∩ (Φ.V ∩ Θ') := by rw [hset]; exact Or.inl rfl
      have := closure_minimal hsA hcl hu.1
      exact ⟨u, hu.2.1, hu.2.2, this.2⟩
    · obtain ⟨w, hw⟩ : (Φ.V ∩ In).Nonempty := by
        by_contra hne
        rw [not_nonempty_iff_eq_empty] at hne
        rw [hne] at hlt
        simp at hlt
      have hwb := Φ.V_subset hw.1
      have hwΘ := hcuff hwb hw.2
      exact ⟨w, hw.1, hwΘ, (hiff w hwΘ).1 hw.2⟩
  refine ⟨fun s hs ↦ ?_, hcount⟩
  obtain ⟨Θ', hΘ', hsΘ, -⟩ := Frame.side_on_cuff hS Φ hs.1
  have hspc : IsPathConnected s := hs.1.2.2.1
  by_cases hsame : Θ' = Θ
  · subst hsame
    have heq : s \ In = s ∩ A := by
      ext x
      constructor
      · rintro ⟨h₁, h₂⟩
        by_contra h₃
        exact h₂ ((hiff x (hsΘ h₁)).2 fun h ↦ h₃ ⟨h₁, h⟩)
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁, fun h ↦ (hiff x (hsΘ h₁)).1 h h₂⟩
    rw [heq]
    refine oArc_inter_isPathConnected hO hwΘ (fun y hy ↦ ⟨hsΘ hy, ?_⟩) (fun y hy ↦ ⟨hAΘ hy,
      ?_⟩) hspc.isConnected.isPreconnected hApc
    · rintro rfl
      exact (hs.1.2.1 hy).2 hwV
    · rintro rfl
      exact hwA hy
  · have heq : s \ In = s := sdiff_eq_left.2 (disjoint_left.2 fun x hx ↦ hoff hΘ' hsame (hsΘ hx))
    rw [heq]
    exact Or.inr hspc

variable {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}

theorem closure_compl_eq_compl_discInt {T : Type} [TopologicalSpace T]
  (hT : IsClosedSurface T) {Δ : Set T} (hΔ : IsClosedDisc Δ) :
    closure Δᶜ = (discInt Δ)ᶜ := by
  have hman : ∀ x : T, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  ext x
  constructor
  · intro hx hi
    obtain ⟨w, hw, hwi⟩ := _root_.mem_closure_iff.1 hx _ (hΔ.isOpen_discInt hman) hi
    exact hwi (discInt_subset Δ hw)
  · intro hx
    by_cases hxΔ : x ∈ Δ
    · exact discBd_subset_closure_compl hT hΔ (by
        by_contra hb
        exact hx ⟨hxΔ, hb⟩)
    · exact subset_closure hxΔ

/-- What the proof of (10.5) needs of a freedom flaw. -/
structure IsFreeData (D : TangleDatum cap χ) (n : ℕ) (Δ Z : Set Shat) (K : Drawing S) : Prop where
  shape : IsFreeShape cap χ.Φ K Z
  disc : IsClosedDisc Δ
  int_eq : cap.emb ⁻¹' discInt Z = cap.emb ⁻¹' discInt Δ
  family : IsLinkedFamily D (n + 1) (discPairs cap {Δ})
  feature : IsFeature χ.Φ K
  inter : D.P.Γ.U ∩ K.U ⊆ D.P.Γ.V ∩ K.V
  lines : ∀ e ∈ arcComponentsIn (K.U \ K.V), ∃ u v, u ≠ v ∧ closure e ∩ K.V = {u, v}
    ∧ IsLineWithEnds (closure e) u v
  size : K.V.ncard + K.E.ncard ≤ 8 * n
  pieces : ∃ 𝓞 𝓛 : Set (Set S), 𝓞.Finite ∧ 𝓛.Finite ∧ (∀ C ∈ 𝓞, IsOArc C) ∧
    (∀ L ∈ 𝓛, ∃ s t, s ≠ t ∧ IsLineWithEnds L s t ∧ s ∈ bd S ∪ ⋃₀ 𝓞 ∧ t ∈ bd S ∪ ⋃₀ 𝓞) ∧ K.U
      = ⋃₀ 𝓞 ∪ ⋃₀ 𝓛
  roots : ∀ v ∈ D.P.Γ.V, cap.emb v ∈ Δ → cap.emb v ∈ closure Δᶜ → v ∈ K.U
  outer : ∀ v ∈ K.U, cap.emb v ∈ closure Δᶜ
  anchored : IsAnchored D.P.Γ K

/-- All the places over one equivalence class of features are one well-behaved set, as in the proof
of (10.4). -/
theorem exists_class_free (hS : IsSurface S) (hd : χ.IsDisjoint)
    {𝒮 : Set (ColouredPainting χ)} (hcl : IsPaintingClass χ 𝒮) (n : ℕ) (a₀ : β)
      (hS3 : ConditionS3 χ cap) (hS4 : ConditionS4 χ) {Kc : Drawing S}
    (hg : ∃ (D : TangleDatum cap χ) (Δ Z : Set Shat), IsFreeData D n Δ Z Kc) :
    ∃ B : Set (Place χ), IsWellBehavedPlaces B ∧ ∀ D : TangleDatum cap χ, D.P ∈ 𝒮 → n + 1 ≤ D.ord →
      ∀ (Δ Z : Set Shat) (K : Drawing S) (α : S ≃ₜ S), IsFreeData D n Δ Z K
        → IsFramePreservingHomeo χ.Φ α →
      α '' Kc.U = K.U → α '' Kc.V = K.V →
      ∃ L : RootedLocation D.P.Γ, L.Isolates D.tb (n + 1) D.ord D.𝒯 ∧ (⟨hd, D.P, L⟩ : Place χ) ∈ B
        := by
  classical
  have : ConnectedSpace S := χ.connected
  have hT := cap.isClosedSurface
  obtain ⟨D₀, Δ₀, Z₀, hp⟩ := hg
  have hKne : Kc.V ⊆ ⋃ e ∈ arcComponentsIn (Kc.U \ Kc.V), closure e := fun v hv ↦ by
    obtain ⟨e, he, hve⟩ := hp.feature.no_isolated_vertices v hv
    exact mem_biUnion he hve.1
  obtain ⟨𝓞, 𝓛, h𝓞, h𝓛, hO, hL, hU⟩ := hp.pieces
  obtain ⟨Y, tY, t2Y, ψ, hY, hψ, hsheet, -⟩ := exists_pullData_of_shape hS D₀.P.fits hp.inter
    hp.lines hKne h𝓞 h𝓛 hO hL hU
  obtain ⟨B, hB, hmem⟩ := exists_class_cut (χ := χ) (K := Kc) hY (ψ := ψ) 2
    (FreeGood χ.Φ Kc Shat ψ) (fun X ↦ X.P ∈ 𝒮)
    (fun y l h ↦ by
      rcases h.2.2 with h₃ | ⟨h₁, h₂, h₄, h₅⟩
      · exact wellBehaved_S3 hS hp.feature hcl hp.lines hY hψ hsheet y l 2 a₀ hS3 h.1 h₃ h.2.1
      · exact wellBehaved_S4 hS hp.feature hcl hp.lines hY hψ hsheet y l 2 a₀ hS4 h₁ h₂ h₄ h₅ h.2.1)
  refine ⟨_, theorem_9_4_proof hB, ?_⟩
  rintro D hmem𝒮 hord Δ Z K α hK hα hαU hαV
  obtain ⟨y, hy, hgood⟩ := free_fragment hS (cap.ofHomeo α) (hK.shape.ofHomeo α hα hαU hαV) hY hψ
  have hfin : (Kc.V ∩ α ⁻¹' D.P.Γ.V).Finite := Kc.finite_V.subset inter_subset_left
  let Q : ColouredPainting χ := D.P.image α.symm hα.symm
  have hQ : IsColouredImage α.symm D.P Q := ColouredPainting.isImage_image _ _ _
  have I : IsColouredImage α Q D.P := hQ.symm
  have hclΔ := closure_compl_eq_compl_discInt hT hK.disc
  have hrange : range (fun x : connectedComponent y ↦ ψ x.1) = α ⁻¹' ⋂ p ∈ discPairs cap {Δ},
    Prod.snd p := by
    have : range (fun x : connectedComponent y ↦ ψ x.1) = ψ '' connectedComponent y := by
      ext z
      simp
    rw [this, hy, iInter_discPairs]
    ext x
    have hint : cap.emb (α x) ∈ discInt Z ↔ cap.emb (α x) ∈ discInt Δ := by
      have := Set.ext_iff.1 hK.int_eq (α x)
      simpa using this
    simp only [mem_compl_iff, mem_iInter, mem_singleton_iff, forall_eq, mem_preimage, hclΔ]
    exact not_congr hint
  have hinter : Q.Γ.U ∩ Kc.U ⊆ Q.Γ.V ∩ Kc.V := by
    rintro x ⟨hx₁, hx₂⟩
    rw [hQ.U] at hx₁
    obtain ⟨y', hy', rfl⟩ := hx₁
    have hyK : y' ∈ K.U := by
      rw [← hαU]
      exact ⟨_, hx₂, α.apply_symm_apply y'⟩
    obtain ⟨h₁, h₂⟩ := hK.inter ⟨hy', hyK⟩
    refine ⟨?_, ?_⟩
    · rw [hQ.V]
      exact mem_image_of_mem _ h₁
    · rw [← hαV] at h₂
      obtain ⟨z, hz, rfl⟩ := h₂
      rwa [α.symm_apply_apply]
  have hl : ∀ v, v ∈ hfin.toFinset.toList ↔ v ∈ Kc.V ∩ Q.Γ.V := fun v ↦ by
    rw [Finset.mem_toList, hfin.mem_toFinset, hQ.V]
    refine ⟨fun h ↦ ⟨h.1, _, h.2, α.symm_apply_apply v⟩, ?_⟩
    rintro ⟨h₁, u, hu, rfl⟩
    exact ⟨h₁, by simpa using hu⟩
  have hr : ∀ v, v ∈ Kc.U → v ∈ range (fun x : connectedComponent y ↦ ψ x.1) := fun v hv ↦ by
    rw [hrange]
    have hvK : α v ∈ K.U := hαU ▸ mem_image_of_mem _ hv
    rw [mem_preimage, iInter_discPairs]
    exact mem_iInter₂.2 fun Δ' hΔ' ↦ (mem_singleton_iff.1 hΔ') ▸ hK.outer _ hvK
  have hπ : ∀ p ∈ discPairs cap {Δ}, ∀ v ∈ D.P.Γ.V, v ∈ p.1 → v ∈ p.2 → α.symm v ∈ Kc.U := by
    rintro _ ⟨Δ', hΔ', rfl⟩ v hv h₁ h₂
    obtain rfl := mem_singleton_iff.1 hΔ'
    have := hK.roots v hv h₁ h₂
    rw [← hαU] at this
    obtain ⟨z, hz, rfl⟩ := this
    rwa [α.symm_apply_apply]
  have hm : (discPairs cap {Δ}).ncard ≤ 2 := le_trans (ncard_image_le (finite_singleton _))
    (by simp)
  have hanc : IsAnchored Q.Γ Kc := hK.anchored.image hαU I.V
  obtain ⟨X, hXP, hX, hXim⟩ := hK.family.exists_place (K := Kc) hd hα I hrange hinter hanc hl hr hπ
    hm
  have hX𝒮 : X.P ∈ 𝒮 := hXP ▸ hcl.image_mem _ hmem𝒮 _ _ hα.symm hQ
  refine ⟨hK.family.location, hK.family.isolates hS (by omega) hord, X,
    hmem y _ X hgood ?_ hX hX𝒮, α, hXim⟩
  exact fun v hv ↦ ((hl v).1 hv).1

end GraphMinor.GM19

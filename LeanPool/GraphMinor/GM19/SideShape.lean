/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FreeShape
public import LeanPool.GraphMinor.GM19.SideScheme

/-!
# The fragment outside a side flaw

`IsSideShape cap Φ side K Z` says what the proof of (11.1) needs of the closed disc `Z`. It holds
one cuff disc and misses the others, so the fragment outside `Z` has as many cuffs as `Σ`
(`le_numCuffs_fragment`). So it is a copy of `Σ` on which `ψ` is one to one (`outer_fragment`).
Unlike (10.5), this case needs no use of `S₃`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]


/-- The closed disc `Z` around a flaw on a side. -/
structure IsSideShape (cap : IsCappedSurface S Shat) (Φ : Frame S) (side : Set S) (K : Drawing S)
  (Z : Set Shat) : Prop where
  disc : IsClosedDisc Z
  sub : cap.emb '' K.U ⊆ discBd Z
  rest : discBd Z ⊆ cap.discs ∪ cap.emb '' K.U
  cuff : ∃ Θ ∈ cuffs S, closure (cap.cuffDisc Θ) ⊆ Z ∧ ∀ Θ' ∈ cuffs S, Θ' ≠ Θ → Disjoint (closure
    (cap.cuffDisc Θ')) Z
  ne : K.U.Nonempty
  keep : ∀ s ∈ Φ.longSides, s ≠ side → s \ (cap.emb ⁻¹' discInt Z ∪ K.U) = ∅ ∨ IsPathConnected (s \
    (cap.emb ⁻¹' discInt Z ∪ K.U))

/-- What makes a fragment good for (11.1). -/
def OuterGood {Y : Type} [TopologicalSpace Y] (Φ : Frame S) (side : Set S) (K : Drawing S) (ψ : Y
  → S) (c : Set Y) : Prop :=
  (IsOrientableSurface c → IsOrientableSurface S) ∧ Nonempty (c ≃ₜ S) ∧ InjOn ψ c ∧
    ∀ s ∈ Φ.longSides, s ≠ side → (s ∩ (ψ '' c)) \ K.U = ∅ ∨ IsPathConnected ((s ∩ (ψ '' c)) \ K.U)

/-- **The fragment keeps its cuffs.** If `K` meets only the cuff `Θ₀`, and the fragment holds all
the other cuffs and a point of `K`, then it has as many cuffs as `Σ`: the
other cuffs lift, and the point of `K` lies on one more. -/
theorem le_numCuffs_fragment {Y : Type} [TopologicalSpace Y]
  (hS : IsSurface S) {K : Drawing S} {ψ : Y → S} (hY : IsSurface Y) (hψ : IsCutMap ψ K.U) (y : Y)
    {Θ₀ : Set S} (hΘ₀ : Θ₀ ∈ cuffs S) (hoth : ∀ Θ' ∈ cuffs S, Θ' ≠ Θ₀ → Disjoint Θ' K.U)
      (hmem : ∀ Θ' ∈ cuffs S, Θ' ≠ Θ₀ → Θ' ⊆ ψ '' connectedComponent y) {p : S} (hp : p ∈ K.U)
    (hpm : p ∈ ψ '' connectedComponent y) : numCuffs S ≤ numCuffs (connectedComponent y) := by
  classical
  have hfrag := isCuttingFragment_of_cut hS hY hψ (K := K) rfl y
  have hfc : (cuffs S).Finite := (cuff_statement S hS).2.1
  have hfc' : (cuffs (connectedComponent y)).Finite := (cuff_statement _ hfrag.isSurface).2.1
  have : Nonempty (connectedComponent y) := ⟨⟨y, mem_connectedComponent⟩⟩
  let ψ' : connectedComponent y → S := fun x ↦ ψ x.1
  have hbdc : ∀ x : connectedComponent y, ψ' x ∈ bd S ∪ K.U → x ∈ bd (connectedComponent y)
    := fun x hx ↦ by
    by_contra hn
    exact disjoint_left.1 hfrag.maps_interior_disjoint (mem_image_of_mem _ hn) hx
  have hlift : ∀ {z}, z ∈ ψ '' connectedComponent y → ∃ x : connectedComponent y, ψ' x = z := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  set A := cuffs S \ {Θ₀} with hA
  have hex : ∀ Θ', ∃ x : connectedComponent y, Θ' ∈ A → ψ' x ∈ Θ' := fun Θ' ↦ by
    by_cases h : Θ' ∈ A
    · obtain ⟨z, hzb, hzc⟩ := h.1
      have hz : z ∈ Θ' := hzc ▸ mem_connectedComponentIn hzb
      obtain ⟨x, hx⟩ := hlift (hmem Θ' h.1 h.2 hz)
      exact ⟨x, fun _ ↦ hx ▸ hz⟩
    · exact ⟨Classical.arbitrary _, fun h' ↦ absurd h' h⟩
  choose l hl using hex
  obtain ⟨p', hp'⟩ := hlift hpm
  have hpb : p' ∈ bd (connectedComponent y) := hbdc p' (Or.inr (hp' ▸ hp))
  let G : Set S → Set (connectedComponent y) := fun Θ' ↦ connectedComponentIn (bd
    (connectedComponent y)) (l Θ')
  let H : Set (connectedComponent y) := connectedComponentIn (bd (connectedComponent y)) p'
  have hbl : ∀ {Θ'}, Θ' ∈ A → l Θ' ∈ bd (connectedComponent y) := fun h ↦ hbdc _ (Or.inl
    (cuff_subset_bd ⟨_, h.1⟩ (hl _ h)))
  have hstay : ∀ {Θ'}, Θ' ∈ A → ψ' '' G Θ' ⊆ Θ' := by
    intro Θ' hΘ'
    have hcΘ : IsClosed Θ' := isClosed_cuff hS ⟨Θ', hΘ'.1⟩
    have hrest : IsClosed (⋃₀ (cuffs S \ {Θ'}) ∪ K.U) := by
      refine IsClosed.union ((hfc.subset sdiff_subset).isClosed_sUnion fun D hD ↦ isClosed_cuff hS
        ⟨D, hD.1⟩) K.isClosed_U
    have hconn : IsPreconnected (ψ' '' G Θ') := isPreconnected_connectedComponentIn.image _
      hfrag.continuous_ψ.continuousOn
    have hcov : ψ' '' G Θ' ⊆ Θ' ∪ (⋃₀ (cuffs S \ {Θ'}) ∪ K.U) := by
      rintro _ ⟨x, hx, rfl⟩
      have hxb : x ∈ bd (connectedComponent y) := connectedComponentIn_subset _ _ hx
      rcases hfrag.maps_bd (mem_image_of_mem _ hxb) with h | h
      · rw [← sUnion_cuffs (S := S)] at h
        obtain ⟨D, hD, hxD⟩ := h
        by_cases he : D = Θ'
        · exact Or.inl (he ▸ hxD)
        · exact Or.inr (Or.inl ⟨D, ⟨hD, he⟩, hxD⟩)
      · exact Or.inr (Or.inr h)
    have hnone : ψ' '' G Θ' ∩ (Θ' ∩ (⋃₀ (cuffs S \ {Θ'}) ∪ K.U)) = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro x ⟨-, hx, h | h⟩
      · obtain ⟨D, hD, hxD⟩ := h
        exact hD.2 (cuffs_eq_of_mem hD.1 hΘ'.1 hxD hx)
      · exact disjoint_left.1 (hoth Θ' hΘ'.1 hΘ'.2) hx h
    rcases isPreconnected_iff_subset_of_disjoint_closed.1 hconn _ _ hcΘ hrest hcov hnone with h | h
    · exact h
    · exfalso
      have hm : ψ' (l Θ') ∈ ψ' '' G Θ' := mem_image_of_mem _ (mem_connectedComponentIn (hbl hΘ'))
      rcases h hm with ⟨D, hD, hxD⟩ | h'
      · exact hD.2 (cuffs_eq_of_mem hD.1 hΘ'.1 hxD (hl _ hΘ'))
      · exact disjoint_left.1 (hoth Θ' hΘ'.1 hΘ'.2) (hl _ hΘ') h'
  have hinj : InjOn G A := by
    intro Θ₁ h₁ Θ₂ h₂ he
    have hm : l Θ₁ ∈ G Θ₂ := he ▸ mem_connectedComponentIn (hbl h₁)
    exact cuffs_eq_of_mem h₁.1 h₂.1 (hl _ h₁) (hstay h₂ (mem_image_of_mem _ hm))
  have hGc : ∀ {Θ'}, Θ' ∈ A → G Θ' ∈ cuffs (connectedComponent y) := fun h ↦ ⟨_, hbl h, rfl⟩
  have hHc : H ∈ cuffs (connectedComponent y) := ⟨_, hpb, rfl⟩
  have hHn : H ∉ G '' A := by
    rintro ⟨Θ', h, he⟩
    have hm : p' ∈ G Θ' := he ▸ mem_connectedComponentIn hpb
    have := hstay h (mem_image_of_mem _ hm)
    rw [hp'] at this
    exact disjoint_left.1 (hoth Θ' h.1 h.2) this hp
  have hsub : insert H (G '' A) ⊆ cuffs (connectedComponent y) := by
    rintro _ (rfl | ⟨Θ', h, rfl⟩)
    · exact hHc
    · exact hGc h
  have h₁ := ncard_le_ncard hsub hfc'
  rw [ncard_insert_of_notMem hHn ((hfc.subset sdiff_subset).image _), hinj.ncard_image] at h₁
  have h₂ := ncard_sdiff_add_ncard_of_subset (singleton_subset_iff.2 hΘ₀) hfc
  rw [ncard_singleton, ← hA] at h₂
  change (cuffs S).ncard ≤ (cuffs (connectedComponent y)).ncard
  omega

/-- **The fragment outside `Z`.** -/
theorem outer_fragment {Y : Type} [TopologicalSpace Y] [T2Space Y] [ConnectedSpace S]
  (hS : IsSurface S) (cap : IsCappedSurface S Shat)
    {Φ : Frame S} {side : Set S} {K : Drawing S} {Z : Set Shat} (h : IsSideShape cap Φ side K Z) {ψ
      : Y → S} (hY : IsSurface Y) (hψ : IsCutMap ψ K.U) :
    ∃ y : Y, ψ '' connectedComponent y = (cap.emb ⁻¹' discInt Z)ᶜ ∧ OuterGood Φ side K ψ
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
  obtain ⟨Θ₁, hΘ₁, hin, hdis⟩ := h.cuff
  have htouch : ∀ Θ ∈ cuffs S, ¬ closure (cap.cuffDisc Θ) ⊆ Z → (closure
    (cap.cuffDisc Θ) ∩ Z).Subsingleton := fun Θ hΘ hn ↦ by
    have hne : Θ ≠ Θ₁ := fun he ↦ hn (he ▸ hin)
    rw [disjoint_iff_inter_eq_empty.1 (hdis Θ hΘ hne)]
    exact subsingleton_empty
  obtain ⟨y, hy, hcap, hnum, T', _, e, P, hT', ⟨hom⟩, hP, hs, ht⟩ := exists_outer_fragment_core hS
    cap hY hψ hD.isClosed
    (hD.isOpen_discInt hman) (discInt_subset Z) (fun c hc ↦ isCell_disc hT
      (isClosedDisc_image_injOn hD c.continuous.continuousOn hc).1)
    (h.sub.trans (Surface.discBd_subset Z)) (hbd.trans h.rest) (hbd.trans
      (discBd_subset_closure_compl hT hD)) htouch
  have hy' : ψ '' connectedComponent y = (cap.emb ⁻¹' discInt Z)ᶜ := by rw [hy, preimage_compl]
  refine ⟨y, hy', fun ⟨ω⟩ ↦ ?_, ?_⟩
  · have : T2Space T' := hT'.2.1
    have : ConnectedSpace Shat := cap.connected
    have : ConnectedSpace T' := hom.symm.surjective.connectedSpace hom.symm.continuous
    have h₁ := isOrientable_of_inside hT' hP e hs ht (ω.isPartial _)
    exact isOrientable_of_embedding cap.isEmbedding (isOrientable_of_embedding hom.symm.isEmbedding
      h₁)
  have hall : ∀ Θ ∈ cuffs S, closure (cap.cuffDisc Θ) ⊆ Z ∨ Disjoint (closure (cap.cuffDisc Θ)) Z
    := fun Θ hΘ ↦ by
    by_cases hne : Θ = Θ₁
    · exact Or.inl (hne ▸ hin)
    · exact Or.inr (hdis Θ hΘ hne)
  have hnotin : ∀ {x}, x ∈ K.U → cap.emb x ∉ discInt Z := fun hx hi ↦ hi.2 (h.sub
    (mem_image_of_mem _ hx))
  obtain ⟨p, hp⟩ := h.ne
  have hfrag := isCuttingFragment_of_cut hS hY hψ (K := K) rfl y
  have hconn := hfrag.connected
  obtain ⟨Shat₁, _, ⟨cap₁⟩⟩ := exists_cappedSurface _ (connectedComponent y) hfrag.isSurface hconn
    rfl
  have hle : numCuffs S ≤ numCuffs (connectedComponent y) := by
    refine le_numCuffs_fragment hS hY hψ y hΘ₁ (fun Θ' hΘ' hne ↦ disjoint_left.2 fun x hx hxK ↦ ?_)
      (fun Θ' hΘ' hne x hx ↦ ?_) hp (by rw [hy']; exact hnotin hp)
    · exact disjoint_left.1 (hdis Θ' hΘ' hne) (cap.mem_closure_emb hΘ' hx)
        (Surface.discBd_subset _ (h.sub (mem_image_of_mem _ hxK)))
    · rw [hy']
      exact fun hi ↦ disjoint_left.1 (hdis Θ' hΘ' hne) (cap.mem_closure_emb hΘ' hx)
        (discInt_subset _ hi)
  have hcard : numCuffs (connectedComponent y) = numCuffs S := by
    refine le_antisymm ?_ hle
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
  have hset : ∀ s : Set S, (s ∩ (ψ '' connectedComponent y)) \ K.U = s \
    (cap.emb ⁻¹' discInt Z ∪ K.U) := fun s ↦ by
    rw [hy']
    ext x
    simp only [mem_sdiff, mem_inter_iff, mem_compl_iff, mem_union, not_or]
    tauto
  refine ⟨nonempty_homeomorph_of_cap hfrag.isSurface hconn hS ‹_› cap₁ cap (hcap _ cap₁) hcard,
    ?_, ?_⟩
  · refine injOn_of_outside hS cap hY hψ y hD h.sub h.rest hall ?_
    rw [hy']
  · intro s hs' hne
    rw [hset]
    exact h.keep s hs' hne

omit [T2Space S] [T2Space Shat] in
/-- The shape moves to the cap twisted by a homeomorphism that keeps the frame. -/
theorem IsSideShape.ofHomeo {cap : IsCappedSurface S Shat} {Φ : Frame S} {side : Set
  S} {K K' : Drawing S} {Z : Set Shat}
    (h : IsSideShape cap Φ side K' Z) (f : S ≃ₜ S) (hf : IsFramePreservingHomeo Φ f) (hU : f '' K.U
      = K'.U) :
    IsSideShape (cap.ofHomeo f) Φ side K Z := by
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
  · obtain ⟨Θ, hΘ, hin, hdis⟩ := h.cuff
    refine ⟨_, (hc' hΘ).1, by rw [(hc' hΘ).2]; exact hin, fun Θ' hΘ' hne ↦ ?_⟩
    rw [(hc hΘ').2]
    refine hdis _ (hc hΘ').1 fun he ↦ hne ?_
    rw [← he]
    ext x
    simp
  · have : K'.U.Nonempty := h.ne
    rw [← hU] at this
    exact this.of_image
  · intro s hs hne
    set In' := cap.emb ⁻¹' discInt Z ∪ K'.U with hIn'
    have hmem : ∀ x, x ∈ (cap.ofHomeo f).emb ⁻¹' discInt Z ∪ K.U ↔ f x ∈ In' := fun x ↦ by
      refine or_congr Iff.rfl ?_
      rw [← hU]
      exact (f.injective.mem_set_image).symm
    have hside : ∀ x, f x ∈ s ↔ x ∈ s := fun x ↦ by
      have := hf.preserve_sides s hs.1
      constructor
      · intro hx
        rw [← this] at hx
        obtain ⟨y, hy, he⟩ := hx
        exact f.injective he ▸ hy
      · intro hx
        rw [← this]
        exact mem_image_of_mem _ hx
    have heq : s \ ((cap.ofHomeo f).emb ⁻¹' discInt Z ∪ K.U) = f.symm '' (s \ In') := by
      ext x
      simp only [mem_sdiff, hmem]
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨f x, ⟨(hside x).2 h₁, h₂⟩, f.symm_apply_apply x⟩
      · rintro ⟨y, ⟨h₁, h₂⟩, rfl⟩
        refine ⟨?_, by rwa [f.apply_symm_apply]⟩
        rw [← hside, f.apply_symm_apply]
        exact h₁
    rw [heq]
    rcases h.keep s hs hne with h' | h'
    · left
      rw [h', image_empty]
    · exact Or.inr (h'.image f.symm.continuous)

end GraphMinor.GM19

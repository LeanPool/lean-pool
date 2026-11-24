/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FragmentForm
public import LeanPool.GraphMinor.GM12.Section3PuncturedModel
public import LeanPool.GraphMinor.GM12.Section3BoundaryEquality
public import LeanPool.GraphMinor.Surface.CutIArc
public import LeanPool.GraphMinor.Surface.ModelCriterion
public import LeanPool.GraphMinor.GM19.CapModel
public import LeanPool.GraphMinor.GM19.Section5o

/-!
# Two discs joined by a line

Let `D₁` and `D₂` be disjoint closed discs of a closed connected surface `T`, joined by a line `L`.
Then `D₁ ∪ L ∪ D₂` is cellular: `T` without
this set is a surface homeomorphic to `T`, without a point (`isCell_bridge`). We remove the insides
of the two discs. Then `L` is a proper arc with ends in different cuffs. Cutting along it gives a
connected surface with one cuff, and with the same genus (`cutIArc`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Metric Filter GraphMinor.Surface GraphMinor.GM12

variable {T : Type} [TopologicalSpace T] [T2Space T] [ConnectedSpace T]

private theorem cut_model_interior_image_is_open
    {T : Type}
    [TopologicalSpace T]
    [T2Space T]
    {D₁ : Set T}
    {D₂ : Set T}
    (h₁ : IsClosedDisc D₁)
    (h₂ : IsClosedDisc D₂)
    (Δ : Bool → Set T)
    (hZout : (D₁ ∪ D₂)ᶜ ⊆ discComplement Δ)
    (hZin : ∀ {x : T}, x ∈ discComplement Δ → x ∉ discBd D₁ → x ∉ discBd D₂ → x ∉ D₁ ∪ D₂)
    (hbdZ : ∀ (z : ↑(discComplement Δ)), z ∈ bd ↑(discComplement Δ) ↔ ↑z ∈ discBd D₁ ∨ ↑z ∈ discBd
      D₂)
    (a₁ : ℕ)
    (b₁ : ℕ)
    [CompactSpace (SurfaceModel a₁ b₁ 1)]
    (ψ' : SurfaceModel a₁ b₁ 1 → ↑(discComplement Δ))
    (F : Set (discComplement Δ)) (hψ' : IsCutMap ψ' F)
    (hsoff : ∀ w ∉ bd (SurfaceModel a₁ b₁ 1), ψ' w ∉ F ∧ ψ' w ∉ bd
      ↑(discComplement Δ)) :
    ∀ u ⊆ (bd (SurfaceModel a₁ b₁ 1))ᶜ, IsOpen u →
      IsOpen ((fun w => ((ψ' w : discComplement Δ) : T)) '' u) := by
  intro u hu huo
  have hop : IsOpen (ψ' '' u) := isOpen_image_of_isCutMap hψ' (fun w hw ↦ (hsoff w (hu hw)).1) huo
  obtain ⟨O, hO, hOe⟩ := isOpen_induced_iff.1 hop
  have hset : (fun w ↦ (ψ' w).1) '' u = O ∩ (D₁ ∪ D₂)ᶜ := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hin : ψ' w ∈ ψ' '' u := mem_image_of_mem _ hw
      rw [← hOe] at hin
      have hb' := (hsoff w (hu hw)).2
      rw [hbdZ, not_or] at hb'
      exact ⟨hin, hZin (ψ' w).2 hb'.1 hb'.2⟩
    · rintro ⟨hxO, hxn⟩
      have hin : (⟨x, hZout hxn⟩ : discComplement Δ) ∈ ψ' '' u := by
        rw [← hOe]
        exact hxO
      obtain ⟨w, hw, he⟩ := hin
      exact ⟨w, hw, congrArg Subtype.val he⟩
  rw [hset]
  exact hO.inter (h₁.isClosed.union h₂.isClosed).isOpen_compl

private theorem cut_model_interior_image_is_bridge_complement
    {T : Type}
    [TopologicalSpace T]
    [T2Space T]
    {D₁ : Set T}
    {D₂ : Set T}
    {L : Set T}
    (Δ : Bool → Set T)
    (hZout : (D₁ ∪ D₂)ᶜ ⊆ discComplement Δ)
    (hZin : ∀ {x : T}, x ∈ discComplement Δ → x ∉ discBd D₁ → x ∉ discBd D₂ → x ∉ D₁ ∪ D₂)
    (hbdZ : ∀ (z : ↑(discComplement Δ)), z ∈ bd ↑(discComplement Δ) ↔ ↑z ∈ discBd D₁ ∨ ↑z ∈ discBd
      D₂)
    (hFc : IsClosed ((Subtype.val : discComplement Δ → T) ⁻¹' L))
    (a₁ : ℕ)
    (b₁ : ℕ)
    [this : CompactSpace (SurfaceModel a₁ b₁ 1)]
    (ψ' : SurfaceModel a₁ b₁ 1 → ↑(discComplement Δ))
    (hψ' : IsCutMap ψ' ((Subtype.val : discComplement Δ → T) ⁻¹' L))
    (hsoff : ∀ w ∉ bd (SurfaceModel a₁ b₁ 1), ψ' w ∉ ((Subtype.val : discComplement Δ → T) ⁻¹' L) ∧
      ψ' w ∉ bd
      ↑(discComplement Δ)) :
    (fun w => ↑(ψ' w)) '' (bd (SurfaceModel a₁ b₁ 1))ᶜ = (D₁ ∪ L ∪ D₂)ᶜ := by
  let F := (Subtype.val : discComplement Δ → T) ⁻¹' L
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨hnF, hnb⟩ := hsoff w hw
    rw [hbdZ, not_or] at hnb
    have h₃ := hZin (ψ' w).2 hnb.1 hnb.2
    rintro ((h | h) | h)
    · exact h₃ (Or.inl h)
    · exact hnF h
    · exact h₃ (Or.inr h)
  · intro hx
    have hx₁ : x ∉ D₁ ∪ D₂ := by
      rintro (h | h)
      · exact hx (Or.inl (Or.inl h))
      · exact hx (Or.inr h)
    have hxL : x ∉ L := fun h ↦ hx (Or.inl (Or.inr h))
    obtain ⟨w, hw⟩ := hψ'.2.1 ⟨x, hZout hx₁⟩
    refine ⟨w, fun hb' ↦ ?_, congrArg Subtype.val hw⟩
    have hnF : ψ' w ∉ F := fun h ↦ hxL (by rw [hw] at h; exact h)
    have := bd_of_bd_cutMap hψ' hFc hb' hnF
    rw [hbdZ, hw] at this
    rcases this with h | h
    · exact hx₁ (Or.inl (Surface.discBd_subset _ h))
    · exact hx₁ (Or.inr (Surface.discBd_subset _ h))

theorem isCell_bridge (hT : IsClosedSurface T) {D₁ D₂ L : Set T} (h₁ : IsClosedDisc D₁)
  (h₂ : IsClosedDisc D₂) (hd : Disjoint D₁ D₂)
    {a b : T} (ha : a ∈ discBd D₁) (hb : b ∈ discBd D₂) (hl : IsLineWithEnds L a b) (hL₁ : L ∩ D₁
      = {a}) (hL₂ : L ∩ D₂ = {b}) :
    IsCell T (D₁ ∪ L ∪ D₂) := by
  classical
  have : CompactSpace T := hT.1
  have hman : ∀ x : T, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  let Δ : Bool → Set T := fun i ↦ if i then D₁ else D₂
  have hΔ : ∀ i, IsClosedDisc (Δ i) := fun i ↦ by cases i <;> simpa [Δ]
  have hdisj : Pairwise fun i j ↦ Disjoint (Δ i) (Δ j) := by
    intro i j hij
    cases i <;> cases j <;> simp_all [Δ, disjoint_comm]
  have hZs := discComplement_isSurface hT Δ hΔ hdisj
  have hZc : ConnectedSpace (discComplement Δ) := Subtype.connectedSpace
    (discComplement_isConnected hT Δ hΔ hdisj)
  obtain ⟨a₀, b₀, c₀, ⟨e₀⟩⟩ := classification T hT.isSurface inferInstance
  have hc₀ : c₀ = 0 := by
    have := numCuffs_eq e₀
    rw [numCuffs_model] at this
    have hb : bd T = ∅ := eq_empty_of_forall_notMem fun x hx ↦ hx (hT.2.2 x)
    rw [← this, numCuffs, cuffs, hb]
    simp [componentsIn]
  subst hc₀
  obtain ⟨e₁⟩ := discComplement_model_of_closed_model hT Δ hΔ hdisj e₀
  have hZcl : IsClosed (discComplement Δ) := isClosed_closure
  have hun : (⋃ i, Δ i) = D₁ ∪ D₂ := by
    ext x
    simp [Δ, or_comm]
  have hZout : (D₁ ∪ D₂)ᶜ ⊆ discComplement Δ := by
    intro x hx
    apply subset_closure
    rwa [hun]
  have hZin : ∀ {x}, x ∈ discComplement Δ → x ∉ discBd D₁ → x ∉ discBd D₂ → x ∉ D₁ ∪ D₂ := by
    have key : ∀ {x D}, IsClosedDisc D → D ⊆ D₁ ∪ D₂ → x ∈ discComplement Δ → x ∉ discBd D → x ∉ D
      := by
      intro x D hD hsub hx hb hxD
      obtain ⟨w, hw, hwn⟩ := _root_.mem_closure_iff.1 hx _ (hD.isOpen_discInt hman) ⟨hxD, hb⟩
      apply hwn
      rw [hun]
      exact hsub (discInt_subset D hw)
    rintro x hx hb₁ hb₂ (h | h)
    · exact key h₁ subset_union_left hx hb₁ h
    · exact key h₂ subset_union_right hx hb₂ h
  have hbdZ : ∀ z : discComplement Δ, z ∈ bd (discComplement Δ) ↔ z.1 ∈ discBd D₁ ∨ z.1 ∈ discBd D₂
    := by
    intro z
    rw [discComplement_boundary_eq hT Δ hΔ]
    simp [Δ, or_comm]
  have hb₁Z : discBd D₁ ⊆ discComplement Δ := disc_boundary_subset_discComplement hT Δ hΔ hdisj true
  have hb₂Z : discBd D₂ ⊆ discComplement Δ := disc_boundary_subset_discComplement hT Δ hΔ hdisj
    false
  have ha₁ : a ∈ D₁ := Surface.discBd_subset _ ha
  have hb₂ : b ∈ D₂ := Surface.discBd_subset _ hb
  have hLZ : L ⊆ discComplement Δ := by
    intro x hx
    by_cases hx₁ : x ∈ D₁
    · have : x ∈ L ∩ D₁ := ⟨hx, hx₁⟩
      rw [hL₁] at this
      rw [mem_singleton_iff.1 this]
      exact hb₁Z ha
    by_cases hx₂ : x ∈ D₂
    · have : x ∈ L ∩ D₂ := ⟨hx, hx₂⟩
      rw [hL₂] at this
      rw [mem_singleton_iff.1 this]
      exact hb₂Z hb
    · exact hZout (by simp [hx₁, hx₂])
  have hLc : IsClosed L := by
    obtain ⟨f, -, -⟩ := hl
    have : L = range fun t ↦ (f t).1 := by
      ext x
      constructor
      · intro hx
        exact ⟨f.symm ⟨x, hx⟩, by simp⟩
      · rintro ⟨t, rfl⟩
        exact (f t).2
    rw [this]
    exact (isCompact_range (continuous_subtype_val.comp f.continuous)).isClosed
  have hLa : a ∈ L := by
    have : a ∈ L ∩ D₁ := by rw [hL₁]; rfl
    exact this.1
  have hLb : b ∈ L := by
    have : b ∈ L ∩ D₂ := by rw [hL₂]; rfl
    exact this.1
  let a' : discComplement Δ := ⟨a, hLZ hLa⟩
  let b' : discComplement Δ := ⟨b, hLZ hLb⟩
  set F : Set (discComplement Δ) := Subtype.val ⁻¹' L with hF
  have hFc : IsClosed F := hLc.preimage continuous_subtype_val
  have hab : a ≠ b := fun h ↦ disjoint_left.1 hd ha₁ (h ▸ hb₂)
  have hne : a' ≠ b' := fun h ↦ hab (congrArg Subtype.val h)
  have hline : IsLineWithEnds F a' b' := by
    refine isLine_comap (j := Subtype.val) hZcl.isClosedEmbedding_subtypeVal ?_
    have : (Subtype.val : discComplement Δ → T) '' F = L := by
      rw [hF, Subtype.image_preimage_coe]
      exact inter_eq_right.2 hLZ
    rw [this]
    exact hl
  have hFbd : F ∩ bd (discComplement Δ) = {a', b'} := by
    ext z
    constructor
    · rintro ⟨hz, hzb⟩
      rcases (hbdZ z).1 hzb with h | h
      · have : z.1 ∈ L ∩ D₁ := ⟨hz, Surface.discBd_subset _ h⟩
        rw [hL₁] at this
        exact Or.inl (Subtype.ext this)
      · have : z.1 ∈ L ∩ D₂ := ⟨hz, Surface.discBd_subset _ h⟩
        rw [hL₂] at this
        exact Or.inr (Subtype.ext this)
    · rintro (rfl | h)
      · exact ⟨hLa, (hbdZ _).2 (Or.inl ha)⟩
      · rw [mem_singleton_iff.1 h]
        exact ⟨hLb, (hbdZ _).2 (Or.inr hb)⟩
  have ha'b : a' ∈ bd (discComplement Δ) := (hbdZ _).2 (Or.inl ha)
  have hb'b : b' ∈ bd (discComplement Δ) := (hbdZ _).2 (Or.inr hb)
  have hcuffs : connectedComponentIn (bd (discComplement Δ)) a' ≠ connectedComponentIn (bd
    (discComplement Δ)) b' := by
    intro he
    have hmem : connectedComponentIn (bd (discComplement Δ)) a' ∈ cuffs (discComplement Δ)
      := mem_image_of_mem _ ha'b
    rw [discComplement_cuffs_eq hT Δ hΔ hdisj] at hmem
    obtain ⟨i, hi⟩ := hmem
    have h₁' : a ∈ discBd (Δ i) := by
      have : a' ∈ (Subtype.val : discComplement Δ → T) ⁻¹' discBd (Δ i) := by
        have hi' := hi
        simp only at hi'
        rw [hi']
        exact mem_connectedComponentIn ha'b
      exact this
    have h₂' : b ∈ discBd (Δ i) := by
      have : b' ∈ (Subtype.val : discComplement Δ → T) ⁻¹' discBd (Δ i) := by
        have hi' := hi
        simp only at hi'
        rw [hi', he]
        exact mem_connectedComponentIn hb'b
      exact this
    cases i
    · exact disjoint_left.1 hd ha₁ (Surface.discBd_subset _ (by simpa [Δ] using h₁'))
    · exact disjoint_left.1 hd (Surface.discBd_subset _ (by simpa [Δ] using h₂')) hb₂
  obtain ⟨S', tS', ψ, hS', hcut, hdiff, -, -⟩ := cutIArc _ F a' b' hZs hZc hne hFbd hline
  obtain ⟨hS'c, a₁, b₁, c₁, ⟨e₂⟩, ⟨e₃⟩⟩ := hdiff hcuffs
  obtain ⟨hc, h2, hb0⟩ := (modelCriterion.2 _ _ _ _ _ _).1 ⟨e₂.symm.trans e₁⟩
  have hc₁ : c₁ = 1 := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_bool] at hc
    omega
  subst hc₁
  obtain ⟨f⟩ := (modelCriterion.2 a₁ b₁ 0 a₀ b₀ 0).2 ⟨rfl, h2, hb0⟩
  obtain ⟨cap⟩ := nonempty_capped_model a₁ b₁ 1
  have hW : IsSurface (SurfaceModel a₁ b₁ 1) := (modelCriterion.1 a₁ b₁ 1).1
  have : T2Space (SurfaceModel a₁ b₁ 1) := (presents_ew a₁ b₁ 1).1
  have : ConnectedSpace (SurfaceModel a₁ b₁ 1) := (modelCriterion.1 a₁ b₁ 1).2
  have : CompactSpace (SurfaceModel a₁ b₁ 1) := hW.1
  obtain ⟨e₄, Q, hQ, hs₄, ht₄, hn⟩ := exists_cap_chart hW cap
  rw [numCuffs_model] at hn
  have hψc : IsCutMap ψ F := IsCutting.isCutMap hcut
  let ψ' : SurfaceModel a₁ b₁ 1 → discComplement Δ := ψ ∘ e₃.symm
  have hψ' : IsCutMap ψ' F := by
    refine ⟨hψc.1.comp e₃.symm.continuous, hψc.2.1.comp e₃.symm.surjective, ?_, ?_, ?_⟩
    · intro x hx y hy hxy
      exact e₃.symm.injective (hψc.2.2.1 hx hy hxy)
    · intro x
      have : ψ' ⁻¹' {x} = e₃ '' (ψ ⁻¹' {x}) := by
        ext w
        constructor
        · intro hw
          exact ⟨e₃.symm w, hw, e₃.apply_symm_apply w⟩
        · rintro ⟨u, hu, rfl⟩
          simpa [ψ'] using hu
      rw [this]
      exact (hψc.2.2.2.1 x).image _
    · intro w hw
      have h := hψc.2.2.2.2 hw
      have : e₃ (e₃.symm w) ∈ e₃ '' bd S' := mem_image_of_mem _ h
      rw [e₃.apply_symm_apply, image_bd_homeomorph] at this
      exact this
  have hcZ : CompactSpace (discComplement Δ) := isCompact_iff_compactSpace.1 hZcl.isCompact
  have hbW : IsClosed (bd (SurfaceModel a₁ b₁ 1)) := (cuff_statement _ hW).1
  have hsoff : ∀ w, w ∉ bd (SurfaceModel a₁ b₁ 1) → ψ' w ∉ F ∧ ψ' w ∉ bd (discComplement Δ) := by
    intro w hw
    have hnF : ψ' w ∉ F := fun h ↦ hw (hψ'.2.2.2.2 h)
    have hint : IsInteriorPoint w := by
      by_contra h
      exact hw h
    exact ⟨hnF, fun h ↦ h (isInteriorPoint_image hψ' hFc hint hnF)⟩
  have hinjS : InjOn ψ' (bd (SurfaceModel a₁ b₁ 1))ᶜ := hψ'.2.2.1.mono fun w hw ↦ (hsoff w hw).1
  have hopen : ∀ u ⊆ (bd (SurfaceModel a₁ b₁ 1))ᶜ, IsOpen u → IsOpen ((fun w ↦ (ψ' w).1) '' u) := by
    exact cut_model_interior_image_is_open (T := T) (D₁ := D₁) (D₂ := D₂) h₁ h₂ Δ hZout hZin hbdZ
      a₁ b₁ ψ' F hψ' hsoff
  have himg : (fun w ↦ (ψ' w).1) '' (bd (SurfaceModel a₁ b₁ 1))ᶜ = (D₁ ∪ L ∪ D₂)ᶜ := by
    exact cut_model_interior_image_is_bridge_complement (T := T) (D₁ := D₁) (D₂ := D₂) (L := L) Δ
      hZout hZin hbdZ hFc a₁ b₁ ψ' hψ' hsoff
  obtain ⟨e₅, hs₅, ht₅, hf₅⟩ := exists_oph (f := fun w ↦ (ψ' w).1) (s := (bd
    (SurfaceModel a₁ b₁ 1))ᶜ)
    (t := (D₁ ∪ L ∪ D₂)ᶜ) hbW.isOpen_compl (continuous_subtype_val.comp hψ'.1).continuousOn
    (fun x hx y hy hxy ↦ hinjS hx hy (Subtype.ext hxy)) hopen himg
  refine ⟨SurfaceModel a₁ b₁ 0, inferInstance, e₅.symm.trans' e₄ (by simp [hs₅, hs₄]), Q,
    cap.isClosedSurface,
    ⟨f.trans e₀.symm⟩, hQ, hn.le, ?_, ?_⟩
  · simp [ht₅]
  · simp [ht₄]

end GraphMinor.GM19

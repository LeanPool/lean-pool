/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.RadialExists
public import LeanPool.GraphMinor.Surface.PasteDisc

/-!
# The capped surface exists

Graph Minors XIX, Section 2 (page 327): "The surface obtained from $\Sigma$ by “pasting” a disc onto
each
cuff we denote by $\hat{\Sigma}$." We paste the discs one cuff at a time, using
`Surface.paste_disc`, and show
that the result is an `IsCappedSurface`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Function Topology GraphMinor.Surface

universe u

variable {S T : Type u} [TopologicalSpace S] [TopologicalSpace T]

theorem image_connectedComponentIn_of_isEmbedding {ι : S → T} (hι : IsEmbedding ι) {F : Set S}
    {y : S} (hy : y ∈ F) : ι '' connectedComponentIn F y = connectedComponentIn (ι '' F) (ι y) := by
  apply Subset.antisymm
  · refine (isPreconnected_connectedComponentIn.image ι hι.continuous.continuousOn
      |>.subset_connectedComponentIn (mem_image_of_mem _ (mem_connectedComponentIn hy))
      (image_mono (connectedComponentIn_subset _ _)))
  · set D := connectedComponentIn (ι '' F) (ι y) with hD
    have hDsub : D ⊆ ι '' F := connectedComponentIn_subset _ _
    have hDr : ι '' (ι ⁻¹' D) = D :=
      image_preimage_eq_of_subset (hDsub.trans (image_subset_range _ _))
    have hpre : IsPreconnected (ι ⁻¹' D) := by
      rw [← hι.isInducing.isPreconnected_image, hDr]
      exact isPreconnected_connectedComponentIn
    have hsub : ι ⁻¹' D ⊆ F := fun x hx ↦ by
      obtain ⟨z, hz, hzx⟩ := hDsub hx
      exact hι.injective hzx ▸ hz
    have hyD : y ∈ ι ⁻¹' D := mem_connectedComponentIn (mem_image_of_mem _ hy)
    rw [← hDr]
    exact image_mono (hpre.subset_connectedComponentIn hyD hsub)

theorem connectedComponentIn_bd_diff {C : Set S} (hC : C ∈ cuffs S) {y : S} (hy : y ∈ bd S \ C) :
    connectedComponentIn (bd S \ C) y = connectedComponentIn (bd S) y := by
  obtain ⟨z, hz, rfl⟩ := hC
  apply Subset.antisymm (connectedComponentIn_mono _ sdiff_subset)
  refine isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (mem_connectedComponentIn hy.1) fun w hw ↦ ⟨connectedComponentIn_subset _ _ hw, fun hw' ↦ ?_⟩
  apply hy.2
  rw [(connectedComponentIn_eq hw').trans (connectedComponentIn_eq hw).symm]
  exact mem_connectedComponentIn hy.1

/-- The cuffs after pasting a disc onto the cuff `C`. -/
theorem cuffs_paste {C : Set S} (hC : C ∈ cuffs S) {ι : S → T} (hι : IsEmbedding ι)
    (hbd : bd T = ι '' (bd S \ C)) : cuffs T = (fun Θ ↦ ι '' Θ) '' (cuffs S \ {C}) := by
  ext D
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [hbd] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨connectedComponentIn (bd S) y, ⟨⟨y, hy.1, rfl⟩, fun h ↦ ?_⟩, ?_⟩
    · exact hy.2 (by rw [← mem_singleton_iff.1 h]; exact mem_connectedComponentIn hy.1)
    · change ι '' _ = _
      rw [← connectedComponentIn_bd_diff hC hy, image_connectedComponentIn_of_isEmbedding hι hy]
  · rintro ⟨_, ⟨⟨y, hy, rfl⟩, hne⟩, rfl⟩
    have hyC : y ∉ C := fun h ↦ hne (by
      obtain ⟨z, hz, rfl⟩ := hC
      exact mem_singleton_iff.2 (connectedComponentIn_eq h).symm)
    refine ⟨ι y, hbd ▸ mem_image_of_mem _ ⟨hy, hyC⟩, ?_⟩
    change connectedComponentIn (bd T) (ι y) = ι '' _
    have hyd : y ∈ bd S \ C := ⟨hy, hyC⟩
    rw [hbd, ← connectedComponentIn_bd_diff hC hyd, image_connectedComponentIn_of_isEmbedding hι
      hyd]

theorem cuffs_disjoint {Θ₁ Θ₂ : Set S} (h₁ : Θ₁ ∈ cuffs S) (h₂ : Θ₂ ∈ cuffs S) (hne : Θ₁ ≠ Θ₂) :
    Disjoint Θ₁ Θ₂ := by
  obtain ⟨a, -, rfl⟩ := h₁
  obtain ⟨b, -, rfl⟩ := h₂
  refine disjoint_left.2 fun x ha hb ↦ hne ?_
  exact (connectedComponentIn_eq ha).trans (connectedComponentIn_eq hb).symm

/-- One step: a capping of the surface with the cuff `C` filled is a capping of the surface. -/
theorem nonempty_capped_of_paste {Shat : Type u} [TopologicalSpace Shat] (_hS : IsSurface S)
    (hT : IsSurface T) {C : Set S} (hC : C ∈ cuffs S) {ι : S → T} (hι : IsClosedEmbedding ι)
    {Δ : Set T} (hΔ : IsClosedDisc Δ) (hcov : range ι ∪ Δ = univ) (hinter : range ι ∩ Δ = ι '' C)
    (hΔb : discBd Δ = ι '' C) (hbd : bd T = ι '' (bd S \ C)) (cap' : IsCappedSurface T Shat) :
    Nonempty (IsCappedSurface S Shat) := by
  classical
  have hsurf := cap'.isSurface
  have : T2Space Shat := hsurf.2.1
  have : T2Space T := hT.2.1
  have : CompactSpace T := hT.1
  set j := cap'.emb with hj
  have hjc : IsClosedEmbedding j :=
    IsClosedEmbedding.of_continuous_injective_isClosedMap cap'.isEmbedding.continuous
      cap'.isEmbedding.injective cap'.isEmbedding.continuous.isClosedMap
  have hcuffs := cuffs_paste hC hι.isEmbedding hbd
  have hmem : ∀ Θ ∈ cuffs S, Θ ≠ C → ι '' Θ ∈ cuffs T := fun Θ hΘ hne ↦ by
    rw [hcuffs]
    exact ⟨Θ, ⟨hΘ, hne⟩, rfl⟩
  have hcl : closure (j '' discInt Δ) = j '' Δ := by
    rw [hjc.closure_image_eq]
    congr 1
    exact Subset.antisymm (closure_minimal (discInt_subset _) hΔ.isClosed) hΔ.subset_closure_discInt
  have hcap : ∀ Θ' ∈ cuffs T, ∀ x ∈ cap'.cuffDisc Θ', x ∉ range j := fun Θ' hΘ' x hx hr ↦ by
    have : x ∈ (range cap'.emb)ᶜ := by
      rw [cap'.compl_eq]
      exact mem_iUnion₂.2 ⟨Θ', hΘ', hx⟩
    exact this hr
  have hdiscint : ∀ z ∈ discInt Δ, z ∉ range ι := fun z hz hr ↦
    hz.2 (hΔb ▸ (hinter ▸ ⟨hr, hz.1⟩))
  have hdisj : ∀ Θ ∈ cuffs S, Θ ≠ C →
      Disjoint (j '' Δ) (closure (cap'.cuffDisc (ι '' Θ))) := fun Θ hΘ hne ↦ by
    refine disjoint_left.2 ?_
    rintro _ ⟨z, hz, rfl⟩ hcl'
    rw [cap'.closure_cuffDisc hT (hmem Θ hΘ hne)] at hcl'
    rcases hcl' with h | ⟨w, ⟨y, hy, rfl⟩, hw⟩
    · exact hcap _ (hmem Θ hΘ hne) _ h (mem_range_self z)
    · obtain rfl := hjc.injective hw
      have : ι y ∈ ι '' C := hinter ▸ ⟨mem_range_self y, hz⟩
      obtain ⟨y', hy', hyy⟩ := this
      obtain rfl := hι.injective hyy
      exact disjoint_left.1 (cuffs_disjoint hΘ hC hne) hy hy'
  refine ⟨{ isSurface := cap'.isSurface, connected := cap'.connected, bd_empty := cap'.bd_empty
            emb := j ∘ ι
            isEmbedding := cap'.isEmbedding.comp hι.isEmbedding
            cuffDisc := fun Θ ↦ if Θ = C then j '' discInt Δ else cap'.cuffDisc (ι '' Θ)
            cuffDisc_closedDisc := ?_, cuffDisc_bd := ?_, cuffDisc_disjoint := ?_,
            compl_eq := ?_ }⟩
  · intro Θ hΘ
    by_cases he : Θ = C
    · simp only [he, ite_true]
      rw [hcl]
      exact (isClosedDisc_image hΔ cap'.isEmbedding).1
    · simp only [he, ite_false]
      exact cap'.cuffDisc_closedDisc _ (hmem Θ hΘ he)
  · intro Θ hΘ
    by_cases he : Θ = C
    · simp only [he, ite_true]
      rw [hcl, (isClosedDisc_image hΔ cap'.isEmbedding).2, hΔb, image_image]
      rfl
    · simp only [he, ite_false]
      rw [cap'.cuffDisc_bd _ (hmem Θ hΘ he), image_image]
      rfl
  · intro Θ₁ hΘ₁ Θ₂ hΘ₂ hne
    by_cases h₁ : Θ₁ = C
    · have h₂ : Θ₂ ≠ C := fun h ↦ hne (h₁.trans h.symm)
      simp only [h₁, h₂, ite_true, ite_false]
      rw [hcl]
      exact hdisj Θ₂ hΘ₂ h₂
    · by_cases h₂ : Θ₂ = C
      · simp only [h₁, h₂, ite_true, ite_false]
        rw [hcl]
        exact (hdisj Θ₁ hΘ₁ h₁).symm
      · simp only [h₁, h₂, ite_false]
        exact cap'.cuffDisc_disjoint _ (hmem Θ₁ hΘ₁ h₁) _ (hmem Θ₂ hΘ₂ h₂)
          fun h ↦ hne (image_injective.2 hι.injective h)
  · ext w
    simp only [mem_compl_iff, mem_iUnion₂, exists_prop]
    constructor
    · intro hw
      by_cases hwr : w ∈ range j
      · obtain ⟨z, rfl⟩ := hwr
        have hzr : z ∉ range ι := fun ⟨y, hy⟩ ↦ hw ⟨y, by simp [hy]⟩
        have hzΔ : z ∈ Δ := by
          have : z ∈ range ι ∪ Δ := hcov ▸ mem_univ z
          exact this.resolve_left hzr
        refine ⟨C, hC, ?_⟩
        rw [ite_eq_left rfl]
        refine mem_image_of_mem _ ⟨hzΔ, fun hb ↦ hzr ?_⟩
        rw [hΔb] at hb
        obtain ⟨y, -, rfl⟩ := hb
        exact mem_range_self y
      · have hmem' : w ∈ ⋃ Θ ∈ cuffs T, cap'.cuffDisc Θ := by
          rw [← cap'.compl_eq]
          exact hwr
        obtain ⟨Θ', hΘ', hwΘ⟩ := mem_iUnion₂.1 hmem'
        rw [hcuffs] at hΘ'
        obtain ⟨Θ, ⟨hΘ, hne⟩, rfl⟩ := hΘ'
        refine ⟨Θ, hΘ, ?_⟩
        rw [ite_eq_right (show Θ ≠ C from hne)]
        exact hwΘ
    · rintro ⟨Θ, hΘ, hw⟩ ⟨y, rfl⟩
      by_cases he : Θ = C
      · rw [ite_eq_left he] at hw
        obtain ⟨z, hz, hzy⟩ := hw
        obtain rfl := hjc.injective hzy
        exact hdiscint _ hz (mem_range_self y)
      · rw [ite_eq_right he] at hw
        exact hcap _ (hmem Θ hΘ he) _ hw (mem_range_self _)

/-- **Every connected surface has a capped surface** (Graph Minors XIX, Section 2, page 327). -/
theorem exists_cappedSurface : ∀ (n : ℕ) (S : Type u) [TopologicalSpace S], IsSurface S →
    ConnectedSpace S → (cuffs S).ncard = n →
    ∃ (Shat : Type u) (_ : TopologicalSpace Shat), Nonempty (IsCappedSurface S Shat) := by
  intro n
  induction n with
  | zero =>
    intro S _ hS hconn hn
    obtain ⟨-, hfin, -⟩ := cuff_statement.{u} S hS
    have hempty : cuffs S = ∅ := (ncard_eq_zero hfin).1 hn
    have hbd : bd S = ∅ := by
      refine eq_empty_of_forall_notMem fun y hy ↦ ?_
      have : connectedComponentIn (bd S) y ∈ cuffs S := ⟨y, hy, rfl⟩
      rw [hempty] at this
      exact this
    refine ⟨S, inferInstance, ⟨{ isSurface := hS, connected := hconn, bd_empty := hbd, emb := id
                                 isEmbedding := IsEmbedding.id, cuffDisc := fun _ ↦ ∅
                                 cuffDisc_closedDisc := ?_, cuffDisc_bd := ?_
                                 cuffDisc_disjoint := ?_, compl_eq := ?_ }⟩⟩
    · intro Θ hΘ
      rw [hempty] at hΘ
      exact absurd hΘ (notMem_empty _)
    · intro Θ hΘ
      rw [hempty] at hΘ
      exact absurd hΘ (notMem_empty _)
    · intro Θ hΘ
      rw [hempty] at hΘ
      exact absurd hΘ (notMem_empty _)
    · simp
  | succ n ih =>
    intro S _ hS hconn hn
    obtain ⟨-, hfin, -⟩ := cuff_statement.{u} S hS
    have hne : (cuffs S).Nonempty := by
      rw [← ncard_pos hfin, hn]
      omega
    obtain ⟨C, hC⟩ := hne
    obtain ⟨T, _, ι, Δ, hT, hι, hΔ, hcov, hinter, hΔb, hbd⟩ := paste_disc.{u} S C hS hC
    have : T2Space T := hT.2.1
    have hTconn : ConnectedSpace T := by
      refine connectedSpace_iff_univ.2 ?_
      rw [← hcov]
      have h₁ : IsConnected (range ι) := isConnected_range hι.continuous
      have h₂ : IsConnected Δ := (IsClosedDisc.isPathConnected hΔ).isConnected
      refine h₁.union ?_ h₂
      obtain ⟨c, hc, rfl⟩ := id hC
      exact ⟨ι c, hinter ▸ mem_image_of_mem _ (mem_connectedComponentIn hc)⟩
    have hcount : (cuffs T).ncard = n := by
      rw [cuffs_paste hC hι.isEmbedding hbd,
        ncard_image_of_injective _ (image_injective.2 hι.injective), ncard_sdiff_singleton_of_mem
          hC, hn]
      rfl
    obtain ⟨Shat, _, ⟨cap'⟩⟩ := ih T hT hTconn hcount
    exact ⟨Shat, inferInstance, nonempty_capped_of_paste hS hT hC hι hΔ hcov hinter hΔb hbd cap'⟩

end GraphMinor.GM19

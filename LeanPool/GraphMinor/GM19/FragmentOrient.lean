/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FragmentExtend
public import LeanPool.GraphMinor.GM19.CapModel

/-!
# Orientations of fragments

We prove the orientation steps of Graph Minors XIX. Let `W` be a connected surface whose inside is a
closed surface `T'` without a finite
set. An orientation of the inside of `W` gives one of `T'` (`extend_orientation`). If `T'` caps `W`,
this gives one of `W`.

So a fragment of an oriented surface is orientable. By `sameOn_const` an orientation of the fragment
is equal on its inside to the
orientation read through `ψ`, or reverse to it, and we reverse it in the second case
(`fragmentOrientation`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Metric Filter GraphMinor.Surface

variable {W T' : Type} [TopologicalSpace W] [T2Space W] [TopologicalSpace T'] [T2Space T']

/-- An orientation with all discs as domain is an orientation. -/
def orientationOfPartial {X : Type} [TopologicalSpace X] {pos : Set X → X → X → X
  → Prop}
    (h : IsPartialOrientation univ pos) : SurfaceOrientation X :=
  ⟨pos, fun Δ hΔ ↦ h.dir Δ (mem_univ _) hΔ, fun Δ₁ Δ₂ h₁ h₂ ↦ h.agree Δ₁ (mem_univ _) Δ₂
    (mem_univ _) h₁ h₂⟩

theorem isOrientable_of_inside [ConnectedSpace T'] (hT : IsClosedSurface T') {P : Set T'}
  (hP : P.Finite) (e : OpenPartialHomeomorph W T')
    (hs : e.source = (bd W)ᶜ) (ht : e.target = Pᶜ) {pos : Set W → W → W → W → Prop}
      (hpos : IsPartialOrientation {Δ | Δ ⊆ (bd W)ᶜ} pos) :
    IsOrientableSurface T' := by
  have hs' : ∀ Δ ∈ {Δ : Set T' | Δ ⊆ Pᶜ}, ContinuousOn e.symm Δ ∧ InjOn e.symm Δ
    ∧ e.symm '' Δ ∈ {Δ | Δ ⊆ (bd W)ᶜ} := by
    intro Δ hΔ
    have hΔ' : Δ ⊆ e.target := ht ▸ hΔ
    refine ⟨e.continuousOn_symm.mono hΔ', e.symm.injOn.mono hΔ', ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have := e.map_target (hΔ' hx)
    rwa [hs] at this
  obtain ⟨ω, -⟩ := extend_orientation hT hP (hpos.pull hs')
  exact ⟨ω⟩

/-- A surface whose inside is oriented is orientable. -/
theorem isOrientable_of_interior (hW : IsSurface W) [ConnectedSpace W] {pos : Set W → W → W → W
  → Prop}
    (hpos : IsPartialOrientation {Δ | Δ ⊆ (bd W)ᶜ} pos) : IsOrientableSurface W := by
  obtain ⟨T, _, ⟨cap⟩⟩ := exists_cappedSurface _ W hW inferInstance rfl
  have : T2Space T := cap.isSurface.2.1
  have : ConnectedSpace T := cap.connected
  obtain ⟨x⟩ : Nonempty W := inferInstance
  have : Nonempty W := ⟨x⟩
  obtain ⟨e, P, hP, hs, ht, -⟩ := exists_cap_chart hW cap
  exact isOrientable_of_embedding cap.isEmbedding (isOrientable_of_inside cap.isClosedSurface hP e
    hs ht hpos)

/-- **The step of the proof of (5.4)**, Graph Minors XIX, page 338: a fragment takes its orientation
from the surface. -/
theorem fragmentOrientation : FragmentOrientationStatement := by
  intro S S₁ _ _ _ _ K ψ hS hc hf ω
  have hS₁ := hf.isSurface
  have := hf.connected
  have hman : ∀ x : S₁, IsManifoldPoint x := hS₁.2.2
  have hψ := hf.continuous_ψ
  let 𝓙 : Set (Set S₁) := {Δ | InjOn ψ Δ}
  have hJ : IsPartialOrientation 𝓙 (pullPos ψ ω.pos) :=
    (ω.isPartial univ).pull fun Δ hΔ ↦ ⟨hψ.continuousOn, hΔ, mem_univ _⟩
  have hhered : ∀ Δ ∈ 𝓙, ∀ Δ' ⊆ Δ, Δ' ∈ 𝓙 := fun Δ hΔ Δ' hs ↦ InjOn.mono hs hΔ
  have hIJ : {Δ | Δ ⊆ (bd S₁)ᶜ} ⊆ 𝓙 := fun Δ hΔ ↦ hf.injOn_interior.mono hΔ
  have hIopen : IsOpen (bd S₁)ᶜ := (cuff_statement S₁ hS₁).1.isOpen_compl
  have hIc := isConnected_interior hS₁
  have hIint : ∀ x ∈ (bd S₁)ᶜ, IsInteriorPoint x := fun x hx ↦ by
    by_contra h
    exact hx h
  obtain ⟨ω₂⟩ := isOrientable_of_interior hS₁ (hJ.mono hIJ)
  obtain ⟨x₀, hx₀⟩ := hIc.nonempty
  obtain ⟨E, hE, -, hEs⟩ := exists_small_disc (hIint x₀ hx₀) hIopen hx₀
  have hdir₂ := (ω₂.isPartial 𝓙).dir E (hIJ hEs) hE
  have hdirJ := hJ.dir E (hIJ hEs) hE
  obtain ⟨pos₁, hpos₁, hE₁⟩ : ∃ pos₁, IsPartialOrientation univ pos₁ ∧ SameOn pos₁
    (pullPos ψ ω.pos) E := by
    by_cases hs : SameOn ω₂.pos (pullPos ψ ω.pos) E
    · exact ⟨ω₂.pos, ω₂.isPartial univ, hs⟩
    · exact ⟨revPos ω₂.pos, (ω₂.isPartial univ).rev, sameOn_rev_left (sameOn_of_notSame hdir₂ hdirJ
      hs)⟩
  refine ⟨orientationOfPartial hpos₁, fun Δ hΔ hinj a b c ha hb hc hab hbc hac ↦ ?_⟩
  have hP : IsPartialOrientation 𝓙 pos₁ := hpos₁.mono (subset_univ _)
  obtain ⟨y, hyI, hyΔ⟩ := (dense_interior' hS₁).inter_open_nonempty _
    (hΔ.isOpen_discInt hman) hΔ.nonempty_discInt
  have hyI' : y ∈ (bd S₁)ᶜ := hyΔ
  obtain ⟨D, hD, -, hDs⟩ := exists_small_disc (hIint y hyI') (hIopen.inter
    (hΔ.isOpen_discInt hman)) ⟨hyI', hyI⟩
  have hDI : D ⊆ (bd S₁)ᶜ := hDs.trans inter_subset_left
  have hDΔ : D ⊆ Δ := hDs.trans (inter_subset_right.trans (discInt_subset Δ))
  have hG : SameOn pos₁ (pullPos ψ ω.pos) D :=
    (sameOn_const hman hIopen hIc.isPreconnected hIint (hP.mono hIJ) (hJ.mono hIJ) hE hD hEs hDI).1
      hE₁
  exact (sameOn_of_subset hman hhered hP hJ hinj hD hΔ hDΔ).1 hG a b c ha hb hc hab hbc hac

/-- **The steps of the proof of (10.4)**, Graph Minors XIX, page 357. -/
theorem outerSide : OuterSideStatement := by
  intro S Shat _ _ _ _ cap K 𝓓 hS hshape Y _ _ ψ hY hψ
  obtain ⟨y, hy, hcap, hnum, T', _, e, P, hT', ⟨hom⟩, hP, hs, ht⟩ := outer_shape (ψ
    := ψ) hS cap hY hψ hshape
  refine ⟨y, hy, hcap, hnum, fun ⟨ω⟩ ↦ ?_⟩
  have : T2Space T' := hT'.2.1
  have : ConnectedSpace Shat := cap.connected
  have : ConnectedSpace T' := hom.symm.surjective.connectedSpace hom.symm.continuous
  have h₁ := isOrientable_of_inside hT' hP e hs ht (ω.isPartial _)
  exact isOrientable_of_embedding cap.isEmbedding (isOrientable_of_embedding hom.symm.isEmbedding
    h₁)

end GraphMinor.GM19

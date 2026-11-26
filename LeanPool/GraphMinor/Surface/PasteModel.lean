/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CutOArc

/-!
# Pasting a disc on a cuff removes one cuff

We show that pasting a disc on a cuff of `Σ(a, b, c)` gives `Σ(a, b, c - 1)` (`paste_model`). The
surface and the disc side by side are
the result of cutting the new surface along the old cuff, so the words of cut surfaces apply.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology

universe u v

/-- A boundary point stays a boundary point under an open embedding. -/
theorem bd_of_isOpenEmbedding {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {e : X → Y} (he : IsOpenEmbedding e) {x : X}
    (hx : x ∈ bd X) : e x ∈ bd Y := by
  intro hint
  obtain ⟨U, hU, hxU, hsub, ⟨f⟩⟩ := hint.exists_subset he.isOpen_range (mem_range_self x)
  have h1 : e '' (e ⁻¹' U) = U := image_preimage_eq_of_subset hsub
  exact hx ⟨e ⁻¹' U, hU.preimage he.continuous, hxU, ⟨(he.isEmbedding.homeomorphImage _).trans
    ((Homeomorph.setCongr h1).trans f)⟩⟩

/-- Two surfaces pasted along one cuff of each: the models add up, and both cuffs are gone. -/
theorem glue_model {S S' : Type u} [TopologicalSpace S] [TopologicalSpace S']
  (hS : IsSurface S) {C : Set S} (hC : IsCuff C) {ι : S → S'} {Δ : Set S'}
    (hΔS : IsSurface Δ) (hS' : T2Space S') (hι : IsClosedEmbedding ι) (hu : range ι ∪ Δ = univ)
      (hm : range ι ∩ Δ = ι '' C) (hOF : IsOArc (ι '' C))
    (hBb : Subtype.val ⁻¹' (ι '' C) ⊆ bd Δ) {a b c a₂ b₂ c₂ : ℕ} (e : S ≃ₜ SurfaceModel a b c)
      (d' : Δ ≃ₜ SurfaceModel a₂ b₂ c₂) :
    0 < c ∧ 0 < c₂ ∧ Nonempty (S' ≃ₜ SurfaceModel (a₂ + a) (b₂ + b) (c₂ - 1 + (c - 1))) := by
  classical
  have hcS : CompactSpace S := hS.1
  have ht2 : T2Space S := hS.2.1
  have hΔc : CompactSpace Δ := hΔS.1
  have hCb : C ⊆ bd S := by
    obtain ⟨x, -, rfl⟩ := hC
    exact connectedComponentIn_subset _ _
  let ψ : S ⊕ Δ → S' := Sum.elim ι Subtype.val
  have hψc : Continuous ψ := hι.continuous.sumElim continuous_subtype_val
  have hF : ∀ x ∈ ι '' C, x ∈ Δ := fun x hx => (hm ▸ hx : x ∈ range ι ∩ Δ).2
  let B : Set Δ := Subtype.val ⁻¹' (ι '' C)
  have hY : IsSurface (S ⊕ Δ) := ⟨inferInstance, inferInstance, fun x => by
    rcases x with x | x
    · exact isManifoldPoint_of_isOpenEmbedding IsOpenEmbedding.inl (hS.2.2 x)
    · exact isManifoldPoint_of_isOpenEmbedding IsOpenEmbedding.inr (hΔS.2.2 x)⟩
  have hpre : ψ ⁻¹' (ι '' C) = Sum.inl '' C ∪ Sum.inr '' B := by
    ext x
    rcases x with x | x
    · constructor
      · rintro ⟨y, hy, he⟩
        exact .inl ⟨y, hy, by rw [hι.injective he]⟩
      · rintro (⟨y, hy, he⟩ | ⟨y, -, he⟩)
        · rw [← Sum.inl.inj he]
          exact ⟨y, hy, rfl⟩
        · simp at he
    · constructor
      · intro h
        exact .inr ⟨x, h, rfl⟩
      · rintro (⟨y, -, he⟩ | ⟨y, hy, he⟩)
        · simp at he
        · rw [← Sum.inr.inj he]
          exact hy
  have hcut : IsCutting ψ (ι '' C) := by
    refine ⟨hψc, ?_, ?_, ?_, ?_⟩
    · intro x
      have h1 : x ∈ range ι ∪ Δ := hu ▸ mem_univ x
      rcases h1 with ⟨y, rfl⟩ | h1
      · exact ⟨.inl y, rfl⟩
      · exact ⟨.inr ⟨x, h1⟩, rfl⟩
    · rintro (x | x) hx (y | y) hy he
      · rw [hι.injective he]
      · exact absurd (hm ▸ (⟨⟨x, rfl⟩, he ▸ y.2⟩ : ψ (.inl x) ∈ range ι ∩ Δ)) hx
      · have h2 : ι y ∈ Δ := by
          have h3 : ψ (.inr x) = x.1 := rfl
          have h4 : ψ (.inl y) = ι y := rfl
          rw [← h4, ← he, h3]
          exact x.2
        exact absurd (show ι y ∈ ι '' C from hm ▸ ⟨⟨y, rfl⟩, h2⟩) hy
      · rw [Subtype.ext he]
    · rintro _ ⟨x, hx, rfl⟩
      have h1 : ψ ⁻¹' {ι x} = {.inl x, .inr ⟨ι x, hF _ ⟨x, hx, rfl⟩⟩} := by
        ext z
        rcases z with z | z
        · simp only [mem_preimage, mem_singleton_iff, mem_insert_iff, Sum.inl.injEq,
            reduceCtorEq, or_false]
          exact ⟨fun h => hι.injective h, fun h => by rw [h]; rfl⟩
        · simp only [mem_preimage, mem_singleton_iff, mem_insert_iff, Sum.inr.injEq,
            reduceCtorEq, false_or]
          exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
      rw [h1, ncard_pair (by simp)]
    · rw [hpre]
      rintro _ (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · exact bd_of_isOpenEmbedding IsOpenEmbedding.inl (hCb hx)
      · exact bd_of_isOpenEmbedding IsOpenEmbedding.inr (hBb hx)
  obtain ⟨φC⟩ := (cuff_statement.{u} S hS).2.2 C hC
  have hOX : IsOArc (Sum.inl '' C : Set (S ⊕ Δ)) := ⟨φC.trans (IsEmbedding.inl.homeomorphImage C)⟩
  have hOX' : IsOArc (Sum.inr '' B : Set (S ⊕ Δ)) := by
    obtain ⟨φF⟩ := hOF
    obtain ⟨e'⟩ := exists_homeo_sub (ι '' C) hF
    exact ⟨φF.trans (e'.symm.trans (IsEmbedding.inr.homeomorphImage B))⟩
  have b1 : BijOn ψ (Sum.inl '' C) (ι '' C) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩ he
      rw [hι.injective he]
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨.inl x, ⟨x, hx, rfl⟩, rfl⟩
  have b2 : BijOn ψ (Sum.inr '' B) (ι '' C) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hx
    · rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩ he
      rw [Subtype.ext he]
    · intro x hx
      exact ⟨.inr ⟨x, hF x hx⟩, ⟨_, hx, rfl⟩, rfl⟩
  have hW₁ : IsClopen (range (Sum.inl : S → S ⊕ Δ)) := isClopen_range_inl
  have hW₂ : IsClopen (range (Sum.inr : Δ → S ⊕ Δ)) := isClopen_range_inr
  have hd : Disjoint (range (Sum.inl : S → S ⊕ Δ)) (range (Sum.inr : Δ → S ⊕ Δ)) := by
    rw [disjoint_left]
    rintro _ ⟨x, rfl⟩ ⟨y, he⟩
    simp at he
  have hU : range (Sum.inl : S → S ⊕ Δ) ∪ range (Sum.inr : Δ → S ⊕ Δ) = univ := by
    ext x
    rcases x with x | x <;> simp
  have e₁ := IsEmbedding.inl.toHomeomorph (f := (Sum.inl : S → S ⊕ Δ)) |>.symm.trans e
  have e₂ := IsEmbedding.inr.toHomeomorph (f := (Sum.inr : Δ → S ⊕ Δ)) |>.symm.trans d'
  obtain ⟨i, j, σ, f, -, -, hi, hj, hf, -⟩ := loop_comps_aux hY hcut hpre.symm b1 b2 hOX hOX' hW₁
    hW₂ hd hU e₁ e₂ (image_subset_range _ _)
    (image_subset_range _ _) (fun x hx => hcut.2.2.2.2 (hpre ▸ .inl hx)) (fun x hx => hcut.2.2.2.2
      (hpre ▸ .inr hx))
  have hne : Nonempty S' := by
    obtain ⟨φ'⟩ := hOF
    exact ⟨(φ' 1).1⟩
  obtain ⟨hN₁, hL₁⟩ := erase_facts c i
  obtain ⟨hN₂, hL₂⟩ := erase_facts c₂ j
  obtain ⟨e'⟩ := homeo_of_two_loop hi hj hN₁ hN₂ hL₁ hL₂ hf
  rw [length_erase_range hi, length_erase_range hj] at e'
  exact ⟨by omega, by omega, ⟨e'⟩⟩

/-- Pasting a closed disc on one cuff of a surface takes one hole away from its model. -/
theorem paste_model {S S' : Type u} [TopologicalSpace S] [TopologicalSpace S']
  (hS : IsSurface S) {C : Set S} (hC : IsCuff C) {ι : S → S'} {Δ : Set S'}
    (hS' : IsSurface S') (hι : IsClosedEmbedding ι) (hΔ : IsClosedDisc Δ) (hu : range ι ∪ Δ = univ)
      (hm : range ι ∩ Δ = ι '' C) (hb : discBd Δ = ι '' C)
    {a b c : ℕ} (e : S ≃ₜ SurfaceModel a b c) : 0 < c ∧ Nonempty (S' ≃ₜ SurfaceModel a b (c - 1))
      := by
  classical
  have hcS : CompactSpace S := hS.1
  have ht2 : T2Space S := hS.2.1
  have hcS' : CompactSpace S' := hS'.1
  have ht2' : T2Space S' := hS'.2.1
  have hCb : C ⊆ bd S := by
    obtain ⟨x, -, rfl⟩ := hC
    exact connectedComponentIn_subset _ _
  have hΔc : CompactSpace Δ := by
    obtain ⟨φ⟩ := hΔ
    have : CompactSpace ClosedUnitDisc := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
    exact φ.surjective.compactSpace φ.continuous
  obtain ⟨φ⟩ := id hΔ
  obtain ⟨d⟩ := nonempty_disc_homeo
  let d' : Δ ≃ₜ SurfaceModel 0 0 1 := φ.symm.trans d.symm
  have hΔS : IsSurface Δ := ⟨hΔc, inferInstance, fun x => by
    have h1 := (isSurface_model 0 0 1).1.2.2 (d' x)
    have h2 := isManifoldPoint_of_isOpenEmbedding d'.symm.isOpenEmbedding h1
    simpa using h2⟩
  have hcS' : T2Space S' := hS'.2.1
  have hBb : Subtype.val ⁻¹' (ι '' C) ⊆ bd Δ := fun x hx => by
    have h1 : x.1 ∈ discBd Δ := hb ▸ hx
    obtain ⟨y, hy, he⟩ := h1
    exact Subtype.ext he ▸ hy
  have hOF : IsOArc (ι '' C) := hb ▸ hΔ.isOArc_discBd
  obtain ⟨h1, -, ⟨e'⟩⟩ := glue_model hS hC hΔS hcS' hι hu hm hOF hBb e d'
  rw [show 0 + a = a by omega, show 0 + b = b by omega, show 1 - 1 + (c - 1) = c - 1 by omega] at e'
  exact ⟨h1, ⟨e'⟩⟩

end GraphMinor.Surface

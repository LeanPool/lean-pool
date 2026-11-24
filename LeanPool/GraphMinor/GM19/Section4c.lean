/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Conditional
public import LeanPool.GraphMinor.GM19.Section4a
public import LeanPool.GraphMinor.GM19.Relabel
public import LeanPool.GraphMinor.GM19.Section4b
public import LeanPool.GraphMinor.Surface.ModelCriterion

/-!
# Graph Minors XIX, (3.1) assuming (4.1)

This is the proof at the end of Section 4 of the paper. We take a bad colour scheme and choose it to
satisfy `S₁`, `S₂`, `S₃`, `S₄` in turn, which contradicts (4.1).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Function Topology GraphMinor.Surface

universe u w

section Homeo

theorem IsInteriorPoint.image_homeo {S : Type u} {T : Type w} [TopologicalSpace S]
    [TopologicalSpace T] (h : S ≃ₜ T) {x : S} (hx : IsInteriorPoint x) : IsInteriorPoint (h x) := by
  obtain ⟨U, hU, hx, ⟨e⟩⟩ := hx
  exact ⟨h '' U, h.isOpenMap U hU, mem_image_of_mem h hx, ⟨(h.image U).symm.trans e⟩⟩

theorem image_bd {S : Type u} {T : Type w} [TopologicalSpace S] [TopologicalSpace T] (h : S ≃ₜ T) :
    h '' bd S = bd T := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ hy
    exact hx (by simpa using IsInteriorPoint.image_homeo h.symm hy)
  · intro hy
    refine ⟨h.symm y, fun hx ↦ hy ?_, by simp⟩
    simpa using IsInteriorPoint.image_homeo h hx

variable {S T : Type u} [TopologicalSpace S] [TopologicalSpace T]

theorem cuffs_eq_image (h : S ≃ₜ T) : cuffs T = (fun C ↦ h '' C) '' cuffs S := by
  ext C
  simp only [cuffs, componentsIn, mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← image_bd h] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨_, ⟨x, hx, rfl⟩, ?_⟩
    rw [← image_bd h]
    exact h.image_connectedComponentIn hx
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨h x, by rw [← image_bd h]; exact mem_image_of_mem h hx, ?_⟩
    rw [← image_bd h]
    exact (h.image_connectedComponentIn hx).symm

theorem numCuffs_eq (h : S ≃ₜ T) : numCuffs S = numCuffs T := by
  have hinj : Injective fun C : Set S ↦ h '' C := image_injective.2 h.injective
  rw [numCuffs, numCuffs, cuffs_eq_image h, ncard_image_of_injective _ hinj]

/-- A capping of `S` is one of each surface homeomorphic to `S`. -/
def IsCappedSurface.ofHomeo {Shat : Type u} [TopologicalSpace Shat] (h : T ≃ₜ S)
    (cap : IsCappedSurface S Shat) : IsCappedSurface T Shat where
  isSurface := cap.isSurface
  connected := cap.connected
  bd_empty := cap.bd_empty
  emb := cap.emb ∘ h
  isEmbedding := cap.isEmbedding.comp h.isEmbedding
  cuffDisc Θ := cap.cuffDisc (h '' Θ)
  cuffDisc_closedDisc Θ hΘ := cap.cuffDisc_closedDisc _ (by
    rw [cuffs_eq_image h]; exact mem_image_of_mem _ hΘ)
  cuffDisc_bd Θ hΘ := by
    rw [cap.cuffDisc_bd _ (by rw [cuffs_eq_image h]; exact mem_image_of_mem _ hΘ), image_image,
      image_comp]
    simp [image_image]
  cuffDisc_disjoint Θ₁ hΘ₁ Θ₂ hΘ₂ hne := cap.cuffDisc_disjoint _
    (by rw [cuffs_eq_image h]; exact mem_image_of_mem _ hΘ₁) _
    (by rw [cuffs_eq_image h]; exact mem_image_of_mem _ hΘ₂)
    fun he ↦ hne (image_injective.2 h.injective he)
  compl_eq := by
    rw [h.surjective.range_comp, cap.compl_eq, cuffs_eq_image h, biUnion_image]

/-- `IsSimplerThan` depends only on the homeomorphism type of its second argument. -/
theorem IsSimplerThan.of_homeo {Z : Type*} [TopologicalSpace Z] (hZ : IsSimplerThan Z S)
    (h : S ≃ₜ T) : IsSimplerThan Z T := by
  obtain ⟨a, b, c, a', b', c', h₁, ⟨h₂⟩, h₃⟩ := hZ
  exact ⟨a, b, c, a', b', c', h₁, ⟨h.symm.trans h₂⟩, h₃⟩

end Homeo

/-- A colour scheme together with its surface and a capping of this surface. -/
structure CappedScheme (β : Type w) : Type (max (u + 1) w) where
  /-- The surface `Σ_χ`. -/
  S : Type u
  /-- The surface `Σ̂_χ`. -/
  Shat : Type u
  [iS : TopologicalSpace S]
  [iH : TopologicalSpace Shat]
  /-- The capping. -/
  cap : IsCappedSurface S Shat
  /-- The colour scheme. -/
  χ : ColourScheme S β

attribute [instance] CappedScheme.iS CappedScheme.iH

/-- The pair of quasi-orders `Ω(3), Ω(2)`, in a form where only the elements matter. -/
noncomputable def CappedScheme.key {β : Type w} (D : CappedScheme.{u, w} β) :
    WQOKey β × WQOKey β :=
  (⟨D.χ.Ω3.norm, QuasiOrder.norm_isWQO D.χ.isWQO_3⟩, ⟨D.χ.Ω2.norm, QuasiOrder.norm_isWQO
    D.χ.isWQO_2⟩)

end GraphMinor.GM19

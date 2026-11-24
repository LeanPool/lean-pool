/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4QuadDiscFamilyMatch
public import LeanPool.GraphMinor.GM12.Section4EndPartition

/-!
# Transporting the source endpoint partition

For XII (4.5), claim (1), page 253, match all four-marked
crossing discs by one ambient homeomorphism. Carry the source
vertex discs and their end classes by that map. Images preserve
their disjointness and exact contact equations. On every
crossing, the two opposite endpoint pairs become the two
prescribed opposite pairs, including when the boundary order
is reversed.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Transport a feasible source endpoint partition to prescribed
four-marked discs, preserving both opposite pairs. This is the
last ambient-map step of XII (4.5), claim (1), page 253. -/
theorem exists_quad_partition_transport {S V E T : Type}
    [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite T]
    (hS : IsClosedSurface S) (A C : T → Set S) (B : V → Set S)
    (hA : ∀ i, IsClosedDisc (A i)) (hC : ∀ i, IsClosedDisc (C i))
    (hAA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hCC : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hB : ∀ w, IsClosedDisc (B w)) (hBB : Pairwise (fun w z => Disjoint (B w) (B z)))
    (p t : T → Circle → S)
    (hp : ∀ i, Continuous (p i) ∧ Function.Injective (p i) ∧ range (p i) = discBd (A i))
    (ht : ∀ i, Continuous (t i) ∧ Function.Injective (t i) ∧ range (t i) = discBd (C i))
    (σ : T × Bool ≃ E) (ends : E × Bool → S) (κ : E × Bool → V)
    (hinj : Function.Injective ends)
    (hcontact : ∀ w, B w ∩ (⋃ i, A i) = edgeEndClass ends κ w)
    (h0 : ∀ i, ({ends (σ (i, false), false), ends (σ (i, false), true)} : Set S) =
      {p i (ee 0), p i (ee (1 / 2))})
    (h1 : ∀ i, ({ends (σ (i, true), false), ends (σ (i, true), true)} : Set S) =
      {p i (ee (1 / 4)), p i (ee (3 / 4))})
    (b₀ b₁ b₂ b₃ : T → ℝ) (hb₀₁ : ∀ i, b₀ i < b₁ i) (hb₁₂ : ∀ i, b₁ i < b₂ i)
    (hb₂₃ : ∀ i, b₂ i < b₃ i) (hb₃ : ∀ i, b₃ i < b₀ i + 1) :
    ∃ (ends' : E × Bool → S) (B' : V → Set S), Function.Injective ends' ∧
      (∀ w, IsClosedDisc (B' w)) ∧ (Pairwise (fun w z => Disjoint (B' w) (B' z))) ∧
      (∀ w, B' w ∩ (⋃ i, C i) = edgeEndClass ends' κ w) ∧
      (∀ i, ({ends' (σ (i, false), false), ends' (σ (i, false), true)} : Set S) =
        {t i (ee (b₀ i)), t i (ee (b₂ i))}) ∧
      (∀ i, ({ends' (σ (i, true), false), ends' (σ (i, true), true)} : Set S) =
        {t i (ee (b₁ i)), t i (ee (b₃ i))}) := by
  obtain ⟨e, he⟩ := exists_quad_disc_family_match hS A C hA hC hAA hCC p t hp ht
    b₀ b₁ b₂ b₃ hb₀₁ hb₁₂ hb₂₃ hb₃
  let ends' := e ∘ ends
  let B' := fun w => e '' B w
  have hclass : ∀ w, e '' edgeEndClass ends κ w = edgeEndClass ends' κ w := by
    intro w
    simp only [edgeEndClass, image_image]
    rfl
  have hcover : e '' (⋃ i, A i) = ⋃ i, C i := by
    rw [image_iUnion]
    exact iUnion_congr (fun i => (he i).1)
  refine ⟨ends', B', e.injective.comp hinj, ?_, ?_, ?_, ?_, ?_⟩
  · intro w
    exact ((hB w).image e.continuous.continuousOn e.symm.continuous.continuousOn
      (fun z _ => e.symm_apply_apply z)).1
  · intro w z hwz
    exact (disjoint_image_iff e.injective).mpr (hBB hwz)
  · intro w
    change (e '' B w) ∩ (⋃ i, C i) = _
    rw [← hcover, ← image_inter e.injective, hcontact w, hclass w]
  · intro i
    have h := congrArg (fun X : Set S => e '' X) (h0 i)
    simp only [image_pair] at h
    change ({e (ends (σ (i, false), false)), e (ends (σ (i, false), true))} : Set S) = _
    rw [h]
    rcases (he i).2 with ⟨h0, _, h2, _⟩ | ⟨h0, _, h2, _⟩ <;> rw [h0, h2]
  · intro i
    have h := congrArg (fun X : Set S => e '' X) (h1 i)
    simp only [image_pair] at h
    change ({e (ends (σ (i, true), false)), e (ends (σ (i, true), true))} : Set S) = _
    rw [h]
    rcases (he i).2 with ⟨_, h1, _, h3⟩ | ⟨_, h1, _, h3⟩
    · rw [h1, h3]
    · rw [h1, h3, pair_comm]

end GraphMinor.GM12

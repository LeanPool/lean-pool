/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3MeetingSurrounding
public import LeanPool.GraphMinor.GM12.Section3SubspaceDrawing

/-!
# The meeting-loop vertex bound

Condition (iii) of XII (3.1), page 245, applies to two circles whose
enclosing discs meet once. The preceding construction supplies these
discs for circles surrounding distinct cuffs. Normality and vertex
counts transfer through the inclusion into the original surface.
-/

public section

namespace GraphMinor.GM12

open Set Surface Topology

/-- The vertex bound for two surrounding circles meeting at one
point, from condition (iii) of XII (3.1), page 245. -/
theorem meeting_loop_vertex_count_gt
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) (Γ : Drawing S) (Δ : ι → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (hcase : ¬ IsSphere S ∨ 3 ≤ Nat.card ι) (hUC : Γ.U ⊆ discComplement Δ)
    (N : ℕ)
    (hbound : ∀ A B D E : Set S,
      Γ.IsNormal (A ∪ B) → IsOArc A → IsOArc B → A ∪ B ⊆ discComplement Δ →
      IsClosedDisc D → IsClosedDisc E → discBd D = A → discBd E = B →
      (D ∩ E).ncard = 1 →
      (∃ i, ∀ l, Δ l ⊆ D ↔ l = i) → (∃ j, ∀ l, Δ l ⊆ E ↔ l = j) →
      N < (Γ.V ∩ (A ∪ B)).ncard)
    {i j : ι} (hij : i ≠ j)
    {F₁ F₂ : Set (discComplement Δ)} {u : discComplement Δ}
    (hF₁ : IsOArc F₁) (hF₂ : IsOArc F₂) (hcap : F₁ ∩ F₂ = {u})
    (hs₁ : GM07.SurroundsCuff F₁ (Subtype.val ⁻¹' discBd (Δ i)))
    (hs₂ : GM07.SurroundsCuff F₂ (Subtype.val ⁻¹' discBd (Δ j)))
    (hn : (drawingInSubspace Γ (discComplement Δ) hUC).IsNormal (F₁ ∪ F₂)) :
    N < ((drawingInSubspace Γ (discComplement Δ) hUC).V ∩ (F₁ ∪ F₂)).ncard := by
  let C := discComplement Δ
  let a : C → S := Subtype.val
  obtain ⟨D, E, hD, hE, hbD, hbE, honeD, honeE, hDE⟩ :=
    exists_meeting_surrounding_discs hS Δ hΔ hdisj hcase hij hF₁ hF₂ hcap hs₁ hs₂
  have hA : IsOArc (a '' F₁) := by
    obtain ⟨φ⟩ := hF₁
    exact ⟨φ.trans (IsEmbedding.subtypeVal.homeomorphImage F₁)⟩
  have hB : IsOArc (a '' F₂) := by
    obtain ⟨φ⟩ := hF₂
    exact ⟨φ.trans (IsEmbedding.subtypeVal.homeomorphImage F₂)⟩
  have hnormal := drawingInSubspace_isNormal_image Γ C hUC hn
  rw [image_union] at hnormal
  have hsupport : a '' F₁ ∪ a '' F₂ ⊆ C := by
    rintro x (⟨y, _, rfl⟩ | ⟨y, _, rfl⟩) <;> exact y.property
  have hmeet : (D ∩ E).ncard = 1 := by rw [hDE, ncard_singleton]
  have hbig := hbound (a '' F₁) (a '' F₂) D E hnormal hA hB hsupport
    hD hE hbD hbE hmeet ⟨i, honeD⟩ ⟨j, honeE⟩
  have hcount := congrArg Set.ncard
    (drawingInSubspace_image_vertices_inter Γ C hUC (F₁ ∪ F₂))
  rw [ncard_image_of_injective _ Subtype.val_injective, image_union] at hcount
  rw [hcount]
  exact hbig

end GraphMinor.GM12

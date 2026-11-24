/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3TwoLoopCount
public import LeanPool.GraphMinor.GM12.Section3MeetingLoopCount
public import LeanPool.GraphMinor.GM12.Section3LoopCuffClassification
import LeanPool.GraphMinor.GM12.Section3PuncturedCuffs
import LeanPool.GraphMinor.GM12.Section3PuncturedSurface

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# Vertex bounds for the schismatic two-loop shapes

Conditions (ii) and (iii) of XII (3.1), page 245, apply to the two-loop
schismatic shapes. Their distinguished loops surround distinct cuffs
by the proved Section 8 classification. Read these cuffs as prescribed
disc boundaries, then use the enclosing-disc vertex bounds. The cuff
labels are obtained by proof rather than supplied as extra hypotheses.
-/

public section

namespace GraphMinor.GM12

open Set Surface

universe u

/-- Condition (ii) of XII (3.1) bounds every normal schismatic first two-loop shape. -/
theorem two_loop_vertex_count_gt_of_schismatic
    {S : Type u} {ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
      [Nonempty ι]
    (hS : IsClosedSurface S) (Γ : Drawing S) (Δ : ι → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (hcase : ¬ IsSphere S ∨ 3 ≤ Nat.card ι) (hUC : Γ.U ⊆ discComplement Δ)
    (N : ℕ)
    (hbound : ∀ (A B P D E : Set S) (u v : S),
      Γ.IsNormal (A ∪ B ∪ P) → IsOArc A → IsOArc B → IsLineWithEnds P u v →
      u ∈ A → v ∈ B → P ∩ A = {u} → P ∩ B = {v} →
      A ∪ B ∪ P ⊆ discComplement Δ → IsClosedDisc D → IsClosedDisc E →
      discBd D = A → discBd E = B → Disjoint D E →
      (∃ i, ∀ l, Δ l ⊆ D ↔ l = i) → (∃ j, ∀ l, Δ l ⊆ E ↔ l = j) →
      N < (Γ.V ∩ (A ∪ B ∪ P)).ncard)
    {F₁ F₂ P : Set (discComplement Δ)} {u v : discComplement Δ}
    (hF₁ : IsOArc F₁) (hF₂ : IsOArc F₂) (hFF : Disjoint F₁ F₂)
    (hP : IsLineWithEnds P u v) (hu : u ∈ F₁) (hv : v ∈ F₂)
    (hP₁ : P ∩ F₁ = {u}) (hP₂ : P ∩ F₂ = {v})
    (hX : GM07.IsSchismatic (F₁ ∪ F₂ ∪ P))
    (hn : (drawingInSubspace Γ (discComplement Δ) hUC).IsNormal (F₁ ∪ F₂ ∪ P)) :
    N < ((drawingInSubspace Γ (discComplement Δ) hUC).V ∩ (F₁ ∪ F₂ ∪ P)).ncard := by
  let : ConnectedSpace (discComplement Δ) :=
    Subtype.connectedSpace (discComplement_isConnected hS Δ hΔ hdisj)
  obtain ⟨C, D, hs₁, hs₂, hCD⟩ := surrounding_cuffs_of_schismatic_x1
    (discComplement_isSurface hS Δ hΔ hdisj) (discComplement_cuffs_nonempty hS Δ hΔ hdisj)
    hF₁ hF₂ hFF hP hu hv hP₁ hP₂ hX
  have hc := hs₁.1
  have hd := hs₂.1
  rw [discComplement_cuffs_eq hS Δ hΔ hdisj] at hc hd
  obtain ⟨i, rfl⟩ := hc
  obtain ⟨j, rfl⟩ := hd
  have hij : i ≠ j := fun he => hCD (congrArg (fun l => Subtype.val ⁻¹' discBd (Δ l)) he)
  exact two_loop_vertex_count_gt hS Γ Δ hΔ hdisj hcase hUC N hbound hij
    hF₁ hF₂ hFF hP hu hv hP₁ hP₂ hs₁ hs₂ hn

/-- Condition (iii) of XII (3.1) bounds every normal schismatic meeting-loop shape. -/
theorem meeting_loop_vertex_count_gt_of_schismatic
    {S : Type u} {ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
      [Nonempty ι]
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
    {F₁ F₂ : Set (discComplement Δ)} {u : discComplement Δ}
    (hF₁ : IsOArc F₁) (hF₂ : IsOArc F₂) (hcap : F₁ ∩ F₂ = {u})
    (hX : GM07.IsSchismatic (F₁ ∪ F₂))
    (hn : (drawingInSubspace Γ (discComplement Δ) hUC).IsNormal (F₁ ∪ F₂)) :
    N < ((drawingInSubspace Γ (discComplement Δ) hUC).V ∩ (F₁ ∪ F₂)).ncard := by
  let : ConnectedSpace (discComplement Δ) :=
    Subtype.connectedSpace (discComplement_isConnected hS Δ hΔ hdisj)
  obtain ⟨C, D, hs₁, hs₂, hCD⟩ := surrounding_cuffs_of_schismatic_x2
    (discComplement_isSurface hS Δ hΔ hdisj) (discComplement_cuffs_nonempty hS Δ hΔ hdisj)
    hF₁ hF₂ hcap hX
  have hc := hs₁.1
  have hd := hs₂.1
  rw [discComplement_cuffs_eq hS Δ hΔ hdisj] at hc hd
  obtain ⟨i, rfl⟩ := hc
  obtain ⟨j, rfl⟩ := hd
  have hij : i ≠ j := fun he => hCD (congrArg (fun l => Subtype.val ⁻¹' discBd (Δ l)) he)
  exact meeting_loop_vertex_count_gt hS Γ Δ hΔ hdisj hcase hUC N hbound hij
    hF₁ hF₂ hcap hs₁ hs₂ hn

end GraphMinor.GM12

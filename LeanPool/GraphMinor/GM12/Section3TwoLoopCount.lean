/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3ThirdDisc
public import LeanPool.GraphMinor.GM12.Section3SubspaceDrawing
import LeanPool.GraphMinor.GM12.Section3SubspaceArcs

/-!
# The two-loop vertex bound

Condition (ii) of XII (3.1), page 245, applies to two disjoint circles
and a joining line. When the circles surround distinct cuffs, the
preceding disc construction gives disjoint enclosing discs, each
including exactly one prescribed disc. Inclusion preserves the line,
its ends, normality and the vertex count, so condition (ii) gives the
required bound for this shape.
-/

public section

namespace GraphMinor.GM12

open Set Surface Topology

/-- The vertex bound for two disjoint surrounding circles joined by
a line, the first two-loop shape in the reduction of XII (3.1). The
ambient hypothesis is condition (ii), with the enclosing discs and
line endpoints written explicitly. -/
theorem two_loop_vertex_count_gt
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
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
    {i j : ι} (hij : i ≠ j)
    {F₁ F₂ P : Set (discComplement Δ)} {u v : discComplement Δ}
    (hF₁ : IsOArc F₁) (hF₂ : IsOArc F₂) (hFF : Disjoint F₁ F₂)
    (hP : IsLineWithEnds P u v) (hu : u ∈ F₁) (hv : v ∈ F₂)
    (hP₁ : P ∩ F₁ = {u}) (hP₂ : P ∩ F₂ = {v})
    (hs₁ : GM07.SurroundsCuff F₁ (Subtype.val ⁻¹' discBd (Δ i)))
    (hs₂ : GM07.SurroundsCuff F₂ (Subtype.val ⁻¹' discBd (Δ j)))
    (hn : (drawingInSubspace Γ (discComplement Δ) hUC).IsNormal (F₁ ∪ F₂ ∪ P)) :
    N < ((drawingInSubspace Γ (discComplement Δ) hUC).V ∩ (F₁ ∪ F₂ ∪ P)).ncard := by
  let C := discComplement Δ
  let a : C → S := Subtype.val
  obtain ⟨D, E, hD, hE, hbD, hbE, honeD, honeE, hDE⟩ :=
    exists_disjoint_surrounding_discs_of_surface_condition hS Δ hΔ hdisj hcase
      hij hF₁ hF₂ hFF hs₁ hs₂
  have hA : IsOArc (a '' F₁) := by
    obtain ⟨φ⟩ := hF₁
    exact ⟨φ.trans (IsEmbedding.subtypeVal.homeomorphImage F₁)⟩
  have hB : IsOArc (a '' F₂) := by
    obtain ⟨φ⟩ := hF₂
    exact ⟨φ.trans (IsEmbedding.subtypeVal.homeomorphImage F₂)⟩
  have hnormal := drawingInSubspace_isNormal_image Γ C hUC hn
  rw [image_union, image_union] at hnormal
  have hPA : a '' P ∩ a '' F₁ = {u.val} := by
    rw [← image_inter Subtype.val_injective, hP₁, image_singleton]
  have hPB : a '' P ∩ a '' F₂ = {v.val} := by
    rw [← image_inter Subtype.val_injective, hP₂, image_singleton]
  have hsupport : a '' F₁ ∪ a '' F₂ ∪ a '' P ⊆ C := by
    rintro x ((⟨y, _, rfl⟩ | ⟨y, _, rfl⟩) | ⟨y, _, rfl⟩) <;> exact y.property
  have hbig := hbound (a '' F₁) (a '' F₂) (a '' P) D E u.val v.val
    hnormal hA hB (isLineWithEnds_subtype_image hP)
    (mem_image_of_mem a hu) (mem_image_of_mem a hv) hPA hPB hsupport
    hD hE hbD hbE hDE ⟨i, honeD⟩ ⟨j, honeE⟩
  have hcount := congrArg Set.ncard
    (drawingInSubspace_image_vertices_inter Γ C hUC (F₁ ∪ F₂ ∪ P))
  rw [ncard_image_of_injective _ Subtype.val_injective, image_union, image_union] at hcount
  rw [hcount]
  exact hbig

end GraphMinor.GM12

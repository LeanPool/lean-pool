/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3EnclosingBranches
public import LeanPool.GraphMinor.GM12.Section3SubspaceDrawing
import LeanPool.GraphMinor.GM12.Section3SubspaceArcs

/-!
# The three-branch vertex bound

Condition (iv) of XII (3.1), page 245, bounds three branches on the
sphere when their three circles surround the three prescribed cuffs.
The enclosing-disc construction excludes each opposite branch.
Inclusion preserves lines, intersections, normality and vertex counts,
so the original condition applies directly.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- The vertex bound for the three-branch shape from XII (3.1)(iv),
page 245. The other two branches form each surrounding circle. -/
theorem three_branch_vertex_count_gt
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hsphere : IsSphere S) (Γ : Drawing S)
    (Δ : Fin 3 → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (hUC : Γ.U ⊆ discComplement Δ) (N : ℕ)
    (hbound : IsSphere S → ∀ (P D : Fin 3 → Set S) (a b : S), a ≠ b →
      Γ.IsNormal (⋃ i, P i) → (∀ i, IsLineWithEnds (P i) a b) →
      (∀ i j, i ≠ j → P i ∩ P j = {a, b}) → (⋃ i, P i) ⊆ discComplement Δ →
      (∀ i, IsClosedDisc (D i) ∧
        discBd (D i) = ⋃ j : {j // j ≠ i}, P j.val ∧ Δ i ⊆ D i ∧ ¬ P i ⊆ D i) →
      N < (Γ.V ∩ ⋃ i, P i).ncard)
    (P : Fin 3 → Set (discComplement Δ)) {a b : discComplement Δ} (hab : a ≠ b)
    (hP : ∀ i, IsLineWithEnds (P i) a b)
    (hcap : ∀ i j, i ≠ j → P i ∩ P j = {a, b})
    (hQ : ∀ i, IsOArc (⋃ j : {j // j ≠ i}, P j.val))
    (hs : ∀ i, GM07.SurroundsCuff (⋃ j : {j // j ≠ i}, P j.val)
      (Subtype.val ⁻¹' discBd (Δ i)))
    (hn : (drawingInSubspace Γ (discComplement Δ) hUC).IsNormal (⋃ i, P i))
    (hnot : ¬ GM07.IsNearPlanar (⋃ i, P i)) :
    N < ((drawingInSubspace Γ (discComplement Δ) hUC).V ∩ ⋃ i, P i).ncard := by
  let C := discComplement Δ
  let Q : Fin 3 → Set C := fun i => ⋃ j : {j // j ≠ i}, P j.val
  have hcover : ∀ i, Q i ∪ P i = ⋃ j, P j := by
    intro i
    ext x
    constructor
    · rintro (hxQ | hxP)
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hxQ
        exact mem_iUnion.mpr ⟨j.val, hj⟩
      · exact mem_iUnion.mpr ⟨i, hxP⟩
    · intro hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      by_cases hji : j = i
      · exact Or.inr (hji ▸ hj)
      · exact Or.inl (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)
  obtain ⟨D, hD⟩ := exists_enclosing_discs_excluding_complementary_parts hS Δ hΔ hdisj
    P Q hcover hQ hs hnot
  let R : Fin 3 → Set S := fun i => (Subtype.val : C → S) '' P i
  have hnormal := drawingInSubspace_isNormal_image Γ C hUC hn
  rw [image_iUnion] at hnormal
  have hcap' : ∀ i j, i ≠ j → R i ∩ R j = {a.val, b.val} := by
    intro i j hij
    change Subtype.val '' P i ∩ Subtype.val '' P j = _
    rw [← image_inter Subtype.val_injective, hcap i j hij, image_pair]
  have hsupport : (⋃ i, R i) ⊆ C := by
    intro x hx
    obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.mp hx
    exact y.property
  have hdiscs : ∀ i, IsClosedDisc (D i) ∧
      discBd (D i) = ⋃ j : {j // j ≠ i}, R j.val ∧ Δ i ⊆ D i ∧ ¬ R i ⊆ D i := by
    intro i
    refine ⟨(hD i).1, ?_, (hD i).2.2.1, (hD i).2.2.2⟩
    rw [(hD i).2.1]
    exact image_iUnion
  have hbig := hbound hsphere R D a.val b.val
    (fun he => hab (Subtype.ext he)) hnormal
    (fun i => isLineWithEnds_subtype_image (hP i)) hcap' hsupport hdiscs
  have hcount := congrArg Set.ncard
    (drawingInSubspace_image_vertices_inter Γ C hUC (⋃ i, P i))
  rw [ncard_image_of_injective _ Subtype.val_injective, image_iUnion] at hcount
  rw [hcount]
  exact hbig

end GraphMinor.GM12

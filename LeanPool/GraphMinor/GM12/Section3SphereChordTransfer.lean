/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3SphereChordBound
public import LeanPool.GraphMinor.GM12.Section3SubspaceDrawing
import LeanPool.GraphMinor.GM12.Section3SubspaceArcs
import LeanPool.GraphMinor.Surface.DiscArcs

/-!
# The sphere chord bound in the complementary disc

The one-disc case of XII (3.2), pages 247--248, applies VI in
the complementary disc, while the tangle lives on the original
sphere drawing. Include the two boundary arcs and the normal chord
into the sphere. Their intersections, endpoints, and drawing vertex
counts are preserved by this inclusion. The sphere chord theorem
therefore gives exactly the minimum-arc inequality used in VI.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Read the normal-chord inequality of XII (3.2), pages 247--248,
in the complementary closed disc where VI (3.6) is applied. -/
theorem sphere_chord_bound_in_complement
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hs : IsSphere S) (Γ : Drawing S) {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : GM10.IsTangle Γ.toHypergraph θ T) {Δ : Set S}
    (hΔ : IsClosedDisc Δ) (havoid : Γ.U ∩ Δ = Γ.V ∩ discBd Δ)
    (hfree : GM10.IsFreeSet Γ.toHypergraph T θ (Γ.V ∩ discBd Δ))
    (C : Set S) (hUC : Γ.U ⊆ C) (hbdC : bd C = (Subtype.val : C → S) ⁻¹' discBd Δ)
    (hCΔ : C ∩ Δ = discBd Δ)
    (x y : C) (A B P : Set C) (hA : IsLineWithEnds A x y) (hB : IsLineWithEnds B x y)
    (hP : IsLineWithEnds P x y) (hAB : A ∩ B = {x, y}) (hAP : A ∩ P = {x, y})
    (hBP : B ∩ P = {x, y}) (hbd : bd C = A ∪ B) (hcap : P ∩ bd C = {x, y})
    (hn : (drawingInSubspace Γ C hUC).IsNormal P) :
    min ((drawingInSubspace Γ C hUC).V ∩ A).ncard
      ((drawingInSubspace Γ C hUC).V ∩ B).ncard ≤
      ((drawingInSubspace Γ C hUC).V ∩ P).ncard := by
  let f : C → S := Subtype.val
  have hbdΔC : discBd Δ ⊆ C := hCΔ.symm.subset.trans inter_subset_left
  have hbimage : f '' bd C = discBd Δ := by
    rw [hbdC, Subtype.image_preimage_coe]
    exact inter_eq_right.mpr hbdΔC
  have hbd' : discBd Δ = f '' A ∪ f '' B :=
    hbimage.symm.trans ((congrArg (Set.image f) hbd).trans (image_union f A B))
  have himageInter : ∀ {L M : Set C}, L ∩ M = {x, y} →
      f '' L ∩ f '' M = {x.val, y.val} := by
    intro L M hLM
    rw [← image_inter Subtype.val_injective, hLM, image_pair]
  have hPΔ : f '' P ∩ Δ = {x.val, y.val} := by
    apply Subset.antisymm
    · rintro z ⟨⟨w, hw, rfl⟩, hwΔ⟩
      have hwBd : w.val ∈ discBd Δ := hCΔ.subset ⟨w.property, hwΔ⟩
      have hwB : w ∈ bd C := hbdC.symm ▸ hwBd
      rcases hcap.subset ⟨hw, hwB⟩ with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro z hz
      rcases hz with rfl | rfl
      · have hx := hcap.symm.subset (Or.inl rfl)
        refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
        exact Surface.discBd_subset Δ (hbdC.subset hx.2)
      · have hy := hcap.symm.subset (Or.inr rfl)
        refine ⟨⟨y, hy.1, rfl⟩, ?_⟩
        exact Surface.discBd_subset Δ (hbdC.subset hy.2)
  have hcount := normal_chord_vertex_count_ge_min hS hs hT hΔ hbd' havoid hfree
    (isLineWithEnds_subtype_image hA) (isLineWithEnds_subtype_image hB)
    (isLineWithEnds_subtype_image hP) (himageInter hAB) (himageInter hAP) (himageInter hBP)
    hPΔ (drawingInSubspace_isNormal_image Γ C hUC hn)
  have hcounts : ∀ Q : Set C, (Γ.V ∩ f '' Q).ncard = ((drawingInSubspace Γ C hUC).V ∩ Q).ncard := by
    intro Q
    rw [← drawingInSubspace_image_vertices_inter Γ C hUC Q,
      Set.ncard_image_of_injective _ Subtype.val_injective]
  rw [hcounts A, hcounts B, hcounts P] at hcount
  exact hcount

end GraphMinor.GM12

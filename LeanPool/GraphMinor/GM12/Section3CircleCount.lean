/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3NearPlanarCircle
public import LeanPool.GraphMinor.GM12.Section3SubspaceDrawing

/-!
# The circle case of the alpha bound

Condition (i) of XII (3.1), page 245, forces every small normal circle
in Sigma-star to be near-planar. A normal circle which is not
near-planar must therefore meet more than N vertices. Inclusion keeps
normality and the vertex count unchanged.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- The circle case of the schismatic vertex bound in the reduction
of XII (3.1), page 245, to VII (7.5). -/
theorem normal_oArc_vertex_count_gt
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [Finite ι]
    (hS : IsClosedSurface S) (Γ : Drawing S) (Δ : ι → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (hUC : Γ.U ⊆ discComplement Δ) (N : ℕ)
    (hsmall : ∀ F : Set S, Γ.IsNormal F → IsOArc F → F ⊆ discComplement Δ →
      (Γ.V ∩ F).ncard ≤ N →
      ∃ D : Set S, IsClosedDisc D ∧ discBd D = F ∧
        ∀ i j, Δ i ⊆ D → Δ j ⊆ D → i = j)
    {F : Set (discComplement Δ)}
    (hn : (drawingInSubspace Γ (discComplement Δ) hUC).IsNormal F)
    (hF : IsOArc F) (hnot : ¬ GM07.IsNearPlanar F) :
    N < ((drawingInSubspace Γ (discComplement Δ) hUC).V ∩ F).ncard := by
  have hcount : ((drawingInSubspace Γ (discComplement Δ) hUC).V ∩ F).ncard =
      (Γ.V ∩ (Subtype.val : discComplement Δ → S) '' F).ncard := by
    rw [← drawingInSubspace_image_vertices_inter Γ (discComplement Δ) hUC F,
      ncard_image_of_injective _ Subtype.val_injective]
  have hFo : IsOArc ((Subtype.val : discComplement Δ → S) '' F) := by
    obtain ⟨φ⟩ := hF
    exact ⟨φ.trans (Topology.IsEmbedding.subtypeVal.homeomorphImage F)⟩
  by_contra hle
  have hle' : ((drawingInSubspace Γ (discComplement Δ) hUC).V ∩ F).ncard ≤ N :=
    Nat.le_of_not_gt hle
  rw [hcount] at hle'
  obtain ⟨D, hD, hbd, hone⟩ := hsmall _
    (drawingInSubspace_isNormal_image Γ (discComplement Δ) hUC hn) hFo
    (by rintro x ⟨y, _, rfl⟩; exact y.property) hle'
  exact hnot (isNearPlanar_of_bounds_disc_including_at_most_one hS Δ hΔ hdisj hD hbd hone)

end GraphMinor.GM12

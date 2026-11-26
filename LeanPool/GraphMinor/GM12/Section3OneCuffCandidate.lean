/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3NormalEssentialCircle
public import LeanPool.GraphMinor.GM12.Section3SubspaceDrawing
import LeanPool.GraphMinor.GM12.Section3NearPlanarAmbient
public import LeanPool.GraphMinor.GM12.Section3Punctured
import LeanPool.GraphMinor.GM12.Section3PuncturedSurface
import LeanPool.GraphMinor.GM12.Section3SubspaceArcs
import LeanPool.GraphMinor.GM12.Section3CircleSchismatic
import LeanPool.GraphMinor.GM12.Section3SchismaticCandidate
import LeanPool.GraphMinor.GM12.Section3FiniteGraphSolid
import LeanPool.GraphMinor.GM11.Section6

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# An alpha candidate with one prescribed cuff

In the one-disc case of XII (3.1), page 245, the original surface
is not a sphere. VII (5.5) supplies a normal non-null-homotopic circle
outside the deleted disc. Any near-planar set in the punctured surface
is planar in the original surface after filling its cuff. The circle
therefore cannot be near-planar. As a normal schismatic circle, it is
an alpha candidate.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

universe u

/-- The one-disc case of alpha-candidate existence in XII (3.1).
The only external inputs are the original VII (5.1) and (5.5). -/
theorem exists_alphaCandidate_one_disc_of_not_sphere
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hns : ¬ IsSphere S) (Γ : Drawing S) (Δ : Fin 1 → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (havoid : ∀ i, Γ.U ∩ Δ i = Γ.V ∩ discBd (Δ i)) :
    ∃ X, GM07.IsAlphaCandidate (drawingInSubspace Γ (discComplement Δ)
      (drawing_support_subset_discComplement hS Γ Δ hΔ hdisj havoid)) X := by
  have hnD : Γ.IsNormal (discBd (Δ 0)) := by
    rintro x ⟨hxB, hxU⟩
    exact ((havoid 0 ▸ (show x ∈ Γ.U ∩ Δ 0 from
      ⟨hxU, Surface.discBd_subset (Δ 0) hxB⟩)).1)
  obtain ⟨F, hF, hnF, hFout, hnonnull⟩ :=
    exists_normal_nonnull_oArc_outside_disc hS hns Γ (hΔ 0) hnD
  have hCeq : discComplement Δ = closure (Δ 0)ᶜ := by
    have hΔeq : (⋃ i, Δ i) = Δ 0 := by
      ext x
      constructor
      · intro hx
        obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        have hi0 : i = 0 := Subsingleton.elim i 0
        exact hi0 ▸ hi
      · intro hx
        exact mem_iUnion.mpr ⟨0, hx⟩
    rw [discComplement, hΔeq]
  have hFC : F ⊆ discComplement Δ := hCeq.symm ▸ hFout
  let X := (Subtype.val : discComplement Δ → S) ⁻¹' F
  have hX : IsOArc X := isOArc_subtype_preimage hFC hF
  have himage : (Subtype.val : discComplement Δ → S) '' X = F := by
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hFC]
  have hUC := drawing_support_subset_discComplement hS Γ Δ hΔ hdisj havoid
  have hnormal : (drawingInSubspace Γ (discComplement Δ) hUC).IsNormal X := by
    rintro x ⟨hx, hxU⟩
    rw [drawingInSubspace_U] at hxU
    rw [drawingInSubspace_V]
    exact hnF ⟨hx, hxU⟩
  have hnotnear : ¬ GM07.IsNearPlanar X := by
    intro hnear
    have hp := isPlanar_image_of_isNearPlanar_discComplement hS Δ hΔ hdisj hnear
    rw [himage] at hp
    have hproper : F ≠ univ := by
      intro heq
      obtain ⟨x, hx⟩ := (hΔ 0).nonempty_discInt
      have hxF : x ∈ F := heq.symm ▸ mem_univ x
      have hxfr : x ∈ frontier (Δ 0) := by
        rw [frontier_eq_closure_inter_closure]
        exact ⟨subset_closure hx.1, hFout hxF⟩
      exact hx.2 (IsClosedDisc.frontier_eq_discBd hS (hΔ 0) ▸ hxfr)
    apply hnonnull
    exact (GraphMinor.GM07.gm07_theorem_5_1 S ⟨hS.1, hS.2.1, fun x =>
      (hS.2.2 x).isManifoldPoint⟩ inferInstance
      F (isSolid_oArc hF) hproper).mp hp F hF subset_rfl
  let : CompactSpace (discComplement Δ) := (discComplement_isSurface hS Δ hΔ hdisj).1
  exact ⟨X, alphaCandidate_of_normal_schismatic (isSchismatic_oArc hX hnotnear) hnormal⟩

end GraphMinor.GM12

/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3CuffSurrounds
public import LeanPool.GraphMinor.GM12.Section3SubspaceDrawing
import LeanPool.GraphMinor.GM12.Section3NormalPuncturedPaths
import LeanPool.GraphMinor.GM12.Section3SolidUnion
import LeanPool.GraphMinor.GM12.Section3FiniteGraphSolid
import LeanPool.GraphMinor.GM12.Section3SubspaceArcs
import LeanPool.GraphMinor.GM12.Section3PuncturedSurface
import LeanPool.GraphMinor.Surface.ArcInPath
import LeanPool.GraphMinor.GM11.RadialChord
import Mathlib.Analysis.Convex.Contractible

/-!
# An alpha candidate joining two prescribed cuffs

For the minimum-existence step used by XII (3.1), page 245, choose
one point on each of two distinct prescribed cuffs. A normal path in
the punctured surface joins them. Erasing repeated portions gives a
normal line there. Its union with the two cuffs is solid and connected,
and cannot be near-planar because the two cuff circles surround
distinct cuffs. This gives an actual alpha candidate.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

private theorem connected_oArc
    {S : Type*} [TopologicalSpace S] {F : Set S} (hF : IsOArc F) : IsConnected F := by
  obtain ⟨e⟩ := hF
  let : PathConnectedSpace F := e.pathConnectedSpace
  exact (isPathConnected_iff_pathConnectedSpace.mpr inferInstance).isConnected

/-- Two distinct prescribed cuffs supply a normal solid connected
set which is not near-planar, for any drawing in the setup of XII (3.1). -/
theorem exists_alphaCandidate_of_two_prescribed_cuffs
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) (Γ : Drawing S) (Δ : ι → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (hcase : ¬ IsSphere S ∨ 3 ≤ Nat.card ι)
    (havoid : ∀ i, Γ.U ∩ Δ i = Γ.V ∩ discBd (Δ i))
    {i j : ι} (hij : i ≠ j) :
    ∃ X, GM07.IsAlphaCandidate (drawingInSubspace Γ (discComplement Δ)
      (drawing_support_subset_discComplement hS Γ Δ hΔ hdisj havoid)) X := by
  classical
  let C := discComplement Δ
  have hsurf := discComplement_isSurface hS Δ hΔ hdisj
  let : CompactSpace C := hsurf.1
  let F : ι → Set C := fun k => Subtype.val ⁻¹' discBd (Δ k)
  have hF : ∀ k, IsOArc (F k) := fun k => isOArc_subtype_preimage
    (disc_boundary_subset_discComplement hS Δ hΔ hdisj k) (hΔ k).isOArc_discBd
  obtain ⟨e⟩ := hF i
  obtain ⟨f⟩ := hF j
  let x : C := (e 1).val
  let y : C := (f 1).val
  have hx : x ∈ F i := (e 1).property
  have hy : y ∈ F j := (f 1).property
  have hxy : x.val ≠ y.val := by
    intro heq
    exact disjoint_left.mp (hdisj hij) (Surface.discBd_subset (Δ i) hx)
      (heq.symm ▸ Surface.discBd_subset (Δ j) hy)
  have hboundaryN : ∀ k, discBd (Δ k) ⊆ Γ.Uᶜ ∪ Γ.V := by
    intro k z hz
    by_cases hzU : z ∈ Γ.U
    · exact Or.inr ((havoid k ▸ (show z ∈ Γ.U ∩ Δ k from
        ⟨hzU, Surface.discBd_subset (Δ k) hz⟩)).1)
    · exact Or.inl hzU
  obtain ⟨q, hqC, hqN⟩ := exists_normal_path_in_discComplement hS Γ Δ hΔ hdisj havoid
    x.property y.property (hboundaryN i hx) (hboundaryN j hy)
  obtain ⟨g, hgc, hgi, hg0, hg1, hgq⟩ := exists_arc_of_path q.continuous
    (by rw [q.source, q.target]; exact hxy)
  have hgC : range g ⊆ C := hgq.trans hqC
  let gC : unitInterval → C := fun t => ⟨g t, hgC (mem_range_self t)⟩
  have hgCc : Continuous gC := hgc.subtype_mk _
  have hgCi : Function.Injective gC := fun a b he => hgi (congrArg Subtype.val he)
  have hL : IsLineWithEnds (range gC) x y := by
    have h := isLine_range hgCc hgCi
    have h0 : gC 0 = x := Subtype.ext (hg0.trans q.source)
    have h1 : gC 1 = y := Subtype.ext (hg1.trans q.target)
    rwa [h0, h1] at h
  have hLL : IsLine (range gC) := ⟨hL.choose⟩
  have hLconn : IsConnected (range gC) := isConnected_range hgCc
  let X := F i ∪ range gC ∪ F j
  have hsolid : IsSolid X := isSolid_union
    (isSolid_union (isSolid_oArc (hF i)) (isSolid_line hLL)) (isSolid_oArc (hF j))
  have hconn : IsConnected X :=
    ((connected_oArc (hF i)).union ⟨x, hx, hL.left_mem⟩ hLconn).union
      ⟨y, Or.inr hL.right_mem, hy⟩ (connected_oArc (hF j))
  have hUC := drawing_support_subset_discComplement hS Γ Δ hΔ hdisj havoid
  have hnormal : (drawingInSubspace Γ C hUC).IsNormal X := by
    rintro z ⟨(hzF | hzL) | hzF, hzU⟩
    · rw [drawingInSubspace_U] at hzU
      rw [drawingInSubspace_V]
      exact ((havoid i ▸ (show z.val ∈ Γ.U ∩ Δ i from
        ⟨hzU, Surface.discBd_subset (Δ i) hzF⟩)).1)
    · rw [drawingInSubspace_U] at hzU
      rw [drawingInSubspace_V]
      obtain ⟨t, rfl⟩ := hzL
      exact hqN ⟨hgq (mem_range_self t), hzU⟩
    · rw [drawingInSubspace_U] at hzU
      rw [drawingInSubspace_V]
      exact ((havoid j ▸ (show z.val ∈ Γ.U ∩ Δ j from
        ⟨hzU, Surface.discBd_subset (Δ j) hzF⟩)).1)
  refine ⟨X, hsolid, hconn, hnormal, ?_⟩
  exact not_isNearPlanar_of_distinct_surrounding_subcircles hS Δ hΔ hdisj hcase hij
    (hF i) (hF j) (subset_union_left.trans subset_union_left) subset_union_right
    (surroundsCuff_prescribed_boundary hS Δ hΔ hdisj hcase i)
    (surroundsCuff_prescribed_boundary hS Δ hΔ hdisj hcase j)

end GraphMinor.GM12

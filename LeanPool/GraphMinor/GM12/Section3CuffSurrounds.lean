/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3SurroundingUnique
import LeanPool.GraphMinor.GM12.Section3CapComparison
import LeanPool.GraphMinor.GM12.Section3CapTopology
import LeanPool.GraphMinor.GM12.Section3PuncturedSurface
import LeanPool.GraphMinor.GM12.Section3PuncturedCuffs
import LeanPool.GraphMinor.GM12.Section3SubspaceArcs
import LeanPool.GraphMinor.Surface.DiscArcs
import LeanPool.GraphMinor.GM12.Section3DiscUniqueness

/-!
# Each prescribed cuff surrounds itself

For alpha-candidate existence in XII (3.1), page 245, a prescribed
cuff is planar after its deleted disc is filled. It is not planar
before filling: a disc bounded by that cuff would give a second disc
with the same boundary as the deleted disc. Disc uniqueness identifies
them, contradicting the missing interior. In the sphere case a point
in another deleted disc prevents the two discs from covering the sphere.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- Under the surface condition of XII (3.1), each prescribed cuff
is a surrounding circle for that same cuff. -/
theorem surroundsCuff_prescribed_boundary
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (hcase : ¬ IsSphere S ∨ 3 ≤ Nat.card ι) (i : ι) :
    GM07.SurroundsCuff ((Subtype.val : discComplement Δ → S) ⁻¹' discBd (Δ i))
      ((Subtype.val : discComplement Δ → S) ⁻¹' discBd (Δ i)) := by
  classical
  let F := (Subtype.val : discComplement Δ → S) ⁻¹' discBd (Δ i)
  have hF : IsOArc F := isOArc_subtype_preimage
    (disc_boundary_subset_discComplement hS Δ hΔ hdisj i) (hΔ i).isOArc_discBd
  have hC : IsCuff F := by
    change F ∈ cuffs (discComplement Δ)
    rw [discComplement_cuffs_eq hS Δ hΔ hdisj]
    exact ⟨i, rfl⟩
  have hsurface := discComplement_isSurface hS Δ hΔ hdisj
  obtain ⟨T, tT, j, D, hcap⟩ := exists_cappedCuff hsurface hC
  let := tT
  have hpF : GM07.IsPlanarInCappedCuff F F := by
    apply isPlanarInCappedCuff_of_one_cap hsurface hcap
    exact ⟨D, hcap.isClosedDisc, hcap.discBd_eq ▸ Surface.discBd_subset D⟩
  refine ⟨hC, hpF, ?_⟩
  intro hp
  obtain ⟨E, hE, hFE⟩ := hp
  obtain ⟨B, hBprop, _⟩ := disc_oArc E F hE hFE hF
  have hB := hBprop.2.1
  have hbB := hBprop.2.2.1
  obtain ⟨hBamb, hbd⟩ := isClosedDisc_subtype_image hB
  let B' := (Subtype.val : discComplement Δ → S) '' B
  have hB'C : B' ⊆ discComplement Δ := by rintro _ ⟨x, _, rfl⟩; exact x.property
  have hbd' : discBd B' = discBd (Δ i) := by
    rw [hbd, hbB]
    change Subtype.val '' (Subtype.val ⁻¹' discBd (Δ i)) = discBd (Δ i)
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr (disc_boundary_subset_discComplement hS Δ hΔ
      hdisj i)]
  have heq : B' = Δ i := by
    rcases hcase with hns | hthree
    · exact Surface.eq_of_discBd_eq
        ⟨hS.1, hS.2.1, fun x => (hS.2.2 x).isManifoldPoint⟩ hns hBamb (hΔ i) hbd'
    · let := Fintype.ofFinite ι
      have hthree' : 3 ≤ Fintype.card ι := by simpa only [Nat.card_eq_fintype_card] using hthree
      obtain ⟨k, hki, _⟩ := ENat.exists_ne_ne_of_three_le
        (by rw [ENat.card_eq_coe_fintype_card]; exact_mod_cast hthree') i i
      obtain ⟨x, hx⟩ := (hΔ k).nonempty_discInt
      have hnotcover : B' ∪ Δ i ≠ univ := by
        intro hc
        have hxin : x ∈ B' ∪ Δ i := hc.symm ▸ mem_univ x
        rcases hxin with hxB | hxi
        · exact hx.2 (discComplement_inter_disc_subset_boundary hS Δ hΔ k ⟨hB'C hxB, hx.1⟩)
        · exact disjoint_left.mp (hdisj hki) hx.1 hxi
      exact eq_of_discBd_eq_of_union_ne_univ (fun x => (hS.2.2 x).isManifoldPoint)
        hBamb (hΔ i) hbd' hnotcover
  obtain ⟨x, hx⟩ := (hΔ i).nonempty_discInt
  have hxB : x ∈ B' := heq.symm ▸ hx.1
  exact hx.2 (discComplement_inter_disc_subset_boundary hS Δ hΔ i ⟨hB'C hxB, hx.1⟩)

end GraphMinor.GM12

/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexBoundaryDistance

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexBoundaryDistanceLayer

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Boundary layers described by Euclidean distance

The convex inner-boundary-layer estimate is converted into a weak `L¹` tail
for the inverse Euclidean distance to the complement.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- A bounded subset of a positive-dimensional vector space has nonempty
complement. -/
theorem IsOpenBoundedConvexDomain.compl_nonempty (hd : 1 ≤ d)
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) : Uᶜ.Nonempty := by
  have : NeZero d := ⟨Nat.ne_of_gt hd⟩
  rw [Set.nonempty_compl]
  intro hUuniv
  apply NormedSpace.unbounded_univ ℝ (Vec d)
  simpa only [hUuniv] using hU.isBoundedDomain.isBounded

/-- Euclidean boundary distance is positive in an open bounded domain. -/
theorem euclideanBoundaryDistance_pos (hd : 1 ≤ d)
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) {x : Vec d} (hx : x ∈ U) :
    0 < euclideanBoundaryDistance U x := by
  have hcomp : Uᶜ.Nonempty :=
    IsOpenBoundedConvexDomain.compl_nonempty hd hU
  have himage : (HilbertVec.ofVec '' Uᶜ).Nonempty := hcomp.image _
  have hclosed : IsClosed (HilbertVec.ofVec '' Uᶜ) := by
    change IsClosed ((HilbertVec.continuousLinearEquivVec d).symm '' Uᶜ)
    exact (HilbertVec.continuousLinearEquivVec d).symm.toHomeomorph.isClosed_image.mpr
      hU.isOpen.isClosed_compl
  unfold euclideanBoundaryDistance
  rw [← hclosed.notMem_iff_infDist_pos himage]
  rintro ⟨y, hy, heq⟩
  have hxy : x = y := by
    simpa only [HilbertVec.toVec_ofVec] using (congrArg HilbertVec.toVec heq).symm
  exact hy (hxy ▸ hx)

/-- Boundary-distance sublevel sets are exactly the convex inner layers. -/
theorem euclideanBoundaryDistance_lt_iff_not_ball_subset (hd : 1 ≤ d)
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {x : Vec d} {t : ℝ} (ht : 0 ≤ t) :
    euclideanBoundaryDistance U x < t ↔ ¬euclideanBallAt x t ⊆ U := by
  constructor
  · exact not_subset_euclideanBallAt_of_boundaryDistance_lt
      (IsOpenBoundedConvexDomain.compl_nonempty hd hU) ht
  · intro hnot
    exact lt_of_not_ge fun hreach =>
      hnot (euclideanBallAt_subset_of_le_boundaryDistance ht hreach)

/-- The convex boundary layer controls Euclidean-distance sublevels. -/
theorem volume_euclideanBoundaryDistance_lt_le (hd : 1 ≤ d)
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) {rho Rad t : ℝ}
    (hsand : HasBallSandwich U rho Rad) (ht : 0 ≤ t) :
    volume {x : Vec d | x ∈ U ∧ euclideanBoundaryDistance U x < t} ≤
      ENNReal.ofReal ((d : ℝ) * t / rho) * volume U := by
  have hsets :
      {x : Vec d | x ∈ U ∧ euclideanBoundaryDistance U x < t} =
        {x : Vec d | x ∈ U ∧ ¬euclideanBallAt x t ⊆ U} := by
    ext x
    simp only [Set.mem_ofPred_eq, and_congr_right_iff]
    intro _hx
    exact euclideanBoundaryDistance_lt_iff_not_ball_subset hd hU ht
  rw [hsets]
  exact volume_innerBoundaryLayer_le hd hU hsand ht

/-- The inverse boundary distance has a weak `L¹` tail on the domain. -/
theorem measure_inverse_euclideanBoundaryDistance_gt_le (hd : 1 ≤ d)
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) {rho Rad t : ℝ}
    (hsand : HasBallSandwich U rho Rad) (ht : 0 < t) :
    (volume.restrict U)
        {x : Vec d | t < (euclideanBoundaryDistance U x)⁻¹} ≤
      ENNReal.ofReal ((d : ℝ) * t⁻¹ / rho) * volume U := by
  have hmeas : MeasurableSet
      {x : Vec d | t < (euclideanBoundaryDistance U x)⁻¹} :=
    measurableSet_lt measurable_const (measurable_euclideanBoundaryDistance U).inv
  rw [Measure.restrict_apply hmeas]
  have hsets :
      {x : Vec d | t < (euclideanBoundaryDistance U x)⁻¹} ∩ U =
        {x : Vec d | x ∈ U ∧ euclideanBoundaryDistance U x < t⁻¹} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨htail, hx⟩
      exact ⟨hx, (lt_inv_comm₀ ht (euclideanBoundaryDistance_pos hd hU hx)).mp htail⟩
    · rintro ⟨hx, hdist⟩
      exact ⟨(lt_inv_comm₀ ht (euclideanBoundaryDistance_pos hd hU hx)).mpr hdist, hx⟩
  rw [hsets]
  exact volume_euclideanBoundaryDistance_lt_le hd hU hsand (inv_nonneg.mpr ht.le)

end

end HighContrast
end HCPolySupport

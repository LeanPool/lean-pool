/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3ThetaPlanarity
public import LeanPool.GraphMinor.GM12.Section3CapTopology
public import LeanPool.GraphMinor.GM12.Section3CapComparison

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# Distinct cuff labels on the third schismatic shape

VII Section 8, page 241, used by XII (3.1), page 245, says that the
pair circles of a schismatic three-branch shape surround distinct
cuffs. If two pairs became planar after filling the same cuff, their
common branch would make the whole shape planar in that cap. The
original shape misses the new disc interior, so the proper-set premise
of VII (5.1) holds there. Cap comparison returns the result to VII's
universal definition of planarity after filling a cuff.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

universe u

private theorem line_image_embedding
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    {j : S → T} (hj : IsEmbedding j) {P : Set S} {a b : S}
    (hP : IsLineWithEnds P a b) : IsLineWithEnds (j '' P) (j a) (j b) := by
  obtain ⟨φ, hφ0, hφ1⟩ := hP
  exact ⟨φ.trans (hj.homeomorphImage P), congrArg j hφ0, congrArg j hφ1⟩

/-- Filling one cuff makes the whole three-branch shape planar if it
makes two pair circles planar. This is the common-cuff exclusion used
in VII Section 8's classification of the third schismatic shape. -/
theorem planarInCappedCuff_three_branches_of_two_pairs
    {S : Type u} [TopologicalSpace S] [ConnectedSpace S] (hS : IsSurface S)
    {P Q R C : Set S} {a b : S} (hab : a ≠ b)
    (hP : IsLineWithEnds P a b) (hQ : IsLineWithEnds Q a b) (hR : IsLineWithEnds R a b)
    (hPQ : P ∩ Q = {a, b}) (hPR : P ∩ R = {a, b}) (hQR : Q ∩ R = {a, b})
    (hpPQ : GM07.IsPlanarInCappedCuff C (P ∪ Q))
    (hpPR : GM07.IsPlanarInCappedCuff C (P ∪ R)) :
    GM07.IsPlanarInCappedCuff C (P ∪ Q ∪ R) := by
  obtain ⟨T, tT, j, D, hcap⟩ := exists_cappedCuff hS hpPQ.1
  let := tT
  have hconn : ConnectedSpace T := cappedCuff_connectedSpace hcap
  have hp : GM11.IsPlanar (j '' P ∪ j '' Q) := by
    rw [← image_union]
    exact hpPQ.2.2 T j D hcap
  have hq : GM11.IsPlanar (j '' P ∪ j '' R) := by
    rw [← image_union]
    exact hpPR.2.2 T j D hcap
  have hi : ∀ L M : Set S, L ∩ M = {a, b} → j '' L ∩ j '' M = {j a, j b} := by
    intro L M hLM
    rw [← image_inter hcap.isEmbedding.injective, hLM, image_pair]
  have hproper : j '' P ∪ j '' Q ∪ j '' R ≠ univ := by
    rw [← image_union, ← image_union]
    intro heq
    apply cappedCuff_range_ne_univ hcap
    apply Set.eq_univ_of_univ_subset
    rw [← heq]
    exact image_subset_range _ _
  have hplan := planar_three_branches_of_two_planar_pairs hcap.isSurface hconn
    (fun he => hab (hcap.isEmbedding.injective he))
    (line_image_embedding hcap.isEmbedding hP) (line_image_embedding hcap.isEmbedding hQ)
    (line_image_embedding hcap.isEmbedding hR) (hi P Q hPQ) (hi P R hPR) (hi Q R hQR)
    hproper hp hq
  apply isPlanarInCappedCuff_of_one_cap hS hcap
  simpa only [image_union] using hplan

/-- Two pair circles of a non-near-planar theta cannot be planar in
caps of the same cuff. Hence the cuff labels in VII Section 8's third
schismatic shape are distinct whenever they exist. -/
theorem cuff_ne_of_planar_pair_circles
    {S : Type u} [TopologicalSpace S] [ConnectedSpace S] (hS : IsSurface S)
    {P Q R C C' : Set S} {a b : S} (hab : a ≠ b)
    (hP : IsLineWithEnds P a b) (hQ : IsLineWithEnds Q a b) (hR : IsLineWithEnds R a b)
    (hPQ : P ∩ Q = {a, b}) (hPR : P ∩ R = {a, b}) (hQR : Q ∩ R = {a, b})
    (hnot : ¬ GM07.IsNearPlanar (P ∪ Q ∪ R))
    (hpPQ : GM07.IsPlanarInCappedCuff C (P ∪ Q))
    (hpPR : GM07.IsPlanarInCappedCuff C' (P ∪ R)) : C ≠ C' := by
  intro heq
  subst C'
  have hp := planarInCappedCuff_three_branches_of_two_pairs hS hab hP hQ hR
    hPQ hPR hQR hpPQ hpPR
  exact hnot (Or.inr ⟨C, hp.1, hp⟩)

end GraphMinor.GM12

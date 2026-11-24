/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3ThetaProperPairs
public import LeanPool.GraphMinor.GM12.Section3ThetaCuffs
import LeanPool.GraphMinor.GM12.Section3PlanarityMaps

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# The three surrounding cuff labels

VII Section 8, page 241, used by XII (3.1), page 245, asserts that
each pair circle of a schismatic theta surrounds a cuff, and the three
cuffs are distinct. The pairs are near-planar by minimality. None is
planar: combine it with a second near-planar pair in one cap to make
the whole theta near-planar. The common-cuff exclusion then makes
the three labels distinct.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

universe u

/-- A planar pair cannot occur in a non-near-planar theta when a
second pair is near-planar and the surface has a cuff. -/
theorem not_planar_pair_of_not_nearPlanar_theta
    {S : Type u} [TopologicalSpace S] [ConnectedSpace S] (hS : IsSurface S)
    (hcuffs : (cuffs S).Nonempty)
    {P Q R : Set S} {a b : S} (hab : a ≠ b)
    (hP : IsLineWithEnds P a b) (hQ : IsLineWithEnds Q a b) (hR : IsLineWithEnds R a b)
    (hPQ : P ∩ Q = {a, b}) (hPR : P ∩ R = {a, b}) (hQR : Q ∩ R = {a, b})
    (hnot : ¬ GM07.IsNearPlanar (P ∪ Q ∪ R)) (hnearPR : GM07.IsNearPlanar (P ∪ R)) :
    ¬ IsPlanar (P ∪ Q) := by
  intro hplanPQ
  have hex : ∃ C, GM07.IsPlanarInCappedCuff C (P ∪ R) := by
    rcases hnearPR with hp | ⟨C, _, hp⟩
    · obtain ⟨C, hC⟩ := hcuffs
      exact ⟨C, isPlanarInCappedCuff_of_isPlanar hS hC hp⟩
    · exact ⟨C, hp⟩
  obtain ⟨C, hpPR⟩ := hex
  have hpPQ := isPlanarInCappedCuff_of_isPlanar hS hpPR.1 hplanPQ
  have hpX := planarInCappedCuff_three_branches_of_two_pairs hS hab hP hQ hR
    hPQ hPR hQR hpPQ hpPR
  exact hnot (Or.inr ⟨C, hpX.1, hpX⟩)

private theorem surrounds_of_nearPlanar_not_planar
    {S : Type u} [TopologicalSpace S] {F : Set S}
    (hn : GM07.IsNearPlanar F) (hp : ¬ IsPlanar F) :
    ∃ C : Set S, GM07.SurroundsCuff F C := by
  rcases hn with hn | ⟨C, hC, hn⟩
  · exact (hp hn).elim
  · exact ⟨C, hC, hn, hp⟩

/-- The surrounding-cuff assertion for the third schismatic shape
in VII Section 8, page 241. Each pair surrounds a cuff, and those three
cuffs are pairwise distinct. The sphere and cuff-count classification
is a separate topological step. -/
theorem surrounding_pairs_of_schismatic_theta
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsSurface S) (hcuffs : (cuffs S).Nonempty)
    {P Q R : Set S} {a b : S} (hab : a ≠ b)
    (hP : IsLineWithEnds P a b) (hQ : IsLineWithEnds Q a b) (hR : IsLineWithEnds R a b)
    (hPQ : P ∩ Q = {a, b}) (hPR : P ∩ R = {a, b}) (hQR : Q ∩ R = {a, b})
    (hX : GM07.IsSchismatic (P ∪ Q ∪ R)) :
    ∃ C₁ C₂ C₃ : Set S,
      GM07.SurroundsCuff (P ∪ Q) C₁ ∧ GM07.SurroundsCuff (P ∪ R) C₂ ∧
      GM07.SurroundsCuff (Q ∪ R) C₃ ∧ C₁ ≠ C₂ ∧ C₁ ≠ C₃ ∧ C₂ ≠ C₃ := by
  obtain ⟨hnPQ, hnPR, hnQR⟩ := nearPlanar_pairs_of_schismatic_theta hP hQ hR hPQ hPR hQR hX
  have hQP : Q ∩ P = {a, b} := (inter_comm Q P).trans hPQ
  have hRP : R ∩ P = {a, b} := (inter_comm R P).trans hPR
  have hRQ : R ∩ Q = {a, b} := (inter_comm R Q).trans hQR
  have hnPQR := hX.2.1
  have hnPRQ : ¬ GM07.IsNearPlanar (P ∪ R ∪ Q) := by rwa [union_right_comm]
  have hnQRP : ¬ GM07.IsNearPlanar (Q ∪ R ∪ P) := by
    simpa only [union_assoc, union_left_comm, union_comm] using hnPQR
  have hnpPQ := not_planar_pair_of_not_nearPlanar_theta hS hcuffs hab hP hQ hR
    hPQ hPR hQR hnPQR hnPR
  have hnpPR := not_planar_pair_of_not_nearPlanar_theta hS hcuffs hab hP hR hQ
    hPR hPQ hRQ hnPRQ hnPQ
  have hnQP : GM07.IsNearPlanar (Q ∪ P) := by rwa [union_comm]
  have hnpQR := not_planar_pair_of_not_nearPlanar_theta hS hcuffs hab hQ hR hP
    hQR hQP hRP hnQRP hnQP
  obtain ⟨C₁, hs₁⟩ := surrounds_of_nearPlanar_not_planar hnPQ hnpPQ
  obtain ⟨C₂, hs₂⟩ := surrounds_of_nearPlanar_not_planar hnPR hnpPR
  obtain ⟨C₃, hs₃⟩ := surrounds_of_nearPlanar_not_planar hnQR hnpQR
  have h12 := cuff_ne_of_planar_pair_circles hS hab hP hQ hR hPQ hPR hQR hnPQR
    hs₁.2.1 hs₂.2.1
  have hpQP : GM07.IsPlanarInCappedCuff C₁ (Q ∪ P) := by simpa only [union_comm] using hs₁.2.1
  have hnQPR : ¬ GM07.IsNearPlanar (Q ∪ P ∪ R) := by rwa [union_comm Q P]
  have h13 := cuff_ne_of_planar_pair_circles hS hab hQ hP hR hQP hQR hPR hnQPR
    hpQP hs₃.2.1
  have hpRP : GM07.IsPlanarInCappedCuff C₂ (R ∪ P) := by simpa only [union_comm] using hs₂.2.1
  have hpRQ : GM07.IsPlanarInCappedCuff C₃ (R ∪ Q) := by simpa only [union_comm] using hs₃.2.1
  have hnRPQ : ¬ GM07.IsNearPlanar (R ∪ P ∪ Q) := by
    simpa only [union_assoc, union_left_comm, union_comm] using hnPQR
  have h23 := cuff_ne_of_planar_pair_circles hS hab hR hP hQ hRP hRQ hPQ hnRPQ hpRP hpRQ
  exact ⟨C₁, C₂, C₃, hs₁, hs₂, hs₃, h12, h13, h23⟩

end GraphMinor.GM12

/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3ThetaCircles
public import LeanPool.GraphMinor.GM12.Section3SurroundingUnique

/-!
# The third schismatic shape

For the three-branch shape of VII Section 8, used by XII (3.1), page
245, its circles are exactly the three pairs of branches. If those
pairs are near-planar but their whole union is not, the union is
schismatic. In particular, this applies when the pairs surround cuffs
and two of those cuffs are distinct. The distinct-cuff criterion proves
non-near-planarity of the whole union.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Three branches form a schismatic set when all three circles are
near-planar and the full union is not. The circle classification proves
the entire minimal-circle clause of VII Section 8, page 241. -/
theorem isSchismatic_x3_of_nearPlanar_pairs
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {P Q R : Set S} {u v : S} (huv : u ≠ v)
    (hP : IsLineWithEnds P u v) (hQ : IsLineWithEnds Q u v) (hR : IsLineWithEnds R u v)
    (hPQ : P ∩ Q = {u, v}) (hPR : P ∩ R = {u, v}) (hQR : Q ∩ R = {u, v})
    (hnPQ : GM07.IsNearPlanar (P ∪ Q)) (hnPR : GM07.IsNearPlanar (P ∪ R))
    (hnQR : GM07.IsNearPlanar (Q ∪ R))
    (hnot : ¬ GM07.IsNearPlanar (P ∪ Q ∪ R)) : GM07.IsSchismatic (P ∪ Q ∪ R) := by
  refine ⟨Or.inr (Or.inr (Or.inr ⟨P, Q, R, u, v, huv, hP, hQ, hR, hPQ, hPR, hQR, rfl⟩)),
    hnot, ?_⟩
  intro Z hZ hZY
  rcases oArc_eq_pair_of_three_branches huv hP hQ hR hPQ hPR hQR hZ hZY.1 with h | h | h
  · exact h ▸ hnPQ
  · exact h ▸ hnPR
  · exact h ▸ hnQR

/-- Surrounding pairs with two distinct cuff labels supply the third
schismatic shape inside the actual punctured surface of XII (3.1).
No planarity or minimality assertion is included as data. -/
theorem isSchismatic_x3_of_surrounding_pairs
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (hcase : ¬ IsSphere S ∨ 3 ≤ Nat.card ι)
    {P Q R : Set (discComplement Δ)} {u v : discComplement Δ} (huv : u ≠ v)
    (hP : IsLineWithEnds P u v) (hQ : IsLineWithEnds Q u v) (hR : IsLineWithEnds R u v)
    (hPQ : P ∩ Q = {u, v}) (hPR : P ∩ R = {u, v}) (hQR : Q ∩ R = {u, v})
    {i j k : ι} (hij : i ≠ j)
    (hsPQ : GM07.SurroundsCuff (P ∪ Q) (Subtype.val ⁻¹' discBd (Δ i)))
    (hsPR : GM07.SurroundsCuff (P ∪ R) (Subtype.val ⁻¹' discBd (Δ j)))
    (hsQR : GM07.SurroundsCuff (Q ∪ R) (Subtype.val ⁻¹' discBd (Δ k))) :
    GM07.IsSchismatic (P ∪ Q ∪ R) := by
  have hnot := not_isNearPlanar_of_distinct_surrounding_subcircles hS Δ hΔ hdisj hcase hij
    (isOArc_union_of_lines_inter_eq_ends hP hQ hPQ)
    (isOArc_union_of_lines_inter_eq_ends hP hR hPR)
    (X := P ∪ Q ∪ R) subset_union_left
    (union_subset (subset_union_left.trans subset_union_left) subset_union_right) hsPQ hsPR
  exact isSchismatic_x3_of_nearPlanar_pairs huv hP hQ hR hPQ hPR hQR
    (Or.inr ⟨_, hsPQ.1, hsPQ.2.1⟩) (Or.inr ⟨_, hsPR.1, hsPR.2.1⟩)
    (Or.inr ⟨_, hsQR.1, hsQR.2.1⟩) hnot

end GraphMinor.GM12

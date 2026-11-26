/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3CircleObstructions
import LeanPool.GraphMinor.GM12.Section3BarbellCircles

/-!
# The first two-loop obstruction is schismatic

In the Section 8 argument used by XII (3.1), page 245, the two original
loops are near-planar but their joined set is not. Every circle in
that set lies in one original loop, so it is near-planar. This proves
the minimal-circle clause of the schismatic definition and closes the
disjoint-selected-circle case of extraction.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- A first two-loop shape with near-planar loops and a whole set
which is not near-planar is schismatic in VII's exact definition. -/
theorem isSchismatic_x1_of_nearPlanar_loops
    {S : Type*} [TopologicalSpace S] [T2Space S] {F A P : Set S} {a b : S}
    (hF : IsOArc F) (hA : IsOArc A) (hdis : Disjoint F A)
    (hP : IsLineWithEnds P a b) (ha : a ∈ F) (hb : b ∈ A)
    (hPF : P ∩ F = {a}) (hPA : P ∩ A = {b})
    (hnearF : GM07.IsNearPlanar F) (hnearA : GM07.IsNearPlanar A)
    (hnot : ¬ GM07.IsNearPlanar (F ∪ A ∪ P)) : GM07.IsSchismatic (F ∪ A ∪ P) := by
  refine ⟨Or.inr (Or.inl ⟨F, A, P, a, b, hF, hA, hdis, hP, ha, hb, hPF, hPA, rfl⟩), hnot, ?_⟩
  intro Z hZ hZY
  rcases oArc_subset_disjoint_circle_or hF hA hdis hP ha hb hPF hPA hZ hZY.1 with hZF | hZA
  · exact isNearPlanar_mono hZF hnearF
  · exact isNearPlanar_mono hZA hnearA

/-- Disjoint selected circles around distinct cuffs give a schismatic
first two-loop set inside the original connected solid candidate. -/
theorem exists_schismatic_x1_of_disjoint_surrounding_subcircles
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (hcase : ¬ IsSphere S ∨ 3 ≤ Nat.card ι)
    {X F A : Set (discComplement Δ)} (hX : IsSolid X) (hconn : IsConnected X)
    {i j : ι} (hij : i ≠ j) (hF : IsOArc F) (hA : IsOArc A)
    (hFX : F ⊆ X) (hAX : A ⊆ X) (hFA : Disjoint F A)
    (hsi : GM07.SurroundsCuff F (Subtype.val ⁻¹' discBd (Δ i)))
    (hsj : GM07.SurroundsCuff A (Subtype.val ⁻¹' discBd (Δ j))) :
    ∃ Y : Set (discComplement Δ), Y ⊆ X ∧ GM07.IsSchismatic Y := by
  have harc := isArcConnected_of_isConnected_isLocallyArcConnected hconn hX.1
  obtain ⟨P, a, b, hP, hPX, ha, hb, _, hPF, hPA⟩ :=
    exists_joining_line_between_disjoint_circles harc hF hA hFX hAX hFA
  have hnot : ¬ GM07.IsNearPlanar (F ∪ A ∪ P) :=
    not_isNearPlanar_of_distinct_surrounding_subcircles hS Δ hΔ hdisj hcase hij hF hA
      (subset_union_left.trans subset_union_left) (subset_union_right.trans subset_union_left) hsi
        hsj
  refine ⟨F ∪ A ∪ P, union_subset (union_subset hFX hAX) hPX, ?_⟩
  exact isSchismatic_x1_of_nearPlanar_loops hF hA hFA hP ha hb hPF hPA
    (Or.inr ⟨_, hsi.1, hsi.2.1⟩) (Or.inr ⟨_, hsj.1, hsj.2.1⟩) hnot

end GraphMinor.GM12

/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2ThetaDiscs
public import LeanPool.GraphMinor.GM12.Section3PuncturedBoundary
public import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# Enclosing theta discs cover and exhaust the deletions

For the third schismatic shape in VII Section 8, used by XII (3.1),
page 245, the three pair circles surround distinct deleted discs. If
their enclosing discs did not cover the surface, one would be the union
of the other two, contradicting its unique enclosed deletion. Coverage
then puts every deletion in one of these three discs. Its connected
interior avoids each boundary, so meeting a disc means lying wholly
in it. The three cuff labels therefore exhaust the deletion family.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Distinct unique enclosed labels exclude each possible disc-union
relation for a theta, so the three enclosing discs cover the surface. -/
theorem theta_disc_cover_of_distinct_enclosed_labels
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (Δ : ι → Set S)
    {P Q R D₀ D₁ D₂ : Set S} {a b : S}
    (hP : IsLineWithEnds P a b) (hQ : IsLineWithEnds Q a b) (hR : IsLineWithEnds R a b)
    (hPQ : P ∩ Q = {a, b}) (hPR : P ∩ R = {a, b}) (hQR : Q ∩ R = {a, b})
    (hD₀ : IsClosedDisc D₀) (hD₁ : IsClosedDisc D₁) (hD₂ : IsClosedDisc D₂)
    (hb₀ : discBd D₀ = Q ∪ R) (hb₁ : discBd D₁ = R ∪ P) (hb₂ : discBd D₂ = P ∪ Q)
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : Δ i ⊆ D₀) (hj : Δ j ⊆ D₁) (hk : Δ k ⊆ D₂)
    (hone₀ : ∀ l, Δ l ⊆ D₀ → l = i) (hone₁ : ∀ l, Δ l ⊆ D₁ → l = j)
    (hone₂ : ∀ l, Δ l ⊆ D₂ → l = k) : D₀ ∪ D₁ ∪ D₂ = univ := by
  classical
  by_contra hnot
  have hRP : R ∩ P = {a, b} := (inter_comm R P).trans hPR
  rcases theta_disc_union_of_not_cover hS hP hQ hR hPQ hQR hRP hD₀ hD₁ hD₂
    hb₀ hb₁ hb₂ hnot with h | h | h
  · exact hij (hone₀ j (by rw [h]; exact hj.trans subset_union_left)).symm
  · exact hjk (hone₁ k (by rw [h]; exact hk.trans subset_union_left)).symm
  · exact hik (hone₂ i (by rw [h]; exact hi.trans subset_union_left))

/-- A deletion whose interior meets an enclosing disc lies wholly
in that disc, since the enclosing boundary stays in Sigma-star. -/
theorem deleted_disc_subset_of_interior_meets_disc
    {S ι : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    {D : Set S} (hD : IsClosedDisc D) (hbd : discBd D ⊆ discComplement Δ)
    (i : ι) (hmeet : (discInt (Δ i) ∩ D).Nonempty) : Δ i ⊆ D := by
  have hdis : Disjoint (discInt (Δ i)) (discBd D) := by
    apply Set.disjoint_left.mpr
    intro x hxI hxB
    exact hxI.2 (discComplement_inter_disc_subset_boundary hS Δ hΔ i ⟨hbd hxB, hxI.1⟩)
  rcases hD.side (fun x => (hS.2.2 x).isManifoldPoint) (hΔ i).isPreconnected_discInt hdis with hin
    | hout
  · have hcl : closure (discInt (Δ i)) ⊆ D := by
      rw [← hD.isClosed.closure_eq]
      exact closure_mono (hin.trans (discInt_subset D))
    exact (hΔ i).subset_closure_discInt.trans hcl
  · exact (Set.not_nonempty_iff_eq_empty.mpr (Set.disjoint_iff_inter_eq_empty.mp hout) hmeet).elim

/-- Three covering enclosing discs, each with its unique prescribed
deletion, leave no fourth deletion label. -/
theorem deletion_labels_exhaust_of_three_disc_cover
    {S ι : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    {D₀ D₁ D₂ : Set S} (hD₀ : IsClosedDisc D₀) (hD₁ : IsClosedDisc D₁) (hD₂ : IsClosedDisc D₂)
    (hb₀ : discBd D₀ ⊆ discComplement Δ) (hb₁ : discBd D₁ ⊆ discComplement Δ)
    (hb₂ : discBd D₂ ⊆ discComplement Δ) (hcover : D₀ ∪ D₁ ∪ D₂ = univ)
    {i j k : ι} (hone₀ : ∀ l, Δ l ⊆ D₀ → l = i) (hone₁ : ∀ l, Δ l ⊆ D₁ → l = j)
    (hone₂ : ∀ l, Δ l ⊆ D₂ → l = k) : ∀ l, l = i ∨ l = j ∨ l = k := by
  intro l
  obtain ⟨x, hx⟩ := (hΔ l).nonempty_discInt
  have hxD : x ∈ D₀ ∪ D₁ ∪ D₂ := hcover.symm ▸ mem_univ x
  rcases hxD with (hx₀ | hx₁) | hx₂
  · exact Or.inl (hone₀ l (deleted_disc_subset_of_interior_meets_disc hS Δ hΔ hD₀ hb₀ l ⟨x, hx,
      hx₀⟩))
  · exact Or.inr (Or.inl (hone₁ l
      (deleted_disc_subset_of_interior_meets_disc hS Δ hΔ hD₁ hb₁ l ⟨x, hx, hx₁⟩)))
  · exact Or.inr (Or.inr (hone₂ l
      (deleted_disc_subset_of_interior_meets_disc hS Δ hΔ hD₂ hb₂ l ⟨x, hx, hx₂⟩)))

/-- Three distinct labels exhausting a finite family give exactly
three members. -/
theorem card_eq_three_of_exhausting_labels
    {ι : Type*} [Finite ι] {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hex : ∀ l, l = i ∨ l = j ∨ l = k) : Nat.card ι = 3 := by
  have hu : (univ : Set ι) = {i, j, k} := Set.ext fun l =>
    ⟨fun _ => hex l, fun _ => mem_univ l⟩
  have hi : i ∉ ({j, k} : Set ι) := fun h => h.elim hij hik
  rw [← Set.ncard_univ, hu, Set.ncard_insert_of_notMem hi, Set.ncard_pair hjk]

end GraphMinor.GM12

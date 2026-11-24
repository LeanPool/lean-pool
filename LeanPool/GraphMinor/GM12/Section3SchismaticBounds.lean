/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3CircleCount
public import LeanPool.GraphMinor.GM12.Section3LoopSchismaticCount
public import LeanPool.GraphMinor.GM12.Section3ThetaSchismaticCount

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# Conditions (i)--(iv) bound every normal schismatic set

In XII (3.1), page 245, the four geometric conditions handle the four
schismatic shapes of VII Section 8. The circle case uses (i), the two
loop cases use (ii) and (iii), and the theta case uses (iv). The theta
classification proves that its deletion count is three, allowing that
last condition to be applied. All shape and cuff classifications are
proved before this case split.
-/

public section

namespace GraphMinor.GM12

open Set Surface

universe u

/-- Conditions (i)--(iv) of XII (3.1), page 245, force every normal
schismatic set in Sigma-star to meet more than `N` vertices.
The equality argument in condition (iv) just reads the deletion family
as a three-element family in the case where that condition applies. -/
theorem normal_schismatic_vertex_count_gt
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    {t : ℕ} [Nonempty (Fin t)]
    (hS : IsClosedSurface S) (Γ : Drawing S) (Δ : Fin t → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (hcase : ¬ IsSphere S ∨ 3 ≤ t) (hUC : Γ.U ⊆ discComplement Δ) (N : ℕ)
    (hsmall : ∀ F : Set S, Γ.IsNormal F → IsOArc F → F ⊆ discComplement Δ →
      (Γ.V ∩ F).ncard ≤ N →
      ∃ D : Set S, IsClosedDisc D ∧ discBd D = F ∧
        ∀ i j, Δ i ⊆ D → Δ j ⊆ D → i = j)
    (hii : ∀ (A B P D E : Set S) (u v : S),
      Γ.IsNormal (A ∪ B ∪ P) → IsOArc A → IsOArc B → IsLineWithEnds P u v →
      u ∈ A → v ∈ B → P ∩ A = {u} → P ∩ B = {v} →
      A ∪ B ∪ P ⊆ discComplement Δ → IsClosedDisc D → IsClosedDisc E →
      discBd D = A → discBd E = B → Disjoint D E →
      (∃ i, ∀ l, Δ l ⊆ D ↔ l = i) → (∃ j, ∀ l, Δ l ⊆ E ↔ l = j) →
      N < (Γ.V ∩ (A ∪ B ∪ P)).ncard)
    (hiii : ∀ A B D E : Set S,
      Γ.IsNormal (A ∪ B) → IsOArc A → IsOArc B → A ∪ B ⊆ discComplement Δ →
      IsClosedDisc D → IsClosedDisc E → discBd D = A → discBd E = B →
      (D ∩ E).ncard = 1 →
      (∃ i, ∀ l, Δ l ⊆ D ↔ l = i) → (∃ j, ∀ l, Δ l ⊆ E ↔ l = j) →
      N < (Γ.V ∩ (A ∪ B)).ncard)
    (hiv : ∀ ht : t = 3, IsSphere S → ∀ (P D : Fin 3 → Set S) (a b : S), a ≠ b →
      Γ.IsNormal (⋃ i, P i) → (∀ i, IsLineWithEnds (P i) a b) →
      (∀ i j, i ≠ j → P i ∩ P j = {a, b}) → (⋃ i, P i) ⊆ discComplement Δ →
      (∀ i, IsClosedDisc (D i) ∧
        discBd (D i) = ⋃ j : {j // j ≠ i}, P j.val ∧ Δ (Fin.cast ht.symm i) ⊆ D i ∧ ¬ P i ⊆ D i) →
      N < (Γ.V ∩ ⋃ i, P i).ncard)
    {X : Set (discComplement Δ)} (hX : GM07.IsSchismatic X)
    (hn : (drawingInSubspace Γ (discComplement Δ) hUC).IsNormal X) :
    N < ((drawingInSubspace Γ (discComplement Δ) hUC).V ∩ X).ncard := by
  have hcase' : ¬ IsSphere S ∨ 3 ≤ Nat.card (Fin t) := by
    rw [Nat.card_fin]
    exact hcase
  have hshape := hX.1
  rcases hshape with hF | h1 | h2 | h3
  · exact normal_oArc_vertex_count_gt hS Γ Δ hΔ hdisj hUC N hsmall hn hF hX.2.1
  · obtain ⟨A, B, P, a, b, hA, hB, hAB, hP, ha, hb, hPA, hPB, rfl⟩ := h1
    exact two_loop_vertex_count_gt_of_schismatic hS Γ Δ hΔ hdisj hcase' hUC N hii
      hA hB hAB hP ha hb hPA hPB hX hn
  · obtain ⟨A, B, a, hA, hB, hAB, rfl⟩ := h2
    exact meeting_loop_vertex_count_gt_of_schismatic hS Γ Δ hΔ hdisj hcase' hUC N hiii
      hA hB hAB hX hn
  · obtain ⟨P, Q, R, a, b, hab, hP, hQ, hR, hPQ, hPR, hQR, rfl⟩ := h3
    have ht : t = 3 := (Nat.card_fin t).symm.trans
      (sphere_card_three_of_schismatic_theta hS Δ hΔ hdisj hab hP hQ hR hPQ hPR hQR hX).2
    subst t
    exact three_branch_vertex_count_gt_of_schismatic hS Γ Δ hΔ hdisj hUC N (hiv rfl)
      hab hP hQ hR hPQ hPR hQR hX hn

end GraphMinor.GM12

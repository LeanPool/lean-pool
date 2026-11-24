/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3SchismaticBounds
public import LeanPool.GraphMinor.GM12.Section3Extraction

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# The alpha estimate from the four geometric conditions

The reduction of XII (3.1), page 245, to VII (7.5) uses the minimum
over normal schismatic sets. The preceding proofs bound every such
set from conditions (i)--(iv). Extraction and minimum attainment then
give the alpha bound. Candidate existence stays explicit, so this theorem does not claim to
close the numbered result.
-/

public section

namespace GraphMinor.GM12

open Set Surface

universe u

/-- Conditions (i)--(iv) of XII (3.1) give the alpha estimate after
candidate existence.
Every shape, cuff-label and numerical count step is proved. -/
theorem alpha_gt_of_geometric_conditions
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
    (hex : ∃ X, GM07.IsAlphaCandidate (drawingInSubspace Γ (discComplement Δ) hUC) X) :
    N < GM07.alpha (drawingInSubspace Γ (discComplement Δ) hUC) := by
  have hcase' : ¬ IsSphere S ∨ 3 ≤ Nat.card (Fin t) := by
    rw [Nat.card_fin]
    exact hcase
  apply Nat.lt_of_succ_le
  apply alpha_ge_of_solid_extraction hS Δ hΔ hdisj hcase'
    (drawingInSubspace Γ (discComplement Δ) hUC) (N + 1) hex
  intro Y hY hn
  rw [inter_comm Y]
  exact Nat.succ_le_of_lt (normal_schismatic_vertex_count_gt hS Γ Δ hΔ hdisj hcase hUC
    N hsmall hii hiii hiv hY hn)

end GraphMinor.GM12

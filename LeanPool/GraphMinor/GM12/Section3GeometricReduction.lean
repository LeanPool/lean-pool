/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3UniformAlphaReduction
public import LeanPool.GraphMinor.GM12.Section3GeometricAlpha
import LeanPool.GraphMinor.GM12.Section3CandidateExistence

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# Connecting subdrawings from the geometric conditions

Choose the uniform threshold supplied by the fixed surface model and
VII (7.5). Conditions (i)--(iv) give its alpha estimate, condition (v)
gives boundary linkage, and topological feasibility supplies the forest.
Alpha candidates are supplied by the proved one-cuff and two-cuff
constructions. The zero-disc case uses empty connecting subdrawings.
-/

public section

namespace GraphMinor.GM12

open Set Surface

universe u

/-- Graph Minors VII, (7.5), proved unconditionally from `GM07.gm07_theorem_7_5`. -/
theorem gm07_theorem_7_5_proved : GM07Theorem75Statement.{u} :=
  GM07.gm07_theorem_7_5

/-- Graph Minors XII, (3.1), page 245. The geometric conditions
(i)--(vi) give disjoint connected subdrawings for the prescribed
boundary partition, with one threshold for all drawings and disc
placements on the fixed surface. -/
theorem theorem_3_1_proof
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (t z : ℕ) (hcase : ¬ IsSphere S ∨ 3 ≤ t) :
    ∃ N : ℕ, ∀ (Γ : Drawing S) (Δ : Fin t → Set S)
      (_hΔ : ∀ i, IsClosedDisc (Δ i))
      (_hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
      (_havoid : ∀ i, Γ.U ∩ Δ i = Γ.V ∩ discBd (Δ i))
      (p : ℕ) (Zs : Fin p → Set S)
      (_hsmall : ∀ F : Set S, Γ.IsNormal F → IsOArc F → F ⊆ discComplement Δ →
        (Γ.V ∩ F).ncard ≤ N →
        ∃ D : Set S, IsClosedDisc D ∧ discBd D = F ∧
          ∀ i j, Δ i ⊆ D → Δ j ⊆ D → i = j)
      (_hii : ∀ (A B P D E : Set S) (u v : S),
        Γ.IsNormal (A ∪ B ∪ P) → IsOArc A → IsOArc B → IsLineWithEnds P u v →
        u ∈ A → v ∈ B → P ∩ A = {u} → P ∩ B = {v} →
        A ∪ B ∪ P ⊆ discComplement Δ → IsClosedDisc D → IsClosedDisc E →
        discBd D = A → discBd E = B → Disjoint D E →
        (∃ i, ∀ l, Δ l ⊆ D ↔ l = i) → (∃ j, ∀ l, Δ l ⊆ E ↔ l = j) →
        N < (Γ.V ∩ (A ∪ B ∪ P)).ncard)
      (_hiii : ∀ A B D E : Set S,
        Γ.IsNormal (A ∪ B) → IsOArc A → IsOArc B → A ∪ B ⊆ discComplement Δ →
        IsClosedDisc D → IsClosedDisc E → discBd D = A → discBd E = B →
        (D ∩ E).ncard = 1 →
        (∃ i, ∀ l, Δ l ⊆ D ↔ l = i) → (∃ j, ∀ l, Δ l ⊆ E ↔ l = j) →
        N < (Γ.V ∩ (A ∪ B)).ncard)
      (_hiv : ∀ ht : t = 3, IsSphere S → ∀ (P D : Fin 3 → Set S) (a b : S), a ≠ b →
        Γ.IsNormal (⋃ i, P i) → (∀ i, IsLineWithEnds (P i) a b) →
        (∀ i j, i ≠ j → P i ∩ P j = {a, b}) → (⋃ i, P i) ⊆ discComplement Δ →
        (∀ i, IsClosedDisc (D i) ∧
          discBd (D i) = ⋃ j : {j // j ≠ i}, P j.val ∧ Δ (Fin.cast ht.symm i) ⊆ D i ∧ ¬ P i ⊆ D i) →
        N < (Γ.V ∩ ⋃ i, P i).ncard),
      (⋃ j, Zs j) = discBoundaryVertices Γ Δ →
      (∀ i j, i ≠ j → Disjoint (Zs i) (Zs j)) →
      IsTopologicallyFeasible Δ Zs →
      (∀ F : Set S, Γ.IsNormal F → IsOArc F → F ⊆ discComplement Δ →
        ∀ D : Set S, IsClosedDisc D → discBd D = F →
        ∀ i, (∀ j, Δ j ⊆ D ↔ j = i) →
          (Γ.V ∩ discBd (Δ i)).ncard ≤ (Γ.V ∩ F).ncard) →
      (discBoundaryVertices Γ Δ).ncard ≤ z →
      HasConnectingSubdrawings Γ (discBoundaryVertices Γ Δ) Zs := by
  by_cases ht : t = 0
  · subst t
    refine ⟨0, ?_⟩
    intro Γ Δ hΔ hdisj havoid p Zs _ _ _ _ hcover _ _ _ _
    have hZ : discBoundaryVertices Γ Δ = ∅ := by simp [discBoundaryVertices]
    rw [hZ] at hcover ⊢
    exact hasConnectingSubdrawings_of_empty_union Γ Zs hcover
  · let : Nonempty (Fin t) := ⟨⟨0, Nat.pos_of_ne_zero ht⟩⟩
    obtain ⟨N, hN⟩ := exists_uniform_connecting_alpha_threshold hS t z hcase
    refine ⟨N, ?_⟩
    intro Γ Δ hΔ hdisj havoid p Zs hsmall hii hiii hiv hcover hdisZ hfeasible hbound hcount
    have hUC := drawing_support_subset_discComplement hS Γ Δ hΔ hdisj havoid
    have hα := alpha_gt_of_geometric_conditions hS Γ Δ hΔ hdisj hcase hUC N
      hsmall hii hiii hiv
      (exists_alphaCandidate_in_discComplement hS ht hcase Γ Δ hΔ hdisj havoid)
    exact hN Γ Δ hΔ hdisj havoid p Zs hcover hdisZ hfeasible hbound hcount (Nat.le_of_lt hα)

end GraphMinor.GM12

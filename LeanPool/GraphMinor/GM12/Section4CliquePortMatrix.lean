/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4CliquePorts
public import LeanPool.GraphMinor.GM12.Section4HamiltonCrossingWitness

/-!
# Vertex-pair coordinates for the clique ports

The crossing tests for XII (4.5), page 252, use a port coordinate
for each ordered pair of vertices. The edge-port bijection gives
these coordinates for distinct vertices. Give each unused diagonal
entry the coordinate of a non-Hamilton port in the same block.
This preserves the vertex-block order and Hamilton priorities,
without adding any port to the drawing.
-/

public section

namespace GraphMinor.GM12

open Set

/-- Rewrite an ordered clique port configuration as vertex-pair
coordinates for the crossing tests in XII (4.5), page 252. Diagonal
entries reuse a non-Hamilton port and are never edge ends. -/
theorem exists_clique_port_matrix {p : ℕ} (hp : 4 ≤ p)
    (ψ : (Fin (p * (p - 1) / 2) × Bool) ≃ {q : Fin p × Fin p // q.1 ≠ q.2})
    (s : Fin (p * (p - 1) / 2) × Bool → ℝ) (hs : ∀ x, s x ∈ Ioo 0 1)
    (hblocks : ∀ x y, (ψ x).val.1 < (ψ y).val.1 → s x < s y)
    (hpriority : ∀ x y, (ψ x).val.1 = (ψ y).val.1 →
      hamiltonPortPriority (ψ x).val.1 (ψ x).val.2 <
        hamiltonPortPriority (ψ y).val.1 (ψ y).val.2 → s x < s y) :
    ∃ F : Fin p → Fin p → ℝ,
      (∀ v w, F v w ∈ Ioo 0 1) ∧
      (∀ v w i j, v < i → F v w < F i j) ∧
      (∀ v w z, hamiltonPortPriority v w < hamiltonPortPriority v z → F v w < F v z) ∧
      ∀ v w (hvw : v ≠ w), F v w = s (ψ.symm ⟨(v, w), hvw⟩) := by
  classical
  choose τ hτv hτpre hτnext using exists_nonHamilton_neighbor hp
  let ν : Fin p → Fin p → Fin p := fun v w => if v = w then τ v else w
  have hν : ∀ v w, v ≠ ν v w := by
    intro v w
    by_cases hvw : v = w
    · simpa only [ν, hvw, ↓reduceIte] using (hτv w).symm
    · rw [show ν v w = w by simp only [ν, hvw, ↓reduceIte]]
      exact hvw
  let P : Fin p → Fin p → Fin (p * (p - 1) / 2) × Bool :=
    fun v w => ψ.symm ⟨(v, ν v w), hν v w⟩
  have howner : ∀ v w, (ψ (P v w)).val.1 = v := fun v w =>
    congrArg (fun q : {q : Fin p × Fin p // q.1 ≠ q.2} => q.val.1)
      (ψ.apply_symm_apply ⟨(v, ν v w), hν v w⟩)
  have hneighbor : ∀ v w, (ψ (P v w)).val.2 = ν v w := fun v w =>
    congrArg (fun q : {q : Fin p × Fin p // q.1 ≠ q.2} => q.val.2)
      (ψ.apply_symm_apply ⟨(v, ν v w), hν v w⟩)
  have hprio : ∀ v w, hamiltonPortPriority v (ν v w) = hamiltonPortPriority v w := by
    intro v w
    by_cases hvw : v = w
    · subst w
      simp only [ν, ↓reduceIte]
      rw [hamiltonPortPriority_other (hτpre v) (hτnext v),
        hamiltonPortPriority_other
          (Ne.symm (finRotate_predecessor_ne_self_of_two_le (by omega : 2 ≤ p) v))
          (Ne.symm (finRotate_ne_self_of_two_le (by omega : 2 ≤ p) v))]
    · simp only [ν, hvw, ↓reduceIte]
  refine ⟨fun v w => s (P v w), fun v w => hs _, ?_, ?_, ?_⟩
  · intro v w i j hvi
    exact hblocks _ _ (by simpa only [howner] using hvi)
  · intro v w z hwz
    apply hpriority (P v w) (P v z) (by rw [howner, howner])
    simpa only [howner, hneighbor, hprio] using hwz
  · intro v w hvw
    simp only [P, ν, hvw, ↓reduceIte]

end GraphMinor.GM12

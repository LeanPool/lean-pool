/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# The finite projection argument underlying the Pauli bound

Finite families of symmetric idempotent lifts with zero double occupancy satisfy a
projection-sum bound. The operator relations are explicit hypotheses.
-/

public section

namespace LiebThirring

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*} [Fintype ι]

/-- Symmetric idempotent lifts with zero double occupancy have a bounded sum
of squared projected norms. All operator relations are explicit inputs to this
abstract lemma. -/
theorem sum_norm_sq_le_of_projection_relations (P : ι → E →L[ℂ] E) (ψ : E)
    (hsym : ∀ i x y, inner ℂ (P i x) y = inner ℂ x (P i y))
    (hid : ∀ i, P i (P i ψ) = P i ψ)
    (hzero : ∀ i j, i ≠ j → P i (P j ψ) = 0) :
    ∑ i : ι, ‖P i ψ‖ ^ 2 ≤ ‖ψ‖ ^ 2 := by
  classical
  have horth (i j : ι) (hij : i ≠ j) : inner ℂ (P i ψ) (P j ψ) = 0 := by
    rw [hsym, hzero i j hij, inner_zero_right]
  have hdiag (i : ι) : inner ℂ ψ (P i ψ) = inner ℂ (P i ψ) (P i ψ) := by
    rw [hsym, hid]
  have hv : ‖∑ i : ι, P i ψ‖ ^ 2 = ∑ i : ι, ‖P i ψ‖ ^ 2 := by
    have hinner : inner ℂ (∑ i : ι, P i ψ) (∑ i : ι, P i ψ) =
        ∑ i : ι, inner ℂ (P i ψ) (P i ψ) := by
      rw [sum_inner]
      apply Finset.sum_congr rfl
      intro i _
      rw [inner_sum]
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact horth i j hji.symm
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hinner]
    simp only [map_sum, inner_self_eq_norm_sq]
  have hψv : RCLike.re (inner ℂ ψ (∑ i : ι, P i ψ)) = ∑ i : ι, ‖P i ψ‖ ^ 2 := by
    rw [inner_sum]
    simp only [hdiag, map_sum, inner_self_eq_norm_sq]
  have hnorm := norm_sub_sq (𝕜 := ℂ) ψ (∑ i : ι, P i ψ)
  rw [hv, hψv] at hnorm
  linarith only [hnorm, sq_nonneg ‖ψ - ∑ i : ι, P i ψ‖]

/-- Equal projection norms turn the projection sum estimate into an occupation
estimate. This is abstract infrastructure, not Pauli occupation on the state space. -/
theorem card_mul_norm_sq_le_of_projection_relations (P : ι → E →L[ℂ] E) (ψ : E)
    (hsym : ∀ i x y, inner ℂ (P i x) y = inner ℂ x (P i y))
    (hid : ∀ i, P i (P i ψ) = P i ψ)
    (hzero : ∀ i j, i ≠ j → P i (P j ψ) = 0)
    (i : ι) (hequal : ∀ j, ‖P j ψ‖ = ‖P i ψ‖) :
    (Fintype.card ι : ℝ) * ‖P i ψ‖ ^ 2 ≤ ‖ψ‖ ^ 2 := by
  have h := sum_norm_sq_le_of_projection_relations P ψ hsym hid hzero
  simpa only [hequal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h

end

end LiebThirring

end

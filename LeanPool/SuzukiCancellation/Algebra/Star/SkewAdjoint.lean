/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import Mathlib.Algebra.Star.Module
public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Basic.Real.Star

/-!
# Algebraic closure of skew-adjoint elements

Real scalar multiples and finite sums preserve the skew-adjoint identity.

## Main results

* `TrotterError.star_smul_of_skew`.
* `TrotterError.sum_skewAdjoint`.
-/

@[expose] public section

namespace TrotterError

open scoped BigOperators

/-- `star (c • A) = -(c • A)` whenever `star A = -A` and `c` is real. -/
lemma star_smul_of_skew {𝔸 : Type*} [Star 𝔸] [AddGroup 𝔸] [DistribSMul ℝ 𝔸] [StarModule ℝ 𝔸]
    {A : 𝔸} {c : ℝ} (hA : star A = -A) :
    star (c • A) = -(c • A) := by
  rw [StarModule.star_smul, hA, star_trivial, smul_neg]

/-- A sum of anti-Hermitian elements is anti-Hermitian. -/
lemma sum_skewAdjoint {𝔸 : Type*} [AddCommGroup 𝔸] [StarAddMonoid 𝔸] {ι : Type*} [Fintype ι]
    (H : ι → 𝔸) (h : ∀ i, star (H i) = -(H i)) :
    star (∑ i : ι, H i) = -(∑ i : ι, H i) := by
  calc
    star (∑ i : ι, H i) = ∑ i : ι, star (H i) := star_sum Finset.univ H
    _ = ∑ i : ι, -(H i) := by simp [h]
    _ = -(∑ i : ι, H i) := by simp

end TrotterError

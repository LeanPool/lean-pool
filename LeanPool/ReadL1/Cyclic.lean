/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

-- Modified for Lean Pool.

module

public import LeanPool.ReadL1.Defs

/-!
# From cyclic vectors to no invariant subspace

A closed subspace `W` that `T` maps into itself, and that contains a vector `x`, contains every
`Tⁿ x`, hence their span, hence (being closed) the closure of that span. So if some vector `x₀`
has a dense orbit span, and `x₀` lies in the closed orbit span of every nonzero vector, then any
nonzero closed invariant subspace contains `x₀` and therefore everything: there is no nontrivial
one.

This is the last step of Read's argument as Śliwa writes it (W. Śliwa, Rocky Mountain J. Math. 40
(2010), proof of Theorem 7, p. 640), and Noel's Corollary 2.2.7 (J. A. Noel, *The Invariant
Subspace Problem*, BSc thesis, Thompson Rivers University, 2011).
-/

@[expose] public section

namespace ReadL1

open InvariantSubspaceProblem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The span of the orbit `x, T x, T² x, …`. -/
def orbitSpan (T : E →L[ℂ] E) (x : E) : Submodule ℂ E :=
  Submodule.span ℂ (Set.range fun n : ℕ ↦ (T ^ n) x)

/-- A subspace that `T` maps into itself contains `Tⁿ x` whenever it contains `x`. -/
lemma pow_apply_mem {T : E →L[ℂ] E} {W : Submodule ℂ E} (hW : W.map T.toLinearMap ≤ W)
    {x : E} (hx : x ∈ W) (n : ℕ) : (T ^ n) x ∈ W := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp]
    exact hW ⟨_, ih, rfl⟩

/-- A closed invariant subspace containing `x` contains the closure of its orbit span. -/
lemma topologicalClosure_orbitSpan_le {T : E →L[ℂ] E} {W : Submodule ℂ E}
    (hW : W.map T.toLinearMap ≤ W) (hWc : IsClosed (W : Set E)) {x : E} (hx : x ∈ W) :
    (orbitSpan T x).topologicalClosure ≤ W :=
  Submodule.topologicalClosure_minimal _
    (Submodule.span_le.2 (Set.range_subset_iff.2 fun n ↦ pow_apply_mem hW hx n)) hWc

/-- **No invariant subspace from one universally reachable cyclic vector.** If `x₀` has a dense
orbit span, and lies in the closed orbit span of every nonzero vector, then `T` has no nontrivial
closed invariant subspace. -/
theorem isEmpty_closedInvariantSubspace_of_cyclic (T : E →L[ℂ] E) (x₀ : E)
    (hdense : (orbitSpan T x₀).topologicalClosure = ⊤)
    (hreach : ∀ x : E, x ≠ 0 → x₀ ∈ (orbitSpan T x).topologicalClosure) :
    IsEmpty (ClosedInvariantSubspace T) := by
  refine ⟨fun W ↦ W.ne_top ?_⟩
  -- `W` contains a nonzero vector `x`.
  obtain ⟨x, hxW, hx0⟩ := (Submodule.ne_bot_iff _).1 W.ne_bot
  -- So it contains the closed orbit span of `x`, hence `x₀`, hence the closed orbit span of
  -- `x₀`, which is everything.
  have hx₀ : x₀ ∈ W.toSubspace :=
    topologicalClosure_orbitSpan_le W.is_fixed W.is_closed hxW (hreach x hx0)
  exact eq_top_iff.2 (hdense ▸ topologicalClosure_orbitSpan_le W.is_fixed W.is_closed hx₀)

end ReadL1

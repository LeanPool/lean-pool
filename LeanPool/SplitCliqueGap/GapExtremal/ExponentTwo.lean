/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GapExtremal.ExactOrder

/-!
# The split-graph gap at bounded order

The exact-order construction also gives the `n ^ (2 - ε)` bound under a vertex budget of `n`.
-/

@[expose] public section

namespace GapExtremal

/-- For every `ε > 0`, split graphs with at most `n` vertices have gap at least
`c * n ^ (2 - ε)` for some positive `c` and every sufficiently large `n`. -/
theorem exponent_two {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ (V' : Type) (_ : Fintype V') (_ : DecidableEq V') (G' : SimpleGraph V'),
        Fintype.card V' ≤ n ∧ IsSplit G' ∧ c * (n : ℝ) ^ (2 - ε) ≤ gap G' := by
  obtain ⟨c, hc, N, hN⟩ := exponent_two_exact hε
  refine ⟨c, hc, N, fun n hn => ?_⟩
  obtain ⟨V, fV, dV, G, hcard, hsplit, _, hgap⟩ := hN n hn
  exact ⟨V, fV, dV, G, hcard.le, hsplit, hgap⟩

end GapExtremal

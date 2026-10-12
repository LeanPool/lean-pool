/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Defs.State
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Antisymmetric states

Simultaneous spatial and spin permutation with the fermionic sign.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

/-- Fermionic sign under simultaneous permutation of spatial and spin coordinates. -/
@[expose] def antisymmetric {N q : ℕ} (ψ : State N q) : Prop :=
  ∀ σ : Equiv.Perm (Fin N), ∀ᵐ x ∂(volume : Measure (Configuration N)),
    ∀ s : SpinLabels N q,
      ψ (permutePositions σ x) (permuteSpins σ s) =
        (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * ψ x s

end LiebThirring

end

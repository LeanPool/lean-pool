/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselUniformEnergyStep

/-!
# Coverage of nonnegative time by uniform continuation intervals

A fixed positive continuation step covers every finite nonnegative time
after finitely many restarts.
-/

public section

noncomputable section

namespace CKN.Leray

/-- Every nonnegative time lies in a closed interval between consecutive
multiples of a fixed positive step. -/
theorem regularisedUniformStepGrid_cover
    (δ t : ℝ) (hδ : 0 < δ) (ht : 0 ≤ t) :
    ∃ n : ℕ, (n : ℝ) * δ ≤ t ∧ t ≤ ((n + 1 : ℕ) : ℝ) * δ := by
  let n : ℕ := ⌊t / δ⌋₊
  have hq : 0 ≤ t / δ := div_nonneg ht hδ.le
  have hfloor : (n : ℝ) ≤ t / δ := Nat.floor_le hq
  have hnext : t / δ < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨n, (le_div_iff₀ hδ).mp hfloor, ?_⟩
  have hstrict : t < ((n : ℝ) + 1) * δ :=
    (div_lt_iff₀ hδ).mp hnext
  simpa only [Nat.cast_add, Nat.cast_one] using hstrict.le

end CKN.Leray

end

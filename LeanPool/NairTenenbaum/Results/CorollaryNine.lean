/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Hooley.HooleyAverageReductions
public import LeanPool.NairTenenbaum.Hooley.HooleyTotientMean

/-! # Corollary 9: averaged prime counts in arithmetic progressions

The estimate is uniform in the dyadic cutoff and in the nonzero residue
with `|a|≤x`, the range inherited from Corollary 8. In particular it applies
eventually for every fixed nonzero residue.
-/

@[expose] public section

namespace NairTenenbaum

open Real

/-- The statement of Corollary 9, with the scope recorded in the source alignment. -/
def CorollaryNine : Prop :=
  ∀ ε η : ℝ, 0 < ε → ε < 1 → Real.sqrt 2 < η →
    ∃ x₀ C : ℝ, 1 < x₀ ∧ 0 < C ∧ ∀ a : ℤ, a ≠ 0 → ∀ K x y : ℝ,
      0 < K → x₀ < x → (a.natAbs : ℝ) ≤ x → x ^ ε ≤ y → y ≤ x →
        dyadicPrimeProgressionSum K a x y ≤ C * (y / Real.log x * hooleySubexponential η x)

theorem corollaryNine : CorollaryNine := by
  intro ε η hε _ hη
  obtain ⟨x₁, A, _, hA, HA⟩ := exists_dyadicPrimeProgressionSum_root_bound hε
  obtain ⟨x₂, B, hx₂, hB, HB⟩ := exists_totient_hooleyRootSum_sharp_bound hη
  refine ⟨max x₁ x₂, A * B, hx₂.trans_le (le_max_right _ _), mul_pos hA hB,
    fun a ha K x y hK hx hax hy hyx => ?_⟩
  have hx₂' := (le_max_right x₁ x₂).trans_lt hx
  have hy₀ : 0 ≤ y := (Real.rpow_nonneg (by linarith : 0 ≤ x) ε).trans hy
  apply (HA a ha K x y hK ((le_max_left _ _).trans_lt hx) hax hy hyx).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (HB x hx₂' a.natAbs (Int.natAbs_ne_zero.mpr ha) hax y hy₀) hA.le

end NairTenenbaum

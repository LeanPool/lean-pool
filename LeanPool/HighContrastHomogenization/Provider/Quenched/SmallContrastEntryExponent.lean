/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRecursionAssembly

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastEntryExponent

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The entry exponent

The only hypothesis of `hrec_final_sharp_at_jb_src` that is not an algebraic identity is the
entry-exponent condition

  `3 c_w u_n² ≤ δ (3^{-α})^n`,

where `u_n` is the source group of the weak base at the shifted generation
`n` (absolute generation `N₀ + n`).  The source group carries the bad-event
moment at the depth `Δ = N₀ + n + G - 1 - s_K`, so it decays *jointly* in the
entry delay `N₀` and in `n`:

  `u_n² ≤ C_src · 3^{-(N₀ + n)}`.

This file records the consequence: **any** `α ≤ 1` is admissible for the
source leg, the whole condition being met by a delay
`N₀ ≥ log₃(3 c_w C_src / δ)`.  Since the iteration decay separately caps
`α ≤ 1/2`, the exponent is fixed at

  `α := 1/2`,

and the entry threshold is the explicit delay below — law-polynomial,
because `C_src` is polynomial in `2 + aspectRatio 𝐄 · K` and the delay enters
only through its logarithm.
-/

namespace HCPolySupport.HighContrast.Quenched

noncomputable section

/-! ## The corrected exponents

`α = 1/2` is not admissible: the rooted drop slot of
`weakValueSharpMajorant_le_three_group_summed_at_level`
carries the weight `3^{-(1/2 - ρ/2)j}`, and `exists_account_one_step_entry_of_block_at_level`
binds `g ≤ ρ < 1`, so that weight's rate is always `< 1/2`.  The consistent
choice pairs the two exponents:

  `ρ := (1 + g)/2`,   `α := (1 - g)/4`,

for which the rooted-drop rate `1/2 - ρ/2` and the window-tail rate
`(1 - ρ)/2` are *both* exactly `α`. -/

/-- The corrected weak-cap load exponent `ρ = (1+g)/2`. -/
@[expose]
def contrastRho (g : ℝ) : ℝ := (1 + g) / 2

/-- The corrected recursion rate `α = (1-g)/4`. -/
@[expose]
def contrastAlpha (g : ℝ) : ℝ := (1 - g) / 4

theorem contrastRho_pos {g : ℝ} (hg0 : 0 ≤ g) : 0 < contrastRho g := by
  rw [contrastRho]; linarith only [hg0]

theorem le_contrastRho {g : ℝ} (hg1 : g < 1) : g ≤ contrastRho g := by
  rw [contrastRho]; linarith only [hg1]

theorem contrastRho_lt_one {g : ℝ} (hg1 : g < 1) : contrastRho g < 1 := by
  rw [contrastRho]; linarith only [hg1]

theorem contrastAlpha_pos {g : ℝ} (hg1 : g < 1) : 0 < contrastAlpha g := by
  rw [contrastAlpha]; linarith only [hg1]

theorem contrastAlpha_le_half {g : ℝ} (hg0 : 0 ≤ g) : contrastAlpha g ≤ 1 / 2 := by
  rw [contrastAlpha]; linarith only [hg0]

/-- **The rooted-drop weight of the weak value is exactly the recursion
rate.** -/
theorem rooted_weight_eq_contrastAlpha (g : ℝ) :
    1 / 2 - contrastRho g / 2 = contrastAlpha g := by
  rw [contrastRho, contrastAlpha]; ring

/-! ## The drop-history sum is monotone in its ratio -/

/-- **Monotonicity of the drop-history sum in the ratio.**  This is what lets a
drop sum produced at one geometric rate be read at the (smaller) recursion
rate: `iterationDropSum` is increasing in `r`, so a conversion at rate `r₁`
feeds a recursion at any rate `r₂ ≥ r₁`. -/
theorem iterationDropSum_mono_r {F : ℕ → ℝ}
    (hFmono : ∀ p q : ℕ, p ≤ q → F q ≤ F p) {r₁ r₂ : ℝ}
    (hr1 : 0 ≤ r₁) (hr : r₁ ≤ r₂) (n : ℕ) :
    iterationDropSum r₁ F n ≤ iterationDropSum r₂ F n := by
  refine Finset.sum_le_sum fun k _ => ?_
  refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr1 hr _) ?_
  exact sub_nonneg.mpr (hFmono _ _ (Nat.sub_le _ _))

end

end HCPolySupport.HighContrast.Quenched

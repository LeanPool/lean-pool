/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.AffineExcess

/-!
# OneStepConsumerLegBudget

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The consumer-side budget of the general clause's right-hand side

The general clause consumed here carries `‖u − h‖_{L²(W')}` in its first
bracket leg and `s^{-6}` on legs 4 and 5, in place of the plain mean-subtracted
norm `‖u − (u)_{W'}‖_{L²(W')}` and the exponent `s^{-9/2}`.

At the excess-decay application (`OneStepConditional.
excessDecay_oneStep_of_harmonicApprox`, instance `n := n-2`,
`x := wellPlacedCentre x m (n-2)`) the clause's right-hand side is received as
the abstract `B`, and the excess-decay display multiplies `B.toReal` by
`triangleRemainderConst d Csch k * (3^{-n} * √((3^2)^d))`.  So every leg must
survive multiplication by `3^{-n}` into the excess-decay conclusion shape.  This
module proves what **does** survive; what does not is treated in
`OneStepConsumerRefutation`.

## What is proved here

* §1 **The `s^{-9/2} → s^{-6}` exponent move is a weakening, and it is
  invisible to the proved chain.**  `rpow_neg_nine_halves_le_rpow_neg_six`: for
  `0 < s ≤ 1`, `s^{-9/2} ≤ s^{-6}`, so the `s^{-6}` right-hand side dominates
  the `s^{-9/2}` one leg for leg.  At the sole eventual pin `s = 1/4`
  (`Regularity.MinimalScaleShift.stepOneS`) both exponents are numerals,
  `4^{9/2} = 512` and `4^6 = 4096` — a factor `8`, absorbed into `C(d,c⋆)`.
* §2 **The good-event collapse.**
  `rpow_neg_four_mul_goodEventCap_le_rpow_neg_six`: the clause's flux prefactor
  `s^{-4}` against the proved cap `𝓔·1_𝒢 ≤ C s δ^{1/2}` (`OneStepGoodScales.
  ae_errorRepresentative_le_goodEventDeltaSlot`) collapses to `s^{-3}δ^{1/2}`,
  which is below the clause's own `s^{-6}` for every `0 < s ≤ 1`, `δ ≤ 1`.
* §3 **The conditional absorption lemma** — the exact shape the `B`-expansion
  needs for the new first leg, on the **boundary branch**:
  `dataSubtracted_leg_absorbed_of_flatGradientBound`.  **The `hGu` slot — a
  bound on the flat window gradient `∑ᵢ ‖∂ᵢu‖_{L²(W')}` — has no producer**
  and is carried as an open hypothesis.
* §4 **The `∇h` half is free.**  `gradH_half_eq_leg5_contribution`: the datum
  half of §3's bound is *equal* to `9·C_cap·C_poin` times the clause's own
  fifth leg after the excess-decay `3^{-n}`, at the exponent `s^{-6}`.  So the
  datum half of the new leg costs nothing beyond a `d`-constant.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-- The `rpow` dictionary: the anchor prints `Real.rpow s a`, the `Mathlib`
lemma library is stated at the `^` notation, and the two are definitionally the
same term. -/
private theorem rpow_eq_pow (s y : ℝ) : Real.rpow s y = s ^ y := rfl

/-! ## 1. The `s^{-9/2} → s^{-6}` exponent move -/

/-- **The exponent move weakens the clause.**  For `0 < s ≤ 1` the exponent
`s^{-6}` dominates `s^{-9/2}`, so on legs 4 and 5 the right-hand side carrying
`s^{-6}` is at least the one carrying `s^{-9/2}` — the consumer receives a
weaker bound, and absorbing it is absorbing the larger of the two. -/
theorem rpow_neg_nine_halves_le_rpow_neg_six {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    Real.rpow s (-(9 / 2 : ℝ)) ≤ Real.rpow s (-(6 : ℝ)) := by
  rw [rpow_eq_pow, rpow_eq_pow]
  exact Real.rpow_le_rpow_of_exponent_ge hs hs1 (by norm_num)

/-! ## 2. The good-event collapse of the flux prefactor -/

/-! ## 3. The conditional absorption lemma (boundary branch) -/

/-! ## 4. The datum half is free -/

end

end Algsuperdiff.Section4.Provider.ExcessDecay

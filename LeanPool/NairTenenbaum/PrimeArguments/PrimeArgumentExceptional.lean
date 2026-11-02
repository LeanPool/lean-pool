/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Contributions.ValueBoundContributions

/-! # Power savings with the growth margin of Theorem 3

The admissibility exponent `εδ/3` leaves a smaller positive gap than the
progression bound requires. Keeping that gap explicit avoids strengthening
the hypotheses on the arithmetic function.
-/

@[expose] public section

namespace NairTenenbaum

theorem PolynomialSystem.primePowerContribution_primeArgument_power_saving {k r g : ℕ}
    (P : PolynomialSystem k r) (hdeg : P.total.natDegree = g)
    {A B σ ε c x y : ℝ} {F : ArithmeticMap k} (hF : Admissible A B σ F)
    (hB : 0 ≤ B) (hσ : 0 ≤ σ) (hε : 0 ≤ ε) (hx : 1 ≤ x)
    (hmargin : c * σ ≤ 17 * (g : ℝ) * ε / 24) {a b : ℤ} (hab : a ≤ b)
    (hlevel : (x ^ ((g : ℝ) * ε / 2)) ^ 4 ≤ (b : ℝ) - a)
    (hlen : (b : ℝ) - a ≤ 2 * y)
    (hvalue : ∀ t ∈ Finset.Ioc a b, ((P.total.eval t).natAbs : ℝ) ≤ x ^ c) :
    P.primePowerContribution F (x ^ ((g : ℝ) * ε / 2)) a b ≤
      (8 * (g : ℝ) * (max g (P.badDiscriminant ^ 3) : ℕ) * B) *
        y * x ^ (-((g : ℝ) * ε / 24)) * F 1 := by
  apply P.primePowerContribution_power_saving_of_margin hdeg hF hB hσ hε hx _ hab hlevel hlen hvalue
  nlinarith [mul_nonneg (Nat.cast_nonneg g : (0 : ℝ) ≤ _) hε]

/-- The same growth margin pays the smooth-divisor saving. -/
theorem PolynomialSystem.smoothDivisorContribution_primeArgument_power_saving {k r g : ℕ}
    (P : PolynomialSystem k r) (hdeg : P.total.natDegree = g)
    {A B σ ε c x y : ℝ} {F : ArithmeticMap k} (hF : Admissible A B σ F)
    (hB : 0 ≤ B) (hσ : 0 ≤ σ) (hx : 1 ≤ x)
    (hmargin : c * σ ≤ 17 * (g : ℝ) * ε / 24) (s : Finset ℕ) (N : ℕ+)
    {a b : ℤ} (hab : a ≤ b) (hlevel : (N : ℝ) ≤ (b : ℝ) - a)
    (hlen : (b : ℝ) - a ≤ 2 * y)
    (hvalue : ∀ t ∈ Finset.Ioc a b, ((P.total.eval t).natAbs : ℝ) ≤ x ^ c) :
    P.smoothDivisorContribution F s N (x ^ (3 * (g : ℝ) * ε / 2)) a b ≤
      (4 * smoothDivisorBound g P.badDiscriminant s * B) *
        y * x ^ (-((g : ℝ) * ε / 24)) * F 1 := by
  exact P.smoothDivisorContribution_power_saving_of_margin hdeg hF hB hσ hx
    (by linarith) s N hab hlevel hlen hvalue

end NairTenenbaum

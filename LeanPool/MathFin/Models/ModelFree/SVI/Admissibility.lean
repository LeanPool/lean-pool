/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.SVI.Reduction

/-! # Positive variance as a polynomial gate

Part of the SVI polynomial-sign certificate (#174).

`varianceGate`, a condition on signs of polynomials in the parameters, is equivalent to the SVI
variance being positive at every log-strike (`varianceGate_iff`), for `σ > 0`, `b ≥ 0`,
`ρ² ≤ 1`. The cases `b = 0` and `ρ = ±1` are included.

## Main definitions

* `varianceGate`: the polynomial positive-variance gate, `b = 0 ∧ 0 < a` or
  `0 < b ∧ (0 ≤ a ∨ a² < b²σ²(1 − ρ²))`.

## Main results

* `quadratic_pos_iff`: for `α, γ ≥ 0` with `α + γ > 0`, `αt² + 2at + γ > 0` for all `t > 0` iff
  `0 ≤ a` or `a² < αγ`.
* `variance_pos_iff_A_pos`: for `σ > 0`, the SVI variance is positive at every log-strike iff `A`
  is positive at every `t > 0`.
* `varianceGate_iff`: for `σ > 0`, `b ≥ 0` and `ρ² ≤ 1`, `varianceGate` holds iff the variance is
  positive at every log-strike.

## Tags

positive variance, raw SVI, polynomial sign gate, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI

/-- Positivity of a quadratic on the open positive half-line. The strict
sum condition permits either endpoint coefficient to vanish. -/
theorem quadratic_pos_iff (alpha gamma a : ℝ) (ha : 0 ≤ alpha) (hg : 0 ≤ gamma)
    (hs : 0 < alpha + gamma) :
    (∀ t : ℝ, 0 < t → 0 < alpha*t^2 + 2*a*t + gamma) ↔
      0 ≤ a ∨ a^2 < alpha*gamma := by
  constructor
  · intro h
    by_cases hapos : 0 ≤ a
    · exact Or.inl hapos
    have haneg : a < 0 := lt_of_not_ge hapos
    have halpha : 0 < alpha := by
      by_contra hn
      have he : alpha = 0 := le_antisymm (le_of_not_gt hn) ha
      subst alpha
      have ht : 0 < (gamma + 1) / (-2*a) := div_pos (by linarith) (by nlinarith)
      have hh := h _ ht
      have hc : 2*a*((gamma+1)/(-2*a)) = -(gamma+1) := by
        field_simp [ne_of_lt haneg]
      rw [zero_mul, zero_add, hc] at hh
      linarith
    have ht : 0 < -a/alpha := div_pos (neg_pos.mpr haneg) halpha
    have hh := h _ ht
    have hm := mul_pos halpha hh
    have he : alpha*(alpha*(-a/alpha)^2 + 2*a*(-a/alpha) + gamma) =
        alpha*gamma-a^2 := by
      field_simp
      ring
    rw [he] at hm
    exact Or.inr (by linarith)
  · rintro (hapos | hdisc) t ht
    · have hsum : 0 < alpha*t^2 + gamma := by
        by_cases hzero : alpha = 0
        · simp only [hzero, zero_mul, zero_add]
          linarith
        · have : 0 < alpha := lt_of_le_of_ne ha (Ne.symm hzero)
          positivity
      have : 0 ≤ 2*a*t := by positivity
      linarith
    · have halpha : 0 < alpha := by
        by_contra hn
        have hz : alpha = 0 := le_antisymm (le_of_not_gt hn) ha
        rw [hz, zero_mul] at hdisc
        nlinarith [sq_nonneg a]
      by_contra hn
      have hm := mul_nonpos_of_nonneg_of_nonpos ha (le_of_not_gt hn)
      nlinarith [sq_nonneg (alpha*t+a)]

/-- The entirely polynomial positive-variance gate from condition (A). -/
def varianceGate (p : Params) : Prop :=
  (p.b = 0 ∧ 0 < p.a) ∨
    (0 < p.b ∧ (0 ≤ p.a ∨ p.a^2 < p.b^2*p.sigma^2*(1-p.rho^2)))

theorem variance_pos_iff_A_pos (p : Params) (hs : 0 < p.sigma) :
    (∀ k : ℝ, 0 < variance p k) ↔ (∀ t : ℝ, 0 < t → 0 < A p t) := by
  constructor
  · intro h t ht
    have hh := h (strike p t)
    rw [variance_at_strike p hs t ht] at hh
    exact (div_pos_iff.mp hh).resolve_right (by intro hn; linarith [hn.2]) |>.1
  · intro h k
    obtain ⟨t, ht, rfl⟩ := strike_surjective p hs k
    rw [variance_at_strike p hs t ht]
    exact div_pos (h t ht) (by positivity)

/-- Exact admissibility, including b=0 and rho=±1 with a=0. -/
theorem varianceGate_iff (p : Params) (hs : 0 < p.sigma) (hb : 0 ≤ p.b)
    (hr : 0 ≤ 1 - p.rho ^ 2) :
    varianceGate p ↔ ∀ k : ℝ, 0 < variance p k := by
  by_cases hb0 : p.b = 0
  · simp [varianceGate, variance, hb0]
  have hbpos : 0 < p.b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hrp : 0 ≤ 1+p.rho := by nlinarith [sq_nonneg (p.rho+1)]
  have hrm : 0 ≤ 1-p.rho := by nlinarith [sq_nonneg (p.rho-1)]
  rw [variance_pos_iff_A_pos p hs]
  have hq := quadratic_pos_iff (p.b*p.sigma*(1+p.rho))
    (p.b*p.sigma*(1-p.rho)) p.a (by positivity) (by positivity)
    (by nlinarith [mul_pos hbpos hs])
  have he : p.b*p.sigma*(1+p.rho)*(p.b*p.sigma*(1-p.rho)) =
      p.b^2*p.sigma^2*(1-p.rho^2) := by ring
  rw [he] at hq
  simpa [varianceGate, hb0, hbpos, A] using hq.symm

end SVI
end MathFin

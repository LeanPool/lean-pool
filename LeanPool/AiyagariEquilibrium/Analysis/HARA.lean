/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Analysis.RelativeRiskAversion
public import LeanPool.AiyagariEquilibrium.Models.CRRA

/-!
# HARA utility

Hyperbolic absolute risk aversion: absolute risk tolerance `-u' / u''` is affine in consumption.
Toda (2021) shows HARA is NECESSARY for the consumption function to be concave under regularity
conditions, so it is the class in which Carroll and Kimball (1996) -- and hence Light's
uniqueness argument -- can possibly hold.

## The definition

Stating "risk tolerance is affine" needs second derivatives. Since risk tolerance `a + c` scaled
by `1/γ` integrates to a shifted CRRA, the family can instead be given by its members, which is
derivative-free and is what every proof below actually uses:

  `u c = k · (a + c) ^ (1 - γ) / (1 - γ) + l`,  and the `γ = 1` logarithm,

with `k > 0`. This is the `b ≠ 0` branch of HARA -- the one that contains CRRA, and the one
macroeconomics uses. The quadratic branch (`b < 0`) is excluded because it satiates, and that
exclusion is now a theorem rather than a remark: `Models.Quadratic.no_incomeFluctuation_quadUtility`
shows no economy in this development can have quadratic utility, for any bliss point, since the
structure asks for monotone utility on the whole of `dom` and a quadratic falls beyond its bliss
point. `Models.Quadratic` also records what the branch would give if it could be hosted — Hall's
certainty equivalence, the aggregator being the plain weighted mean.

CARA (`b = 0`) is NOT excluded, and an earlier version of this docstring was wrong about why it
might be: `u c = -exp (-α c) / α` is bounded above by `0` and equals `-1/α` at zero consumption,
so a capped model admits it -- `Models.IncomeFluctuationCARA.caraWitness` is one. What CARA does
not have is Light's condition, since relative risk aversion `α c` is unbounded
(`not_monotoneOn_mul_deriv_caraUtility`). It is covered separately because its Carroll--Kimball
step needs a different aggregator, the soft minimum of `Analysis.SoftMin` rather than a power
mean; see `Models.IncomeFluctuationCARA`.

The shift `a` is the subsistence level of Stone and Geary. `a = 0` is CRRA exactly.

## The result that matters

`relativeRiskAversionLeOne_haraUtility`: HARA with a NONNEGATIVE shift and `γ ≤ 1` satisfies
Light's condition. Relative risk aversion of the shifted family is `γ c / (a + c)`, which for
`a ≥ 0` is at most `γ`; a negative shift (genuine subsistence) pushes it above `γ` and can break
the condition however small `γ` is, so the sign of the shift is not a technicality.

The proof is derivative-free in the sense that matters: it factors

  `c · u' c = c ^ (1 - γ) · (c / (a + c)) ^ γ`

into two nonnegative nondecreasing factors, which is exactly `u' c · c` nondecreasing, which is
relative risk aversion at most one.
-/

@[expose] public section

open Set Filter Topology

namespace LeanEconomics

/-- Shifted CRRA: the `b ≠ 0` branch of HARA, with subsistence level `a`. -/
noncomputable def haraUtility (γ a c : ℝ) : ℝ := crraUtility γ (a + c)

/-- A zero shift recovers ordinary CRRA utility. -/
theorem haraUtility_zero (γ : ℝ) : haraUtility γ 0 = crraUtility γ := by
  funext c
  simp only [haraUtility, zero_add]

@[simp] theorem haraUtility_zero_shift (γ : ℝ) : haraUtility γ 0 = crraUtility γ := by
  funext c; simp [haraUtility]

/-- **HARA**, as a class of functions: a positive affine transformation of a shifted CRRA. -/
def IsHARA (u : ℝ → ℝ) : Prop :=
  ∃ γ a k l : ℝ, 0 < γ ∧ 0 < k ∧ ∀ c, u c = k * haraUtility γ a c + l

theorem isHARA_haraUtility {γ : ℝ} (hγ : 0 < γ) (a : ℝ) : IsHARA (haraUtility γ a) :=
  ⟨γ, a, 1, 0, hγ, one_pos, fun c => by ring⟩

/-- **CRRA is HARA**, with no shift. -/
theorem isHARA_crraUtility {γ : ℝ} (hγ : 0 < γ) : IsHARA (crraUtility γ) := by
  simpa using isHARA_haraUtility hγ 0

/-- **Log utility is HARA**, as the `γ = 1` member. -/
theorem isHARA_log : IsHARA Real.log := by
  refine ⟨1, 0, 1, 0, one_pos, one_pos, fun c => ?_⟩
  simp [haraUtility]

theorem hasDerivAt_haraUtility (γ : ℝ) {a c : ℝ} (hac : 0 < a + c) :
    HasDerivAt (haraUtility γ a) ((a + c) ^ (-γ)) c := by
  have h := (hasDerivAt_crraUtility γ hac).comp c ((hasDerivAt_id c).const_add a)
  rw [mul_one] at h
  exact h

/-! ### Light's condition -/

/-- The factorisation used for Light's condition: when the shift is nonnegative and
`0 < γ ≤ 1`, both factors are nonnegative and nondecreasing on positive consumption. -/
theorem mul_rpow_neg_eq {γ a c : ℝ} (hc : 0 < c) (hac : 0 < a + c) :
    c * (a + c) ^ (-γ) = c ^ (1 - γ) * (c / (a + c)) ^ γ := by
  rw [Real.div_rpow hc.le hac.le, Real.rpow_neg hac.le]
  rw [show c ^ (1 - γ) * (c ^ γ / (a + c) ^ γ)
      = (c ^ (1 - γ) * c ^ γ) / (a + c) ^ γ from by ring]
  rw [← Real.rpow_add hc, show (1 : ℝ) - γ + γ = 1 from by ring, Real.rpow_one]
  field_simp

/-- **HARA with a nonnegative shift and `γ ≤ 1` satisfies Light's condition.** -/
theorem relativeRiskAversionLeOne_haraUtility {γ a : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (ha : 0 ≤ a) : RelativeRiskAversionLeOne (haraUtility γ a) := by
  refine relativeRiskAversionLeOne_of_monotoneOn
    (du := fun c => (a + c) ^ (-γ))
    (fun c hc => hasDerivAt_haraUtility γ (by have := mem_Ioi.mp hc; linarith)) ?_
  intro c₁ h₁ c₂ h₂ h₁₂
  have hc₁ : (0 : ℝ) < c₁ := h₁
  have hc₂ : (0 : ℝ) < c₂ := h₂
  have hac₁ : (0 : ℝ) < a + c₁ := by linarith
  have hac₂ : (0 : ℝ) < a + c₂ := by linarith
  change c₁ * (a + c₁) ^ (-γ) ≤ c₂ * (a + c₂) ^ (-γ)
  rw [mul_rpow_neg_eq hc₁ hac₁, mul_rpow_neg_eq hc₂ hac₂]
  -- the first factor rises because `1 - γ ≥ 0`
  have hfst : c₁ ^ (1 - γ) ≤ c₂ ^ (1 - γ) := Real.rpow_le_rpow hc₁.le h₁₂ (by linarith)
  -- the second because `c / (a + c)` rises when the shift is nonnegative
  have hratio : c₁ / (a + c₁) ≤ c₂ / (a + c₂) := by
    rw [div_le_div_iff₀ hac₁ hac₂]
    nlinarith [ha, hc₁, h₁₂]
  have hsnd : (c₁ / (a + c₁)) ^ γ ≤ (c₂ / (a + c₂)) ^ γ :=
    Real.rpow_le_rpow (by positivity) hratio hγ0.le
  exact mul_le_mul hfst hsnd (by positivity) (by positivity)

/-- The same for the whole class, since a positive affine transformation preserves convexity in
log consumption. -/
theorem IsHARA.relativeRiskAversionLeOne {u : ℝ → ℝ} {γ a k l : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (ha : 0 ≤ a) (hk : 0 < k) (hu : ∀ c, u c = k * haraUtility γ a c + l) :
    RelativeRiskAversionLeOne u := by
  have hbase := relativeRiskAversionLeOne_haraUtility hγ0 hγ1 ha
  have hfun : (fun t => u (Real.exp t))
      = fun t => k * haraUtility γ a (Real.exp t) + l := by
    funext t; exact hu _
  simp only [RelativeRiskAversionLeOne, hfun]
  exact (hbase.smul hk.le).add_const l

/-- **A negative shift breaks it**, however small `γ` is: relative risk aversion `γ c / (a + c)`
exceeds one as consumption approaches the subsistence level from above. Recorded to show that
`0 ≤ a` in the theorem above is doing work. -/
theorem haraUtility_rra_gt_one_of_neg_shift {γ a c : ℝ} (hac : 0 < a + c)
    (hnear : (a + c) < γ * c) :
    1 < γ * c / (a + c) := by
  rw [lt_div_iff₀ hac]
  linarith

end LeanEconomics

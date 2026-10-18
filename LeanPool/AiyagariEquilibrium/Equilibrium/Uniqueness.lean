/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Equilibrium.Firm

/-!
# Uniqueness of the equilibrium interest rate

Existence came from the intermediate value theorem. Uniqueness comes from single crossing:
capital demand falls in the interest rate, so if capital supply RISES in it the two curves
meet at most once. This file proves that skeleton and supplies the demand half.

## What the literature says, and why only the skeleton is here

The supply half is the whole difficulty, and it is not a theorem about the model — it is a
restriction on the calibration.

Light (2018) proves uniqueness for CRRA utility and Cobb–Douglas production when relative
risk aversion `γ ≤ 1`. The argument is exactly the one below: individual savings rise with
the interest rate (his Theorem 1), hence aggregate savings do (Theorem 2), and since the
capital-to-wage ratio `k(R)/w(R)` strictly falls, the curves cross once (Theorem 3). The
economics of `γ ≤ 1` is that the substitution effect dominates the income effect: a higher
rate raises the price of current consumption, but also makes existing wealth worth more, and
only when `γ ≤ 1` does the first dominate.

For `γ > 1` supply need not rise. Açıkgöz (2018) exhibits multiple stationary equilibria at
`γ = 6.5`. Walsh and Young (2025) search 24,000 parameter draws and find multiplicity in 250
of them — always exactly three equilibria — and report that they never see it with risk
aversion below about 1.49, depreciation below about 0.19, or income persistence below about
0.47, and only ever with a disaster state for income. Their mechanism is precautionary: with
a disaster state, persistent income and high risk aversion, agents facing a low return still
amass capital to insure against near-zero income, so capital supply bends back and can cross
downward-sloping demand more than once.

Kirkby (2018) approaches it computationally and finds both Aiyagari (1994) and Pijoan-Mas
(2006) "almost certainly have a unique general equilibrium".

So the honest formal target is CONDITIONAL uniqueness — uniqueness given monotone supply —
plus, separately, whatever route establishes monotone supply for a restricted class. That is
what is proved here. An unconditional uniqueness theorem for this model would be false.
-/

@[expose] public section

open Set

namespace LeanEconomics

/-- **Single crossing.** A non-decreasing supply curve meets a strictly decreasing demand
curve at most once. This is the skeleton of Light (2018) Theorem 3. -/
theorem eq_of_monotoneOn_of_strictAntiOn {S D : ℝ → ℝ} {s : Set ℝ}
    (hS : MonotoneOn S s) (hD : StrictAntiOn D s) {r₁ r₂ : ℝ} (h₁ : r₁ ∈ s) (h₂ : r₂ ∈ s)
    (he₁ : S r₁ = D r₁) (he₂ : S r₂ = D r₂) : r₁ = r₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hs := hS h₁ h₂ h.le
    have hd := hD h₁ h₂ h
    rw [he₁, he₂] at hs
    exact absurd hs (not_le.mpr hd)
  · have hs := hS h₂ h₁ h.le
    have hd := hD h₂ h₁ h
    rw [he₁, he₂] at hs
    exact absurd hs (not_le.mpr hd)

/-- Capital demand falls STRICTLY in the interest rate, which is the half of single crossing
that is a theorem about the technology rather than about the households. -/
theorem capitalDemand_strictAntiOn {A δ rlo rhi : ℝ} (hA : A ≠ 0) (h : 0 < rlo + δ) :
    StrictAntiOn (capitalDemand A δ) (Icc rlo rhi) := by
  intro a ha b hb hab
  have ha' : 0 < a + δ := lt_of_lt_of_le h (by linarith [ha.1])
  have hb' : 0 < b + δ := by linarith
  have hA2 : 0 < A ^ 2 := by positivity
  simp only [capitalDemand]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have hsq : (a + δ) ^ 2 < (b + δ) ^ 2 := by nlinarith [ha', hb']
  nlinarith [hA2, hsq]

/-- **Conditional uniqueness of the equilibrium interest rate.** Given that capital supply is
non-decreasing in the rate, the equilibrium rate is unique.

The hypothesis `hS` is the entire economic content, and it is restrictive: it holds for CRRA
with `γ ≤ 1` (Light 2018) and fails for the calibrations of Açıkgöz (2018) and Walsh and
Young (2025). See the module docstring. -/
theorem equilibriumRate_unique {A δ rlo rhi : ℝ} (hA : A ≠ 0) (hδ : 0 < rlo + δ) {S : ℝ → ℝ}
    (hS : MonotoneOn S (Icc rlo rhi)) {r₁ r₂ : ℝ} (h₁ : r₁ ∈ Icc rlo rhi) (h₂ : r₂ ∈ Icc rlo rhi)
    (he₁ : S r₁ = capitalDemand A δ r₁) (he₂ : S r₂ = capitalDemand A δ r₂) : r₁ = r₂ :=
  eq_of_monotoneOn_of_strictAntiOn hS (capitalDemand_strictAntiOn hA hδ) h₁ h₂ he₁ he₂

/-- **A larger capital supply means a lower equilibrium rate.** With demand strictly decreasing,
two economies whose supply schedules are ordered have their equilibrium rates ordered the other
way. This is what uniqueness buys: without it "the" equilibrium rate is not a number to compare.

The hypothesis is only needed at `r₂`, and only monotonicity of the SMALLER supply is used. -/
theorem equilibriumRate_le_of_supply_le {A δ rlo rhi : ℝ} (hA : A ≠ 0) (hδ : 0 < rlo + δ)
    {S T : ℝ → ℝ} (hS : MonotoneOn S (Icc rlo rhi)) (hle : ∀ r ∈ Icc rlo rhi, S r ≤ T r)
    {r₁ r₂ : ℝ} (h₁ : r₁ ∈ Icc rlo rhi) (h₂ : r₂ ∈ Icc rlo rhi)
    (he₁ : S r₁ = capitalDemand A δ r₁) (he₂ : T r₂ = capitalDemand A δ r₂) : r₂ ≤ r₁ := by
  by_contra hcon
  rw [not_le] at hcon
  have hD : capitalDemand A δ r₂ < capitalDemand A δ r₁ :=
    capitalDemand_strictAntiOn hA hδ h₁ h₂ hcon
  have hchain : capitalDemand A δ r₁ ≤ capitalDemand A δ r₂ := by
    calc capitalDemand A δ r₁ = S r₁ := he₁.symm
      _ ≤ S r₂ := hS h₁ h₂ hcon.le
      _ ≤ T r₂ := hle r₂ h₂
      _ = capitalDemand A δ r₂ := he₂
  linarith

end LeanEconomics

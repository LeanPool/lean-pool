/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuationEuler
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuationIterate
public import LeanPool.AiyagariEquilibrium.Analysis.HARA

/-!
# The minimal marginal propensity to consume

Carroll and Shanker (2026), Lemma 1, bound the consumption SHARE of cash on hand between two
constants — the maximal and minimal marginal propensities to consume. This file proves the
minimal one,

  `κ · m ≤ c(m)`,   `κ = 1 - Þ/R`,   `Þ = (βR)^(1/γ)`,

for CRRA utility at a zero borrowing limit. `Þ` is Carroll's absolute patience factor, and `κ`
is the MPC of a perfect-foresight consumer with no human wealth.

## Why this one and not the other

The MAXIMAL MPC is `1 - ℘^(1/γ)Þ/R`, where `℘` is the probability of a zero-income event. This
model has `minIncome_pos`, so `℘ = 0`, the maximal MPC is `1`, and the bound it gives —
`c(m) ≤ m` — is the budget constraint and nothing more. That is not a defect of the estimate: a
liquidity-constrained household at the borrowing limit really does consume everything, and our
own corner condition says so. So only the minimal MPC has content here.

## The proof is one Euler step, and the bound is self-reproducing

Suppose the continuation's consumption function already satisfies `c ≥ κ m`. At an interior
choice `A > 0` the Euler inequality `u'(c) ≤ βR E[u'(c'(m'))]` applies, and `m' ≥ R A` because
income is positive, so

  `c^(-γ) ≤ βR (κ R A)^(-γ)`,  hence  `c ≥ (κR/Þ) A = (κR/Þ)(m - c)`,

and `(κR/Þ)/(1 + κR/Þ) = κ` precisely because `1 - κ = Þ/R`. At the corner `A = 0` the household
consumes everything, so `c = m ≥ κ m` outright. The bound therefore survives the Bellman
operator, and holds at the zero continuation because the household with no future eats
everything.

No limit of a sequence of MPCs is taken: `κ` is a fixed point of the recursion
`κ⁻¹ ↦ 1 + (Þ/R)κ⁻¹`, so the single constant reproduces itself.

## The sign of the rate

Everything below is stated with `0 < κ` as the hypothesis, not `0 ≤ r`. Return impatience
`βR < 1` at a non-negative rate gives `0 < κ` (`minMPC_pos`), but at `γ = 1` one has
`κ = 1 - β` (`minMPC_one`) at EVERY rate `r > -1`, so the log bounds — and with them the
capital ceiling — run into negative rates, where Aiyagari's `K(r)` has to be excluded too.

## What it is for

Two consequences the development already had homes for. `policy_lt_self_of_consumption_lower_bound`
turns it into the DECLINE condition, which was a raw assumption; and
`aggregateCapital_le_of_consumption_bound` turns it into a quantitative ceiling on capital
supply, in place of the asset cap. Both conditions ask for `(1-κ)R < 1`, and `(1-κ)R = Þ`, so
both are exactly `βR < 1`.
-/

@[expose] public section

open Set Finset Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ} (P : IncomeFluctuation Z assetFloor assetCap)

/-- **The minimal marginal propensity to consume**, `κ = 1 - Þ/R` with `Þ = (βR)^(1/γ)`. -/
noncomputable def minMPC (γ : ℝ) : ℝ :=
  1 - ((P.discount : ℝ) * (1 + P.interest)) ^ (1 / γ) / (1 + P.interest)

variable {P}

/-- The absolute patience factor is positive when the household discounts at all. -/
theorem patience_pos {γ : ℝ} (_hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ)) :
    0 < ((P.discount : ℝ) * (1 + P.interest)) ^ (1 / γ) :=
  Real.rpow_pos_of_pos (mul_pos hβ P.interest_gt_neg_one) _

/-- **Impatience is exactly `Þ < 1`.** -/
theorem patience_lt_one {γ : ℝ} (hγ0 : 0 < γ)
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1) :
    ((P.discount : ℝ) * (1 + P.interest)) ^ (1 / γ) < 1 := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  exact Real.rpow_lt_one (by positivity) hβR (by positivity)

/-- `(1 - κ)R = Þ`: the factor by which assets grow under the bound is the patience factor. -/
theorem one_sub_minMPC_mul {γ : ℝ} :
    (1 - P.minMPC γ) * (1 + P.interest)
      = ((P.discount : ℝ) * (1 + P.interest)) ^ (1 / γ) := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  simp only [minMPC]
  field_simp
  ring

theorem minMPC_le_one {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ)) :
    P.minMPC γ ≤ 1 := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have := patience_pos (P := P) hγ0 hβ
  simp only [minMPC]
  have : (0 : ℝ) < ((P.discount : ℝ) * (1 + P.interest)) ^ (1 / γ) / (1 + P.interest) := by
    positivity
  linarith

/-- **At `γ = 1` the patience factor is `βR` itself**, so `κ = 1 - β`: log and log Stone--Geary
need no root at all. -/
theorem minMPC_one : P.minMPC 1 = 1 - (P.discount : ℝ) := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  simp only [minMPC, div_one, Real.rpow_one]
  rw [mul_div_assoc, div_self hR.ne', mul_one]

/-- **The minimal MPC is positive** exactly when the household is impatient and the rate is
non-negative — Carroll's return impatience, which `βR < 1` implies once `R ≥ 1`. -/
theorem minMPC_pos {γ : ℝ} (hγ0 : 0 < γ) (hint : 0 ≤ P.interest)
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1) : 0 < P.minMPC γ := by
  have hR : (1 : ℝ) ≤ 1 + P.interest := by linarith
  have hT := patience_lt_one (P := P) hγ0 hβR
  simp only [minMPC, sub_pos]
  rw [div_lt_one (by linarith)]
  linarith

/-- Negative powers reverse the order: a smaller `x ^ (-γ)` means a larger `x`. -/
theorem le_of_rpow_neg_le {x y γ : ℝ} (hx : 0 < x) (hy : 0 < y) (hγ : 0 < γ)
    (h : x ^ (-γ) ≤ y ^ (-γ)) : y ≤ x := by
  have hxp : (0 : ℝ) < x ^ γ := Real.rpow_pos_of_pos hx _
  have hyp : (0 : ℝ) < y ^ γ := Real.rpow_pos_of_pos hy _
  rw [Real.rpow_neg hx.le, Real.rpow_neg hy.le, inv_le_inv₀ hxp hyp] at h
  by_contra hcon
  exact absurd h (not_le.mpr (Real.rpow_lt_rpow hx.le (not_le.mp hcon) hγ))

/-! ### The bound along the iteration -/

/-- **One Euler step of the minimal-MPC bound.** If a continuation `v` satisfies
`κ m ≤ c_v(m)` everywhere, with consumption positive and the cap slack against it, then so does
`bellman v`. Extracted from the induction so that it can also drive a SIMULTANEOUS induction on
cap slack (`crra_minMPC_of_cap`), which is what large `β` needs. -/
theorem crra_minMPC_step {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hfl : assetFloor = 0) (hκ : 0 < P.minMPC γ) (hβ : 0 < (P.discount : ℝ))
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1) {v : (ℝ × Z) →ᵇ ℝ}
    (hposv : ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap, 0 < P.consumptionFnOf v z a)
    (hcapv : ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, P.policyOf v (a, z) < assetCap)
    (hposW : ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap,
      0 < P.consumptionFnOf (P.toExtended.bellman v) z a)
    (ih : ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap,
      P.minMPC γ * P.resources (a, z) ≤ P.consumptionFnOf v z a)
    (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    P.minMPC γ * P.resources (a, z) ≤ P.consumptionFnOf (P.toExtended.bellman v) z a := by
  subst hfl
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hβR0 : (0 : ℝ) < (P.discount : ℝ) * (1 + P.interest) := mul_pos hβ hR
  set T : ℝ := ((P.discount : ℝ) * (1 + P.interest)) ^ (1 / γ) with hTdef
  have hT0 : 0 < T := patience_pos (P := P) hγ0 hβ
  have hκ0 : 0 < P.minMPC γ := hκ
  have hκ1 : P.minMPC γ ≤ 1 := minMPC_le_one (P := P) hγ0 hβ
  have hkey : (1 - P.minMPC γ) * (1 + P.interest) = T := one_sub_minMPC_mul (P := P)
  have hTneg : T ^ (-γ) = ((P.discount : ℝ) * (1 + P.interest))⁻¹ := by
    rw [hTdef, ← Real.rpow_mul hβR0.le,
      show (1 / γ) * (-γ) = -1 from by field_simp, Real.rpow_neg_one]
  set W : (ℝ × Z) →ᵇ ℝ := P.toExtended.bellman v with hWdef
  set A : ℝ := P.policyOf W (a, z) with hAdef
  have hAmem : A ∈ Icc (0 : ℝ) assetCap := P.feasible_subset_region (P.policyOf_mem W (a, z))
  set c : ℝ := P.consumptionFnOf W z a with hcdef
  have hcA : c = P.resources (a, z) - A := rfl
  have hc0 : 0 < c := hposW z a ha
  rcases eq_or_lt_of_le hAmem.1 with hA0 | hA0
  · nlinarith only [hκ1, hc0, hcA, hA0]
  · have hslack : ∀ z' : Z, P.policyOf v (A, z') < P.maxSaving (A, z') := fun z' =>
      P.policyOf_lt_maxSaving_of_pos (hposv z' A hAmem) (hcapv A hAmem z')
    have hc' : ∀ z' : Z, 0 < P.consumptionFnOf v z' A := fun z' => hposv z' A hAmem
    have hder : ∀ z' : Z, HasDerivAt P.u ((P.consumptionFnOf v z' A) ^ (-γ))
        (P.consumptionFnOf v z' A) := by
      intro z'; rw [hu]; exact hasDerivAt_crraUtility γ (hc' z')
    have heuler := P.euler_ge (v := v) (z := z) (a := a) (A := A) ha rfl hA0 hslack hc0
      (by rw [hu]; exact hasDerivAt_crraUtility γ hc0) hc' hder
    set X : ℝ := P.minMPC γ * ((1 + P.interest) * A) with hXdef
    have hX0 : 0 < X := by rw [hXdef]; positivity
    have hstep : ∀ z' : Z, X ≤ P.consumptionFnOf v z' A := by
      intro z'
      refine le_trans ?_ (ih z' A hAmem)
      have hres : P.resources (A, z') = P.income z' + (1 + P.interest) * A := by
        simp only [resources, max_eq_right hAmem.1]
      have hinc : 0 < P.income z' := lt_of_lt_of_le P.minIncome_pos (P.minIncome_le z')
      rw [hres, hXdef]
      nlinarith only [hκ0, hinc]
    have hsum : ∑ z' : Z, P.transitionMatrix z z' * (P.consumptionFnOf v z' A) ^ (-γ)
        ≤ X ^ (-γ) := by
      calc ∑ z' : Z, P.transitionMatrix z z' * (P.consumptionFnOf v z' A) ^ (-γ)
          ≤ ∑ z' : Z, P.transitionMatrix z z' * X ^ (-γ) :=
            Finset.sum_le_sum fun z' _ =>
              mul_le_mul_of_nonneg_left (rpow_neg_antitone hγ0 hX0 (hstep z'))
                (P.transitionMatrix_nonneg z z')
        _ = X ^ (-γ) := by rw [← Finset.sum_mul, P.transitionMatrix_sum z, one_mul]
    have hchain : c ^ (-γ) ≤ (P.discount : ℝ) * (1 + P.interest) * X ^ (-γ) := by
      have := le_trans heuler
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hR.le) hβ.le)
      linarith [this]
    have hTc : (T * c) ^ (-γ) ≤ X ^ (-γ) := by
      rw [Real.mul_rpow hT0.le hc0.le, hTneg, inv_mul_le_iff₀ hβR0]
      linarith [hchain]
    have hXTc : X ≤ T * c := le_of_rpow_neg_le (by positivity) hX0 hγ0 hTc
    rw [hXdef] at hXTc
    refine le_of_mul_le_mul_right (a := 1 + P.interest) ?_ hR
    linear_combination hXTc - c * hkey - (P.minMPC γ * (1 + P.interest)) * hcA

/-- **The minimal-MPC bound, at every iterate.** Consumption is at least `κ` times cash on hand,
uniformly in the horizon — so it passes to the value function.

The hypotheses beyond CRRA are the two the Euler inequality needs and nothing else: consumption
positive at each iterate, and the saving cap slack there. Both are fields (or immediate
consequences of fields) of `Calibrated`. -/
theorem crra_minMPC_mul_le_consumptionFnOf {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hfl : assetFloor = 0) (hκ : 0 < P.minMPC γ) (hβ : 0 < (P.discount : ℝ))
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1)
    (hpos : ∀ n : ℕ, ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap,
      0 < P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a)
    (hcap : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      P.policyOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < assetCap) :
    ∀ n : ℕ, ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap,
      P.minMPC γ * P.resources (a, z)
        ≤ P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a := by
  subst hfl
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hβR0 : (0 : ℝ) < (P.discount : ℝ) * (1 + P.interest) := mul_pos hβ hR
  set T : ℝ := ((P.discount : ℝ) * (1 + P.interest)) ^ (1 / γ) with hTdef
  have hT0 : 0 < T := patience_pos (P := P) hγ0 hβ
  have hκ0 : 0 < P.minMPC γ := hκ
  have hκ1 : P.minMPC γ ≤ 1 := minMPC_le_one (P := P) hγ0 hβ
  have hkey : (1 - P.minMPC γ) * (1 + P.interest) = T := one_sub_minMPC_mul (P := P)
  -- `Þ ^ (-γ) = 1/(βR)`, the one rpow identity the step needs
  have hTneg : T ^ (-γ) = ((P.discount : ℝ) * (1 + P.interest))⁻¹ := by
    rw [hTdef, ← Real.rpow_mul hβR0.le,
      show (1 / γ) * (-γ) = -1 from by field_simp, Real.rpow_neg_one]
  intro n
  induction n with
  | zero =>
    intro z a ha
    have hz : P.policyOf (0 : (ℝ × Z) →ᵇ ℝ) (a, z) = 0 := P.policyOf_zero (s := (a, z)) ha
    have hres : (0 : ℝ) ≤ P.resources (a, z) := (P.assetFloor_lt_resources (a, z)).le
    have heq : P.consumptionFnOf ((P.toExtended.bellman)^[0] (0 : (ℝ × Z) →ᵇ ℝ)) z a
        = P.resources (a, z) := by
      change P.consumption (a, z) (P.policyOf (0 : (ℝ × Z) →ᵇ ℝ) (a, z)) = P.resources (a, z)
      rw [hz]; simp [consumption]
    rw [heq]
    nlinarith only [hres, hκ1]
  | succ k ih =>
    intro z a ha
    have hiter : (P.toExtended.bellman)^[k + 1] (0 : (ℝ × Z) →ᵇ ℝ)
        = P.toExtended.bellman ((P.toExtended.bellman)^[k] (0 : (ℝ × Z) →ᵇ ℝ)) :=
      Function.iterate_succ_apply' _ _ _
    rw [hiter]
    exact P.crra_minMPC_step hγ0 hu rfl hκ hβ hβR (hpos k) (hcap k)
      (fun z' b hb => by have := hpos (k + 1) z' b hb; rwa [hiter] at this) ih z ha

/-! ### At the fixed point, and what it buys

The bound is uniform in the horizon, so it survives the limit: `tendsto_policyOf` says argmaxes
follow uniform limits when the limit has concave slices, which the value function does. -/

/-- **The minimal-MPC bound at the value function.** -/
theorem crra_minMPC_mul_le_consumptionFn {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hfl : assetFloor = 0) (hκ : 0 < P.minMPC γ) (hβ : 0 < (P.discount : ℝ))
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1)
    (hpos : ∀ n : ℕ, ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap,
      0 < P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a)
    (hcap : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      P.policyOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < assetCap)
    (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    P.minMPC γ * P.resources (a, z) ≤ P.consumptionFn z a := by
  have hiter := P.crra_minMPC_mul_le_consumptionFnOf hγ0 hu hfl hκ hβ hβR hpos hcap
  have hmem : ((a, z) : ℝ × Z).1 ∈ Icc assetFloor assetCap := by rw [hfl]; exact ha
  have htend : Tendsto
      (fun n => P.policyOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z)) atTop
      (𝓝 (P.policy (a, z))) :=
    P.tendsto_policyOf (P.toExtended.tendsto_iterate_valueFunction 0)
      P.concaveSlices_valueFunction hmem
  have htendc : Tendsto
      (fun n => P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a) atTop
      (𝓝 (P.consumptionFn z a)) := by
    have hcf : P.consumptionFn z a = P.resources (a, z) - P.policy (a, z) := rfl
    rw [hcf]
    simpa only [consumptionFnOf, consumption] using (tendsto_const_nhds (x := P.resources (a, z))
      (f := atTop (α := ℕ))).sub htend
  exact ge_of_tendsto htendc (Filter.Eventually.of_forall fun n => hiter n z a ha)

/-- **The decline condition, from primitives.** Above an explicit asset level the household runs
its assets down, because it consumes at least the share `κ` of cash on hand and
`(1-κ)R = Þ < 1`. This is the hypothesis `hdecl` of `exists_exhaust_of_decline`, which the
development has carried as an assumption. -/
theorem crra_policy_lt_self_of_minMPC {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hfl : assetFloor = 0) (hκ : 0 < P.minMPC γ) (hβ : 0 < (P.discount : ℝ))
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1)
    (hpos : ∀ n : ℕ, ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap,
      0 < P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a)
    (hcap : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      P.policyOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < assetCap)
    (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap)
    (hgt : (1 - P.minMPC γ) * P.income z
      < (1 - (1 - P.minMPC γ) * (1 + P.interest)) * a) :
    P.policy (a, z) < a := by
  subst hfl
  refine P.policy_lt_self_of_consumption_lower_bound (ε := P.minMPC γ) ha ?_ (by linarith)
  simpa using P.crra_minMPC_mul_le_consumptionFn hγ0 hu rfl hκ hβ hβR hpos hcap z ha

/-! ### Cap slack from the bound itself

The induction above ASSUMES the cap is slack at every iterate. At small `β` that is supplied by
an oscillation bound; at Aiyagari's `β = 0.96` no such bound is available. But the minimal-MPC
bound itself implies cap slack — saving is at most `(1-κ) m`, and `(1-κ)(maxIncome + R·cap)
< cap` once the cap is large enough — so the two can be proved TOGETHER, one induction carrying
both. The cap is then bookkeeping again: any `cap > (1-κ)maxIncome / (1 - (1-κ)R)` will do, and
`1 - (1-κ)R = 1 - Þ > 0`. -/

/-- Saving under the minimal-MPC bound is at most `(1-κ) m`, hence below the cap once the cap
clears `(1-κ)(maxIncome + R·cap)`. -/
theorem crra_policyOf_lt_cap_of_minMPC_bound {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ))
    (hfl : assetFloor = 0)
    (hthr : (1 - P.minMPC γ) * (P.maxIncome + (1 + P.interest) * assetCap) < assetCap)
    {v : (ℝ × Z) →ᵇ ℝ}
    (hv : ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap,
      P.minMPC γ * P.resources (a, z) ≤ P.consumptionFnOf v z a)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z) : P.policyOf v (a, z) < assetCap := by
  subst hfl
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hκ1 : P.minMPC γ ≤ 1 := minMPC_le_one (P := P) hγ0 hβ
  have hres : P.resources (a, z) = P.income z + (1 + P.interest) * a := by
    simp only [resources, max_eq_right ha.1]
  have hbd : P.income z + (1 + P.interest) * a ≤ P.maxIncome + (1 + P.interest) * assetCap := by
    have := P.le_maxIncome z
    nlinarith [ha.2, hR]
  have hpol : P.policyOf v (a, z) = P.resources (a, z) - P.consumptionFnOf v z a := by
    simp only [consumptionFnOf, consumption]; ring
  have hmpc := hv z a ha
  have hmono : (1 - P.minMPC γ) * P.resources (a, z)
      ≤ (1 - P.minMPC γ) * (P.maxIncome + (1 + P.interest) * assetCap) := by
    rw [hres]; exact mul_le_mul_of_nonneg_left hbd (by linarith)
  rw [hpol]
  linarith

/-- **The minimal-MPC bound and cap slack, by one induction.** Nothing is assumed about the cap
beyond one inequality among the primitives. -/
theorem crra_minMPC_of_cap {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hfl : assetFloor = 0) (hκ : 0 < P.minMPC γ) (hβ : 0 < (P.discount : ℝ))
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1)
    (hpos : ∀ n : ℕ, ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap,
      0 < P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a)
    (hthr : (1 - P.minMPC γ) * (P.maxIncome + (1 + P.interest) * assetCap) < assetCap) :
    ∀ n : ℕ,
      (∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap,
        P.minMPC γ * P.resources (a, z)
          ≤ P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a)
      ∧ (∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
        P.policyOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < assetCap) := by
  intro n
  induction n with
  | zero =>
    have hκ1 : P.minMPC γ ≤ 1 := minMPC_le_one (P := P) hγ0 hβ
    have hm : ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap,
        P.minMPC γ * P.resources (a, z)
          ≤ P.consumptionFnOf ((P.toExtended.bellman)^[0] (0 : (ℝ × Z) →ᵇ ℝ)) z a := by
      intro z a ha
      subst hfl
      have hz : P.policyOf (0 : (ℝ × Z) →ᵇ ℝ) (a, z) = 0 := P.policyOf_zero (s := (a, z)) ha
      have hres : (0 : ℝ) ≤ P.resources (a, z) := (P.assetFloor_lt_resources (a, z)).le
      have heq : P.consumptionFnOf ((P.toExtended.bellman)^[0] (0 : (ℝ × Z) →ᵇ ℝ)) z a
          = P.resources (a, z) := by
        change P.consumption (a, z) (P.policyOf (0 : (ℝ × Z) →ᵇ ℝ) (a, z)) = P.resources (a, z)
        rw [hz]; simp [consumption]
      rw [heq]
      nlinarith only [hres, hκ1]
    exact ⟨hm, fun a ha z => P.crra_policyOf_lt_cap_of_minMPC_bound hγ0 hβ hfl hthr hm ha z⟩
  | succ k ih =>
    obtain ⟨ihm, ihc⟩ := ih
    have hiter : (P.toExtended.bellman)^[k + 1] (0 : (ℝ × Z) →ᵇ ℝ)
        = P.toExtended.bellman ((P.toExtended.bellman)^[k] (0 : (ℝ × Z) →ᵇ ℝ)) :=
      Function.iterate_succ_apply' _ _ _
    have hm : ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap,
        P.minMPC γ * P.resources (a, z)
          ≤ P.consumptionFnOf ((P.toExtended.bellman)^[k + 1] (0 : (ℝ × Z) →ᵇ ℝ)) z a := by
      intro z a ha
      rw [hiter]
      exact P.crra_minMPC_step hγ0 hu hfl hκ hβ hβR (hpos k) ihc
        (fun z' b hb => by have := hpos (k + 1) z' b hb; rwa [hiter] at this) ihm z ha
    exact ⟨hm, fun a ha z => P.crra_policyOf_lt_cap_of_minMPC_bound hγ0 hβ hfl hthr hm ha z⟩

/-- **The minimal-MPC bound at the value function, with the cap from primitives.** -/
theorem crra_minMPC_mul_le_consumptionFn_of_cap {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hfl : assetFloor = 0) (hκ : 0 < P.minMPC γ) (hβ : 0 < (P.discount : ℝ))
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1)
    (hpos : ∀ n : ℕ, ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap,
      0 < P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a)
    (hthr : (1 - P.minMPC γ) * (P.maxIncome + (1 + P.interest) * assetCap) < assetCap)
    (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    P.minMPC γ * P.resources (a, z) ≤ P.consumptionFn z a :=
  P.crra_minMPC_mul_le_consumptionFn hγ0 hu hfl hκ hβ hβR hpos
    (fun n => (P.crra_minMPC_of_cap hγ0 hu hfl hκ hβ hβR hpos hthr n).2) z ha

/-- **The cap is slack at the fixed point**, from primitives. -/
theorem crra_policy_lt_cap_of_minMPC {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hfl : assetFloor = 0) (hκ : 0 < P.minMPC γ) (hβ : 0 < (P.discount : ℝ))
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1)
    (hpos : ∀ n : ℕ, ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap,
      0 < P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a)
    (hthr : (1 - P.minMPC γ) * (P.maxIncome + (1 + P.interest) * assetCap) < assetCap)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z) : P.policy (a, z) < assetCap :=
  P.crra_policyOf_lt_cap_of_minMPC_bound hγ0 hβ hfl hthr
    (fun z' _b hb =>
      P.crra_minMPC_mul_le_consumptionFn_of_cap hγ0 hu hfl hκ hβ hβR hpos hthr z' hb)
    ha z

/-! ### The shifted-CRRA version

With `u'(c) = (η + c)^(-γ)` the same argument runs on `η + c` against `η + m`:

  `κ (η + m) ≤ η + c(m)`,

with the SAME `κ`. The step produces `c ≥ κ m + η(κ - Þ)/R`, and what has to be checked is that
this is at least `κ m - η(1-κ)`, which holds because `κ ≥ 0`. So the subsistence level costs
nothing in the constant; it only shifts what the constant multiplies.

Read as a bound on saving this is `policy ≤ (1-κ)(η + m)`, so the household behaves like a CRRA
household with income raised by `η` — which is what a subsistence level is. -/

/-- **The minimal-MPC bound for shifted CRRA, at every iterate.** -/
theorem hara_minMPC_mul_le_consumptionFnOf {γ η : ℝ} (hγ0 : 0 < γ) (hη : 0 ≤ η)
    (hu : P.u = haraUtility γ η)
    (hfl : assetFloor = 0) (hκ : 0 < P.minMPC γ) (hβ : 0 < (P.discount : ℝ))
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1)
    (hpos : ∀ n : ℕ, ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap,
      0 < P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a)
    (hcap : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      P.policyOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < assetCap) :
    ∀ n : ℕ, ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap,
      P.minMPC γ * (η + P.resources (a, z))
        ≤ η + P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a := by
  subst hfl
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hβR0 : (0 : ℝ) < (P.discount : ℝ) * (1 + P.interest) := mul_pos hβ hR
  set T : ℝ := ((P.discount : ℝ) * (1 + P.interest)) ^ (1 / γ) with hTdef
  have hT0 : 0 < T := patience_pos (P := P) hγ0 hβ
  have hκ0 : 0 < P.minMPC γ := hκ
  have hκ1 : P.minMPC γ ≤ 1 := minMPC_le_one (P := P) hγ0 hβ
  have hkey : (1 - P.minMPC γ) * (1 + P.interest) = T := one_sub_minMPC_mul (P := P)
  have hTneg : T ^ (-γ) = ((P.discount : ℝ) * (1 + P.interest))⁻¹ := by
    rw [hTdef, ← Real.rpow_mul hβR0.le,
      show (1 / γ) * (-γ) = -1 from by field_simp, Real.rpow_neg_one]
  intro n
  induction n with
  | zero =>
    intro z a ha
    have hz : P.policyOf (0 : (ℝ × Z) →ᵇ ℝ) (a, z) = 0 := P.policyOf_zero (s := (a, z)) ha
    have hres : (0 : ℝ) ≤ P.resources (a, z) := (P.assetFloor_lt_resources (a, z)).le
    have heq : P.consumptionFnOf ((P.toExtended.bellman)^[0] (0 : (ℝ × Z) →ᵇ ℝ)) z a
        = P.resources (a, z) := by
      change P.consumption (a, z) (P.policyOf (0 : (ℝ × Z) →ᵇ ℝ) (a, z)) = P.resources (a, z)
      rw [hz]; simp [consumption]
    rw [heq]
    nlinarith only [hres, hκ1, hη]
  | succ k ih =>
    intro z a ha
    have hiter : (P.toExtended.bellman)^[k + 1] (0 : (ℝ × Z) →ᵇ ℝ)
        = P.toExtended.bellman ((P.toExtended.bellman)^[k] (0 : (ℝ × Z) →ᵇ ℝ)) :=
      Function.iterate_succ_apply' _ _ _
    set v : (ℝ × Z) →ᵇ ℝ := (P.toExtended.bellman)^[k] (0 : (ℝ × Z) →ᵇ ℝ) with hvdef
    rw [hiter]
    set W : (ℝ × Z) →ᵇ ℝ := P.toExtended.bellman v with hWdef
    set A : ℝ := P.policyOf W (a, z) with hAdef
    have hAmem : A ∈ Icc (0 : ℝ) assetCap := P.feasible_subset_region (P.policyOf_mem W (a, z))
    set c : ℝ := P.consumptionFnOf W z a with hcdef
    have hcA : c = P.resources (a, z) - A := rfl
    have hc0 : 0 < c := by
      have := hpos (k + 1) z a ha
      rwa [hiter] at this
    rcases eq_or_lt_of_le hAmem.1 with hA0 | hA0
    · nlinarith only [hκ1, hc0, hcA, hA0, hη]
    · have hslack : ∀ z' : Z, P.policyOf v (A, z') < P.maxSaving (A, z') := fun z' =>
        P.policyOf_lt_maxSaving_of_pos (hpos k z' A hAmem) (hcap k A hAmem z')
      have hc' : ∀ z' : Z, 0 < P.consumptionFnOf v z' A := fun z' => hpos k z' A hAmem
      have hder : ∀ z' : Z, HasDerivAt P.u ((η + P.consumptionFnOf v z' A) ^ (-γ))
          (P.consumptionFnOf v z' A) := by
        intro z'; rw [hu]
        exact hasDerivAt_haraUtility γ (by linarith [hc' z'])
      have heuler := P.euler_ge (v := v) (z := z) (a := a) (A := A) ha rfl hA0 hslack hc0
        (by rw [hu]; exact hasDerivAt_haraUtility γ (by linarith)) hc' hder
      -- the continuation's shifted consumption is at least `κ (η + R A)`
      set X : ℝ := P.minMPC γ * (η + (1 + P.interest) * A) with hXdef
      have hX0 : 0 < X := by
        have : (0 : ℝ) < (1 + P.interest) * A := by positivity
        rw [hXdef]; nlinarith [hκ0, hη]
      have hstep : ∀ z' : Z, X ≤ η + P.consumptionFnOf v z' A := by
        intro z'
        refine le_trans ?_ (ih z' A hAmem)
        have hres : P.resources (A, z') = P.income z' + (1 + P.interest) * A := by
          simp only [resources, max_eq_right hAmem.1]
        have hinc : 0 < P.income z' := lt_of_lt_of_le P.minIncome_pos (P.minIncome_le z')
        rw [hres, hXdef]
        nlinarith only [hκ0, hinc]
      have hsum : ∑ z' : Z, P.transitionMatrix z z'
            * (η + P.consumptionFnOf v z' A) ^ (-γ) ≤ X ^ (-γ) := by
        calc ∑ z' : Z, P.transitionMatrix z z' * (η + P.consumptionFnOf v z' A) ^ (-γ)
            ≤ ∑ z' : Z, P.transitionMatrix z z' * X ^ (-γ) :=
              Finset.sum_le_sum fun z' _ =>
                mul_le_mul_of_nonneg_left (rpow_neg_antitone hγ0 hX0 (hstep z'))
                  (P.transitionMatrix_nonneg z z')
          _ = X ^ (-γ) := by rw [← Finset.sum_mul, P.transitionMatrix_sum z, one_mul]
      have hchain : (η + c) ^ (-γ) ≤ (P.discount : ℝ) * (1 + P.interest) * X ^ (-γ) := by
        have := le_trans heuler
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hR.le) hβ.le)
        linarith [this]
      have hTc : (T * (η + c)) ^ (-γ) ≤ X ^ (-γ) := by
        rw [Real.mul_rpow hT0.le (by linarith), hTneg, inv_mul_le_iff₀ hβR0]
        linarith [hchain]
      have hXTc : X ≤ T * (η + c) :=
        le_of_rpow_neg_le (by positivity) hX0 hγ0 hTc
      rw [hXdef] at hXTc
      -- `κR + Þ = R`, and the extra `η` term has the right sign because `κ ≥ 0`
      refine le_of_mul_le_mul_right (a := 1 + P.interest) ?_ hR
      linear_combination hXTc - (η + c) * hkey
        - (P.minMPC γ * (1 + P.interest)) * hcA + mul_nonneg hκ0.le hη

/-- **The shifted-CRRA bound at the value function.** -/
theorem hara_minMPC_mul_le_consumptionFn {γ η : ℝ} (hγ0 : 0 < γ) (hη : 0 ≤ η)
    (hu : P.u = haraUtility γ η)
    (hfl : assetFloor = 0) (hκ : 0 < P.minMPC γ) (hβ : 0 < (P.discount : ℝ))
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1)
    (hpos : ∀ n : ℕ, ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap,
      0 < P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a)
    (hcap : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      P.policyOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < assetCap)
    (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    P.minMPC γ * (η + P.resources (a, z)) ≤ η + P.consumptionFn z a := by
  have hiter := P.hara_minMPC_mul_le_consumptionFnOf hγ0 hη hu hfl hκ hβ hβR hpos hcap
  have hmem : ((a, z) : ℝ × Z).1 ∈ Icc assetFloor assetCap := by rw [hfl]; exact ha
  have htend : Tendsto
      (fun n => P.policyOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z)) atTop
      (𝓝 (P.policy (a, z))) :=
    P.tendsto_policyOf (P.toExtended.tendsto_iterate_valueFunction 0)
      P.concaveSlices_valueFunction hmem
  have htendc : Tendsto
      (fun n => η + P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a) atTop
      (𝓝 (η + P.consumptionFn z a)) := by
    have hcf : P.consumptionFn z a = P.resources (a, z) - P.policy (a, z) := rfl
    rw [hcf, ← add_sub_assoc]
    simpa only [consumptionFnOf, consumption, ← add_sub_assoc] using
      (tendsto_const_nhds (x := η + P.resources (a, z)) (f := atTop (α := ℕ))).sub htend
  exact ge_of_tendsto htendc (Filter.Eventually.of_forall fun n => hiter n z a ha)

/-- **The share form.** `κ(η + m) ≤ η + c` is not a bound on the SHARE `c/m`, because of the
constant. Charging the constant against the smallest cash on hand there can be gives one:
`1 - (1-κ)(1 + η/minIncome)` is a share the household always consumes. It is what the capital
ceiling needs, and it degrades gracefully — at `η = 0` it is `κ` itself. -/
noncomputable def minMPCShare (γ η : ℝ) : ℝ :=
  P.minMPC γ - (1 - P.minMPC γ) * η / P.minIncome

theorem hara_minMPCShare_mul_le_consumptionFn {γ η : ℝ} (hγ0 : 0 < γ) (hη : 0 ≤ η)
    (hu : P.u = haraUtility γ η)
    (hfl : assetFloor = 0) (hκ : 0 < P.minMPC γ) (hβ : 0 < (P.discount : ℝ))
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1)
    (hpos : ∀ n : ℕ, ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap,
      0 < P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a)
    (hcap : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      P.policyOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < assetCap)
    (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    P.minMPCShare γ η * P.resources (a, z) ≤ P.consumptionFn z a := by
  have hbound := P.hara_minMPC_mul_le_consumptionFn hγ0 hη hu hfl hκ hβ hβR hpos hcap z ha
  have hκ1 : P.minMPC γ ≤ 1 := minMPC_le_one (P := P) hγ0 hβ
  have hy : 0 < P.minIncome := P.minIncome_pos
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hres : P.resources (a, z) = P.income z + (1 + P.interest) * a := by
    simp only [resources, max_eq_right (hfl ▸ ha.1 : assetFloor ≤ a)]
  have hmin : P.minIncome ≤ P.resources (a, z) := by
    have h1 : P.minIncome ≤ P.income z := P.minIncome_le z
    have h2 : (0 : ℝ) ≤ (1 + P.interest) * a := by
      have : (0 : ℝ) ≤ a := hfl ▸ ha.1
      positivity
    rw [hres]; linarith
  set κ : ℝ := P.minMPC γ with hκdef
  set m : ℝ := P.resources (a, z) with hmdef
  set q : ℝ := (1 - κ) * η / P.minIncome with hqdef
  have hnn : (0 : ℝ) ≤ (1 - κ) * η := mul_nonneg (by linarith) hη
  have hgap : η - κ * η ≤ m * q := by
    rw [hqdef, ← mul_div_assoc, le_div_iff₀ hy]
    nlinarith [mul_le_mul_of_nonneg_left hmin hnn]
  have hbound' : κ * η + κ * m ≤ η + P.consumptionFn z a := by nlinarith [hbound]
  simp only [minMPCShare, ← hκdef, ← hqdef]
  nlinarith [hbound', hgap]

/-- **The decline condition for shifted CRRA.** Saving is at most `(1-κ)(η + m)`, so the
household behaves like a CRRA household whose income is raised by the subsistence level. -/
theorem hara_policy_lt_self_of_minMPC {γ η : ℝ} (hγ0 : 0 < γ) (hη : 0 ≤ η)
    (hu : P.u = haraUtility γ η)
    (hfl : assetFloor = 0) (hκ : 0 < P.minMPC γ) (hβ : 0 < (P.discount : ℝ))
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1)
    (hpos : ∀ n : ℕ, ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap,
      0 < P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a)
    (hcap : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      P.policyOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < assetCap)
    (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap)
    (hgt : (1 - P.minMPC γ) * (η + P.income z)
      < (1 - (1 - P.minMPC γ) * (1 + P.interest)) * a) :
    P.policy (a, z) < a := by
  have hbound := P.hara_minMPC_mul_le_consumptionFn hγ0 hη hu hfl hκ hβ hβR hpos hcap z ha
  have hres : P.resources (a, z) = P.income z + (1 + P.interest) * a := by
    simp only [resources, max_eq_right (hfl ▸ ha.1 : assetFloor ≤ a)]
  have hpol : P.policy (a, z) = P.resources (a, z) - P.consumptionFn z a := by
    simp only [consumptionFn, consumption]; ring
  rw [hpol, hres]
  rw [hres] at hbound
  nlinarith [hbound, hgt]

/-- **The Doeblin exhaustion data for shifted CRRA**, with no assumption on the income process. -/
theorem hara_exists_exhaust_of_minMPC {γ η : ℝ} (hγ0 : 0 < γ) (hη : 0 ≤ η)
    (hu : P.u = haraUtility γ η)
    (hfl : assetFloor = 0) (hκ : 0 < P.minMPC γ) (hβ : 0 < (P.discount : ℝ))
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1)
    (hpos : ∀ n : ℕ, ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap,
      0 < P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a)
    (hcap : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      P.policyOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < assetCap)
    {z₀ : Z} {a₀ : ℝ} (ha₀ : 0 < a₀) (hle : a₀ ≤ assetCap)
    (hzero : ∀ a ∈ Icc (0 : ℝ) a₀, P.policy (a, z₀) = 0)
    (hthr : (1 - P.minMPC γ) * (η + P.income z₀)
      < (1 - (1 - P.minMPC γ) * (1 + P.interest)) * a₀) :
    ∃ N : ℕ, (P.gBad z₀)^[N] P.topState = P.botState := by
  subst hfl
  have hslope : (0 : ℝ) < 1 - (1 - P.minMPC γ) * (1 + P.interest) := by
    rw [one_sub_minMPC_mul (P := P)]
    have := patience_lt_one (P := P) hγ0 hβR
    linarith
  refine P.exists_exhaust_of_decline ha₀ hle hzero fun a ha => ?_
  refine P.hara_policy_lt_self_of_minMPC hγ0 hη hu rfl hκ hβ hβR hpos hcap z₀
    ⟨le_trans ha₀.le ha.1, ha.2⟩ ?_
  have hmono : (1 - (1 - P.minMPC γ) * (1 + P.interest)) * a₀
      ≤ (1 - (1 - P.minMPC γ) * (1 + P.interest)) * a :=
    mul_le_mul_of_nonneg_left ha.1 hslope.le
  linarith

/-! ### The exhaustion data, without `IidIncome`

`exists_exhaust_of_impatient` (Açıkgöz Proposition 4) also supplies the decline half from
impatience, but it gets there by comparing income states: consumption is lowest where income is
lowest, which needs `IidIncome` so that the continuation does not depend on today's state. The
minimal-MPC route compares nothing. It is a statement about the budget and the Euler inequality
at ONE state, so it holds whatever the income process does.

What it costs instead is the two iterate-level hypotheses, which the Açıkgöz route asks for only
at the fixed point. -/

/-- **The Doeblin exhaustion data from the minimal MPC.** Only the corner condition and one
threshold inequality are left to the calibration — and no assumption is made about the income
process. -/
theorem crra_exists_exhaust_of_minMPC {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hfl : assetFloor = 0) (hκ : 0 < P.minMPC γ) (hβ : 0 < (P.discount : ℝ))
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1)
    (hpos : ∀ n : ℕ, ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap,
      0 < P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a)
    (hcap : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      P.policyOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < assetCap)
    {z₀ : Z} {a₀ : ℝ} (ha₀ : 0 < a₀) (hle : a₀ ≤ assetCap)
    (hzero : ∀ a ∈ Icc (0 : ℝ) a₀, P.policy (a, z₀) = 0)
    (hthr : (1 - P.minMPC γ) * P.income z₀
      < (1 - (1 - P.minMPC γ) * (1 + P.interest)) * a₀) :
    ∃ N : ℕ, (P.gBad z₀)^[N] P.topState = P.botState := by
  subst hfl
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  -- the decline threshold only has to be cleared once: the gap grows with assets
  have hslope : (0 : ℝ) < 1 - (1 - P.minMPC γ) * (1 + P.interest) := by
    rw [one_sub_minMPC_mul (P := P)]
    have := patience_lt_one (P := P) hγ0 hβR
    linarith
  refine P.exists_exhaust_of_decline ha₀ hle hzero fun a ha => ?_
  refine P.crra_policy_lt_self_of_minMPC hγ0 hu rfl hκ hβ hβR hpos hcap z₀
    ⟨le_trans ha₀.le ha.1, ha.2⟩ ?_
  have hmono : (1 - (1 - P.minMPC γ) * (1 + P.interest)) * a₀
      ≤ (1 - (1 - P.minMPC γ) * (1 + P.interest)) * a :=
    mul_le_mul_of_nonneg_left ha.1 hslope.le
  linarith

end IncomeFluctuation

end LeanEconomics

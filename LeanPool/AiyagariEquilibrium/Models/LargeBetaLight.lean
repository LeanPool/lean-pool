/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Models.MinimalMPC
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuationRateStep
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuationHARA


/-!
# Light's Theorem 1 at large `β`

`policy_mono_withRate_hara` — a household facing a higher rate saves at least as much — needs
the saving cap slack along BOTH iterations, and in particular for the higher-rate economy
choosing against the lower-rate economy's iterates. `Calibrated` supplies that from an oscillation
bound uniform in the rate, which at Aiyagari's `β = 0.96` is off by orders of magnitude.

This file supplies it from the minimal MPC instead, and the price is that the two rates have to
be CLOSE: within `1 - Þ₁` of each other, where `Þ₁ = (βR₁)^(1/γ)` is the patience factor at the
lower rate. That is not a defect of the estimate but of the comparison — a household facing a
much higher rate against an old continuation can save more than its own cap — and it costs
nothing, because monotonicity on overlapping short intervals is monotonicity on their union
(`monotoneOn_of_local`).

## The hybrid bound

Economy 2 choosing against economy 1's iterate `v` at assets `a` is economy 1 choosing against
`v` at `t a`, `t = R₁/R₂ ≤ 1` (`consumptionFnOf_withRate`). Consumption rises with assets, so
economy 2's consumption at `a` is at least economy 1's at `a` itself, which the minimal MPC bounds
by `κ₁ (y + R₁ a)`. Saving is then at most `(1-κ₁) y + (R₂ - κ₁ R₁) a`, and `R₂ - κ₁ R₁ = Þ₁ +
(r₂ - r₁)`: the coefficient on assets exceeds `Þ₁` by exactly the rate gap.
-/

@[expose] public section

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

/-! ### Local monotonicity is monotonicity -/

/-- **Monotone on short steps, monotone on the interval.** If `f x ≤ f y` whenever `x ≤ y` are at
most `ε` apart, then `f` is monotone on the interval: walk from `x` to `y` in steps of `ε`. -/
theorem monotoneOn_of_local {f : ℝ → ℝ} {lo hi ε : ℝ} (hε : 0 < ε)
    (h : ∀ x ∈ Icc lo hi, ∀ y ∈ Icc lo hi, x ≤ y → y - x ≤ ε → f x ≤ f y) :
    MonotoneOn f (Icc lo hi) := by
  have key : ∀ n : ℕ, ∀ x ∈ Icc lo hi, ∀ y ∈ Icc lo hi, x ≤ y → y ≤ x + n * ε → f x ≤ f y := by
    intro n
    induction n with
    | zero =>
      intro x hx y hy hxy hle
      simp only [Nat.cast_zero, zero_mul, add_zero] at hle
      exact h x hx y hy hxy (by linarith)
    | succ k ih =>
      intro x hx y hy hxy hle
      by_cases hshort : y - x ≤ ε
      · exact h x hx y hy hxy hshort
      · push Not at hshort
        set m : ℝ := y - ε with hm
        have hxm : x ≤ m := by rw [hm]; linarith
        have hmy : m ≤ y := by rw [hm]; linarith
        have hmmem : m ∈ Icc lo hi := ⟨le_trans hx.1 hxm, le_trans hmy hy.2⟩
        have hmle : m ≤ x + k * ε := by
          rw [hm]; push_cast at hle; linarith
        exact le_trans (ih x hx m hmmem hxm hmle) (h m hmmem y hy hmy (by rw [hm]; linarith))
  intro x hx y hy hxy
  obtain ⟨n, hn⟩ := exists_nat_ge ((y - x) / ε)
  refine key n x hx y hy hxy ?_
  have := (div_le_iff₀ hε).mp hn
  linarith

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]

section AnyFloor

variable {assetFloor assetCap : ℝ} (P : IncomeFluctuation Z assetFloor assetCap)

/-- Every iterate from `0` has concave slices. -/
theorem concaveSlices_iterate_zero (n : ℕ) :
    ConcaveSlices assetFloor assetCap ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) := by
  induction n with
  | zero => exact concaveSlices_zero
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact P.concaveSlices_bellman ih

end AnyFloor

variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-! ### The hybrid cap slack -/

/-- **Cap slack for the higher-rate economy against the lower-rate economy's iterates**, from the
minimal MPC at the lower rate. The condition is one inequality in which the rate gap appears
explicitly. -/
theorem crra_policyOf_withRate_lt_cap {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂)
    (hκ₁ : 0 < (P.withRate r₁ h₁).minMPC γ)
    (hβ : 0 < (P.discount : ℝ)) (hβR₁ : (P.discount : ℝ) * (1 + r₁) < 1)
    (hpos₁ : ∀ n : ℕ, ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap, 0 <
      (P.withRate r₁ h₁).consumptionFnOf
        (((P.withRate r₁ h₁).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a)
    (hthr₁ : (1 - (P.withRate r₁ h₁).minMPC γ) * (P.maxIncome + (1 + r₁) * assetCap) < assetCap)
    (hgap : (1 - (P.withRate r₁ h₁).minMPC γ) * P.maxIncome
      + ((1 - (P.withRate r₁ h₁).minMPC γ) * (1 + r₁) + (r₂ - r₁)) * assetCap < assetCap)
    (n : ℕ) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z) :
    (P.withRate r₂ h₂).policyOf
      (((P.withRate r₁ h₁).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < assetCap := by
  set Q₁ := P.withRate r₁ h₁ with hQ₁
  set Q₂ := P.withRate r₂ h₂ with hQ₂
  set v : (ℝ × Z) →ᵇ ℝ := (Q₁.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ) with hv
  set κ : ℝ := Q₁.minMPC γ with hκ
  have hR₁ : (0 : ℝ) < 1 + r₁ := h₁.1
  have hR₂ : (0 : ℝ) < 1 + r₂ := h₂.1
  have hslices : ConcaveSlices (0 : ℝ) assetCap v := Q₁.concaveSlices_iterate_zero n
  have hκ1 : κ ≤ 1 := minMPC_le_one (P := Q₁) hγ0 hβ
  -- economy 1's minimal-MPC bound at this iterate
  have hmpc : κ * Q₁.resources (a, z) ≤ Q₁.consumptionFnOf v z a :=
    (Q₁.crra_minMPC_of_cap hγ0 (show Q₁.u = crraUtility γ from hu) rfl
      hκ₁ hβ hβR₁ hpos₁ hthr₁ n).1 z a ha
  -- the rescale, and monotonicity of consumption in assets
  set t : ℝ := (1 + r₁) / (1 + r₂) with ht
  have ht0 : 0 < t := div_pos hR₁ hR₂
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hR₂]; linarith
  have hta : t * a ∈ Icc (0 : ℝ) assetCap :=
    ⟨mul_nonneg ht0.le ha.1, le_trans (by nlinarith [ha.1, ha.2]) ha.2⟩
  have htale : t * a ≤ a := by nlinarith [ha.1]
  have hrescale : Q₁.consumptionFnOf v z a = Q₂.consumptionFnOf v z (t * a) :=
    P.consumptionFnOf_withRate h₁ h₂ hr hslices z ha
  have hmono : Q₂.consumptionFnOf v z (t * a) ≤ Q₂.consumptionFnOf v z a :=
    Q₂.consumptionFnOf_mono hslices hta ha htale
  -- so economy 2 consumes at least `κ (y + R₁ a)` here
  have hres₁ : Q₁.resources (a, z) = P.income z + (1 + r₁) * a := by
    simp only [hQ₁, resources, withRate_income, withRate_interest, max_eq_right ha.1]
  have hres₂ : Q₂.resources (a, z) = P.income z + (1 + r₂) * a := by
    simp only [hQ₂, resources, withRate_income, withRate_interest, max_eq_right ha.1]
  have hpol : Q₂.policyOf v (a, z) = Q₂.resources (a, z) - Q₂.consumptionFnOf v z a := by
    simp only [consumptionFnOf, consumption]; ring
  have hy : P.income z ≤ P.maxIncome := P.le_maxIncome z
  have hcoef : (0 : ℝ) ≤ (1 - κ) * (1 + r₁) + (r₂ - r₁) := by nlinarith
  rw [hpol, hres₂]
  -- saving ≤ (1-κ) y + ((1-κ)(1+r₁) + (r₂-r₁)) a, and that is < cap at a = cap
  have hbound : P.income z + (1 + r₂) * a - Q₂.consumptionFnOf v z a
      ≤ (1 - κ) * P.income z + ((1 - κ) * (1 + r₁) + (r₂ - r₁)) * a := by
    rw [hres₁] at hmpc
    nlinarith [hmpc, hrescale, hmono]
  have hmax : (1 - κ) * P.income z + ((1 - κ) * (1 + r₁) + (r₂ - r₁)) * a
      ≤ (1 - κ) * P.maxIncome + ((1 - κ) * (1 + r₁) + (r₂ - r₁)) * assetCap := by
    have h1 : (1 - κ) * P.income z ≤ (1 - κ) * P.maxIncome :=
      mul_le_mul_of_nonneg_left hy (by linarith)
    have h2 : ((1 - κ) * (1 + r₁) + (r₂ - r₁)) * a
        ≤ ((1 - κ) * (1 + r₁) + (r₂ - r₁)) * assetCap :=
      mul_le_mul_of_nonneg_left ha.2 hcoef
    linarith
  linarith [hbound, hmax, hgap]

/-! ### Light's Theorem 1, locally -/

/-- **A household facing a slightly higher rate saves at least as much**, for CRRA with `γ ≤ 1`,
with every cap-slack hypothesis discharged from the minimal MPC. Positivity against arbitrary
concave continuations is the one hypothesis left, and it is free for CRRA (Inada). -/
theorem crra_policy_mono_withRate_of_minMPC {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hu : P.u = crraUtility γ)
    {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂)
    (hκ₁ : 0 < (P.withRate r₁ h₁).minMPC γ) (hκ₂ : 0 < (P.withRate r₂ h₂).minMPC γ)
    (hβ : 0 < (P.discount : ℝ)) (hβR₂ : (P.discount : ℝ) * (1 + r₂) < 1)
    (hpc₁ : (P.withRate r₁ h₁).PositiveConsumptionAll)
    (hpc₂ : (P.withRate r₂ h₂).PositiveConsumptionAll)
    (hthr₁ : (1 - (P.withRate r₁ h₁).minMPC γ) * (P.maxIncome + (1 + r₁) * assetCap) < assetCap)
    (hthr₂ : (1 - (P.withRate r₂ h₂).minMPC γ) * (P.maxIncome + (1 + r₂) * assetCap) < assetCap)
    (hgap : (1 - (P.withRate r₁ h₁).minMPC γ) * P.maxIncome
      + ((1 - (P.withRate r₁ h₁).minMPC γ) * (1 + r₁) + (r₂ - r₁)) * assetCap < assetCap)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z) :
    (P.withRate r₁ h₁).policy (a, z) ≤ (P.withRate r₂ h₂).policy (a, z) := by
  have hβR₁ : (P.discount : ℝ) * (1 + r₁) < 1 := by nlinarith [hβ]
  -- positivity at the iterates, read in either economy
  have hpos₁ : ∀ n : ℕ, ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap, 0 <
      (P.withRate r₁ h₁).consumptionFnOf
        (((P.withRate r₁ h₁).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a :=
    fun n z a ha => hpc₁ _ ((P.withRate r₁ h₁).concaveSlices_iterate_zero n) z a ha
  have hpos₂ : ∀ n : ℕ, ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap, 0 <
      (P.withRate r₂ h₂).consumptionFnOf
        (((P.withRate r₂ h₂).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a :=
    fun n z a ha => hpc₂ _ ((P.withRate r₂ h₂).concaveSlices_iterate_zero n) z a ha
  have hposv : ∀ n : ℕ, ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap, 0 <
      (P.withRate r₂ h₂).consumptionFnOf
        (((P.withRate r₁ h₁).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a :=
    fun n z a ha => hpc₂ _ ((P.withRate r₁ h₁).concaveSlices_iterate_zero n) z a ha
  -- cap slack along economy 2's own iteration, from its minimal MPC
  have hslackw : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      (P.withRate r₂ h₂).policyOf
        (((P.withRate r₂ h₂).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < assetCap :=
    fun n a ha z => ((P.withRate r₂ h₂).crra_minMPC_of_cap hγ0 hu rfl
      hκ₂ hβ hβR₂ hpos₂ hthr₂ n).2 a ha z
  -- Carroll--Kimball along economy 2's iteration
  have hcons : ∀ n : ℕ, ∀ z : Z, ConcaveOn ℝ (Icc (0 : ℝ) assetCap)
      ((P.withRate r₂ h₂).consumptionFnOf
        (((P.withRate r₂ h₂).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z) :=
    (P.withRate r₂ h₂).concaveOn_consumptionFnOf_iterates_of_hara hγ0 le_rfl hβ
      (by rw [haraUtility_zero_shift]; exact hu) hpos₂
      (fun n a ha z => (P.withRate r₂ h₂).policyOf_lt_maxSaving_of_pos (hpos₂ n z a ha)
        (hslackw n a ha z))
  exact P.policy_mono_withRate_hara hγ0 hγ1 le_rfl (by rw [haraUtility_zero_shift]; exact hu)
    h₁ h₂ hr (fun n a ha z => hposv n z a ha) (fun n a ha z => hpos₂ n z a ha)
    (fun n a ha z => P.crra_policyOf_withRate_lt_cap hγ0 hu h₁ h₂ hr hκ₁ hβ hβR₁ hpos₁ hthr₁
      hgap n ha z)
    hslackw hcons ha z

end IncomeFluctuation

end LeanEconomics

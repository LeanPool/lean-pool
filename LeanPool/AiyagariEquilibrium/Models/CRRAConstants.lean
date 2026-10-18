/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Models.BoundedIncomeFluctuation
public import LeanPool.AiyagariEquilibrium.Models.NaturalAssetBound

/-!
# The quantitative constants for CES

The equilibrium programme runs on four explicit constants: a lower bound on the secant slope of
`u` (which drives the corner condition and the precautionary gain), an upper bound on it (which
gives the value function its Lipschitz constant), a bound on saving (which gives the decline
condition), and the calibration arithmetic that checks they fit together. All four were computed
for `Real.log`, and `hu : P.u = Real.log` propagated through the whole chain.

The common derivative formula `hasDerivAt_crraUtility` covers every `γ > 0`, including log,
so the marginal bounds also cover that case. The closed form `crraSlopeBound` is used only
when `γ ≠ 1`; the logarithmic slope bound is evaluated separately as `2 log 2 / m`.

## The one place the shape changes

For log, marginal utility is `1/c`, so the slope bound available at resources `R` is `1/R` — it
DEGRADES as resources grow, and the multiplicative bound `c ≥ R / (1 + 2G)` is the right output.
For CES with `γ < 1` marginal utility is `c^{-γ}`, and on a capped problem `c ≤ maxConsumption`,
so there is a single slope `maxConsumption ^ (-γ)` that works everywhere. That turns the same
deviation argument into a UNIFORM bound on saving — `policy s ≤ K` for one constant `K` — which
is a cleaner route to the decline condition than the multiplicative bound, and the natural asset
bound falls straight out of it.

`policy_le_of_marginal_bound` is stated for any `u` with a uniform slope bound, so log gets the
uniform version too, with `m = 1 / maxConsumption`.
-/

@[expose] public section

open scoped NNReal
open Set Filter Topology MeasureTheory

namespace LeanEconomics

/-! ### Rational exponents reduce to integer powers

At `γ = 1 - 1/n` every exponent the CES constants produce is `m/n` for integers `m, n`, and a
comparison of `x ^ (m/n)` against a rational is equivalent to one of `x ^ m` against `c ^ n`.
These two lemmas are the whole bridge, and they are what keeps `γ` near 1 arithmetically
tractable: `norm_num` settles the integer form. -/

theorem rpow_le_of_pow_le {x c p : ℝ} {m n : ℕ} (hn : n ≠ 0) (hx : 0 ≤ x) (hc : 0 ≤ c)
    (hp : p = (m : ℝ) / n) (h : x ^ m ≤ c ^ n) : x ^ p ≤ c := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have h1 : x ^ p = (x ^ m) ^ ((n : ℝ)⁻¹) := by
    rw [hp, div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
  have h2 : c = (c ^ n) ^ ((n : ℝ)⁻¹) := by
    rw [← Real.rpow_natCast c n, ← Real.rpow_mul hc, mul_inv_cancel₀ hn'.ne', Real.rpow_one]
  calc x ^ p = (x ^ m) ^ ((n : ℝ)⁻¹) := h1
    _ ≤ (c ^ n) ^ ((n : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = c := h2.symm

/-! ### Negative exponents without a root

The gain and cost sides of the supply floor are both `x ^ (-γ)`. When the base sits on the right
side of one these need no root at all: a base above one makes the power at most one, and a base
below one makes it at most the reciprocal (for `γ ≤ 1`). That covers the COST side of every
calibration, where the base is `η + income - t` with `t` small. The GAIN side, where the base is
small and the bound has to be large, is where a root is genuinely needed —
`le_rpow_neg_of_rpow_le` hands it back to `rpow_le_of_pow_le`. -/

/-- A base of at least one makes the negative power at most one. -/
theorem rpow_neg_le_one_of_one_le {x γ : ℝ} (hx : 1 ≤ x) (hγ : 0 ≤ γ) : x ^ (-γ) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)

/-- A base of at most one makes the negative power at most the reciprocal, when `γ ≤ 1`. -/
theorem rpow_neg_le_inv_of_le_one {x γ : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hγ : γ ≤ 1) :
    x ^ (-γ) ≤ x⁻¹ := by
  have h := Real.rpow_le_rpow_of_exponent_ge hx hx1 (show (-1 : ℝ) ≤ -γ by linarith)
  rwa [Real.rpow_neg_one] at h

/-- The gain side: a bound on `x ^ γ` from above is a bound on `x ^ (-γ)` from below. -/
theorem le_rpow_neg_of_rpow_le {x q γ : ℝ} (hx : 0 < x) (hq : 0 < q) (h : x ^ γ ≤ q⁻¹) :
    q ≤ x ^ (-γ) := by
  have hpos : (0 : ℝ) < x ^ γ := Real.rpow_pos_of_pos hx _
  rw [Real.rpow_neg hx.le, le_inv_comm₀ hq hpos]
  exact h

theorem le_rpow_of_pow_le {x c p : ℝ} {m n : ℕ} (hn : n ≠ 0) (hx : 0 ≤ x) (hc : 0 ≤ c)
    (hp : p = (m : ℝ) / n) (h : c ^ n ≤ x ^ m) : c ≤ x ^ p := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have h1 : x ^ p = (x ^ m) ^ ((n : ℝ)⁻¹) := by
    rw [hp, div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
  have h2 : c = (c ^ n) ^ ((n : ℝ)⁻¹) := by
    rw [← Real.rpow_natCast c n, ← Real.rpow_mul hc, mul_inv_cancel₀ hn'.ne', Real.rpow_one]
  calc c = (c ^ n) ^ ((n : ℝ)⁻¹) := h2
    _ ≤ (x ^ m) ^ ((n : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = x ^ p := h1.symm

/-! ### Secant slopes of CRRA, bounded below -/

/-- **The secant slope of CRRA on `(0, R]` is at least `R ^ (-γ)`.** This is
`log_marginal_bound` for every `γ > 0` at once: at `γ = 1` the bound `R ^ (-1)` is `1 / R`. -/
theorem crra_marginal_bound {γ R : ℝ} (hγ : 0 < γ) {c d : ℝ} (hd : 0 < d) (hdc : d ≤ c)
    (hcR : c ≤ R) : R ^ (-γ) * (c - d) ≤ crraUtility γ c - crraUtility γ d := by
  rcases eq_or_lt_of_le hdc with rfl | hlt
  · simp
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (crraUtility γ)
    (fun x => x ^ (-γ)) hlt
    ((continuousOn_crraUtility γ).mono fun x hx => lt_of_lt_of_le hd hx.1)
    (fun x hx => hasDerivAt_crraUtility γ (hd.trans hx.1))
  have hmono : R ^ (-γ) ≤ ξ ^ (-γ) :=
    rpow_neg_antitone hγ (hd.trans hξ.1) (hξ.2.le.trans hcR)
  rw [hslope, le_div_iff₀ (by linarith)] at hmono
  linarith

/-- **The bound reaches `d = 0` when `γ < 1`.** Utility is finite there, so the statement makes
sense, and the first unit of consumption is worth at least as much as any later one. This is the
case log cannot have. -/
theorem crra_marginal_bound_zero {γ R : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) {c : ℝ}
    (hc : 0 < c) (hcR : c ≤ R) :
    R ^ (-γ) * (c - 0) ≤ crraUtility γ c - crraUtility γ 0 := by
  have hM : R ^ (-γ) ≤ c ^ (-γ) := rpow_neg_antitone hγ0 hc hcR
  have hmul : c ^ (-γ) * c = c ^ (1 - γ) := by
    have hadd := Real.rpow_add hc (-γ) 1
    rw [Real.rpow_one] at hadd
    rw [← hadd, show -γ + 1 = 1 - γ from by ring]
  have h1 : R ^ (-γ) * c ≤ c ^ (1 - γ) := by
    rw [← hmul]; exact mul_le_mul_of_nonneg_right hM hc.le
  have h2 : (0 : ℝ) ≤ c ^ (1 - γ) := (Real.rpow_pos_of_pos hc _).le
  rw [crraUtility_zero hγ1, crraUtility_of_ne (show γ ≠ 1 by linarith), sub_zero, sub_zero,
    le_div_iff₀ (show (0 : ℝ) < 1 - γ by linarith)]
  nlinarith

/-- The slope bound on all of `Ici 0`, which is the domain CES with `γ < 1` uses. -/
theorem crra_marginal_bound_Ici {γ R : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) {c d : ℝ}
    (hd : d ∈ Ici (0 : ℝ)) (hdc : d ≤ c) (hcR : c ≤ R) :
    R ^ (-γ) * (c - d) ≤ crraUtility γ c - crraUtility γ d := by
  rcases (mem_Ici.mp hd).lt_or_eq with hdpos | hd0
  · exact crra_marginal_bound hγ0 hdpos hdc hcR
  rcases eq_or_lt_of_le (hd0 ▸ hdc : (0 : ℝ) ≤ c) with hc0 | hcpos
  · rw [← hd0, ← hc0]; simp
  · rw [← hd0]; exact crra_marginal_bound_zero hγ0 hγ1 hcpos hcR

/-- **The gain from `d` extra consumption, bounded below.** Taking `R = c + d` in
`crra_marginal_bound` gives the CES form of `log_sub_log_ge`. -/
theorem crra_sub_ge {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) :
    (c + d) ^ (-γ) * d ≤ crraUtility γ (c + d) - crraUtility γ c := by
  have := crra_marginal_bound_Ici hγ0 hγ1 (mem_Ici.mpr hc) (le_add_of_nonneg_right hd)
    (le_refl (c + d))
  simpa using this

/-- **The secant slope of CRRA on `[d, c]` is at most `d ^ (-γ)`.** The mirror image of
`crra_marginal_bound`, and what caps the COST of saving. -/
theorem crra_marginal_bound_above {γ : ℝ} (hγ : 0 < γ) {c d : ℝ} (hd : 0 < d) (hdc : d ≤ c) :
    crraUtility γ c - crraUtility γ d ≤ d ^ (-γ) * (c - d) := by
  rcases eq_or_lt_of_le hdc with rfl | hlt
  · simp
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (crraUtility γ)
    (fun x => x ^ (-γ)) hlt
    ((continuousOn_crraUtility γ).mono fun x hx => lt_of_lt_of_le hd hx.1)
    (fun x hx => hasDerivAt_crraUtility γ (hd.trans hx.1))
  have hmono : ξ ^ (-γ) ≤ d ^ (-γ) := rpow_neg_antitone hγ hd hξ.1.le
  rw [hslope, div_le_iff₀ (by linarith)] at hmono
  linarith

/-- **The cost of saving `h`, capped uniformly in resources.** Resources are at least `m`, so what
is left after saving is at least `m - h`, and marginal utility there is the largest that can
apply. The log form of the same bound is `log (m / (m - h))`. -/
theorem crra_cost_of_saving {γ : ℝ} (hγ : 0 < γ) {m h R b : ℝ} (hh0 : 0 < h) (hhm : h < m)
    (hmR : m ≤ R) (hb0 : 0 ≤ b) (hbh : b ≤ h) :
    crraUtility γ (R - b) - crraUtility γ (R - h) ≤ (m - h) ^ (-γ) * h := by
  have hRh : 0 < R - h := by linarith
  have hstep := crra_marginal_bound_above hγ hRh (show R - h ≤ R - b by linarith)
  have hanti : (R - h) ^ (-γ) ≤ (m - h) ^ (-γ) :=
    rpow_neg_antitone hγ (by linarith) (by linarith)
  have hpos : (0 : ℝ) < (R - h) ^ (-γ) := Real.rpow_pos_of_pos hRh _
  nlinarith [hstep, hanti, hb0]

/-! ### Secant slopes of CRRA, bounded above -/

/-- The closed form of `slopeBound (crraUtility γ)` at the income floor for `γ ≠ 1`.
The literal expression below evaluates to zero at `γ = 1` under total real division, so
the logarithmic case uses `log_slopeBoundU` separately. -/
noncomputable def crraSlopeBound (γ m : ℝ) : ℝ :=
  2 * m ^ (-γ) * (1 - ((2 : ℝ) ^ (1 - γ))⁻¹) / (1 - γ)

theorem slopeBound_crraUtility {γ m : ℝ} (hγ : γ ≠ 1) (hm : 0 < m) :
    slopeBound (crraUtility γ) m = crraSlopeBound γ m := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (1 - γ) := Real.rpow_pos_of_pos (by norm_num) _
  have hhalf : (m / 2) ^ (1 - γ) = m ^ (1 - γ) / (2 : ℝ) ^ (1 - γ) :=
    Real.div_rpow hm.le (by norm_num : (0 : ℝ) ≤ 2) (1 - γ)
  have hexp : m ^ (1 - γ) = m * m ^ (-γ) := by
    have h := Real.rpow_add hm 1 (-γ)
    rw [Real.rpow_one, show (1 : ℝ) + -γ = 1 - γ from by ring] at h
    exact h
  have hγ' : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  simp only [slopeBound, crraSlopeBound, crraUtility_of_ne hγ, hhalf, hexp]
  field_simp

theorem crraSlopeBound_nonneg {γ m : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hm : 0 < m) :
    0 ≤ crraSlopeBound γ m := by
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (1 - γ) :=
    Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) (by linarith)
  have hinv : ((2 : ℝ) ^ (1 - γ))⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by linarith)]; exact h2
  have hmp : (0 : ℝ) < m ^ (-γ) := Real.rpow_pos_of_pos hm _
  refine div_nonneg ?_ (by linarith)
  have : (0 : ℝ) ≤ 1 - ((2 : ℝ) ^ (1 - γ))⁻¹ := by linarith
  positivity

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
-- This layer is the CALIBRATED one: every constant is computed for a household whose borrowing
-- limit is at zero. The general-floor machinery lives upstream; nothing here needs it, and
-- pinning the floor keeps the arithmetic in the primitives.
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-- **A uniform bound on saving from a uniform marginal bound.** Deviate to half the optimal
saving: the extra consumption is worth at least `m` per unit, and concavity of the continuation
caps what the forgone saving could have repaid at `deviationGap`, whatever the state.

The log development could not use this, because for log the available `m` at resources `R` is
`1 / R`, which is not uniform. It is stated generically anyway — log gets the version with
`m = 1 / maxConsumption`, which is uniform after all, just weaker than what the multiplicative
argument extracts. For CES with `γ < 1` the uniform `m = maxConsumption ^ (-γ)` is all there is,
and it is enough. -/
theorem policy_le_of_marginal_bound {m : ℝ} (hm : 0 < m)
    (hmarg : ∀ c d : ℝ, d ∈ P.dom → d ≤ c → c ≤ P.maxConsumption → m * (c - d) ≤ P.u c - P.u d)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z) :
    P.policy (a, z) ≤ 2 * P.deviationGap / m := by
  have h := P.policyOf_le_of_marginal_bound P.concaveOn_valueFunction hm hmarg ha z
  rw [P.policyOf_valueFunction, zero_add] at h
  convert h using 1
  dsimp [deviationGap]
  ring

/-! ### The oscillation gap

`deviationGap = 2 β ‖V‖` is not translation-invariant. For CES, subtracting
`1 / (1-γ)` from `c ^ (1-γ) / (1-γ)` gives the normalization that tends to `log c`
as `γ → 1` for positive `c`; it is not an equality with `log c` at a fixed `γ ≠ 1`.
A value-norm bound is sensitive to that additive utility constant. The comparisons here use
DIFFERENCES of continuation values, so an oscillation bound avoids this normalization dependence:
`(u maxConsumption - u minConsumption) / (1 - β)`. -/

/-- The spread of the value function, from the two constant plans. -/
noncomputable def oscGap : ℝ :=
  (P.u P.maxConsumption - P.u P.minConsumption) / (1 - P.discount)

theorem oscGap_nonneg : 0 ≤ P.oscGap := by
  have hβ : (P.discount : ℝ) < 1 := by exact_mod_cast P.discount_lt_one
  refine div_nonneg (sub_nonneg.mpr ?_) (by linarith)
  exact P.monotoneOn_u_dom (P.mem_dom_of_pos P.minConsumption_pos)
    (P.mem_dom_of_pos P.maxConsumption_pos) P.minConsumption_le_maxConsumption

/-- **The continuation value moves by at most the oscillation gap**, whatever the two saving
levels. This is what replaces `2 ‖V‖` in every comparison. -/
theorem cont_sub_le_oscGap (z : Z) (x y : ℝ) : P.cont z x - P.cont z y ≤ P.oscGap := by
  have hsub : P.cont z x - P.cont z y
      = ∑ z' : Z, P.transitionMatrix z z' *
          (P.toExtended.valueFunction (x, z') - P.toExtended.valueFunction (y, z')) := by
    simp only [cont, ← Finset.sum_sub_distrib, ← mul_sub]
  rw [hsub]
  calc ∑ z' : Z, P.transitionMatrix z z' *
        (P.toExtended.valueFunction (x, z') - P.toExtended.valueFunction (y, z'))
      ≤ ∑ z' : Z, P.transitionMatrix z z' * P.oscGap := by
        refine Finset.sum_le_sum fun z' _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (P.transitionMatrix_nonneg _ _)
        simp only [oscGap, sub_div]
        linarith [P.valueFunction_le_oscBound (x, z'), P.oscBound_le_valueFunction (y, z')]
    _ = P.oscGap := by rw [← Finset.sum_mul, P.transitionMatrix_sum, one_mul]

/-- The Lipschitz constant of the value function under CES, mirroring `logLipschitz`. -/
noncomputable def crraLipschitz (γ : ℝ) : ℝ :=
  crraSlopeBound γ P.minConsumption * (1 + P.interest) / (1 - P.discount * (1 + P.interest))

theorem crraLipschitz_nonneg {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hβR : P.discount * (1 + P.interest) < 1) : 0 ≤ P.crraLipschitz γ := by
  have hs := crraSlopeBound_nonneg hγ0 hγ1 P.minConsumption_pos
  have hr := P.interest_gt_neg_one
  exact div_nonneg (by positivity) (by linarith)

/-- **The value function is Lipschitz with the explicit CES constant.** -/
theorem crra_valueFunction_lipschitz {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hu : P.u = crraUtility γ) (hβR : P.discount * (1 + P.interest) < 1) :
    ∀ z : Z, ∀ x ∈ Icc (0 : ℝ) assetCap, ∀ y ∈ Icc (0 : ℝ) assetCap,
      |P.toExtended.valueFunction (x, z) - P.toExtended.valueFunction (y, z)|
        ≤ P.crraLipschitz γ * |x - y| := by
  refine P.valueFunction_lipschitz (P.crraLipschitz_nonneg hγ0 hγ1 hβR) (le_of_eq ?_)
  have hne : (1 : ℝ) - P.discount * (1 + P.interest) ≠ 0 := by linarith
  simp only [crraLipschitz, slopeBoundU, hu,
    slopeBound_crraUtility (show γ ≠ 1 by linarith) P.minConsumption_pos]
  field_simp
  ring

/-- **The borrowing constraint binds where resources are small**, CES version. The threshold is
`resources ^ (-γ)` where the log version had `1 / resources`. -/
theorem crra_policy_eq_zero_of_resources {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hb : P.Bounded) (hu : P.u = crraUtility γ)
    (hβR : P.discount * (1 + P.interest) < 1) {s : ℝ × Z} (hs : s.1 ∈ Icc (0 : ℝ) assetCap)
    (hlt : P.discount * P.crraLipschitz γ < P.resources s ^ (-γ)) :
    P.policy s = 0 :=
  P.policy_eq_zero_of_corner_at (P.crra_valueFunction_lipschitz hγ0 hγ1 hu hβR) hs
    (fun c d hd hdc hc => by
      rw [hu]
      rw [sub_zero] at hc
      exact crra_marginal_bound_Ici hγ0 hγ1 (by rw [hb] at hd; exact hd) hdc hc)
    hlt

/-- **The CES saving bound in closed form.** Saving never exceeds `2 · deviationGap ·
maxConsumption ^ γ`, whatever the state. -/
theorem crra_policy_le {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hb : P.Bounded)
    (hu : P.u = crraUtility γ) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap)
    (z : Z) : P.policy (a, z) ≤ 2 * P.deviationGap * P.maxConsumption ^ γ := by
  have hmc := P.maxConsumption_pos
  have hm : (0 : ℝ) < P.maxConsumption ^ (-γ) := Real.rpow_pos_of_pos hmc _
  have hkey := P.policy_le_of_marginal_bound hm
    (fun c d hd hdc hc => by
      rw [hu]
      exact crra_marginal_bound_Ici hγ0 hγ1 (by rw [hb] at hd; exact hd) hdc hc)
    ha z
  have hinv : P.maxConsumption ^ (-γ) = (P.maxConsumption ^ γ)⁻¹ := Real.rpow_neg hmc.le γ
  rw [hinv, div_eq_mul_inv, inv_inv] at hkey
  exact hkey

/-- **The natural asset bound for CES.** A uniform cap on saving is a decline condition outright:
above it, assets fall. No linear consumption bound and no `exp` in sight. -/
theorem crra_exists_decline {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hb : P.Bounded)
    (hu : P.u = crraUtility γ) (z : Z) :
    ∃ ā : ℝ, ∀ a ∈ Icc (0 : ℝ) assetCap, ā < a → P.policy (a, z) < a :=
  ⟨2 * P.deviationGap * P.maxConsumption ^ γ, fun _ ha hlt =>
    lt_of_le_of_lt (P.crra_policy_le hγ0 hγ1 hb hu ha _) hlt⟩

/-- **The continuation's gain between two saving levels, CES version.** Where the log form carries
`log (1 + R·(y-x) / (income + R·x))`, this carries `(income + R·y) ^ (-γ) · R·(y-x)`: the extra
resources, valued at the marginal utility of the largest consumption they could buy. -/
theorem crra_cont_sub_ge_gen {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hu : P.u = crraUtility γ) (hpc : P.PositiveConsumption) (z z₀ : Z) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) assetCap) (hy : y ∈ Icc (0 : ℝ) assetCap) (hxy : x ≤ y) :
    P.transitionMatrix z z₀ * ((P.income z₀ + (1 + P.interest) * y) ^ (-γ)
        * ((1 + P.interest) * (y - x)))
      ≤ P.cont z y - P.cont z x := by
  have hRh : 0 ≤ (1 + P.interest) * (y - x) :=
    mul_nonneg P.interest_gt_neg_one.le (by linarith)
  have hsum : P.cont z y - P.cont z x = ∑ z' : Z, P.transitionMatrix z z' *
      (P.toExtended.valueFunction (y, z') - P.toExtended.valueFunction (x, z')) := by
    simp only [cont, ← Finset.sum_sub_distrib, ← mul_sub]
  have hterm : P.transitionMatrix z z₀ *
      (P.toExtended.valueFunction (y, z₀) - P.toExtended.valueFunction (x, z₀))
        ≤ P.cont z y - P.cont z x := by
    rw [hsum]
    refine Finset.single_le_sum (f := fun z' : Z => P.transitionMatrix z z' *
      (P.toExtended.valueFunction (y, z') - P.toExtended.valueFunction (x, z')))
      (fun z' _ => ?_) (Finset.mem_univ z₀)
    exact mul_nonneg (P.transitionMatrix_nonneg _ _)
      (by linarith [P.valueFunction_le_of_le hpc (z := z') hx hy hxy])
  have hc0 : 0 < P.consumption (x, z₀) (P.policy (x, z₀)) := P.consumption_policy_pos hpc hx
  have hresx : P.resources (x, z₀) = P.income z₀ + (1 + P.interest) * x := by
    simp only [resources, max_eq_right hx.1]
  have hcle : P.consumption (x, z₀) (P.policy (x, z₀))
      ≤ P.income z₀ + (1 + P.interest) * x := by
    simp only [consumption, hresx]
    linarith [(P.policy_mem_region (x, z₀)).1]
  have hgain := P.valueFunction_sub_ge hpc hx hy hxy z₀
  rw [hu] at hgain
  -- the marginal bound, at the largest consumption the richer state could reach
  have hbound : (P.income z₀ + (1 + P.interest) * y) ^ (-γ) * ((1 + P.interest) * (y - x))
      ≤ crraUtility γ (P.consumption (x, z₀) (P.policy (x, z₀)) + (1 + P.interest) * (y - x))
        - crraUtility γ (P.consumption (x, z₀) (P.policy (x, z₀))) := by
    have hR : P.consumption (x, z₀) (P.policy (x, z₀)) + (1 + P.interest) * (y - x)
        ≤ P.income z₀ + (1 + P.interest) * y := by nlinarith [hcle]
    have := crra_marginal_bound_Ici hγ0 hγ1 (mem_Ici.mpr hc0.le)
      (le_add_of_nonneg_right hRh) hR
    simpa using this
  exact le_trans (mul_le_mul_of_nonneg_left (le_trans hbound hgain)
    (P.transitionMatrix_nonneg z z₀)) hterm

/-- **The continuation's gain from zero, CES version.** -/
theorem crra_cont_sub_ge {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hu : P.u = crraUtility γ) (hpc : P.PositiveConsumption) (z z₀ : Z) {h : ℝ}
    (hh : h ∈ Icc (0 : ℝ) assetCap) :
    P.transitionMatrix z z₀ * ((P.income z₀ + (1 + P.interest) * h) ^ (-γ)
        * ((1 + P.interest) * h))
      ≤ P.cont z h - P.cont z 0 := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) assetCap := ⟨le_rfl, P.assetCap_nonneg⟩
  have := P.crra_cont_sub_ge_gen hγ0 hγ1 hu hpc z z₀ h0 hh hh.1
  simpa using this

/-! ### The sharp decline constant

`crra_policy_le` bounds saving by a constant, which is enough for a natural asset bound but far
too weak for the corner condition to meet it: the corner needs the threshold to be comparable to
the LOW income, and an absolute bound does not shrink with it. The log development gets a
PROPORTIONAL bound instead, `c ≥ R / (1 + 2G)`, whose decline threshold is proportional to income.

The CES analogue deviates to `θ` times the optimal saving rather than to half of it, and prices
the extra consumption at the margin where it lands: `b ≤ (β · oscGap / θ) · (c + (1-θ) b) ^ γ`.
Taking `θ` near 1 makes the right-hand side nearly `(β · oscGap) c ^ γ`, proportional to
consumption, which is the shape the decline condition needs. -/

/-- **The proportional CES bound on saving.** -/
theorem crra_policy_le_mul {γ θ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (_hb : P.Bounded) (hu : P.u = crraUtility γ) (hpc : P.PositiveConsumption)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z) :
    P.policy (a, z)
      ≤ (P.discount * P.oscGap / θ)
        * (P.consumption (a, z) (P.policy (a, z)) + (1 - θ) * P.policy (a, z)) ^ γ := by
  have h := P.policyOf_le_mul_of_power_marginal (γ := γ) (η := 0) hθ0 hθ1
    P.concaveOn_valueFunction P.oscGap_nonneg
    (by simpa only [oscSpread, oscGap] using P.oscOn_valueFunction)
    (fun c d hc hcd _ => by
      simpa only [zero_add, hu] using
        crra_marginal_bound_Ici hγ0 hγ1 (P.nonneg_of_mem_dom hc) hcd (le_refl d)) ha z
    (by simpa only [zero_add, P.consumptionFnOf_valueFunction] using
      P.consumptionFn_pos hpc ha z)
  simpa only [P.policyOf_valueFunction, consumptionFnOf, zero_add, sub_zero] using h

/-- **Assets fall above an explicit threshold**, in the income state that matters. The threshold
is `(β · oscGap / θ) · (income z + (1 + r - θ) · assetCap) ^ γ`; with `θ` near one the second
factor is close to `income z ^ γ`, so the threshold shrinks with the income of the state -- which
is exactly what lets the corner condition reach it. -/
theorem crra_policy_lt_self {γ θ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hθr : θ ≤ 1 + P.interest) (hb : P.Bounded) (hu : P.u = crraUtility γ)
    (hpc : P.PositiveConsumption) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z)
    (hlt : (P.discount * P.oscGap / θ)
        * (P.income z + (1 + P.interest - θ) * assetCap) ^ γ < a) :
    P.policy (a, z) < a := by
  by_contra hcon
  rw [not_lt] at hcon
  have hosc := P.oscGap_nonneg
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  set b : ℝ := P.policy (a, z) with hbdef
  set c : ℝ := P.consumption (a, z) b with hcdef
  have hkey := P.crra_policy_le_mul hγ0 hγ1 hθ0 hθ1 hb hu hpc ha z
  rw [← hbdef, ← hcdef] at hkey
  have hres : P.resources (a, z) = P.income z + (1 + P.interest) * a := by
    simp only [resources, max_eq_right ha.1]
  have hsum : c + (1 - θ) * b = P.income z + (1 + P.interest) * a - θ * b := by
    simp only [hcdef, consumption, hres]; ring
  have hle : c + (1 - θ) * b ≤ P.income z + (1 + P.interest - θ) * assetCap := by
    rw [hsum]
    have h1 : θ * a ≤ θ * b := mul_le_mul_of_nonneg_left hcon hθ0.le
    have h2 : (1 + P.interest - θ) * a ≤ (1 + P.interest - θ) * assetCap :=
      mul_le_mul_of_nonneg_left ha.2 (by linarith)
    nlinarith [h1, h2]
  have hnn : (0 : ℝ) ≤ c + (1 - θ) * b := by
    have hc0 : 0 < c := by rw [hcdef, hbdef]; exact P.consumption_policy_pos hpc ha
    have : 0 ≤ (1 - θ) * b := mul_nonneg (by linarith) (P.policy_mem_region (a, z)).1
    linarith
  have hmono : (c + (1 - θ) * b) ^ γ
      ≤ (P.income z + (1 + P.interest - θ) * assetCap) ^ γ :=
    Real.rpow_le_rpow hnn hle hγ0.le
  have hscale : (P.discount * P.oscGap / θ) * (c + (1 - θ) * b) ^ γ
      ≤ (P.discount * P.oscGap / θ)
        * (P.income z + (1 + P.interest - θ) * assetCap) ^ γ :=
    mul_le_mul_of_nonneg_left hmono (by positivity)
  linarith

/-! ### The asset cap never binds

`not_concaveOn_consumptionFn_of_cap_binds` makes Carroll and Kimball's conclusion FALSE wherever
saving reaches the cap, so the cap is the obstruction to Light's uniqueness argument, not the
utility class. It can be removed by calibration rather than by weakening the theory: run
`crra_policy_le_mul` by contradiction. If saving reached the cap then consumption would be at
most `maxIncome + (1 + r - θ) · assetCap`, and the saving bound evaluated THERE has to exceed
the cap.

The point of doing it this way is that the bound does not degrade as the cap grows -- the
right-hand side rises with `assetCap` while the left rises only through `oscGap` -- so raising
the cap always eventually works. A cruder estimate that keeps `maxConsumption ^ γ` on the left
grows on both sides and closes the window for `γ` near one, which is an artefact of the
estimate.

Related literature: Marcet, Obiols-Homs and Weil (2007), *Incomplete Markets, Labor Supply
and Capital Accumulation*. The sufficient criterion below is specific to this capped household
model: it uses the displayed quantitative inequality, bounded utility and positive optimal
consumption. Its fixed-point and iterative versions share the same comparison argument. -/

/-- **Saving never reaches the asset cap.** -/
theorem crra_policy_lt_assetCap {γ θ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hb : P.Bounded) (hu : P.u = crraUtility γ)
    (hpc : P.PositiveConsumption)
    (hlt : (P.discount * P.oscGap / θ)
        * (P.maxIncome + (1 + P.interest - θ) * assetCap) ^ γ < assetCap)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z) :
    P.policy (a, z) < assetCap := by
  have h := P.policyOf_lt_cap_of_power_bound (η := 0) hγ0.le hθ0.le hθ1.le
    (show 0 ≤ (P.discount : ℝ) * P.oscGap / θ by
      exact div_nonneg (mul_nonneg P.discount.coe_nonneg P.oscGap_nonneg) hθ0.le)
    (v := P.toExtended.valueFunction) ha z
    (by simpa only [zero_add, P.consumptionFnOf_valueFunction] using
      (P.consumptionFn_pos hpc ha z).le)
    (by simpa only [P.policyOf_valueFunction, consumptionFnOf, zero_add, sub_zero] using
      P.crra_policy_le_mul hγ0 hγ1 hθ0 hθ1 hb hu hpc ha z)
    (by simpa only [zero_add, mul_zero, sub_zero] using hlt)
  simpa only [P.policyOf_valueFunction] using h

/-- **The disproof of Carroll and Kimball is disarmed.** Where saving never reaches the cap, the
hypothesis of `not_concaveOn_consumptionFn_of_cap_binds` -- a flat stretch of the policy at the
top of the asset region -- cannot occur, so nothing in this development contradicts concavity of
the consumption function. That is not a proof of concavity; it is the removal of the obstruction
that made one impossible. -/
theorem no_flat_at_cap {γ θ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hb : P.Bounded) (hu : P.u = crraUtility γ)
    (hpc : P.PositiveConsumption)
    (hlt : (P.discount * P.oscGap / θ)
        * (P.maxIncome + (1 + P.interest - θ) * assetCap) ^ γ < assetCap)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z) :
    P.policy (a, z) ≠ assetCap :=
  ne_of_lt (P.crra_policy_lt_assetCap hγ0 hγ1 hθ0 hθ1 hb hu hpc hlt ha z)

/-- **A quantitative CES saving floor**, the form the sign-change argument consumes. -/
theorem crra_policy_ge_of_gain {γ : ℝ} (hγ : 0 < γ) (hu : P.u = crraUtility γ)
    (hpc : P.PositiveConsumption) (z₁ : Z) {h : ℝ} (hh0 : 0 < h) (hhcap : h ≤ assetCap)
    (hhinc : h < P.income z₁)
    (hgain : (P.income z₁ - h) ^ (-γ) * h < P.discount * (P.cont z₁ h - P.cont z₁ (h / 2)))
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    h / 2 ≤ P.policy (a, z₁) := by
  refine P.policy_ge_of_cost rfl hpc z₁ hh0 hhcap hhinc (fun R b hm hb0 hbh => ?_) hgain ha
  rw [hu]
  exact crra_cost_of_saving hγ hh0 hhinc hm hb0 hbh

section Measure

variable [MeasurableSpace Z] [BorelSpace Z]

/-- **Positive aggregate capital for CES, from primitives alone.** The log condition
`log (m / (m - h)) < β · P z₁ z₀ · log (1 + R h / income z₀)` becomes
`(m - h) ^ (-γ) · h  <  β · P z₁ z₀ · (income z₀ + R h) ^ (-γ) · R h`: the saved unit priced at
the margin where consumption is lowest, against its return in the bad state. -/
theorem crra_aggregateCapital_pos_of_primitives {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hu : P.u = crraUtility γ) (hpc : P.PositiveConsumption)
    {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) {z₁ z₀ : Z} {p₀ : ℝ} (hp0 : 0 < p₀)
    (hp : ∀ z, p₀ ≤ P.transitionMatrix z z₁)
    {h : ℝ} (hh0 : 0 < h) (hhcap : h ≤ assetCap) (hhinc : h < P.income z₁)
    (hgain : (P.income z₁ - h) ^ (-γ) * h
      < P.discount * (P.transitionMatrix z₁ z₀
          * ((P.income z₀ + (1 + P.interest) * h) ^ (-γ) * ((1 + P.interest) * h)))) :
    0 < P.aggregateCapital μ := by
  refine P.aggregateCapital_pos_of_cost rfl hμ hp0 hp hh0 hhcap hhinc (fun R hm => ?_)
    (lt_of_lt_of_le hgain ?_)
  · rw [hu]
    simpa using crra_cost_of_saving hγ0 hh0 hhinc hm (le_refl (0 : ℝ)) hh0.le
  · exact mul_le_mul_of_nonneg_left (P.crra_cont_sub_ge hγ0 hγ1 hu hpc z₁ z₀ ⟨hh0.le, hhcap⟩)
      P.discount.coe_nonneg

end Measure

end IncomeFluctuation

end LeanEconomics

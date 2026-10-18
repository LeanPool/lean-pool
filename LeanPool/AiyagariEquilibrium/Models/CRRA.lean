/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuation
public import LeanPool.AiyagariEquilibrium.Analysis.RelativeRiskAversion


/-!
# CRRA utility, and where it fits

Two separate strands of the development each ask something of `u`, and this file specialises to
the CRRA family to see what they ask together.

* The income fluctuation structure requires `tendsto_atBot_u`: utility falls to `-∞` as
  consumption vanishes. That is what makes consumption positive at the optimum without a floor,
  and everything downstream — the policy, the distribution, the equilibrium — rests on it.
* Light (2018) requires relative risk aversion at most one, `RelativeRiskAversionLeOne`.

Within CRRA the first holds exactly when `γ ≥ 1` and the second exactly when `γ ≤ 1`, so
**together they hold only at `γ = 1`: log utility**. That is `crra_pinch`, the point of this file.

The pinch is sharp in both directions and neither side is an artefact of the proofs. For `γ < 1`
period utility is bounded below by zero, so it cannot tend to `-∞` under any argument
(`not_tendsto_atBot_crraUtility`); for `γ > 1` the utility is strictly CONCAVE in log consumption,
so `RelativeRiskAversionLeOne` fails as badly as it can
(`strictConcaveOn_crra_comp_exp`).

## What this says about the uniqueness programme

The formalisation's only worked witness, `NonVacuity.impatient`, uses `u c = -c⁻¹`, which is CRRA
with `γ = 2` (`crraUtility_two`). It satisfies the existence machinery and fails Light's
condition. Log utility is the one CRRA calibration where both can hold, and it sits on the
boundary of each — `u ∘ exp` is affine there, neither convex-strictly nor concave-strictly.

This is the parametric cost of the uniqueness argument stated exactly, and it matches what the
survey literature reports: Toda and Walsh (2024) call `RRA ≤ 1` "a quite strong parametric
restriction". Escaping `γ = 1` means giving up `tendsto_atBot_u`, which means carrying a
consumption floor or an Inada-free treatment of the corner — a different development, not a
different proof.

## The single derivative formula

`hasDerivAt_crraUtility` gives `u' c = c ^ (-γ)` for every `γ`, log included, since `log' c = c⁻¹`
is the `γ = 1` case. Monotonicity, strict concavity and the Inada condition are all read off it,
so the two branches of the definition are only ever separated once.
-/

@[expose] public section

open Set Filter Topology

namespace LeanEconomics

/-- **CRRA period utility.** `c ^ (1 - γ) / (1 - γ)`, with the removable case `γ = 1` filled in
by `log`, which is its limit. -/
noncomputable def crraUtility (γ c : ℝ) : ℝ :=
  if γ = 1 then Real.log c else c ^ (1 - γ) / (1 - γ)

theorem crraUtility_of_ne {γ : ℝ} (h : γ ≠ 1) (c : ℝ) :
    crraUtility γ c = c ^ (1 - γ) / (1 - γ) := by simp [crraUtility, h]

@[simp] theorem crraUtility_one : crraUtility 1 = Real.log := by
  funext c; simp [crraUtility]

/-- The existing non-vacuity witness `u c = -c⁻¹` is CRRA with `γ = 2`. -/
theorem crraUtility_two : crraUtility 2 = fun c : ℝ => -c⁻¹ := by
  funext c
  rw [crraUtility_of_ne (by norm_num), show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one]
  ring

/-! ### The derivative, and everything read off it -/

/-- **Marginal utility is `c ^ (-γ)`**, log included. -/
theorem hasDerivAt_crraUtility (γ : ℝ) {c : ℝ} (hc : 0 < c) :
    HasDerivAt (crraUtility γ) (c ^ (-γ)) c := by
  rcases eq_or_ne γ 1 with rfl | hγ
  · rw [crraUtility_one, show -(1 : ℝ) = -1 from rfl, Real.rpow_neg_one]
    exact Real.hasDerivAt_log hc.ne'
  · have h : HasDerivAt (fun x : ℝ => x ^ (1 - γ)) ((1 - γ) * c ^ (1 - γ - 1)) c :=
      Real.hasDerivAt_rpow_const (Or.inl hc.ne')
    have h2 := h.div_const (1 - γ)
    have hne : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
    rw [show (1 - γ) * c ^ (1 - γ - 1) / (1 - γ) = c ^ (-γ) by
      rw [show (1 : ℝ) - γ - 1 = -γ by ring]; field_simp] at h2
    exact h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => crraUtility_of_ne hγ x)

theorem deriv_crraUtility (γ : ℝ) {c : ℝ} (hc : 0 < c) :
    deriv (crraUtility γ) c = c ^ (-γ) := (hasDerivAt_crraUtility γ hc).deriv

theorem continuousOn_crraUtility (γ : ℝ) : ContinuousOn (crraUtility γ) (Ioi 0) :=
  fun _ hc => ((hasDerivAt_crraUtility γ hc).continuousAt).continuousWithinAt

theorem strictMonoOn_crraUtility (γ : ℝ) : StrictMonoOn (crraUtility γ) (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) (continuousOn_crraUtility γ) fun c hc => ?_
  rw [interior_Ioi] at hc
  rw [deriv_crraUtility γ hc]
  exact Real.rpow_pos_of_pos hc _

theorem monotoneOn_crraUtility (γ : ℝ) : MonotoneOn (crraUtility γ) (Ioi 0) :=
  (strictMonoOn_crraUtility γ).monotoneOn

theorem strictConcaveOn_crraUtility {γ : ℝ} (hγ : 0 < γ) :
    StrictConcaveOn ℝ (Ioi 0) (crraUtility γ) := by
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi 0) (continuousOn_crraUtility γ)
    fun x hx y hy hxy => ?_
  rw [interior_Ioi] at hx hy
  rw [deriv_crraUtility γ hx, deriv_crraUtility γ hy, Real.rpow_neg hx.le, Real.rpow_neg hy.le]
  rw [inv_lt_inv₀ (Real.rpow_pos_of_pos hy _) (Real.rpow_pos_of_pos hx _)]
  exact Real.rpow_lt_rpow hx.le hxy hγ

/-! ### The Inada condition holds exactly for `γ ≥ 1` -/

theorem tendsto_atBot_crraUtility {γ : ℝ} (hγ : 1 ≤ γ) :
    Tendsto (crraUtility γ) (𝓝[>] 0) atBot := by
  rcases eq_or_lt_of_le hγ with rfl | hγ1
  · rw [crraUtility_one]; exact Real.tendsto_log_nhdsGT_zero
  · have hpos : (0 : ℝ) < γ - 1 := by linarith
    have hcont : Tendsto (fun c : ℝ => c ^ (γ - 1)) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun x : ℝ => x ^ (γ - 1)) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ (γ - 1))) :=
        (Real.continuousAt_rpow_const 0 (γ - 1) (Or.inr hpos.le)).continuousWithinAt
      rwa [Real.zero_rpow hpos.ne'] at h
    have hwithin : Tendsto (fun c : ℝ => c ^ (γ - 1)) (𝓝[>] 0) (𝓝[>] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hcont
        (eventually_nhdsWithin_of_forall fun c hc => Real.rpow_pos_of_pos hc _)
    have hinv : Tendsto (fun c : ℝ => (c ^ (γ - 1))⁻¹) (𝓝[>] 0) atTop :=
      tendsto_inv_nhdsGT_zero.comp hwithin
    have hrw : Tendsto (fun c : ℝ => c ^ (1 - γ)) (𝓝[>] 0) atTop := by
      refine hinv.congr' (eventually_nhdsWithin_of_forall fun c hc => ?_)
      have hcc : c ^ (1 - γ) = (c ^ (γ - 1))⁻¹ := by
        rw [show (1 : ℝ) - γ = -(γ - 1) by ring, Real.rpow_neg (le_of_lt hc)]
      exact hcc.symm
    have hneg : (1 : ℝ) / (1 - γ) < 0 := by
      apply div_neg_of_pos_of_neg one_pos; linarith
    refine (hrw.const_mul_atTop_of_neg hneg).congr fun c => ?_
    rw [crraUtility_of_ne (by linarith : γ ≠ 1)]
    ring

/-- **For `γ < 1` the Inada condition fails**, and not for want of an argument: period utility is
then bounded below by zero, so it cannot tend to `-∞` along any filter that is not trivial. -/
theorem not_tendsto_atBot_crraUtility {γ : ℝ} (hγ : γ < 1) :
    ¬ Tendsto (crraUtility γ) (𝓝[>] 0) atBot := by
  intro h
  have hnn : ∀ᶠ c : ℝ in 𝓝[>] 0, (0 : ℝ) ≤ crraUtility γ c :=
    eventually_nhdsWithin_of_forall fun c hc => by
      rw [crraUtility_of_ne (by linarith : γ ≠ 1)]
      exact div_nonneg (Real.rpow_nonneg (le_of_lt hc) _) (by linarith)
  have hlt : ∀ᶠ c : ℝ in 𝓝[>] 0, crraUtility γ c < 0 := h.eventually (eventually_lt_atBot 0)
  obtain ⟨c, hc1, hc2⟩ := (hnn.and hlt).exists
  linarith

/-! ### The pinch -/

/-- **Relative risk aversion at most one holds for CRRA exactly when `γ ≤ 1`.** -/
theorem relativeRiskAversionLeOne_crraUtility_iff {γ : ℝ} :
    RelativeRiskAversionLeOne (crraUtility γ) ↔ γ ≤ 1 := by
  rcases lt_trichotomy γ 1 with h | rfl | h
  · refine ⟨fun _ => h.le, fun _ => ?_⟩
    have he : crraUtility γ = fun c => c ^ (1 - γ) / (1 - γ) :=
      funext (crraUtility_of_ne (by linarith))
    rw [he]
    exact relativeRiskAversionLeOne_crra h
  · simpa using relativeRiskAversionLeOne_log
  · refine ⟨fun hcon => absurd hcon ?_, fun hle => absurd h (by linarith)⟩
    have he : crraUtility γ = fun c => c ^ (1 - γ) / (1 - γ) :=
      funext (crraUtility_of_ne (by linarith))
    rw [he]
    exact not_relativeRiskAversionLeOne_crra h

/-- **The two requirements pinch CRRA to log utility.** The income fluctuation structure needs
utility to fall to `-∞` at zero consumption, which forces `γ ≥ 1`; Light's uniqueness argument
needs relative risk aversion at most one, which forces `γ ≤ 1`. -/
theorem crra_pinch {γ : ℝ} :
    (Tendsto (crraUtility γ) (𝓝[>] 0) atBot ∧ RelativeRiskAversionLeOne (crraUtility γ))
      ↔ γ = 1 := by
  constructor
  · rintro ⟨hinada, hrra⟩
    have hge : 1 ≤ γ := by
      by_contra hlt
      exact not_tendsto_atBot_crraUtility (by linarith) hinada
    have hle : γ ≤ 1 := relativeRiskAversionLeOne_crraUtility_iff.mp hrra
    linarith
  · rintro rfl
    exact ⟨tendsto_atBot_crraUtility le_rfl, relativeRiskAversionLeOne_crraUtility_iff.mpr le_rfl⟩

/-- The existing witness fails Light's condition, as `γ = 2 > 1` requires. -/
theorem not_relativeRiskAversionLeOne_neg_inv :
    ¬ RelativeRiskAversionLeOne fun c : ℝ => -c⁻¹ := by
  rw [← crraUtility_two]
  exact fun h => absurd (relativeRiskAversionLeOne_crraUtility_iff.mp h) (by norm_num)

/-! ### A log-utility economy

The pinch is not vacuous: `γ = 1` really is an income fluctuation problem. This is
`NonVacuity.impatient` with its `-c⁻¹` — which is `γ = 2` by `crraUtility_two` — replaced by log,
so the two witnesses sit on either side of Light's condition, and every utility axiom is now
discharged by a single lemma about the CRRA family. -/

/-- An impatient household with log utility: `β = 1/100`, `r = 0`, income in `{1, 2}`, cap `1`. -/
noncomputable def logImpatient : IncomeFluctuation (Fin 2) 0 1 where
  income z := if z = 0 then 1 else 2
  transitionMatrix _ _ := 1 / 2
  interest := 0
  discount := 1 / 100
  u := crraUtility 1
  minIncome := 1
  maxIncome := 2
  minIncome_pos := by norm_num
  minIncome_le z := by fin_cases z <;> norm_num
  le_maxIncome z := by fin_cases z <;> norm_num
  transitionMatrix_nonneg _ _ := by norm_num
  transitionMatrix_sum _ := by simp
  interest_gt_neg_one := by norm_num
  assetFloor_le_assetCap := by norm_num
  assetCap_nonneg := by norm_num
  minConsumption_pos := by norm_num
  minConsumption_le_floor := le_rfl
  discount_lt_one := by norm_num
  dom := Ioi 0
  Ioi_subset_dom := subset_rfl
  dom_subset_Ici := Ioi_subset_Ici_self
  continuousOn_u_dom := continuousOn_crraUtility 1
  monotoneOn_u_dom := monotoneOn_crraUtility 1
  strictConcaveOn_u_dom := strictConcaveOn_crraUtility one_pos
  continuousOn_extendDom :=
    continuousOn_extendDom_Ioi (continuousOn_crraUtility 1) (tendsto_atBot_crraUtility le_rfl)

@[simp] theorem logImpatient_u : logImpatient.u = Real.log := crraUtility_one

/-- **The log economy satisfies Light's condition**, and by `crra_pinch` it is the only CRRA
economy that can. -/
theorem logImpatient_relativeRiskAversionLeOne :
    RelativeRiskAversionLeOne logImpatient.u :=
  relativeRiskAversionLeOne_crraUtility_iff.mpr le_rfl

end LeanEconomics

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.Call

/-!
# Black–Scholes digital option pricing formulas

Two **digital** (a.k.a. **binary**) European derivatives:

* **Cash-or-nothing call** pays `$1` at maturity `T` iff `S_T > K`.
  Price: `V_cash = e^{-rT} · Φ(d_2)`.
* **Asset-or-nothing call** pays `S_T` at maturity `T` iff `S_T > K`.
  Price: `V_asset = S_0 · Φ(d_1)`.

Both are derived directly from the BS hypothesis via the same machinery
as the vanilla call: HasLaw transfer to standard normal, `1_{S_T > K}` on
`Ioi(-d_2)`, then either `gaussianReal_Ioi_toReal` (cash case) or
`integral_exp_mul_gaussianPDFReal_Ioi` (asset case).

The standard decomposition `Call = AssetDigital − K · CashDigital` is
also proved as a corollary.

## Main results

* `bs_cash_or_nothing_formula`: under `BSCallHyp`, the discounted expected payoff of the
  cash-or-nothing call (`1` if `S_T > K`) is `e^{−rT} · Φ(d₂)`.
* `bs_asset_or_nothing_formula`: under `BSCallHyp`, the discounted expected payoff of the
  asset-or-nothing call (`S_T` if `S_T > K`) is `S_0 · Φ(d₁)`.
* `bs_call_eq_asset_minus_K_cash`: under `BSCallHyp`, the discounted expected call payoff is the
  asset-or-nothing value minus `K` times the cash-or-nothing value.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], 26.1

## Tags

digital option, binary option, cash-or-nothing, asset-or-nothing, Black–Scholes, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-- **Indicator pushforward through `bsTerminal`.** For any payoff `f`, the payoff-on-`{S_T > K}`
read as a function of the standard-normal driver `z` is the `Ioi (-d₂)`-indicator of `f ∘ S_T`:
`1_{Ioi K}(S_T z) · f = 1_{Ioi (-d₂)}(z) · (f ∘ S_T)`. Both digital formulas below instantiate it
(at `f = fun _ ↦ 1` and `f = fun s ↦ s`), sharing the `bsTerminal_gt_K_iff` case split. -/
private lemma indicator_bsTerminal_Ioi_comp {S_0 K r σ T : ℝ}
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) (f : ℝ → ℝ) (z : ℝ) :
    (Set.Ioi K).indicator f (bsTerminal S_0 r σ T z)
      = (Set.Ioi (-bsd2 S_0 K r σ T)).indicator (f ∘ bsTerminal S_0 r σ T) z := by
  by_cases hz : bsTerminal S_0 r σ T z ∈ Set.Ioi K
  · have h_z_mem : z ∈ Set.Ioi (-bsd2 S_0 K r σ T) :=
      (bsTerminal_gt_K_iff hS_0 hK hσ hT z).mp hz
    rw [Set.indicator_of_mem hz, Set.indicator_of_mem h_z_mem, Function.comp_apply]
  · have h_z_le : z ≤ -bsd2 S_0 K r σ T := by
      by_contra hcontra
      exact hz ((bsTerminal_gt_K_iff hS_0 hK hσ hT z).mpr (not_le.mp hcontra))
    have h_z_not_mem : z ∉ Set.Ioi (-bsd2 S_0 K r σ T) := not_lt.mpr h_z_le
    rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem h_z_not_mem]

/-! ### Cash-or-nothing digital -/

/-- **Cash-or-nothing call** pricing formula.

Pays `$1` at maturity iff `S_T > K`. Its discounted expected payoff under
the risk-neutral measure is
`V_cash = e^{-rT} · Φ(d_2)` where `d_2 = (log(S_0/K) + (r - σ²/2)T) / (σ√T)`.

Real derivation: HasLaw transfer to standard normal, identify
`{S_T(z) > K} = Ioi(-d_2)` via `bsTerminal_gt_K_iff`, then
`∫ 1_{Ioi(-d_2)}(z) · pdf(0,1,z) dz = (gaussianReal 0 1 (Ioi(-d_2))).toReal
= Φ(d_2)` via `gaussianReal_Ioi_toReal`. -/
theorem bs_cash_or_nothing_formula {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) :
    ∫ ω, Real.exp (-r * T) *
        (Set.Ioi K).indicator (fun _ ↦ (1 : ℝ)) (bsTerminal S_0 r σ T (Z ω)) ∂Q
      = Real.exp (-r * T) * Phi (bsd2 S_0 K r σ T) := by
  obtain ⟨hS_0, hK, hσ, hT, hZ⟩ := h
  set d_2 : ℝ := bsd2 S_0 K r σ T
  -- Indicator on {S_T > K} viewed as a function of z equals indicator on Ioi(-d_2)
  have h_indic_eq : ∀ z : ℝ,
      (Set.Ioi K).indicator (fun _ ↦ (1 : ℝ)) (bsTerminal S_0 r σ T z)
        = (Set.Ioi (-d_2)).indicator (fun _ ↦ (1 : ℝ)) z :=
    fun z ↦ indicator_bsTerminal_Ioi_comp hS_0 hK hσ hT (fun _ ↦ (1 : ℝ)) z
  -- Measurability of the payoff
  have h_payoff_meas : Measurable fun z : ℝ ↦
      (Set.Ioi K).indicator (fun _ ↦ (1 : ℝ)) (bsTerminal S_0 r σ T z) := by
    have h_simp : (fun z : ℝ ↦
        (Set.Ioi K).indicator (fun _ ↦ (1 : ℝ)) (bsTerminal S_0 r σ T z))
          = (Set.Ioi (-d_2)).indicator (fun _ ↦ (1 : ℝ)) := funext h_indic_eq
    rw [h_simp]
    exact (measurable_const.indicator measurableSet_Ioi)
  -- Pull out e^{-rT}, HasLaw transfer
  rw [integral_const_mul]
  rw [show (fun ω ↦ (Set.Ioi K).indicator (fun _ ↦ (1 : ℝ)) (bsTerminal S_0 r σ T (Z ω)))
        = (fun z ↦ (Set.Ioi K).indicator (fun _ ↦ (1 : ℝ)) (bsTerminal S_0 r σ T z)) ∘ Z
        from rfl,
      hZ.integral_comp h_payoff_meas.aestronglyMeasurable,
      integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
  -- Replace the indicator by the Ioi(-d_2) form, integrate against pdf
  have h_smul_eq :
      (fun z : ℝ ↦ gaussianPDFReal 0 1 z •
          (Set.Ioi K).indicator (fun _ ↦ (1 : ℝ)) (bsTerminal S_0 r σ T z))
        = (Set.Ioi (-d_2)).indicator (fun z ↦ gaussianPDFReal 0 1 z) := by
    funext z
    rw [smul_eq_mul, h_indic_eq z]
    by_cases hz : z ∈ Set.Ioi (-d_2)
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, mul_one]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero]
  rw [h_smul_eq, integral_indicator measurableSet_Ioi]
  -- ∫ z ∈ Ioi(-d_2), pdf = Phi(d_2) via gaussianReal_Ioi_toReal
  have h_pdf_int_eq :
      ∫ z in Set.Ioi (-d_2), gaussianPDFReal 0 1 z = Phi d_2 := by
    rw [setIntegral_gaussianPDFReal_eq_toReal measurableSet_Ioi (0 : ℝ),
        gaussianReal_Ioi_toReal, neg_neg]
  rw [h_pdf_int_eq]

/-! ### Asset-or-nothing digital -/

/-- **Asset-or-nothing call** pricing formula.

Pays `S_T` at maturity iff `S_T > K`. Its discounted expected payoff under
the risk-neutral measure is `V_asset = S_0 · Φ(d_1)`.

Real derivation: HasLaw transfer + identify `{S_T > K} = Ioi(-d_2)` +
`integral_exp_mul_gaussianPDFReal_Ioi` for the `exp(ν_log · z) · pdf`
integrand on the exercise region. The BS martingale algebra
`(r - σ²/2)T + σ²T/2 = rT` and `ν_log - (-d_2) = d_1` close the proof. -/
theorem bs_asset_or_nothing_formula {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) :
    ∫ ω, Real.exp (-r * T) *
        (Set.Ioi K).indicator
          (fun s ↦ s) (bsTerminal S_0 r σ T (Z ω)) ∂Q
      = S_0 * Phi (bsd1 S_0 K r σ T) := by
  obtain ⟨hS_0, hK, hσ, hT, hZ⟩ := h
  set d_1 : ℝ := bsd1 S_0 K r σ T with d_1_def
  set d_2 : ℝ := bsd2 S_0 K r σ T with d_2_def
  set μ_log : ℝ := (r - σ^2 / 2) * T
  set ν_log : ℝ := σ * Real.sqrt T with ν_log_def
  have hsqrT_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hν_log_pos : 0 < ν_log := mul_pos hσ hsqrT_pos
  have hν_log_sq : ν_log^2 = σ^2 * T := by
    rw [ν_log_def, mul_pow, Real.sq_sqrt hT.le]
  have h_algebra : μ_log + ν_log^2 / 2 = r * T := by rw [hν_log_sq]; ring
  have h_shift_eq : ν_log - (-d_2) = d_1 := by
    rw [d_1_def, d_2_def, bsd2]; ring
  -- payoff(z) = if S_T(z) > K then S_T(z) else 0
  --          = indicator(Ioi(-d_2), S_T)(z)
  have h_indic_eq : ∀ z : ℝ,
      (Set.Ioi K).indicator (fun s ↦ s) (bsTerminal S_0 r σ T z)
        = (Set.Ioi (-d_2)).indicator (fun z' ↦ bsTerminal S_0 r σ T z') z :=
    fun z ↦ indicator_bsTerminal_Ioi_comp hS_0 hK hσ hT (fun s ↦ s) z
  have h_payoff_meas : Measurable fun z : ℝ ↦
      (Set.Ioi K).indicator (fun s ↦ s) (bsTerminal S_0 r σ T z) := by
    have h_simp : (fun z : ℝ ↦
        (Set.Ioi K).indicator (fun s ↦ s) (bsTerminal S_0 r σ T z))
          = (Set.Ioi (-d_2)).indicator
              (fun z' ↦ bsTerminal S_0 r σ T z') := funext h_indic_eq
    rw [h_simp]
    exact Measurable.indicator (by unfold bsTerminal; fun_prop) measurableSet_Ioi
  -- Pull out e^{-rT}, HasLaw transfer, convert to volume
  rw [integral_const_mul]
  rw [show (fun ω ↦ (Set.Ioi K).indicator (fun s ↦ s) (bsTerminal S_0 r σ T (Z ω)))
        = (fun z ↦ (Set.Ioi K).indicator (fun s ↦ s) (bsTerminal S_0 r σ T z)) ∘ Z
        from rfl,
      hZ.integral_comp h_payoff_meas.aestronglyMeasurable,
      integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
  have h_smul_eq :
      (fun z : ℝ ↦ gaussianPDFReal 0 1 z •
          (Set.Ioi K).indicator (fun s ↦ s) (bsTerminal S_0 r σ T z))
        = (Set.Ioi (-d_2)).indicator
            (fun z ↦ gaussianPDFReal 0 1 z * bsTerminal S_0 r σ T z) := by
    funext z
    rw [smul_eq_mul, h_indic_eq z]
    by_cases hz : z ∈ Set.Ioi (-d_2)
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero]
  rw [h_smul_eq, integral_indicator measurableSet_Ioi]
  -- Decompose: pdf · S_T(z) = S_0 · exp(μ_log) · (exp(ν_log z) · pdf)
  have h_split_integrand : ∀ z : ℝ,
      gaussianPDFReal 0 1 z * bsTerminal S_0 r σ T z
        = (S_0 * Real.exp μ_log) * (Real.exp (ν_log * z) * gaussianPDFReal 0 1 z) := by
    intro z
    unfold bsTerminal
    have h_exp : Real.exp ((r - σ^2 / 2) * T + σ * Real.sqrt T * z)
                = Real.exp μ_log * Real.exp (ν_log * z) := by
      change Real.exp ((r - σ^2 / 2) * T + σ * Real.sqrt T * z)
            = Real.exp ((r - σ^2 / 2) * T) * Real.exp (σ * Real.sqrt T * z)
      exact Real.exp_add _ _
    rw [h_exp]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun z _ ↦ h_split_integrand z)]
  rw [integral_const_mul, integral_exp_mul_gaussianPDFReal_Ioi, h_shift_eq]
  -- Final algebra: e^{-rT} · S_0 · e^{μ_log} · e^{ν_log²/2} · Phi(d_1) = S_0 · Phi(d_1)
  have h_exp_combine : Real.exp (-r * T) * Real.exp μ_log * Real.exp (ν_log^2 / 2) = 1 := by
    rw [mul_assoc, ← Real.exp_add, ← Real.exp_add,
        show -r * T + (μ_log + ν_log^2 / 2) = 0 from by rw [h_algebra]; ring]
    exact Real.exp_zero
  calc Real.exp (-r * T) *
        (S_0 * Real.exp μ_log * (Real.exp (ν_log^2 / 2) * Phi d_1))
      = (Real.exp (-r * T) * Real.exp μ_log * Real.exp (ν_log^2 / 2)) * (S_0 * Phi d_1) := by
        ring
    _ = 1 * (S_0 * Phi d_1) := by rw [h_exp_combine]
    _ = S_0 * Phi d_1 := by rw [one_mul]

/-! ### Call decomposition into digitals -/

/-- The vanilla European call decomposes as `AssetDigital − K · CashDigital`:
  `C = (S_0 · Φ(d_1)) − K · (e^{-rT} · Φ(d_2))`.

A direct algebraic consequence of `bs_call_formula`,
`bs_asset_or_nothing_formula`, and `bs_cash_or_nothing_formula`. -/
theorem bs_call_eq_asset_minus_K_cash {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) :
    (∫ ω, Real.exp (-r * T) * max (bsTerminal S_0 r σ T (Z ω) - K) 0 ∂Q)
      =
    (∫ ω, Real.exp (-r * T) *
        (Set.Ioi K).indicator
          (fun s ↦ s) (bsTerminal S_0 r σ T (Z ω)) ∂Q)
    - K *
    (∫ ω, Real.exp (-r * T) *
        (Set.Ioi K).indicator (fun _ ↦ (1 : ℝ)) (bsTerminal S_0 r σ T (Z ω)) ∂Q) := by
  rw [bs_call_formula h, bs_asset_or_nothing_formula h, bs_cash_or_nothing_formula h]
  ring

end MathFin

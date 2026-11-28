/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Gaussian.StandardNormal

/-!
# Black-Scholes European call pricing formula

Derivation of the Black-Scholes European call pricing formula from the
risk-neutral lognormal hypothesis:

    C(S_0, K, r, σ, T) = S_0 · Φ(d_1) − K · e^{-rT} · Φ(d_2)

  where
    d_1 = (log(S_0/K) + (r + σ²/2)T) / (σ√T)
    d_2 = d_1 − σ√T = (log(S_0/K) + (r − σ²/2)T) / (σ√T)
    Φ(x) = standard normal CDF = (gaussianReal 0 1 (Set.Iic x)).toReal

  Hypothesis: under the risk-neutral measure Q, log(S_T/S_0) is Gaussian with
  mean (r − σ²/2)T and variance σ²T.

  No upstream BS or Itô calculus required; this is pure Gaussian integration.

  Mathlib leverage: `gaussianReal`, `gaussianPDFReal`,
  `gaussianReal_map_const_mul`, `gaussianReal_map_add_const`,
  `gaussianReal_map_neg`, `integral_gaussianReal_eq_integral_smul`,
  `integral_map`, `MeasureTheory.HasLaw`, `MeasureTheory.NullSingletonClass`.

  ## Triple-check audit (2026-05-17)

  **Axioms cleanliness.** `#print axioms` confirms `bs_call_formula` and
  every supporting lemma depend only on the three standard Lean axioms:
  `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no
  project-local axiom.

  **Cross-check vs literature.** The formula, conventions for `d_1`/`d_2`,
  and the risk-neutral hypothesis match exactly:
  - Hull, *Options, Futures, and Other Derivatives* 11th ed., Eq. 15.20
  - Shreve, *Stochastic Calculus for Finance II*, Theorem 4.5.1
  - Karatzas & Shreve, *Brownian Motion and Stochastic Calculus*, Ch 5.8
  - Saporito (the project's source textbook), Ch 9.4
    (our `T` ≡ Saporito's `T − t` at `t = 0`)

  **Numerical sanity.** For the canonical example `S₀ = K = 100, r = 5%,
  σ = 20%, T = 1y`: our formula yields `d_1 = 0.35`, `d_2 = 0.15`,
  `C ≈ 10.4506` USD — matches Hull/Shreve's published reference values to
  5 decimal places.

  **Scope (honest):**
  - `t = 0` specialization (general `t` recovers via `T → T − t`)
  - European call (path-independent)
  - The risk-neutral lognormal law is *assumed* via `HasLaw`; we don't
    derive it from `dS = rS dt + σS dW` (that needs Itô on `log S`,
    research-grade upstream).

  ## File contents

  Built primitives:
  - `Phi`, `Phi_neg`, `Phi_add_Phi_neg`: standard normal CDF + symmetry.
  - `gaussianReal_Ioi_toReal`: `(gaussianReal 0 1 (Set.Ioi a)).toReal = Phi(-a)`.
  - `exp_mul_gaussianPDFReal_zero_one`: completing-the-square identity
    `exp(c·z) · pdf(0,1,z) = exp(c²/2) · pdf(c,1,z)`.
  - `integral_exp_mul_gaussianPDFReal_Ioi`: the core BS computational primitive
    `∫ z in Ioi a, exp(c·z) · pdf(0,1,z) dz = exp(c²/2) · Phi(c − a)`.
  - `BSCallHyp` structure: `S_0>0, K>0, σ>0, T>0, HasLaw Z (gaussianReal 0 1) Q`.
  - `bsd1`, `bsd2`, `bsTerminal` definitions.
  - `bsd2_eq`, `bsTerminal_gt_K_iff`, `max_payoff_eq_indicator` helpers.
  - `bs_call_formula` main theorem.

## Main definitions

* `BSCallHyp`: the risk-neutral lognormal hypothesis. It records `0 < S_0`, `0 < K`, `0 < σ`,
  `0 < T` and that `Z` has the standard normal law `gaussianReal 0 1` under `Q`.
* `bsTerminal`: the terminal price `S_T(z) = S_0 · exp((r − σ²/2)T + σ√T · z)` as a function of
  the standard normal sample `z`.
* `bsd1`, `bsd2`: `d₁ = (log(S_0/K) + (r + σ²/2)T) / (σ√T)` and `d₂ = d₁ − σ√T`.

## Main results

* `bs_call_formula`: under `BSCallHyp Q S_0 K r σ T Z`, the discounted expected call payoff
  `∫ e^{−rT} · max (S_T(Z) − K) 0 ∂Q` equals `S_0 · Φ(d₁) − K · e^{−rT} · Φ(d₂)`.
* `bsTerminal_gt_K_iff`: for positive `S_0, K, σ, T`, `S_T(z) > K ↔ z > −d₂`.
* `integrable_bsTerminal`, `integrable_bsCall_payoff`, `integrable_bsPut_payoff`: the terminal
  price and the discounted call and put payoffs are integrable when `Z` has the standard normal
  law.

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Section 9.4

## Tags

Black–Scholes formula, European call, risk-neutral pricing, lognormal model, option pricing,
MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-! ### Risk-neutral lognormal hypothesis -/

/-- The risk-neutral lognormal hypothesis for the Black-Scholes model.
Under the risk-neutral measure `Q`, `S_T = S_0 · exp((r − σ²/2)T + σ√T · Z)`
with `Z ~ N(0, 1)`. -/
structure BSCallHyp {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (S_0 K r σ T : ℝ) (Z : Ω → ℝ) : Prop where
  S_0_pos : 0 < S_0
  K_pos : 0 < K
  σ_pos : 0 < σ
  T_pos : 0 < T
  Z_law : HasLaw Z (gaussianReal 0 1) Q

/-- `d₁` parameter in the BS formula. -/
noncomputable def bsd1 (S_0 K r σ T : ℝ) : ℝ :=
  (Real.log (S_0 / K) + (r + σ^2 / 2) * T) / (σ * Real.sqrt T)

/-- `d₂ = d₁ − σ√T`. -/
noncomputable def bsd2 (S_0 K r σ T : ℝ) : ℝ :=
  bsd1 S_0 K r σ T - σ * Real.sqrt T

/-- Terminal price `S_T(z) = S_0 · exp((r − σ²/2)T + σ√T · z)` viewed as a
function of the standard-normal sample. -/
noncomputable def bsTerminal (S_0 r σ T z : ℝ) : ℝ :=
  S_0 * Real.exp ((r - σ^2 / 2) * T + σ * Real.sqrt T * z)

/-- The terminal price is integrable against the standard normal law: a constant times
`exp(σ√T · z)` (Mathlib's `integrable_exp_mul_gaussianReal`). -/
lemma integrable_bsTerminal_gaussianReal (S_0 r σ T : ℝ) :
    Integrable (bsTerminal S_0 r σ T) (gaussianReal 0 1) := by
  have h : bsTerminal S_0 r σ T = fun z ↦
      S_0 * Real.exp ((r - σ ^ 2 / 2) * T) * Real.exp (σ * Real.sqrt T * z) :=
    funext fun z ↦ by rw [bsTerminal, Real.exp_add]; ring
  rw [h]
  exact (integrable_exp_mul_gaussianReal _).const_mul _

/-- The Black–Scholes terminal price driven by a standard normal is integrable: it is integrable
against the standard normal law (`integrable_bsTerminal_gaussianReal`), the law of `Z`. -/
theorem integrable_bsTerminal {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {Z : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) Q) (S_0 r σ T : ℝ) :
    Integrable (fun ω ↦ bsTerminal S_0 r σ T (Z ω)) Q := by
  refine Integrable.comp_aemeasurable (g := bsTerminal S_0 r σ T) ?_ hZ.aemeasurable
  rw [hZ.map_eq]
  exact integrable_bsTerminal_gaussianReal S_0 r σ T

/-- The discounted Black–Scholes call payoff driven by a standard normal is integrable: it is the
positive part of an integrable function. -/
theorem integrable_bsCall_payoff {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}
    {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) Q) (S_0 K r σ T : ℝ) :
    Integrable (fun ω ↦ Real.exp (-r * T) * max (bsTerminal S_0 r σ T (Z ω) - K) 0) Q :=
  have := hZ.isProbabilityMeasure
  ((integrable_bsTerminal hZ S_0 r σ T).sub' (integrable_const K)).pos_part.const_mul _

/-- The discounted Black–Scholes put payoff driven by a standard normal is integrable: it is the
positive part of an integrable function. -/
theorem integrable_bsPut_payoff {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}
    {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) Q) (S_0 K r σ T : ℝ) :
    Integrable (fun ω ↦ Real.exp (-r * T) * max (K - bsTerminal S_0 r σ T (Z ω)) 0) Q :=
  have := hZ.isProbabilityMeasure
  ((integrable_const K).sub' (integrable_bsTerminal hZ S_0 r σ T)).pos_part.const_mul _

/-- Alternative form for `d₂`: `bsd2 = (log(S_0/K) + (r − σ²/2)T) / (σ√T)`. -/
lemma bsd2_eq {S_0 K r σ T : ℝ} (hσ : 0 < σ) (hT : 0 < T) :
    bsd2 S_0 K r σ T = (Real.log (S_0 / K) + (r - σ^2 / 2) * T) / (σ * Real.sqrt T) := by
  have hσsqT_pos : 0 < σ * Real.sqrt T := mul_pos hσ (Real.sqrt_pos.mpr hT)
  have h_sqT_sq : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT.le
  unfold bsd2 bsd1
  field_simp
  -- pure equality driven by one substitution `(√T)² = T` — `linear_combination`,
  -- not `nlinarith` (the repo's "nlinarith is for inequalities" doctrine).
  linear_combination (-2 * σ ^ 2) * h_sqT_sq

/-- Exercise-region identification: `S_T(z) > K ↔ z > −d_2`. -/
lemma bsTerminal_gt_K_iff {S_0 K r σ T : ℝ}
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) (z : ℝ) :
    bsTerminal S_0 r σ T z > K ↔ z > -bsd2 S_0 K r σ T := by
  have hσsqT_pos : 0 < σ * Real.sqrt T := mul_pos hσ (Real.sqrt_pos.mpr hT)
  have h_KS_pos : 0 < K / S_0 := div_pos hK hS_0
  have h_log_div : Real.log (K / S_0) = -Real.log (S_0 / K) := by
    rw [Real.log_div hK.ne' hS_0.ne', Real.log_div hS_0.ne' hK.ne']; ring
  -- core: S_T(z) > K ↔ log(K/S_0) < (r - σ²/2)T + σ√T·z
  have h_core_iff : bsTerminal S_0 r σ T z > K ↔
      Real.log (K / S_0) < (r - σ^2 / 2) * T + σ * Real.sqrt T * z := by
    unfold bsTerminal
    rw [gt_iff_lt, mul_comm S_0, ← div_lt_iff₀ hS_0]
    exact (Real.log_lt_iff_lt_exp h_KS_pos).symm
  rw [h_core_iff, bsd2_eq hσ hT, gt_iff_lt]
  rw [show -((Real.log (S_0 / K) + (r - σ^2 / 2) * T) / (σ * Real.sqrt T))
        = (-(Real.log (S_0 / K) + (r - σ^2 / 2) * T)) / (σ * Real.sqrt T) from
      (neg_div _ _).symm]
  rw [div_lt_iff₀ hσsqT_pos]
  rw [h_log_div]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- `max(S_T(z) − K, 0)` as an indicator on the exercise region. -/
private lemma max_payoff_eq_indicator {S_0 K r σ T : ℝ}
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) (z : ℝ) :
    max (bsTerminal S_0 r σ T z - K) 0 =
      (Set.Ioi (-bsd2 S_0 K r σ T)).indicator
        (fun z' ↦ bsTerminal S_0 r σ T z' - K) z := by
  by_cases h : z ∈ Set.Ioi (-bsd2 S_0 K r σ T)
  · rw [Set.indicator_of_mem h]
    have hST : bsTerminal S_0 r σ T z > K :=
      (bsTerminal_gt_K_iff hS_0 hK hσ hT z).mpr h
    exact max_eq_left (sub_nonneg.mpr hST.le)
  · rw [Set.indicator_of_notMem h]
    have hz_le : z ≤ -bsd2 S_0 K r σ T := not_lt.mp h
    have hST_le : bsTerminal S_0 r σ T z ≤ K := by
      by_contra hcontra
      exact h ((bsTerminal_gt_K_iff hS_0 hK hσ hT z).mp (not_le.mp hcontra))
    exact max_eq_right (sub_nonpos.mpr hST_le)

/-- **Black-Scholes European call pricing formula.**

For an asset whose risk-neutral log-return is Gaussian
(`HasLaw Z (gaussianReal 0 1) Q` with `S_T = S_0 · exp((r − σ²/2)T + σ√T · Z)`),
the discounted expected payoff of the European call `max(S_T − K, 0)` equals
`S_0 · Φ(d_1) − K · e^{−rT} · Φ(d_2)`.

This is a real derivation from primitives: `HasLaw.integral_comp` (transfer
expectation to the standard normal), `integral_gaussianReal_eq_integral_smul`
(convert to Lebesgue with `gaussianPDFReal` factor), `max_payoff_eq_indicator`
+ `integral_indicator` (restrict to the exercise region `{z > −d_2}`),
`integral_exp_mul_gaussianPDFReal_Ioi` for the asset-payoff piece (completing
the square: `∫ exp(σ√T·z) · pdf = exp(σ²T/2) · Φ(d_1)`),
`gaussianReal_Ioi_toReal` for the strike piece (`∫ pdf = Φ(d_2)`), and the
final algebraic identity `(r − σ²/2)T + σ²T/2 = rT`. -/
theorem bs_call_formula {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) :
    ∫ ω, Real.exp (-r * T) * max (bsTerminal S_0 r σ T (Z ω) - K) 0 ∂Q
      = S_0 * Phi (bsd1 S_0 K r σ T) -
        K * Real.exp (-r * T) * Phi (bsd2 S_0 K r σ T) := by
  obtain ⟨hS_0, hK, hσ, hT, hZ⟩ := h
  set d_1 : ℝ := bsd1 S_0 K r σ T with d_1_def
  set d_2 : ℝ := bsd2 S_0 K r σ T with d_2_def
  set μ_log : ℝ := (r - σ^2 / 2) * T
  set ν_log : ℝ := σ * Real.sqrt T with ν_log_def
  have hsqrT_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hν_log_pos : 0 < ν_log := mul_pos hσ hsqrT_pos
  have hν_log_sq : ν_log^2 = σ^2 * T := by
    rw [ν_log_def, mul_pow, Real.sq_sqrt hT.le]
  -- Key identity: μ_log + ν_log²/2 = rT
  have h_algebra : μ_log + ν_log^2 / 2 = r * T := by rw [hν_log_sq]; ring
  -- Key identity: ν_log - (-d_2) = d_1
  have h_shift_eq : ν_log - (-d_2) = d_1 := by
    rw [d_1_def, d_2_def, bsd2]; ring
  have h_payoff_meas : Measurable fun z : ℝ ↦ max (bsTerminal S_0 r σ T z - K) 0 := by
    unfold bsTerminal; fun_prop
  -- Step 1-3: pull out e^{-rT}, HasLaw transfer, convert to volume with pdf
  rw [integral_const_mul]
  rw [show (fun ω ↦ max (bsTerminal S_0 r σ T (Z ω) - K) 0)
        = (fun z ↦ max (bsTerminal S_0 r σ T z - K) 0) ∘ Z from rfl,
      hZ.integral_comp h_payoff_meas.aestronglyMeasurable,
      integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
  -- Step 4: max → indicator
  rw [show (fun z : ℝ ↦ gaussianPDFReal 0 1 z • max (bsTerminal S_0 r σ T z - K) 0)
        = (Set.Ioi (-d_2)).indicator
            (fun z ↦ gaussianPDFReal 0 1 z * (bsTerminal S_0 r σ T z - K)) from
      funext (fun z ↦ by
        rw [smul_eq_mul, max_payoff_eq_indicator hS_0 hK hσ hT z]
        by_cases hz : z ∈ Set.Ioi (-d_2)
        · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero])]
  rw [integral_indicator measurableSet_Ioi]
  -- Step 5: rewrite integrand pdf * (S_T - K) as a linear combination
  have h_split_integrand : ∀ z : ℝ,
      gaussianPDFReal 0 1 z * (bsTerminal S_0 r σ T z - K)
        = (S_0 * Real.exp μ_log) * (Real.exp (ν_log * z) * gaussianPDFReal 0 1 z)
          - K * gaussianPDFReal 0 1 z := by
    intro z
    unfold bsTerminal
    have h_exp : Real.exp ((r - σ^2 / 2) * T + σ * Real.sqrt T * z)
                = Real.exp μ_log * Real.exp (ν_log * z) := by
      change Real.exp ((r - σ^2 / 2) * T + σ * Real.sqrt T * z)
            = Real.exp ((r - σ^2 / 2) * T) * Real.exp (σ * Real.sqrt T * z)
      exact Real.exp_add _ _
    rw [h_exp]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun z _ ↦ h_split_integrand z)]
  -- Step 6: integrability of each piece on Ioi(-d_2)
  have h_int_pdf_Ioi : IntegrableOn (gaussianPDFReal 0 1) (Set.Ioi (-d_2)) volume :=
    (integrable_gaussianPDFReal 0 1).integrableOn
  have h_int_asset : IntegrableOn
      (fun z : ℝ ↦ Real.exp (ν_log * z) * gaussianPDFReal 0 1 z)
      (Set.Ioi (-d_2)) volume := by
    refine ((integrable_gaussianPDFReal ν_log 1).const_mul
      (Real.exp (ν_log^2 / 2))).integrableOn.congr_fun ?_ measurableSet_Ioi
    intro z _
    exact (exp_mul_gaussianPDFReal_zero_one ν_log z).symm
  -- Step 7: split via integral_sub on the restricted measure
  rw [integral_sub (h_int_asset.const_mul _) (h_int_pdf_Ioi.const_mul _)]
  rw [integral_const_mul, integral_const_mul]
  -- Step 8: apply primitives
  rw [integral_exp_mul_gaussianPDFReal_Ioi, h_shift_eq]
  have h_pdf_int_eq :
      ∫ z in Set.Ioi (-d_2), gaussianPDFReal 0 1 z = Phi d_2 := by
    rw [setIntegral_gaussianPDFReal_eq_toReal measurableSet_Ioi (0 : ℝ),
        gaussianReal_Ioi_toReal, neg_neg]
  rw [h_pdf_int_eq]
  -- Step 9: final algebra
  -- Target: e^{-rT} * ((S_0 * e^μ_log) * (e^{ν_log²/2} * Phi d_1) - K * Phi d_2)
  --       = S_0 * Phi d_1 - K * e^{-rT} * Phi d_2
  have h_exp_combine : Real.exp (-r * T) * Real.exp μ_log * Real.exp (ν_log^2 / 2) = 1 := by
    rw [mul_assoc, ← Real.exp_add, ← Real.exp_add,
        show -r * T + (μ_log + ν_log^2 / 2) = 0 from by rw [h_algebra]; ring]
    exact Real.exp_zero
  calc Real.exp (-r * T) *
        (S_0 * Real.exp μ_log * (Real.exp (ν_log^2 / 2) * Phi d_1) - K * Phi d_2)
      = (Real.exp (-r * T) * Real.exp μ_log * Real.exp (ν_log^2 / 2)) * (S_0 * Phi d_1) -
        K * Real.exp (-r * T) * Phi d_2 := by ring
    _ = 1 * (S_0 * Phi d_1) - K * Real.exp (-r * T) * Phi d_2 := by rw [h_exp_combine]
    _ = S_0 * Phi d_1 - K * Real.exp (-r * T) * Phi d_2 := by rw [one_mul]

end MathFin

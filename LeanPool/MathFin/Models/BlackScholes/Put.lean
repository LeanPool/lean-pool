/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.Call

/-!
# Black–Scholes put pricing formula

Derivation of the European put price under the risk-neutral lognormal
hypothesis:

    P(S_0, K, r, σ, T) = K · e^{-rT} · Φ(-d_2) − S_0 · Φ(-d_1)

Built directly, parallel to `bs_call_formula`: HasLaw transfer to standard
normal, `max(K - S_T, 0)` as indicator on `{S_T < K} = Iic(-d_2)`, then
completing-the-square on the left-tail integral.

We also derive **put-call parity**
`C − P = S_0 − K · e^{-rT}` as a corollary using the call formula and
`Phi_add_Phi_neg`.

## Main results

* `bs_put_formula`: under `BSCallHyp`, the discounted expected put payoff is
  `K·e^{−rT}·Φ(−d₂) − S₀·Φ(−d₁)`.
* `bs_put_call_parity`: under `BSCallHyp`, `C − P = S₀ − K·e^{−rT}`.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], 11.4; 16.6
* [S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*][ShreveSCFII], 4.5

## Tags

European put, put–call parity, Black–Scholes put price, risk-neutral pricing, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-! ### Left-tail completing-the-square (Iic counterpart of `_Ioi` lemma) -/

/-- `Q(Iic a) = Φ(a)` for standard normal. Just `Phi_def` unfolded. -/
lemma gaussianReal_Iic_toReal (a : ℝ) :
    (gaussianReal 0 1 (Set.Iic a)).toReal = Phi a := rfl

/-- The shifted Gaussian left-tail integral — the put-side BS computational
primitive:
  `∫ z in Iic a, exp(c·z) · gaussianPDFReal 0 1 z dz = exp(c²/2) · Φ(a − c)`.

Combines `exp_mul_gaussianPDFReal_zero_one` with `gaussianReal_map_add_const`. -/
lemma integral_exp_mul_gaussianPDFReal_Iic (a c : ℝ) :
    ∫ z in Set.Iic a, Real.exp (c * z) * gaussianPDFReal 0 1 z
      = Real.exp (c^2 / 2) * Phi (a - c) := by
  rw [setIntegral_congr_fun measurableSet_Iic
        (fun z _ ↦ exp_mul_gaussianPDFReal_zero_one c z), integral_const_mul]
  congr 1
  have h_int_eq : ∫ z in Set.Iic a, gaussianPDFReal c 1 z
      = (gaussianReal c (1 : ℝ≥0) (Set.Iic a)).toReal :=
    setIntegral_gaussianPDFReal_eq_toReal measurableSet_Iic c
  have h_shift : gaussianReal c (1 : ℝ≥0) (Set.Iic a) =
                 gaussianReal 0 1 (Set.Iic (a - c)) := by
    have hmap : (gaussianReal (0 : ℝ) 1).map (fun y ↦ y + c) = gaussianReal c 1 := by
      rw [gaussianReal_map_add_const, zero_add]
    rw [← hmap, Measure.map_apply (by fun_prop) measurableSet_Iic]
    congr 1; ext y; simp [Set.mem_Iic, le_sub_iff_add_le, add_comm]
  rw [h_int_eq, h_shift]; rfl

/-! ### Put payoff as an indicator -/

/-- `max(K − S_T(z), 0)` as an indicator on the exercise region `Iic(-d_2)`. -/
private lemma max_put_payoff_eq_indicator {S_0 K r σ T : ℝ}
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) (z : ℝ) :
    max (K - bsTerminal S_0 r σ T z) 0 =
      (Set.Iic (-bsd2 S_0 K r σ T)).indicator
        (fun z' ↦ K - bsTerminal S_0 r σ T z') z := by
  by_cases h : z ∈ Set.Iic (-bsd2 S_0 K r σ T)
  · rw [Set.indicator_of_mem h]
    have hz_le : z ≤ -bsd2 S_0 K r σ T := h
    have hST_le : bsTerminal S_0 r σ T z ≤ K := by
      by_contra hcontra
      have h_gt : z > -bsd2 S_0 K r σ T :=
        (bsTerminal_gt_K_iff hS_0 hK hσ hT z).mp (not_le.mp hcontra)
      linarith
    exact max_eq_left (sub_nonneg.mpr hST_le)
  · rw [Set.indicator_of_notMem h]
    have hz_gt : -bsd2 S_0 K r σ T < z := not_le.mp h
    have hST_gt : bsTerminal S_0 r σ T z > K :=
      (bsTerminal_gt_K_iff hS_0 hK hσ hT z).mpr hz_gt
    exact max_eq_right (sub_nonpos.mpr hST_gt.le)

/-! ### Put pricing formula -/

/-- **Black-Scholes European put pricing formula.**

For an asset whose risk-neutral log-return is Gaussian (encoded by `BSCallHyp`),
the discounted expected payoff of the European put `max(K - S_T, 0)` equals
`K · e^{-rT} · Φ(-d_2) − S_0 · Φ(-d_1)`.

Real derivation: HasLaw transfer + `max → indicator` on the exercise region
`{S_T(z) < K} = Iic(-d_2)` + `integral_exp_mul_gaussianPDFReal_Iic` on the
asset-side piece + `gaussianReal_Iic_toReal` on the strike-side piece + the
BS martingale algebra `(r - σ²/2)T + σ²T/2 = rT`. The identification
`-d_2 - σ√T = -d_1` (using `d_1 - d_2 = σ√T`) finishes the asset piece. -/
theorem bs_put_formula {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) :
    ∫ ω, Real.exp (-r * T) * max (K - bsTerminal S_0 r σ T (Z ω)) 0 ∂Q
      = K * Real.exp (-r * T) * Phi (-(bsd2 S_0 K r σ T)) -
        S_0 * Phi (-(bsd1 S_0 K r σ T)) := by
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
  -- Key identity: -d_2 - ν_log = -d_1
  have h_shift_eq : (-d_2) - ν_log = -d_1 := by
    rw [d_1_def, d_2_def, bsd2]; ring
  have h_payoff_meas : Measurable fun z : ℝ ↦ max (K - bsTerminal S_0 r σ T z) 0 := by
    unfold bsTerminal; fun_prop
  -- Step 1-3: pull out e^{-rT}, HasLaw transfer, convert to volume with pdf
  rw [integral_const_mul]
  rw [show (fun ω ↦ max (K - bsTerminal S_0 r σ T (Z ω)) 0)
        = (fun z ↦ max (K - bsTerminal S_0 r σ T z) 0) ∘ Z from rfl,
      hZ.integral_comp h_payoff_meas.aestronglyMeasurable,
      integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
  -- Step 4: max → indicator on Iic(-d_2)
  rw [show (fun z : ℝ ↦ gaussianPDFReal 0 1 z • max (K - bsTerminal S_0 r σ T z) 0)
        = (Set.Iic (-d_2)).indicator
            (fun z ↦ gaussianPDFReal 0 1 z * (K - bsTerminal S_0 r σ T z)) from
      funext (fun z ↦ by
        rw [smul_eq_mul, max_put_payoff_eq_indicator hS_0 hK hσ hT z]
        by_cases hz : z ∈ Set.Iic (-d_2)
        · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero])]
  rw [integral_indicator measurableSet_Iic]
  -- Step 5: rewrite pdf · (K - S_T) as a linear combination
  have h_split_integrand : ∀ z : ℝ,
      gaussianPDFReal 0 1 z * (K - bsTerminal S_0 r σ T z)
        = K * gaussianPDFReal 0 1 z
          - (S_0 * Real.exp μ_log) * (Real.exp (ν_log * z) * gaussianPDFReal 0 1 z) := by
    intro z
    unfold bsTerminal
    have h_exp : Real.exp ((r - σ^2 / 2) * T + σ * Real.sqrt T * z)
                = Real.exp μ_log * Real.exp (ν_log * z) := by
      change Real.exp ((r - σ^2 / 2) * T + σ * Real.sqrt T * z)
            = Real.exp ((r - σ^2 / 2) * T) * Real.exp (σ * Real.sqrt T * z)
      exact Real.exp_add _ _
    rw [h_exp]; ring
  rw [setIntegral_congr_fun measurableSet_Iic (fun z _ ↦ h_split_integrand z)]
  -- Step 6: integrability of each piece on Iic(-d_2)
  have h_int_pdf_Iic : IntegrableOn (gaussianPDFReal 0 1) (Set.Iic (-d_2)) volume :=
    (integrable_gaussianPDFReal 0 1).integrableOn
  have h_int_asset : IntegrableOn
      (fun z : ℝ ↦ Real.exp (ν_log * z) * gaussianPDFReal 0 1 z)
      (Set.Iic (-d_2)) volume := by
    refine ((integrable_gaussianPDFReal ν_log 1).const_mul
      (Real.exp (ν_log^2 / 2))).integrableOn.congr_fun ?_ measurableSet_Iic
    intro z _
    exact (exp_mul_gaussianPDFReal_zero_one ν_log z).symm
  -- Step 7: split integral
  rw [integral_sub (h_int_pdf_Iic.const_mul _) (h_int_asset.const_mul _)]
  rw [integral_const_mul, integral_const_mul]
  -- Step 8: apply primitives
  have h_pdf_int_eq :
      ∫ z in Set.Iic (-d_2), gaussianPDFReal 0 1 z = Phi (-d_2) := by
    rw [setIntegral_gaussianPDFReal_eq_toReal measurableSet_Iic (0 : ℝ),
        gaussianReal_Iic_toReal]
  rw [h_pdf_int_eq, integral_exp_mul_gaussianPDFReal_Iic, h_shift_eq]
  -- Step 9: final algebra
  have h_exp_combine : Real.exp (-r * T) * Real.exp μ_log * Real.exp (ν_log^2 / 2) = 1 := by
    rw [mul_assoc, ← Real.exp_add, ← Real.exp_add,
        show -r * T + (μ_log + ν_log^2 / 2) = 0 from by rw [h_algebra]; ring]
    exact Real.exp_zero
  calc Real.exp (-r * T) *
        (K * Phi (-d_2) - S_0 * Real.exp μ_log * (Real.exp (ν_log^2 / 2) * Phi (-d_1)))
      = K * Real.exp (-r * T) * Phi (-d_2) -
        (Real.exp (-r * T) * Real.exp μ_log * Real.exp (ν_log^2 / 2)) * (S_0 * Phi (-d_1)) := by
        ring
    _ = K * Real.exp (-r * T) * Phi (-d_2) - 1 * (S_0 * Phi (-d_1)) := by rw [h_exp_combine]
    _ = K * Real.exp (-r * T) * Phi (-d_2) - S_0 * Phi (-d_1) := by rw [one_mul]

/-! ### Put-call parity -/

/-- **Put-call parity** for the BS European call and put under the
risk-neutral lognormal hypothesis:
  `C − P = S_0 − K · e^{-rT}`.

A direct algebraic corollary of `bs_call_formula` + `bs_put_formula` + the
symmetry identity `Φ(x) + Φ(-x) = 1`. -/
theorem bs_put_call_parity {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) :
    (∫ ω, Real.exp (-r * T) * max (bsTerminal S_0 r σ T (Z ω) - K) 0 ∂Q)
      - (∫ ω, Real.exp (-r * T) * max (K - bsTerminal S_0 r σ T (Z ω)) 0 ∂Q)
      = S_0 - K * Real.exp (-r * T) := by
  rw [bs_call_formula h, bs_put_formula h]
  have h_d1 := Phi_add_Phi_neg (bsd1 S_0 K r σ T)
  have h_d2 := Phi_add_Phi_neg (bsd2 S_0 K r σ T)
  -- Phi(d_1) + Phi(-d_1) = 1, Phi(d_2) + Phi(-d_2) = 1.
  -- C - P = S_0 (Phi(d_1) + Phi(-d_1)) - K e^{-rT} (Phi(d_2) + Phi(-d_2)) = S_0 - K e^{-rT}
  linear_combination S_0 * h_d1 - K * Real.exp (-r * T) * h_d2

end MathFin

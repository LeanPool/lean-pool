/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Jumps.JumpDiffusionOptionPrices

/-!
# Scaling a jump-diffusion; its exponential martingales

`θ` times a jump-diffusion log-return over a time `τ` is again one, with drift `θb`, volatility
coefficient `θσ`, the same rate and every jump multiplied by `θ`
(`jumpDiffusionIncrementLaw_map_const_mul`). On the canonical model the drift and the Gaussian
coefficient scale inside the log-return, and multiplying the jumps by `θ` changes only the jump
law (`jumpDiffusionMeasure_map_jumps`). On the process, `θX` is a jump-diffusion
(`JumpDiffusionProcess.const_mul`).

The Laplace exponent `κ(θ) = bθ + σ²θ²/2 + Λ(∫ e^{θx} dν − 1)` (`jumpDiffusionExponent`, the
cumulant generating function of the log-return per unit time where `∫ e^{θx} dν < ∞`,
`cgf_id_jumpDiffusionIncrementLaw`) then gives, for the price `S_t = S₀e^{X_t}`:

* `JumpDiffusionProcess.martingale_exp_const_mul_sub`: `t ↦ e^{θX_t − κ(θ)t}` is a martingale for
  every `θ` with `∫ e^{θx} dν < ∞`. It is the discounted price criterion
  (`JumpDiffusionProcess.martingale_iff`) for `θX` at the rate `κ(θ)`. For `b = 0`, `σ = 1` and no
  jumps `κ(θ) = θ²/2`, the exponent of the Wald martingales
  (`IsFilteredPreBrownian.waldExponential_isMartingale`); both families rest on the exponential
  martingale of independent increments (`martingale_exp_sub_of_indep_increments`).
* `JumpDiffusionProcess.martingale_iff_exponent_one`: the discounted price is a martingale if and
  only if `κ(1) = r`.
* `JumpDiffusionProcess.condExp_rpow`, power claims at each date `t ≤ T`: given `𝓕_t`, the
  discounted payoff `e^{−r(T−t)}S_T^p` has conditional expectation `S_t^p e^{(κ(p) − r)(T − t)}`,
  almost surely.

## Main results

* `jumpDiffusionIncrementLaw_map_const_mul`: `θ` times a jump-diffusion log-return over `τ` is
  one with drift `θb`, volatility coefficient `θσ`, the same rate and jump law `ν.map (θ * ·)`.
* `jumpDiffusionMeasure_map_jumps`: applying a measurable `g` to every jump size of the
  canonical model gives the canonical model with jump law `ν.map g`.
* `JumpDiffusionProcess.const_mul`: `θX` is a jump-diffusion with drift `θb`, volatility
  coefficient `θσ`, the same rate and jump law `ν.map (θ * ·)`.
* `JumpDiffusionProcess.martingale_exp_const_mul_sub`: if `∫ e^{θx} dν < ∞`,
  `t ↦ e^{θX_t − κ(θ)t}` is a martingale, with `κ` the Laplace exponent
  `jumpDiffusionExponent`.
* `JumpDiffusionProcess.martingale_iff_exponent_one`: for `∫ eˣ dν < ∞` and `S₀ ≠ 0`, the
  discounted price `e^{−rt} S₀ e^{X_t}` is a martingale iff `κ(1) = r`.
* `JumpDiffusionProcess.condExp_rpow`: for `S₀ > 0`, `∫ e^{px} dν < ∞` and `t ≤ T`, the
  conditional expectation of `e^{−r(T−t)} S_T^p` given `𝓕_t` is `S_t^p e^{(κ(p) − r)(T − t)}`
  almost surely.

## References

* [Cont and Tankov, *Financial Modelling with Jump Processes*][ContTankov2004]

## Tags

exponential martingale, Laplace exponent, scaling of jump-diffusion, Lévy exponent,
compensated jumps, MSC 60G51, MSC 60G44, MSC 91G20
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-! ### Scaling the log-return -/

/-- `eˣ` is integrable under the jump law pushed forward by `x ↦ θx` when `e^{θx}` is integrable
under `ν`. -/
lemma integrable_exp_map_const_mul {ν : Measure ℝ} {θ : ℝ}
    (hν : Integrable (fun x ↦ rexp (θ * x)) ν) : Integrable rexp (ν.map (θ * ·)) :=
  (integrable_map_measure measurable_exp.aestronglyMeasurable
    (measurable_const_mul θ).aemeasurable).2 hν

/-- **Transforming the jumps of the canonical model.** Applying a measurable `g` to every log-jump
size of the canonical model gives the canonical model with jump law `ν.map g`: the diffusion
sample and the jump count are unchanged, and the sizes stay i.i.d.
(`Measure.infinitePi_map_pi`). -/
lemma jumpDiffusionMeasure_map_jumps (Λ : ℝ≥0) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {g : ℝ → ℝ} (hg : Measurable g) :
    (jumpDiffusionMeasure Λ ν).map (Prod.map id (Prod.map id fun j i ↦ g (j i)))
      = jumpDiffusionMeasure Λ (ν.map g) := by
  have hj : Measurable fun (j : ℕ → ℝ) i ↦ g (j i) :=
    .of_eval fun i ↦ hg.comp (measurable_pi_apply i)
  have hid (α : Type) [MeasurableSpace α] : Measurable (@id α) := measurable_id
  unfold jumpDiffusionMeasure
  rw [← Measure.map_prod_map _ _ (hid ℝ) ((hid ℕ).prodMap hj),
    ← Measure.map_prod_map _ _ (hid ℕ) hj, Measure.map_id, Measure.map_id,
    Measure.infinitePi_map_pi (fun _ : ℕ ↦ ν) fun _ ↦ hg]

/-- `θ` times the log-return with drift `b` and volatility coefficient `σ` is the log-return with
drift `θb` and volatility coefficient `θσ` at the jump sizes multiplied by `θ`. -/
lemma const_mul_jumpDiffusionLogReturn (θ b σ : ℝ) (τ : ℝ≥0) (ω : ℝ × ℕ × (ℕ → ℝ)) :
    θ * jumpDiffusionLogReturn b σ τ ω
      = jumpDiffusionLogReturn (θ * b) (θ * σ) τ
          (Prod.map id (Prod.map id fun j i ↦ θ * j i) ω) := by
  simp only [jumpDiffusionLogReturn, Prod.map_fst, Prod.map_snd, id_eq, ← Finset.mul_sum]
  ring

/-- **Scaling a jump-diffusion log-return.** If `Y` is a jump-diffusion log-return over `τ`, then
`θY` is one with drift `θb`, volatility coefficient `θσ`, the same rate, and the jump law `ν`
pushed forward by `x ↦ θx`. -/
theorem jumpDiffusionIncrementLaw_map_const_mul (θ b σ : ℝ) (Λ : ℝ≥0) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (τ : ℝ≥0) :
    (jumpDiffusionIncrementLaw b σ Λ ν τ).map (θ * ·)
      = jumpDiffusionIncrementLaw (θ * b) (θ * σ) Λ (ν.map (θ * ·)) τ := by
  have hj : Measurable (Prod.map (@id ℝ) (Prod.map (@id ℕ) fun (j : ℕ → ℝ) i ↦ θ * j i)) :=
    measurable_id.prodMap (measurable_id.prodMap
      (.of_eval fun i ↦ (measurable_const_mul θ).comp (measurable_pi_apply i)))
  unfold jumpDiffusionIncrementLaw
  rw [← jumpDiffusionMeasure_map_jumps (Λ * τ) ν (measurable_const_mul θ),
    Measure.map_map (measurable_jumpDiffusionLogReturn (θ * b) (θ * σ) τ) hj,
    Measure.map_map (measurable_const_mul θ) (measurable_jumpDiffusionLogReturn b σ τ)]
  congr 1
  exact funext (const_mul_jumpDiffusionLogReturn θ b σ τ)

/-! ### The process -/

namespace JumpDiffusionProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {b σ : ℝ} {Λ : ℝ≥0} {ν : Measure ℝ}

/-- **Scaling the process.** For a jump-diffusion `X`, `θX` is a jump-diffusion with drift `θb`,
volatility coefficient `θσ`, the same rate and the jump law pushed forward by `x ↦ θx`: its
increments are `θ` times those of `X` (`jumpDiffusionIncrementLaw_map_const_mul`). -/
theorem const_mul (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν) [IsProbabilityMeasure ν] (θ : ℝ) :
    JumpDiffusionProcess P 𝓕 (fun t ω ↦ θ * X t ω) (θ * b) (θ * σ) Λ (ν.map (θ * ·)) where
  adapted t := (h.adapted t).const_mul θ
  zero := h.zero.mono fun ω hω ↦ by simp [hω]
  indep s t hst := indep_of_indep_of_le_left (h.indep s t hst)
    (MeasurableSpace.comap_le_comap_of_eq_comp (θ * ·) (measurable_const_mul θ)
      (funext fun ω ↦ (mul_sub θ (X t ω) (X s ω)).symm))
  law s t hst := by
    have hθ : HasLaw (fun x : ℝ ↦ θ * x)
        (jumpDiffusionIncrementLaw (θ * b) (θ * σ) Λ (ν.map (θ * ·)) (t - s))
        (jumpDiffusionIncrementLaw b σ Λ ν (t - s)) :=
      ⟨(measurable_const_mul θ).aemeasurable, jumpDiffusionIncrementLaw_map_const_mul θ b σ Λ ν _⟩
    exact (hθ.fun_comp (h.law s t hst)).congr
      (ae_of_all _ fun ω ↦ (mul_sub θ (X t ω) (X s ω)).symm)

/-- `e^{θX_t}` is integrable when `∫ e^{θx} dν < ∞`: `θX` is a jump-diffusion (`const_mul`). -/
lemma integrable_exp_const_mul (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν) [IsProbabilityMeasure ν]
    {θ : ℝ} (hν : Integrable (fun x ↦ rexp (θ * x)) ν) (t : ℝ≥0) :
    Integrable (fun ω ↦ rexp (θ * X t ω)) P :=
  (h.const_mul θ).integrable_exp (integrable_exp_map_const_mul hν) t

/-- **The exponential martingales of a jump-diffusion.** For `θ` with `∫ e^{θx} dν < ∞`,
`t ↦ e^{θX_t − κ(θ)t}` is an `𝓕`-martingale, `κ` the Laplace exponent: the discounted price
martingale (`martingale_iff`) of the scaled process `θX` (`const_mul`) at the rate `κ(θ)`. -/
theorem martingale_exp_const_mul_sub (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν)
    [IsProbabilityMeasure ν] {θ : ℝ} (hν : Integrable (fun x ↦ rexp (θ * x)) ν) :
    Martingale (fun (t : ℝ≥0) ω ↦ rexp (θ * X t ω - jumpDiffusionExponent b σ Λ ν θ * t))
      𝓕 P := by
  have hM := ((h.const_mul θ).martingale_iff (integrable_exp_map_const_mul hν) one_ne_zero
    (jumpDiffusionExponent b σ Λ ν θ)).2 (by
      rw [integral_map (measurable_const_mul θ).aemeasurable measurable_exp.aestronglyMeasurable,
        jumpDiffusionExponent]
      ring)
  convert hM using 1
  funext t ω
  rw [one_mul, ← Real.exp_add]
  congr 1
  ring

/-- **The martingale condition is `κ(1) = r`.** The discounted price `e^{−rt}S₀e^{X_t}` (`S₀ ≠ 0`)
is a martingale if and only if the Laplace exponent at `1` is the rate: the drift criterion
`martingale_iff`, read through `compensated_iff_exponent_one`. -/
theorem martingale_iff_exponent_one (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν)
    [IsProbabilityMeasure ν] (hν : Integrable rexp ν) {S_0 : ℝ} (hS_0 : S_0 ≠ 0) (r : ℝ) :
    Martingale (fun (t : ℝ≥0) ω ↦ rexp (-r * t) * (S_0 * rexp (X t ω))) 𝓕 P ↔
      jumpDiffusionExponent b σ Λ ν 1 = r :=
  (h.martingale_iff hν hS_0 r).trans (compensated_iff_exponent_one b σ r Λ ν)

/-- **Power claims at each date before maturity.** For `S₀ > 0`, `p` with `∫ e^{px} dν < ∞` and
`t ≤ T`, given `𝓕_t` the discounted payoff `e^{−r(T−t)}S_T^p` of the claim paying the `p`-th power
of the price `S_T = S₀e^{X_T}` has conditional expectation `S_t^p e^{(κ(p) − r)(T − t)}`, almost
surely: the payoff
averaged over the remaining log-return (`condExp_comp`), whose exponential moment at `p` is
`e^{κ(p)(T − t)}` (`integral_exp_const_mul_jumpDiffusionIncrementLaw`). -/
theorem condExp_rpow (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν) [IsProbabilityMeasure ν]
    {p : ℝ} (hν : Integrable (fun x ↦ rexp (p * x)) ν) {S_0 : ℝ} (hS_0 : 0 < S_0) (r : ℝ)
    {t T : ℝ≥0} (htT : t ≤ T) :
    P[fun ω ↦ rexp (-r * (T - t : ℝ≥0)) * (S_0 * rexp (X T ω)) ^ p | 𝓕 t]
      =ᵐ[P] fun ω ↦ (S_0 * rexp (X t ω)) ^ p
        * rexp ((jumpDiffusionExponent b σ Λ ν p - r) * (T - t : ℝ≥0)) := by
  have := h.isProbabilityMeasure
  have hpow (y : ℝ) : (S_0 * rexp y) ^ p = S_0 ^ p * rexp (p * y) := by
    rw [Real.mul_rpow hS_0.le (Real.exp_pos y).le, ← Real.exp_mul, mul_comm y p]
  have hpow_add (x y : ℝ) : (S_0 * rexp (x + y)) ^ p = (S_0 * rexp x) ^ p * rexp (p * y) := by
    rw [hpow, hpow, mul_add, Real.exp_add, mul_assoc]
  have hint : Integrable (fun ω ↦ rexp (-r * (T - t : ℝ≥0)) * (S_0 * rexp (X T ω)) ^ p) P :=
    ((h.integrable_exp_const_mul hν T).const_mul (rexp (-r * (T - t : ℝ≥0)) * S_0 ^ p)).congr
      (ae_of_all _ fun ω ↦ by beta_reduce; rw [hpow, mul_assoc])
  refine (h.condExp_comp (f := fun x ↦ rexp (-r * (T - t : ℝ≥0)) * (S_0 * rexp x) ^ p)
    (measurable_const.mul ((measurable_const.mul measurable_exp).pow_const p)) htT hint).trans
    (ae_of_all _ fun ω ↦ ?_)
  beta_reduce
  simp only [hpow_add (X t ω)]
  rw [integral_const_mul, integral_const_mul,
    integral_exp_const_mul_jumpDiffusionIncrementLaw b σ Λ hν, mul_left_comm, ← Real.exp_add]
  congr 2
  ring

end JumpDiffusionProcess

end MathFin

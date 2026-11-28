/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.ImpliedVolatility
public import LeanPool.MathFin.Models.Jumps.JumpDiffusionMixing

/-!
# Jumps lift the implied volatility

If the log-price is a Gaussian diffusion part plus an independent jump part `Y` with
`𝔼[e^Y] = 1`, the call is worth at least the Black–Scholes call at the diffusion volatility `σ`
(`bsV_le_jumpDiffusion_call`) and at most the spot. Here the lower bound is strict when `Y` is not
almost surely `0`, and the upper bound is strict for a positive strike. Read through the
Black–Scholes price as a function of the volatility, which increases strictly from below the call
price at `σ` towards the spot, the two bounds say that the call has a unique Black–Scholes implied
volatility and that it lies strictly above `σ`. This holds at every positive strike and maturity,
whatever the law of a compensated jump part that is not almost surely `0`.

## Main results

* `bsV_lt_jumpDiffusion_call`: `C_BS(S₀; σ) < C` when `𝔼[e^Y] = 1` and `Y` is not a.s. `0`.
  The Black–Scholes price is strictly convex in the spot (`bsV_spot_tangent_lt`), and `S₀e^Y`,
  whose mean is `S₀`, is not a.s. `S₀`, so Jensen's inequality is strict
  (`lt_integral_of_affine_lt`).
* `jumpDiffusion_call_lt`: `C < S₀·𝔼[e^Y]` for a positive strike, since `(S_T − K)⁺ < S_T`.
* `jumpDiffusion_impliedVol_gt`: the call has a Black–Scholes implied volatility above `σ`, and
  no other positive volatility prices to it (`exists_impliedVol_gt_of_bsV_lt`).
* `JumpDiffusionHyp.impliedVol_gt`: the same for the compound-Poisson model at the compensator
  `κ = Λ(𝔼[e^J] − 1)`, when `𝔼[e^J] < ∞`, the expected jump count `Λ` is positive and the jump
  law is not the
  point mass at `0` (`JumpDiffusionHyp.not_jumpPart_ae_eq_zero`).

## Scope

Each statement concerns one strike and one maturity: the implied volatility exceeds `σ` at every
strike, but nothing is said about how it varies across strikes (the shape of the smile).

## References

* [Cont and Tankov, *Financial Modelling with Jump Processes*][ContTankov2004]
* [R. C. Merton, *Option pricing when underlying stock returns are discontinuous*][Merton1976]

## Tags

implied volatility with jumps, volatility lift, Black–Scholes lower bound, jump risk,
strict inequality, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}

/-- **Jump risk is strictly priced.** If the jump part is compensated, `𝔼[e^Y] = 1`, and not
almost surely `0`, the jump-diffusion call is worth strictly more than the Black–Scholes call at
the diffusion volatility. The Black–Scholes price lies strictly above its tangent at `S₀` away
from `S₀` (`bsV_spot_tangent_lt`), and `S₀e^Y` has mean `S₀` but is not a.s. `S₀`. -/
theorem bsV_lt_jumpDiffusion_call {S_0 K r σ T : ℝ} {Z Y : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) Q) (hY : AEMeasurable Y Q) (hYZ : IndepFun Y Z Q)
    (hexp : Integrable (fun ω ↦ rexp (Y ω)) Q) (hmean : ∫ ω, rexp (Y ω) ∂Q = 1)
    (hY0 : ¬Y =ᵐ[Q] 0) (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    bsV K r σ S_0 T < ∫ ω, rexp (-r * T)
        * max (S_0 * rexp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * Z ω + Y ω) - K) 0 ∂Q := by
  have := hZ.isProbabilityMeasure
  have hm : ∫ ω, S_0 * rexp (Y ω) ∂Q = S_0 := by rw [integral_const_mul, hmean, mul_one]
  rw [jumpDiffusion_call_eq_integral_bsV hZ hY hYZ hexp hS_0 hK hσ hT]
  refine lt_integral_of_affine_lt (f := fun s ↦ bsV K r σ s T) (c := Phi (bsd1 S_0 K r σ T))
    (hexp.const_mul S_0) hm (integrable_bsV_mul_exp hY hexp hS_0 hK hσ hT)
    (ae_of_all _ fun ω hne ↦
      bsV_spot_tangent_lt hK hσ hT hS_0 (mul_pos hS_0 (Real.exp_pos _)) hne) fun hc ↦ hY0 ?_
  filter_upwards [hc] with ω hω
  exact (Real.exp_eq_one_iff _).1 ((mul_eq_left₀ hS_0.ne').1 hω)

/-- **The call is worth strictly less than `S₀·𝔼[e^Y]`** when the strike is positive: the payoff
`(S_T − K)⁺` is strictly below the terminal price `S_T > 0`, and the discounted terminal price
has mean `S₀·𝔼[e^Y]` (`jumpDiffusion_discounted_terminal`). -/
theorem jumpDiffusion_call_lt {S_0 K r σ T : ℝ} {Z Y : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) Q) (hY : AEMeasurable Y Q) (hYZ : IndepFun Y Z Q)
    (hexp : Integrable (fun ω ↦ rexp (Y ω)) Q) (hS_0 : 0 < S_0) (hK : 0 < K) (hT : 0 ≤ T) :
    ∫ ω, rexp (-r * T)
        * max (S_0 * rexp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * Z ω + Y ω) - K) 0 ∂Q
      < S_0 * ∫ ω, rexp (Y ω) ∂Q := by
  have := hZ.isProbabilityMeasure
  rw [← jumpDiffusion_discounted_terminal (r := r) (σ := σ) hZ hY hYZ hT]
  have hf := integrable_jumpDiffusion_call_payoff (S_0 := S_0) (K := K) (r := r) (σ := σ)
    (T := T) hZ hYZ hexp
  have hg := (integrable_jumpDiffusion_terminal (S_0 := S_0) (r := r) (σ := σ) (T := T) hZ hYZ
    hexp).const_mul (rexp (-r * T))
  have hlt (ω : Ω) : rexp (-r * T)
        * max (S_0 * rexp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * Z ω + Y ω) - K) 0
      < rexp (-r * T) * (S_0 * rexp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * Z ω + Y ω)) :=
    mul_lt_mul_of_pos_left (max_lt (by linarith) (mul_pos hS_0 (Real.exp_pos _)))
      (Real.exp_pos _)
  refine integral_lt_integral_of_ae_le_of_not_ae_eq hf hg (ae_of_all _ fun ω ↦ (hlt ω).le)
    fun h_eq ↦ ?_
  obtain ⟨ω, hω⟩ := Filter.Eventually.exists h_eq
  exact (hlt ω).ne hω

/-- **Jumps lift the implied volatility.** If the jump part is compensated, `𝔼[e^Y] = 1`, and
not almost surely `0`, the jump-diffusion call has a Black–Scholes implied volatility `σ_imp`
strictly above the diffusion volatility `σ`, and no other positive volatility gives the
Black–Scholes price equal to the call. The call lies strictly between the Black–Scholes price at
`σ` (`bsV_lt_jumpDiffusion_call`) and the spot (`jumpDiffusion_call_lt`). -/
theorem jumpDiffusion_impliedVol_gt {S_0 K r σ T : ℝ} {Z Y : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) Q) (hY : AEMeasurable Y Q) (hYZ : IndepFun Y Z Q)
    (hexp : Integrable (fun ω ↦ rexp (Y ω)) Q) (hmean : ∫ ω, rexp (Y ω) ∂Q = 1)
    (hY0 : ¬Y =ᵐ[Q] 0) (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    ∃ σ_imp, σ < σ_imp ∧ bsV K r σ_imp S_0 T = ∫ ω, rexp (-r * T)
        * max (S_0 * rexp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * Z ω + Y ω) - K) 0 ∂Q ∧
      ∀ σ' > 0, bsV K r σ' S_0 T = ∫ ω, rexp (-r * T)
        * max (S_0 * rexp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * Z ω + Y ω) - K) 0 ∂Q →
        σ' = σ_imp :=
  exists_impliedVol_gt_of_bsV_lt hK hT hS_0 hσ
    (bsV_lt_jumpDiffusion_call hZ hY hYZ hexp hmean hY0 hS_0 hK hσ hT)
    ((jumpDiffusion_call_lt hZ hY hYZ hexp hS_0 hK hT.le).trans_eq (by rw [hmean, mul_one]))

namespace JumpDiffusionHyp

variable {Λ : ℝ≥0} {Z : Ω → ℝ} {N : Ω → ℕ} {J : ℕ → Ω → ℝ}

/-- **The jump part is not deterministic.** With a positive expected jump count and a jump law
that is not the point mass at `0`, the jump part `−κ + ∑_{i<N} Jᵢ` is not almost surely `0`,
whatever `κ`: with no jump (probability `e^{−Λ}`) it is `−κ`, and with one jump it is `J₀ − κ`. -/
lemma not_jumpPart_ae_eq_zero (h : JumpDiffusionHyp Q Λ Z N J) (hΛ : 0 < Λ)
    (hJ0 : ¬J 0 =ᵐ[Q] 0) (κ : ℝ) :
    ¬(fun ω ↦ -κ + ∑ i ∈ Finset.range (N ω), J i ω) =ᵐ[Q] 0 := by
  intro hY
  have hY' := ae_iff.1 hY
  have hN (n : ℕ) : Q (N ⁻¹' {n}) ≠ 0 := by
    rw [← Measure.map_apply_of_aemeasurable h.N_law.aemeasurable (measurableSet_singleton n),
      h.N_law.map_eq]
    exact fun h0 ↦ (poissonMeasure_real_singleton_pos n hΛ).ne'
      (by rw [measureReal_def, h0, ENNReal.toReal_zero])
  -- with no jump, the jump part is `−κ`
  have hκ : κ = 0 := by
    by_contra hκ
    refine hN 0 (measure_mono_null (fun ω hω ↦ ?_) hY')
    have hNω : N ω = 0 := hω
    simp [hNω, hκ]
  -- with one jump, it is `J₀`
  have hind : Q (N ⁻¹' {1} ∩ J 0 ⁻¹' {0}ᶜ) = Q (N ⁻¹' {1}) * Q (J 0 ⁻¹' {0}ᶜ) :=
    (h.N_indep_J.comp measurable_id (measurable_pi_apply 0)).measure_inter_preimage_eq_mul _ _
      (measurableSet_singleton 1) (measurableSet_singleton 0).compl
  have hnull : Q (N ⁻¹' {1} ∩ J 0 ⁻¹' {0}ᶜ) = 0 := by
    refine measure_mono_null (fun ω hω ↦ ?_) hY'
    have hNω : N ω = 1 := hω.1
    simpa [hNω, hκ] using hω.2
  rw [hind, mul_eq_zero] at hnull
  refine hJ0 (ae_iff.2 (measure_mono_null (fun ω hω ↦ ?_) (hnull.resolve_left (hN 1))))
  simpa using hω

/-- **Jumps lift the implied volatility, for any non-degenerate jump law.** With `𝔼[e^J] < ∞`, a
positive expected jump count, a jump law that is not the point mass at `0` and the compensator
`κ = Λ(𝔼[e^J] − 1)`, the
jump-diffusion call has a Black–Scholes implied volatility strictly above the diffusion
volatility `σ`, and no other positive volatility gives the Black–Scholes price equal to the
call. -/
theorem impliedVol_gt (h : JumpDiffusionHyp Q Λ Z N J) (hJ : Integrable (fun ω ↦ rexp (J 0 ω)) Q)
    (hΛ : 0 < Λ) (hJ0 : ¬J 0 =ᵐ[Q] 0) {S_0 K r σ T : ℝ} (hS_0 : 0 < S_0) (hK : 0 < K)
    (hσ : 0 < σ) (hT : 0 < T) :
    ∃ σ_imp, σ < σ_imp ∧ bsV K r σ_imp S_0 T = ∫ ω, rexp (-r * T) * max (jumpDiffusionTerminal
        S_0 r σ T (Λ * (∫ x, rexp (J 0 x) ∂Q - 1)) (Z ω) (N ω) (fun i ↦ J i ω) - K) 0 ∂Q ∧
      ∀ σ' > 0, bsV K r σ' S_0 T = ∫ ω, rexp (-r * T) * max (jumpDiffusionTerminal
        S_0 r σ T (Λ * (∫ x, rexp (J 0 x) ∂Q - 1)) (Z ω) (N ω) (fun i ↦ J i ω) - K) 0 ∂Q →
        σ' = σ_imp := by
  simp_rw [jumpDiffusionTerminal_eq]
  exact jumpDiffusion_impliedVol_gt h.Z_law (h.aemeasurable_jumpPart _) (h.indepFun_jumpPart _)
    (h.integrable_exp_jumpPart hJ _) (h.integral_exp_compensatedJumpPart hJ)
    (h.not_jumpPart_ae_eq_zero hΛ hJ0 _) hS_0 hK hσ hT

end JumpDiffusionHyp

end MathFin

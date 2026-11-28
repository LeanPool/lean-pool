/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Jumps.CompoundPoissonMGF
public import LeanPool.MathFin.Models.BlackScholes.Forward
public import LeanPool.MathFin.Models.ModelFree.PriceBounds
public import LeanPool.MathFin.Models.BlackScholes.SpotConvexity
public import LeanPool.MathFin.Probability.Analysis.AffineMinorant
public import LeanPool.MathFin.Probability.Gaussian.NormalQuantile

/-!
# Jump-diffusions with an arbitrary jump law

Merton's jump-diffusion (`Models/Jumps/MertonJumpDiffusion.lean`) has Gaussian log-jumps, so that
with `n` jumps the terminal price is again a Black–Scholes terminal price. This file allows any
jump law. Under a probability measure `Q` the terminal price is

  `S_T = S₀ · exp((r − σ²/2)T − κ + σ√T·Z + ∑_{i<N} Jᵢ)`  (`jumpDiffusionTerminal`),

with `Z ∼ N(0, 1)`, a jump count `N ∼ Poisson(Λ)`, i.i.d. log-jumps `Jᵢ` of any law with
`𝔼[e^J] < ∞`, and a drift correction `κ`. The count is independent of the diffusion sample and
the jumps together, and the diffusion sample is independent of the jumps (`JumpDiffusionHyp`).

## Main definitions

* `jumpDiffusionTerminal`: the terminal price
  `S₀ · exp((r − σ²/2)T − κ + σ√T·z + ∑_{i<n} jᵢ)` at a diffusion sample `z`, a jump count `n` and
  log-jump sizes `j`, with drift correction `κ`.
* `JumpDiffusionHyp`: a standard normal diffusion sample `Z`, a jump count `N ∼ Poisson(Λ)` and
  i.i.d. log-jump sizes `Jᵢ`, with `Z`, `N` and the sizes mutually independent.

## Main results

* `jumpDiffusion_call_eq_integral_bsV`, the **mixing formula**: if the log-price is a Gaussian
  diffusion part plus an independent jump part `Y` with `𝔼[e^Y] < ∞`, then
  `𝔼[e^{−rT}(S₀e^{(r−σ²/2)T + σ√T·Z + Y} − K)⁺] = 𝔼[C_BS(S₀e^Y)]`. With `Y` frozen at `y`,
  the terminal price is a Black–Scholes terminal price at the spot `S₀e^y`.
* `jumpDiffusion_discounted_terminal`: the discounted terminal price has mean `S₀·𝔼[e^Y]`.
* `bsV_le_jumpDiffusion_call`, **jump risk is never free**: if `𝔼[e^Y] = 1`, the call is worth
  at least the Black–Scholes call at the diffusion volatility, whatever the law of `Y`. The
  Black–Scholes price is convex in the spot, so it lies above its tangent at `S₀`, and the
  tangent averages to `C_BS(S₀)`. `jumpDiffusion_call_le` is the upper bound `S₀·𝔼[e^Y]`.
* `JumpDiffusionHyp.call_eq_integral_bsV`: for the compound-Poisson model the call is
  `𝔼[C_BS(S₀e^{−κ + ∑_{i<N} Jᵢ})]`. The hypotheses make `Z` independent of the count and the
  jump sizes together (`JumpDiffusionHyp.Z_indep_jumps`).
* `JumpDiffusionHyp.discounted_terminal`: `𝔼[e^{−rT}S_T] = S₀·e^{−κ + Λ(𝔼[e^J] − 1)}`, and
  `JumpDiffusionHyp.discounted_terminal_eq_iff`, **the compensator**: this is `S₀` exactly when
  `κ = Λ(𝔼[e^J] − 1)`.
* `JumpDiffusionHyp.bsV_le_call`: at the compensator the call dominates the Black–Scholes call.
* `JumpDiffusionHyp.call_poisson_mixture`, **Merton's formula for a general jump law** (Merton
  1976): integrating out the count, the call is a Poisson mixture of Black–Scholes prices
  averaged over the jump sizes, `∫ n, 𝔼[C_BS(S₀e^{−κ + ∑_{i<n} Jᵢ})] ∂Poisson(Λ)`.

Merton's model is this one with Gaussian jumps, `𝔼[e^J] = 1 + k`, and the compensator `κ = kΛ`.
`Models/Jumps/JumpDiffusionMerton.lean` derives Merton's call, put and discounted-terminal
formulas from this file's general ones and Gaussian smoothing
(`JumpDiffusionHyp.call_eq_mertonCallPrice`).

## Scope

Only the law of the price at maturity is modelled here. A price process
with independent jump-diffusion increments, its martingale property and its prices at
intermediate dates are in `Models/Jumps/JumpDiffusionProcess.lean` and
`Models/Jumps/JumpDiffusionOptionPrices.lean`; such a process is constructed only without jumps.

## References

* [Cont and Tankov, *Financial Modelling with Jump Processes*][ContTankov2004]
* [R. C. Merton, *Option pricing when underlying stock returns are discontinuous*][Merton1976]

## Tags

jump-diffusion, arbitrary jump law, Poisson mixture, conditioning on jump count, terminal price law,
MSC 91G20, MSC 60G51, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}

/-! ### The mixing formula -/

/-- With the jump part frozen at `y`, the terminal price is the Black–Scholes terminal price at
the spot `S₀e^y`. -/
lemma mul_exp_add_eq_bsTerminal (S_0 r σ T z y : ℝ) :
    S_0 * rexp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * z + y)
      = bsTerminal (S_0 * rexp y) r σ T z := by
  rw [Real.exp_add _ y, bsTerminal]
  ring

/-- The Black–Scholes call price is measurable in the spot. -/
lemma measurable_bsV_spot (K r σ T : ℝ) : Measurable fun S ↦ bsV K r σ S T := by
  have := continuous_Phi.measurable
  unfold bsV bsd2 bsd1
  fun_prop

/-- The Black–Scholes call price is nonnegative: it is a discounted expected call payoff
(`bsV_nonneg` on the standard Gaussian space). -/
lemma bsV_nonneg_of_pos {S K r σ T : ℝ} (hS : 0 < S) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    0 ≤ bsV K r σ S T :=
  bsV_nonneg (Q := gaussianReal 0 1) (Z := id) ⟨hS, hK, hσ, hT, HasLaw.id⟩

/-- The terminal price of a jump-diffusion with an independent jump part `Y` is integrable when
`𝔼[e^Y] < ∞`: it is a constant times `e^{σ√T·Z}·e^Y`, a product of independent integrable
factors. -/
lemma integrable_jumpDiffusion_terminal {S_0 r σ T : ℝ} {Z Y : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) Q) (hYZ : IndepFun Y Z Q)
    (hexp : Integrable (fun ω ↦ rexp (Y ω)) Q) :
    Integrable (fun ω ↦ S_0 * rexp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * Z ω + Y ω)) Q := by
  have hind : IndepFun (fun ω ↦ rexp (σ * Real.sqrt T * Z ω)) (fun ω ↦ rexp (Y ω)) Q :=
    hYZ.symm.comp (φ := fun z ↦ rexp (σ * Real.sqrt T * z)) (ψ := rexp) (by fun_prop)
      measurable_exp
  have hfun : (fun ω ↦ S_0 * rexp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * Z ω + Y ω))
      = fun ω ↦ S_0 * rexp ((r - σ ^ 2 / 2) * T)
        * (rexp (σ * Real.sqrt T * Z ω) * rexp (Y ω)) := by
    funext ω
    rw [Real.exp_add _ (Y ω), Real.exp_add]
    ring
  rw [hfun]
  exact (hind.integrable_mul (hZ.integrable_fun_comp (integrable_exp_mul_gaussianReal _))
    hexp).const_mul _

/-- The discounted call payoff of a jump-diffusion with an independent jump part `Y` is
integrable when `𝔼[e^Y] < ∞`: it is the positive part of an integrable function. -/
lemma integrable_jumpDiffusion_call_payoff {S_0 K r σ T : ℝ} {Z Y : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) Q) (hYZ : IndepFun Y Z Q)
    (hexp : Integrable (fun ω ↦ rexp (Y ω)) Q) :
    Integrable (fun ω ↦ rexp (-r * T)
      * max (S_0 * rexp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * Z ω + Y ω) - K) 0) Q :=
  have := hZ.isProbabilityMeasure
  ((integrable_jumpDiffusion_terminal (S_0 := S_0) (r := r) (σ := σ) (T := T) hZ hYZ
    hexp).sub' (integrable_const K)).pos_part.const_mul _

/-- `C_BS(S₀e^Y)` is integrable when `𝔼[e^Y] < ∞`: it lies between `0` and `S₀e^Y`. -/
lemma integrable_bsV_mul_exp {S_0 K r σ T : ℝ} {Y : Ω → ℝ} (hY : AEMeasurable Y Q)
    (hexp : Integrable (fun ω ↦ rexp (Y ω)) Q) (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ)
    (hT : 0 < T) :
    Integrable (fun ω ↦ bsV K r σ (S_0 * rexp (Y ω)) T) Q := by
  refine (hexp.const_mul S_0).mono'
    ((measurable_bsV_spot K r σ T).comp_aemeasurable
      (hY.exp.const_mul S_0)).aestronglyMeasurable (ae_of_all _ fun ω ↦ ?_)
  have hS : 0 < S_0 * rexp (Y ω) := mul_pos hS_0 (Real.exp_pos _)
  exact (Real.norm_of_nonneg (bsV_nonneg_of_pos (r := r) hS hK hσ hT)).trans_le
    (bsV_le_S K r σ _ T hS.le hK.le)

/-- **The mixing formula.** If the log-price is a Gaussian diffusion part plus an independent
jump part `Y` with `𝔼[e^Y] < ∞`, the discounted expected call payoff is the Black–Scholes price
averaged over the jump part:
`𝔼[e^{−rT}(S₀e^{(r−σ²/2)T + σ√T·Z + Y} − K)⁺] = 𝔼[C_BS(S₀e^Y)]`.
With `Y` frozen at `y` (`integral_comp_prodMk_of_indepFun`) the terminal price is a Black–Scholes
terminal price at the spot `S₀e^y`, which `bs_call_formula` prices. -/
theorem jumpDiffusion_call_eq_integral_bsV {S_0 K r σ T : ℝ} {Z Y : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) Q) (hY : AEMeasurable Y Q) (hYZ : IndepFun Y Z Q)
    (hexp : Integrable (fun ω ↦ rexp (Y ω)) Q) (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ)
    (hT : 0 < T) :
    ∫ ω, rexp (-r * T)
        * max (S_0 * rexp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * Z ω + Y ω) - K) 0 ∂Q
      = ∫ ω, bsV K r σ (S_0 * rexp (Y ω)) T ∂Q := by
  have := hZ.isProbabilityMeasure
  have hgm : Measurable fun p : ℝ × ℝ ↦
      rexp (-r * T) * max (bsTerminal (S_0 * rexp p.1) r σ T p.2 - K) 0 := by
    unfold bsTerminal
    fun_prop
  have hint := integrable_jumpDiffusion_call_payoff (S_0 := S_0) (K := K) (r := r) (σ := σ)
    (T := T) hZ hYZ hexp
  simp_rw [mul_exp_add_eq_bsTerminal] at hint ⊢
  have hprod := (integrable_comp_prodMk_iff_of_indepFun hYZ hY hZ.aemeasurable
    hgm.aestronglyMeasurable).mp hint
  have hbsV : Measurable fun y ↦ bsV K r σ (S_0 * rexp y) T :=
    (measurable_bsV_spot K r σ T).comp (by fun_prop)
  calc ∫ ω, rexp (-r * T) * max (bsTerminal (S_0 * rexp (Y ω)) r σ T (Z ω) - K) 0 ∂Q
      = ∫ y, ∫ ω, rexp (-r * T) * max (bsTerminal (S_0 * rexp y) r σ T (Z ω) - K) 0 ∂Q
          ∂(Q.map Y) := integral_comp_prodMk_of_indepFun hYZ hY hZ.aemeasurable hprod
    _ = ∫ y, bsV K r σ (S_0 * rexp y) T ∂(Q.map Y) := integral_congr_ae <| ae_of_all _ fun y ↦
        integral_bsCall_payoff_eq_bsV ⟨mul_pos hS_0 (Real.exp_pos y), hK, hσ, hT, hZ⟩
    _ = ∫ ω, bsV K r σ (S_0 * rexp (Y ω)) T ∂Q := integral_map hY hbsV.aestronglyMeasurable

/-- **The discounted terminal price** of a jump-diffusion with an independent jump part `Y` has
mean `S₀ · 𝔼[e^Y]`: the discounted diffusion factor has mean `S₀`
(`integral_discounted_bsTerminal`) and is independent of the jump part. No integrability is
assumed: when `𝔼[e^Y] = ∞` both sides are the Bochner integral's `0`. -/
theorem jumpDiffusion_discounted_terminal {S_0 r σ T : ℝ} {Z Y : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) Q) (hY : AEMeasurable Y Q) (hYZ : IndepFun Y Z Q)
    (hT : 0 ≤ T) :
    ∫ ω, rexp (-r * T) * (S_0 * rexp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * Z ω + Y ω)) ∂Q
      = S_0 * ∫ ω, rexp (Y ω) ∂Q := by
  have hmeas : Measurable fun z ↦ rexp (-r * T) * bsTerminal S_0 r σ T z := by
    unfold bsTerminal
    fun_prop
  have hind : IndepFun (fun ω ↦ rexp (-r * T) * bsTerminal S_0 r σ T (Z ω))
      (fun ω ↦ rexp (Y ω)) Q :=
    hYZ.symm.comp (φ := fun z ↦ rexp (-r * T) * bsTerminal S_0 r σ T z) (ψ := rexp) hmeas
      measurable_exp
  have hfun : (fun ω ↦ rexp (-r * T)
        * (S_0 * rexp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * Z ω + Y ω)))
      = fun ω ↦ rexp (-r * T) * bsTerminal S_0 r σ T (Z ω) * rexp (Y ω) := by
    funext ω
    rw [Real.exp_add _ (Y ω), bsTerminal]
    ring
  rw [hfun, hind.integral_fun_mul_eq_mul_integral
    (hmeas.comp_aemeasurable hZ.aemeasurable).aestronglyMeasurable
    (measurable_exp.comp_aemeasurable hY).aestronglyMeasurable,
    integral_discounted_bsTerminal hZ S_0 r σ hT]

/-- **Jump risk is never free.** If the jump part is compensated, `𝔼[e^Y] = 1`, the
jump-diffusion call is worth at least the Black–Scholes call at the diffusion volatility, whatever
the law of `Y`: `C_BS(S₀) ≤ 𝔼[C_BS(S₀e^Y)]`. The Black–Scholes price is convex in the spot, so it
lies above its tangent at `S₀` (`bsV_spot_tangent_le`), and `S₀e^Y` has mean `S₀`
(`le_integral_of_affine_le`). -/
theorem bsV_le_jumpDiffusion_call {S_0 K r σ T : ℝ} {Z Y : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) Q) (hY : AEMeasurable Y Q) (hYZ : IndepFun Y Z Q)
    (hexp : Integrable (fun ω ↦ rexp (Y ω)) Q) (hmean : ∫ ω, rexp (Y ω) ∂Q = 1)
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    bsV K r σ S_0 T ≤ ∫ ω, rexp (-r * T)
        * max (S_0 * rexp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * Z ω + Y ω) - K) 0 ∂Q := by
  have := hZ.isProbabilityMeasure
  have hm : ∫ ω, S_0 * rexp (Y ω) ∂Q = S_0 := by rw [integral_const_mul, hmean, mul_one]
  rw [jumpDiffusion_call_eq_integral_bsV hZ hY hYZ hexp hS_0 hK hσ hT]
  exact le_integral_of_affine_le (f := fun s ↦ bsV K r σ s T) (c := Phi (bsd1 S_0 K r σ T))
    (hexp.const_mul S_0) hm (integrable_bsV_mul_exp hY hexp hS_0 hK hσ hT)
    (ae_of_all _ fun ω ↦ bsV_spot_tangent_le hK hσ hT hS_0 (mul_pos hS_0 (Real.exp_pos _)))

/-- **The upper bound.** The jump-diffusion call is worth at most `S₀·𝔼[e^Y]`, the discounted
mean of the terminal price, since `(S_T − K)⁺ ≤ S_T`. With `𝔼[e^Y] = 1` this is `C ≤ S₀`. -/
theorem jumpDiffusion_call_le {S_0 K r σ T : ℝ} {Z Y : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) Q) (hY : AEMeasurable Y Q) (hYZ : IndepFun Y Z Q)
    (hexp : Integrable (fun ω ↦ rexp (Y ω)) Q) (hS_0 : 0 ≤ S_0) (hK : 0 ≤ K) (hT : 0 ≤ T) :
    ∫ ω, rexp (-r * T)
        * max (S_0 * rexp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * Z ω + Y ω) - K) 0 ∂Q
      ≤ S_0 * ∫ ω, rexp (Y ω) ∂Q := by
  rw [← jumpDiffusion_discounted_terminal (r := r) (σ := σ) hZ hY hYZ hT]
  refine integral_mono (integrable_jumpDiffusion_call_payoff hZ hYZ hexp)
    ((integrable_jumpDiffusion_terminal hZ hYZ hexp).const_mul _) fun ω ↦ ?_
  exact mul_le_mul_of_nonneg_left
    (max_le (by linarith) (mul_nonneg hS_0 (Real.exp_pos _).le)) (Real.exp_pos _).le

/-! ### Compound-Poisson jumps -/

/-- The terminal price of a jump-diffusion at a diffusion sample `z`, a jump count `n` and log-jump
sizes `j`, with drift correction `κ`: `S₀ · exp((r − σ²/2)T − κ + σ√T·z + ∑_{i<n} jᵢ)`.
Merton's model takes `κ = kΛ`. -/
noncomputable def jumpDiffusionTerminal (S_0 r σ T κ z : ℝ) (n : ℕ) (j : ℕ → ℝ) : ℝ :=
  S_0 * rexp ((r - σ ^ 2 / 2) * T - κ + σ * Real.sqrt T * z + ∑ i ∈ Finset.range n, j i)

/-- The jump-diffusion terminal price with the jump part `−κ + ∑_{i<n} jᵢ` split off. -/
lemma jumpDiffusionTerminal_eq (S_0 r σ T κ z : ℝ) (n : ℕ) (j : ℕ → ℝ) :
    jumpDiffusionTerminal S_0 r σ T κ z n j
      = S_0 * rexp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * z
        + (-κ + ∑ i ∈ Finset.range n, j i)) := by
  unfold jumpDiffusionTerminal
  congr 2
  ring

/-- The sum of the first `n` jump sizes is measurable as a function of the count `n` and the
jump sizes: the count takes countably many values. -/
lemma measurable_sum_range_prod :
    Measurable fun p : ℕ × (ℕ → ℝ) ↦ ∑ i ∈ Finset.range p.1, p.2 i :=
  measurable_from_prod_countable_right fun n ↦
    show Measurable fun j : ℕ → ℝ ↦ ∑ i ∈ Finset.range n, j i by fun_prop

/-- The jump part `−κ + ∑_{i<n} jᵢ` is measurable as a function of the count and the jump
sizes. -/
lemma measurable_neg_add_sum_range (κ : ℝ) :
    Measurable fun p : ℕ × (ℕ → ℝ) ↦ -κ + ∑ i ∈ Finset.range p.1, p.2 i :=
  measurable_const.add measurable_sum_range_prod

/-- **A jump-diffusion with an arbitrary jump law**: a standard normal diffusion sample `Z`, a
jump count `N ∼ Poisson(Λ)` and i.i.d. log-jump sizes `Jᵢ`, with the count independent of the
diffusion sample and the sizes together, and the diffusion sample independent of the sizes.
The jump sizes are only a.e.-measurable, which `J_ident` already carries (`aemeasurable_J`).
Together the two independences say that `Z`, `N` and the jump sizes are mutually independent.
Merton's model is the case where the jumps are Gaussian (`JumpDiffusionMerton.lean`). -/
structure JumpDiffusionHyp (Q : Measure Ω) (Λ : ℝ≥0) (Z : Ω → ℝ) (N : Ω → ℕ)
    (J : ℕ → Ω → ℝ) : Prop where
  Z_law : HasLaw Z (gaussianReal 0 1) Q
  N_law : HasLaw N (poissonMeasure Λ) Q
  J_indep : iIndepFun J Q
  J_ident : ∀ i, IdentDistrib (J i) (J 0) Q Q
  Z_indep_J : IndepFun Z (fun ω i ↦ J i ω) Q
  N_indep : IndepFun N (fun ω ↦ (Z ω, fun i ↦ J i ω)) Q

namespace JumpDiffusionHyp

variable {Λ : ℝ≥0} {Z : Ω → ℝ} {N : Ω → ℕ} {J : ℕ → Ω → ℝ}

/-- Each jump size is a.e.-measurable: it is identically distributed with `J 0`, and
`IdentDistrib` carries a.e.-measurability. -/
lemma aemeasurable_J (h : JumpDiffusionHyp Q Λ Z N J) (i : ℕ) : AEMeasurable (J i) Q :=
  (h.J_ident i).aemeasurable_fst

/-- The jump sizes are jointly a.e.-measurable. -/
lemma aemeasurable_jumps (h : JumpDiffusionHyp Q Λ Z N J) :
    AEMeasurable (fun ω i ↦ J i ω) Q :=
  .of_eval h.aemeasurable_J

/-- The jump count is independent of the jump sizes. -/
lemma N_indep_J (h : JumpDiffusionHyp Q Λ Z N J) : IndepFun N (fun ω i ↦ J i ω) Q :=
  h.N_indep.comp measurable_id measurable_snd

/-- The diffusion sample is independent of the jump count and the jump sizes together:
`indepFun_prodMk_of_indepFun_prodMk` re-associates the model's mutual independence. -/
lemma Z_indep_jumps (h : JumpDiffusionHyp Q Λ Z N J) :
    IndepFun Z (fun ω ↦ (N ω, fun i ↦ J i ω)) Q :=
  have := h.J_indep.isProbabilityMeasure
  indepFun_prodMk_of_indepFun_prodMk h.N_law.aemeasurable h.Z_law.aemeasurable
    h.aemeasurable_jumps h.N_indep h.Z_indep_J

/-- The jump part `−κ + ∑_{i<N} Jᵢ` is measurable. -/
lemma aemeasurable_jumpPart (h : JumpDiffusionHyp Q Λ Z N J) (κ : ℝ) :
    AEMeasurable (fun ω ↦ -κ + ∑ i ∈ Finset.range (N ω), J i ω) Q :=
  (measurable_neg_add_sum_range κ).comp_aemeasurable
    (h.N_law.aemeasurable.prodMk h.aemeasurable_jumps)

/-- The jump part `−κ + ∑_{i<N} Jᵢ` is independent of the diffusion sample. -/
lemma indepFun_jumpPart (h : JumpDiffusionHyp Q Λ Z N J) (κ : ℝ) :
    IndepFun (fun ω ↦ -κ + ∑ i ∈ Finset.range (N ω), J i ω) Z Q :=
  h.Z_indep_jumps.symm.comp (measurable_neg_add_sum_range κ) measurable_id

/-- **The exponential moment of the jump part**,
`𝔼[e^{−κ + ∑_{i<N} Jᵢ}] = e^{−κ + Λ(𝔼[e^J] − 1)}`: `e^{−κ}` times the compound-Poisson moment
generating function at `1`. -/
lemma integral_exp_jumpPart (h : JumpDiffusionHyp Q Λ Z N J)
    (hJ : Integrable (fun ω ↦ rexp (J 0 ω)) Q) (κ : ℝ) :
    ∫ ω, rexp (-κ + ∑ i ∈ Finset.range (N ω), J i ω) ∂Q
      = rexp (-κ + Λ * (∫ ω, rexp (J 0 ω) ∂Q - 1)) := by
  have h1 := compoundPoisson_mgf_of_indepFun Λ 1 J h.N_law h.J_indep h.J_ident
    h.N_indep_J (by simpa only [one_mul] using hJ)
  simp only [mgf, one_mul] at h1
  simp_rw [Real.exp_add]
  rw [integral_const_mul, h1]

/-- The exponential of the jump part is integrable: its integral is positive. -/
lemma integrable_exp_jumpPart (h : JumpDiffusionHyp Q Λ Z N J)
    (hJ : Integrable (fun ω ↦ rexp (J 0 ω)) Q) (κ : ℝ) :
    Integrable (fun ω ↦ rexp (-κ + ∑ i ∈ Finset.range (N ω), J i ω)) Q :=
  Integrable.of_integral_ne_zero <| by
    rw [h.integral_exp_jumpPart hJ κ]
    exact (Real.exp_pos _).ne'

/-- At the compensator `κ = Λ(𝔼[e^J] − 1)` the jump part has `𝔼[e^{−κ + ∑_{i<N} Jᵢ}] = 1`. -/
lemma integral_exp_compensatedJumpPart (h : JumpDiffusionHyp Q Λ Z N J)
    (hJ : Integrable (fun ω ↦ rexp (J 0 ω)) Q) :
    ∫ ω, rexp (-(Λ * (∫ x, rexp (J 0 x) ∂Q - 1)) + ∑ i ∈ Finset.range (N ω), J i ω) ∂Q = 1 := by
  rw [h.integral_exp_jumpPart hJ, neg_add_cancel, Real.exp_zero]

/-- **The mixing formula for the jump-diffusion.** The discounted expected call payoff is the
Black–Scholes price averaged over the jump part `−κ + ∑_{i<N} Jᵢ`. -/
theorem call_eq_integral_bsV (h : JumpDiffusionHyp Q Λ Z N J)
    (hJ : Integrable (fun ω ↦ rexp (J 0 ω)) Q) {S_0 K r σ T : ℝ} (hS_0 : 0 < S_0) (hK : 0 < K)
    (hσ : 0 < σ) (hT : 0 < T) (κ : ℝ) :
    ∫ ω, rexp (-r * T)
        * max (jumpDiffusionTerminal S_0 r σ T κ (Z ω) (N ω) (fun i ↦ J i ω) - K) 0 ∂Q
      = ∫ ω, bsV K r σ (S_0 * rexp (-κ + ∑ i ∈ Finset.range (N ω), J i ω)) T ∂Q := by
  simp_rw [jumpDiffusionTerminal_eq]
  exact jumpDiffusion_call_eq_integral_bsV h.Z_law (h.aemeasurable_jumpPart κ)
    (h.indepFun_jumpPart κ) (h.integrable_exp_jumpPart hJ κ) hS_0 hK hσ hT

/-- **The discounted terminal price** has mean `S₀·e^{−κ + Λ(𝔼[e^J] − 1)}`: `S₀` times the
exponential moment of the jump part (`jumpDiffusion_discounted_terminal`,
`integral_exp_jumpPart`). -/
theorem discounted_terminal (h : JumpDiffusionHyp Q Λ Z N J)
    (hJ : Integrable (fun ω ↦ rexp (J 0 ω)) Q) (S_0 r σ : ℝ) {T : ℝ} (hT : 0 ≤ T) (κ : ℝ) :
    ∫ ω, rexp (-r * T) * jumpDiffusionTerminal S_0 r σ T κ (Z ω) (N ω) (fun i ↦ J i ω) ∂Q
      = S_0 * rexp (-κ + Λ * (∫ ω, rexp (J 0 ω) ∂Q - 1)) := by
  simp_rw [jumpDiffusionTerminal_eq]
  rw [jumpDiffusion_discounted_terminal h.Z_law (h.aemeasurable_jumpPart κ)
    (h.indepFun_jumpPart κ) hT, h.integral_exp_jumpPart hJ κ]

/-- **The compensator.** The discounted terminal price has mean `S₀` exactly when the drift
correction is `κ = Λ(𝔼[e^J] − 1)`, the expected number of jumps times the mean relative jump
`𝔼[e^J − 1]`. -/
theorem discounted_terminal_eq_iff (h : JumpDiffusionHyp Q Λ Z N J)
    (hJ : Integrable (fun ω ↦ rexp (J 0 ω)) Q) {S_0 : ℝ} (hS_0 : S_0 ≠ 0) (r σ : ℝ) {T : ℝ}
    (hT : 0 ≤ T) (κ : ℝ) :
    ∫ ω, rexp (-r * T) * jumpDiffusionTerminal S_0 r σ T κ (Z ω) (N ω) (fun i ↦ J i ω) ∂Q = S_0
      ↔ κ = Λ * (∫ ω, rexp (J 0 ω) ∂Q - 1) := by
  rw [h.discounted_terminal hJ S_0 r σ hT κ, mul_eq_left₀ hS_0, Real.exp_eq_one_iff,
    neg_add_eq_zero]

/-- **Jump risk is never free, for any jump law.** With the compensator
`κ = Λ(𝔼[e^J] − 1)`, the jump-diffusion call is worth at least the Black–Scholes call at the
diffusion volatility (`bsV_le_jumpDiffusion_call`). -/
theorem bsV_le_call (h : JumpDiffusionHyp Q Λ Z N J) (hJ : Integrable (fun ω ↦ rexp (J 0 ω)) Q)
    {S_0 K r σ T : ℝ} (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    bsV K r σ S_0 T ≤ ∫ ω, rexp (-r * T) * max (jumpDiffusionTerminal S_0 r σ T
        (Λ * (∫ x, rexp (J 0 x) ∂Q - 1)) (Z ω) (N ω) (fun i ↦ J i ω) - K) 0 ∂Q := by
  simp_rw [jumpDiffusionTerminal_eq]
  exact bsV_le_jumpDiffusion_call h.Z_law (h.aemeasurable_jumpPart _) (h.indepFun_jumpPart _)
    (h.integrable_exp_jumpPart hJ _) (h.integral_exp_compensatedJumpPart hJ) hS_0 hK hσ hT

/-- **Merton's formula for a general jump law** (Merton 1976). The discounted expected call payoff
of the jump-diffusion is the Poisson mixture, over the jump count `n`, of the Black–Scholes price
averaged over the jump sizes:
`𝔼[e^{−rT}(S_T − K)⁺] = ∫ n, 𝔼[C_BS(S₀e^{−κ + ∑_{i<n} Jᵢ})] ∂Poisson(Λ)`. This is the mixing
formula `call_eq_integral_bsV` with the count integrated out: the count is independent of the
jump sizes, and the averaged price is integrable against the product of their laws. -/
theorem call_poisson_mixture (h : JumpDiffusionHyp Q Λ Z N J)
    (hJ : Integrable (fun ω ↦ rexp (J 0 ω)) Q) {S_0 K r σ T : ℝ} (hS_0 : 0 < S_0) (hK : 0 < K)
    (hσ : 0 < σ) (hT : 0 < T) (κ : ℝ) :
    ∫ ω, rexp (-r * T)
        * max (jumpDiffusionTerminal S_0 r σ T κ (Z ω) (N ω) (fun i ↦ J i ω) - K) 0 ∂Q
      = ∫ n, ∫ ω, bsV K r σ (S_0 * rexp (-κ + ∑ i ∈ Finset.range n, J i ω)) T ∂Q
          ∂(poissonMeasure Λ) := by
  have := h.J_indep.isProbabilityMeasure
  have hJm := h.aemeasurable_jumps
  have hg : Measurable fun p : ℕ × (ℕ → ℝ) ↦
      bsV K r σ (S_0 * rexp (-κ + ∑ i ∈ Finset.range p.1, p.2 i)) T :=
    (measurable_bsV_spot K r σ T).comp ((measurable_neg_add_sum_range κ).exp.const_mul S_0)
  rw [h.call_eq_integral_bsV hJ hS_0 hK hσ hT κ, ← h.N_law.map_eq]
  exact integral_comp_prodMk_of_indepFun h.N_indep_J h.N_law.aemeasurable hJm <|
    (integrable_comp_prodMk_iff_of_indepFun h.N_indep_J h.N_law.aemeasurable hJm
      hg.aestronglyMeasurable).mp
      (integrable_bsV_mul_exp (h.aemeasurable_jumpPart κ) (h.integrable_exp_jumpPart hJ κ)
        hS_0 hK hσ hT)

end JumpDiffusionHyp

end MathFin

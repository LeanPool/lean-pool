/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Martingales.EquivMeasure
public import LeanPool.MathFin.Pricing.FTAP.FTAP
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# One-period FTAP on a general probability space (finite-dimensional market)

The Föllmer–Schied / one-period Dalang–Morton–Willinger Fundamental Theorem of Asset
Pricing for a discounted excess return `Y : Ω → F` valued in a **finite-dimensional**
real inner-product space `F` (the `d`-asset market is `F = EuclideanSpace ℝ (Fin d)`) and
**constant** portfolios `θ ∈ F` (trivial initial information) on an **arbitrary**
probability space `(Ω, P)`: no arbitrage ↔ there is an equivalent martingale measure
`Q ~ P` with `Y` integrable and `E_Q[Y] = 0 ∈ F`.

This is the `d`-asset generalisation of the scalar `Pricing/FTAP/FTAPOnePeriod.lean`, which is
its `F = ℝ` corollary and has no proofs of its own. The forward direction is
`MathFin.IsEMM.noArbitrage` (`Pricing/FTAP/FTAP.lean`) at horizon `1`.
Because `θ` ranges over the **finite-dimensional** `F`, the equivalent martingale measure
is **explicit**: the backward direction minimises the smooth convex softplus
potential `θ ↦ E[log(1 + exp⟪θ,Y⟫)]`. The
potential is constant along the **gains kernel** `N = {θ : ⟪θ,Y⟫ = 0 a.e.}` (the
redundant portfolio directions) and, under no arbitrage, coercive on its orthogonal
complement `Nᗮ`; so a minimiser `θ*` exists on `Nᗮ` and, because the potential is flat
along `N`, is a *global* minimiser. Its first-order condition `E[Y · σ(⟪θ*,Y⟫)] = 0`
(with `σ` the logistic function) hands back a strictly-positive bounded weight
`z = σ(⟪θ*,Y⟫)` whose normalisation `z / E[z]` is the EMM density: a bounded
`(0,1)`-valued logistic tilt, the softplus analogue of the exponential Esscher measure
rather than the Esscher measure itself. No Hahn–Banach, no L⁰-cone closedness, no
measurable selection; those are needed only for the general-Ω **multi-period** DMW.

## Scope

One trading period, a **finite-dimensional** market `F`, **trivial `ℱ₀`** (constant `θ`),
and an arbitrary `(Ω, P)`. **No non-redundancy hypothesis**: redundant assets (a `θ ≠ 0`
with `⟪θ,Y⟫ = 0` a.e.) are absorbed by minimising the potential over the gains kernel's
orthogonal complement, where coercivity is recovered. Out of scope (the remaining open
rung): the general-Ω **multi-period** DMW (predictable `L⁰(ℱ_t)`-strategies and the L⁰
gains-cone closedness).

## The one-period EMM of the library

`IsEMM` here is the library's one notion of an equivalent martingale measure for a single
trading period. The other one-period encodings are proved equivalent to it, and the
continuous-time notion restricts to it:

* the scalar `OnePeriod.IsEMM` (`Pricing/FTAP/FTAPOnePeriod.lean`) is defined as this notion
  at `F = ℝ`, and its no-arbitrage condition is this one at `F = ℝ`
  (`OnePeriod.noArbitrage_iff_vector`);
* the finite-state `HasEMMMultiState` (`Pricing/FTAP/FTAPMultiState.lean`) holds iff this
  notion has a witness on `Ω = Fin N` with the asset returns as an `ℝᴹ`-valued `Y`
  (`hasEMMMultiState_iff_exists_isEMM`);
* the discrete-time `MathFin.IsEMM` at horizon `1` with trivial `𝓕 0`
  (`Pricing/FTAP/FTAPDiscrete.lean`) is the scalar one for `Y = S 1 − S 0`
  (`isEMM_one_iff_onePeriod`);
* a continuous-time `IsEMM` gives this notion for every increment
  `S t − S s` (`IsEMM.increment`, in `Pricing/FTAP/FTAPDiscrete.lean`).

## Main definitions

* `NoArbitrage`: any constant portfolio `θ ∈ F` whose gain `⟪θ, Y⟫` is `P`-a.e. nonnegative has
  `⟪θ, Y⟫ = 0` a.e.
* `IsEMM`: `Q ~ P`, `Y` is `Q`-integrable and `E_Q[Y] = 0 ∈ F`.
* `gainsKernel`: the subspace `{θ : ⟪θ, Y⟫ = 0 a.e.}` of portfolios with a.e. zero gain.
* `softplus`, `logistic`: `log (1 + eᵘ)` and its derivative `eᵘ / (1 + eᵘ)`.
* `potential`: the softplus potential `θ ↦ ∫ softplus ⟪θ, Y⟫ ∂P`, whose minimiser's first-order
  condition produces the equivalent martingale measure.

## Main results

* `MathFin.OnePeriodVector.ftap_one_period_vector`

## References

* [H. Föllmer and A. Schied, *Stochastic Finance: An Introduction in Discrete Time*][FollmerSchied],
  §1.2

## Tags

fundamental theorem of asset pricing, softplus potential, d-asset market, no arbitrage,
logistic tilt, Dalang–Morton–Willinger, JEL G13, MSC 91G20, MSC 90C25
-/

@[expose] public section

namespace MathFin.OnePeriodVector

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] (Y : Ω → F)

/-- **No arbitrage** (finite-dim market, one period): no constant portfolio `θ ∈ F` turns
zero cost into a sure non-negative discounted gain `⟪θ, Y⟫` with a chance of profit —
any `θ` whose gain `⟪θ, Y⟫` is `≥ 0` a.e. already has `⟪θ, Y⟫ = 0` a.e. -/
def NoArbitrage : Prop :=
  ∀ θ : F, 0 ≤ᵐ[P] (fun ω ↦ inner ℝ θ (Y ω)) →
    (fun ω ↦ inner ℝ θ (Y ω)) =ᵐ[P] 0

/-- **Equivalent martingale measure** (one period, finite-dim): `Q ~ P`, `Y` is
`Q`-integrable, and `E_Q[Y] = 0 ∈ F`. The library's canonical one-period notion; see the
module docstring for the encodings proved equivalent to it. -/
structure IsEMM (Q : Measure Ω) : Prop extends IsEquivProbMeasure P Q where
  int  : Integrable Y Q
  fair : ∫ ω, Y ω ∂Q = 0

omit [IsProbabilityMeasure P] in
/-- **Forward direction**: an equivalent martingale measure precludes arbitrage. The one-period
market is the horizon-`1` market with `𝓕 0 = ⊥`, the `F`-valued price `S 0 = 0`, `S 1 = Y` and the
constant holding `θ`: `E_Q[Y] = 0` makes `S` a `Q`-martingale up to the horizon, the gain is
`⟪θ, S 1 − S 0⟫ = ⟪θ, Y⟫`, and `MathFin.IsEMM.noArbitrage` does the rest. -/
theorem noArbitrage_of_isEMM (hY : Measurable Y) {Q : Measure Ω} (hQ : IsEMM P Y Q) :
    NoArbitrage P Y := by
  have := hQ.isProb
  intro θ hpos
  -- the two-step filtration `⊥ ≤ mΩ`
  obtain ⟨𝓕, h0, h1⟩ : ∃ 𝓕 : Filtration ℕ mΩ, 𝓕 0 = ⊥ ∧ 𝓕 1 = mΩ :=
    ⟨{ seq := fun n ↦ if n = 0 then ⊥ else mΩ
       mono' := fun a b hab ↦ by
         dsimp only
         split_ifs with ha hb hb
         · exact le_rfl
         · exact bot_le
         · exact absurd (Nat.le_zero.mp (hb ▸ hab)) ha
         · exact le_rfl
       le' := fun n ↦ by
         split_ifs
         · exact bot_le
         · exact le_rfl }, rfl, rfl⟩
  let S : ℕ → Ω → F := fun n ω ↦ if n = 0 then 0 else Y ω
  have hS0 : S 0 = 0 := funext fun ω ↦ ite_eq_left rfl
  have hS1 : S 1 = Y := funext fun ω ↦ ite_eq_right one_ne_zero
  have hgain : martingaleTransform (fun _ _ ↦ θ) S 1 = fun ω ↦ inner ℝ θ (Y ω) := by
    funext ω; simp [martingaleTransform, hS0, hS1]
  have hE : MathFin.IsEMM 𝓕 P S 1 Q := .of_condExp_succ hQ.toIsEquivProbMeasure
    (fun t ht ↦ by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ht with rfl | rfl
      · rw [hS0]; exact stronglyMeasurable_zero
      · rw [hS1, h1]; exact hY.stronglyMeasurable)
    (fun t ht ↦ by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ht with rfl | rfl
      · rw [hS0]; exact integrable_zero _ _ _
      · rw [hS1]; exact hQ.int)
    (fun t ht ↦ by
      obtain rfl : t = 0 := Nat.lt_one_iff.mp ht
      rw [h0, condExp_bot, hS1, hQ.fair, hS0]
      exact Filter.Eventually.of_forall fun ω ↦ by simp)
  have hnull := hE.noArbitrage (fun _ _ ↦ θ) (fun _ _ ↦ stronglyMeasurable_const)
    ⟨‖θ‖, fun _ _ _ ↦ le_rfl⟩ (by rw [hgain]; exact hpos)
  rwa [hgain] at hnull

/-! ### The softplus potential and its logistic derivative

The backward direction minimises `θ ↦ ∫ softplus ⟪θ,Y⟫`; `softplus u = log(1+eᵘ)` is
the smooth convex penalty whose derivative is the **logistic** `σ(u) = eᵘ/(1+eᵘ) ∈
(0,1)`. The bounds `u⁺ ≤ softplus u ≤ |u| + log 2` give coercivity and integrability;
`σ ∈ (0,1)` gives the uniform `L¹` domination for differentiating under the integral. -/

/-- Softplus penalty `log(1 + eᵘ)`. -/
noncomputable def softplus (u : ℝ) : ℝ := Real.log (1 + Real.exp u)

/-- Logistic function `eᵘ/(1 + eᵘ) = σ(u)`, the derivative of `softplus`. -/
noncomputable def logistic (u : ℝ) : ℝ := Real.exp u / (1 + Real.exp u)

lemma logistic_pos (u : ℝ) : 0 < logistic u := by rw [logistic]; positivity

lemma logistic_lt_one (u : ℝ) : logistic u < 1 := by
  rw [logistic, div_lt_one (by positivity)]; linarith [Real.exp_pos u]

lemma softplus_nonneg (u : ℝ) : 0 ≤ softplus u := by
  rw [softplus]; exact Real.log_nonneg (by linarith [Real.exp_pos u])

lemma self_le_softplus (u : ℝ) : u ≤ softplus u := by
  rw [softplus]
  calc u = Real.log (Real.exp u) := (Real.log_exp u).symm
    _ ≤ Real.log (1 + Real.exp u) :=
        Real.log_le_log (Real.exp_pos u) (by linarith [Real.exp_pos u])

/-- `u⁺ = max u 0 ≤ softplus u`: the lower bound powering coercivity of the potential. -/
lemma posPart_le_softplus (u : ℝ) : max u 0 ≤ softplus u :=
  max_le (self_le_softplus u) (softplus_nonneg u)

/-- `softplus u ≤ |u| + log 2`: the linear-growth upper bound giving `L¹`-integrability. -/
lemma softplus_le (u : ℝ) : softplus u ≤ |u| + Real.log 2 := by
  rw [softplus]
  have hb : 1 + Real.exp u ≤ 2 * Real.exp |u| := by
    have h1 : Real.exp u ≤ Real.exp |u| := Real.exp_le_exp.mpr (le_abs_self u)
    have h2 : (1 : ℝ) ≤ Real.exp |u| := Real.one_le_exp (abs_nonneg u)
    linarith
  calc Real.log (1 + Real.exp u) ≤ Real.log (2 * Real.exp |u|) :=
        Real.log_le_log (by positivity) hb
    _ = |u| + Real.log 2 := by
        rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]; ring

/-- `softplus` is differentiable with derivative the logistic `σ`. -/
lemma hasDerivAt_softplus (u : ℝ) : HasDerivAt softplus (logistic u) u := by
  have h2 : (1 : ℝ) + Real.exp u ≠ 0 := by positivity
  have h1 : HasDerivAt (fun v ↦ 1 + Real.exp v) (Real.exp u) u := by
    simpa using (Real.hasDerivAt_exp u).const_add 1
  have h3 := (Real.hasDerivAt_log h2).comp u h1
  rw [show logistic u = (1 + Real.exp u)⁻¹ * Real.exp u from by rw [logistic, div_eq_inv_mul]]
  exact h3

lemma continuous_softplus : Continuous softplus := by
  have hpos : ∀ u : ℝ, (0 : ℝ) < 1 + Real.exp u := fun u ↦ by positivity
  exact (continuous_const.add Real.continuous_exp).log (fun u ↦ (hpos u).ne')

lemma continuous_logistic : Continuous logistic := by
  have hpos : ∀ u : ℝ, (0 : ℝ) < 1 + Real.exp u := fun u ↦ by positivity
  exact Real.continuous_exp.div (continuous_const.add Real.continuous_exp) (fun u ↦ (hpos u).ne')

/-- The **softplus potential** `f(θ) = ∫ softplus⟪θ,Y⟫ ∂P`, minimised in the backward
direction; its first-order condition produces the equivalent martingale measure. -/
noncomputable def potential (θ : F) : ℝ :=
  ∫ ω, softplus (inner ℝ θ (Y ω)) ∂P

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
/-- `softplus⟪θ,Y⟫` is `P`-integrable, dominated by `‖θ‖‖Y‖ + log 2`. -/
lemma integrable_softplus_inner (hYint : Integrable Y P) (θ : F) :
    Integrable (fun ω ↦ softplus (inner ℝ θ (Y ω))) P := by
  have hmeas : AEStronglyMeasurable (fun ω ↦ softplus (inner ℝ θ (Y ω))) P :=
    continuous_softplus.comp_aestronglyMeasurable
      ((continuous_const.inner continuous_id).comp_aestronglyMeasurable hYint.aestronglyMeasurable)
  refine Integrable.mono' (g := fun ω ↦ ‖θ‖ * ‖Y ω‖ + Real.log 2) ?_ hmeas ?_
  · exact (hYint.norm.const_mul ‖θ‖).add (integrable_const _)
  · filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (softplus_nonneg _)]
    exact (softplus_le _).trans (by gcongr; exact abs_real_inner_le_norm _ _)

/-- **Directional derivative of the potential**. For `Y ∈ L¹`, `t ↦ f(θ + t•u)` is
differentiable at `0` with derivative `∫ σ⟪θ,Y⟫ · ⟪u,Y⟫ ∂P` — differentiation under the
integral, dominated by `‖u‖‖Y‖` since `σ ∈ (0,1)`. -/
lemma hasDerivAt_potential_dir (hY : Measurable Y) (hYint : Integrable Y P) (θ u : F) :
    HasDerivAt (fun t : ℝ ↦ potential P Y (θ + t • u))
      (∫ ω, logistic (inner ℝ θ (Y ω)) * inner ℝ u (Y ω) ∂P) 0 := by
  have hbmeas : Measurable (fun ω ↦ inner ℝ u (Y ω)) := measurable_const.inner hY
  have hexp : ∀ (t : ℝ) (ω : Ω),
      inner ℝ (θ + t • u) (Y ω) = inner ℝ θ (Y ω) + t * inner ℝ u (Y ω) := fun t ω ↦ by
    rw [inner_add_left, real_inner_smul_left]
  set Φ : ℝ → Ω → ℝ :=
    fun t ω ↦ softplus (inner ℝ θ (Y ω) + t * inner ℝ u (Y ω)) with hΦ
  set Φ' : ℝ → Ω → ℝ :=
    fun t ω ↦ logistic (inner ℝ θ (Y ω) + t * inner ℝ u (Y ω)) * inner ℝ u (Y ω) with hΦ'
  have hmeas_arg : ∀ t : ℝ, AEStronglyMeasurable
      (fun ω ↦ inner ℝ θ (Y ω) + t * inner ℝ u (Y ω)) P :=
    fun t ↦ ((measurable_const.inner hY).add (hbmeas.const_mul t)).aestronglyMeasurable
  have hΦ_meas : ∀ᶠ t in nhds (0 : ℝ), AEStronglyMeasurable (Φ t) P :=
    Filter.Eventually.of_forall fun t ↦
      continuous_softplus.comp_aestronglyMeasurable (hmeas_arg t)
  have hΦ_int : Integrable (Φ 0) P := by
    simp only [hΦ, zero_mul, add_zero]; exact integrable_softplus_inner P Y hYint θ
  have hΦ'_meas : AEStronglyMeasurable (Φ' 0) P :=
    (continuous_logistic.comp_aestronglyMeasurable (hmeas_arg 0)).mul hbmeas.aestronglyMeasurable
  have h_bound : ∀ᵐ ω ∂P, ∀ x ∈ (Set.univ : Set ℝ), ‖Φ' x ω‖ ≤ ‖u‖ * ‖Y ω‖ := by
    filter_upwards with ω x _
    rw [hΦ', Real.norm_eq_abs, abs_mul]
    have h1 : |logistic (inner ℝ θ (Y ω) + x * inner ℝ u (Y ω))| ≤ 1 := by
      rw [abs_of_pos (logistic_pos _)]; exact (logistic_lt_one _).le
    have h2 : |inner ℝ u (Y ω)| ≤ ‖u‖ * ‖Y ω‖ := abs_real_inner_le_norm u (Y ω)
    calc |logistic (inner ℝ θ (Y ω) + x * inner ℝ u (Y ω))| * |inner ℝ u (Y ω)|
        ≤ 1 * (‖u‖ * ‖Y ω‖) := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ = ‖u‖ * ‖Y ω‖ := one_mul _
  have h_diff : ∀ᵐ ω ∂P, ∀ x ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun t ↦ Φ t ω) (Φ' x ω) x := by
    filter_upwards with ω x _
    have haff : HasDerivAt (fun t : ℝ ↦ inner ℝ θ (Y ω) + t * inner ℝ u (Y ω))
        (inner ℝ u (Y ω)) x := by
      simpa using ((hasDerivAt_id x).mul_const (inner ℝ u (Y ω))).const_add (inner ℝ θ (Y ω))
    have hc := (hasDerivAt_softplus _).comp x haff
    simpa only [hΦ, hΦ', Function.comp_def] using hc
  obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P)
    (bound := fun ω ↦ ‖u‖ * ‖Y ω‖) Filter.univ_mem hΦ_meas hΦ_int hΦ'_meas h_bound
    (hYint.norm.const_mul ‖u‖) h_diff
  have hpot : (fun t : ℝ ↦ potential P Y (θ + t • u)) = fun t ↦ ∫ ω, Φ t ω ∂P := by
    funext t; simp only [potential, hΦ]
    exact integral_congr_ae (by filter_upwards with ω; rw [hexp t ω])
  have hval : (∫ ω, Φ' 0 ω ∂P) = ∫ ω, logistic (inner ℝ θ (Y ω)) * inner ℝ u (Y ω) ∂P := by
    refine integral_congr_ae ?_; filter_upwards with ω; simp only [hΦ', zero_mul, add_zero]
  rw [hpot, ← hval]; exact hderiv

/-- `softplus` is `1`-Lipschitz (its derivative `σ` lies in `(0,1)`). -/
lemma lipschitzWith_softplus : LipschitzWith 1 softplus := by
  refine lipschitzWith_of_nnNorm_deriv_le
    (fun x ↦ (hasDerivAt_softplus x).differentiableAt) fun x ↦ ?_
  rw [(hasDerivAt_softplus x).deriv, ← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_one,
    Real.norm_eq_abs, abs_of_pos (logistic_pos x)]
  exact (logistic_lt_one x).le

omit [IsProbabilityMeasure P] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
/-- For a `1`-Lipschitz `φ`, the averaged map `θ ↦ ∫ φ⟪θ,Y⟫ ∂P` is `(∫‖Y‖)`-Lipschitz
(`φ` is `1`-Lipschitz and `θ ↦ ⟪θ,Y ω⟫` is `‖Y ω‖`-Lipschitz, by Cauchy–Schwarz). -/
lemma lipschitzWith_integral_inner {φ : ℝ → ℝ} (hφ : LipschitzWith 1 φ)
    (hint : ∀ θ : F, Integrable (fun ω ↦ φ (inner ℝ θ (Y ω))) P)
    (hYint : Integrable Y P) :
    LipschitzWith (∫ ω, ‖Y ω‖ ∂P).toNNReal (fun θ ↦ ∫ ω, φ (inner ℝ θ (Y ω)) ∂P) := by
  have hnn : 0 ≤ ∫ ω, ‖Y ω‖ ∂P := integral_nonneg fun ω ↦ norm_nonneg _
  refine LipschitzWith.of_dist_le_mul fun θ θ' ↦ ?_
  rw [Real.dist_eq, Real.coe_toNNReal _ hnn, ← integral_sub (hint θ) (hint θ'), dist_eq_norm]
  have hbound : ∀ ω, ‖φ (inner ℝ θ (Y ω)) - φ (inner ℝ θ' (Y ω))‖ ≤ ‖Y ω‖ * ‖θ - θ'‖ := by
    intro ω
    have h1 := hφ.dist_le_mul (inner ℝ θ (Y ω)) (inner ℝ θ' (Y ω))
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at h1
    calc ‖φ (inner ℝ θ (Y ω)) - φ (inner ℝ θ' (Y ω))‖
        = |φ (inner ℝ θ (Y ω)) - φ (inner ℝ θ' (Y ω))| := Real.norm_eq_abs _
      _ ≤ |inner ℝ θ (Y ω) - inner ℝ θ' (Y ω)| := h1
      _ = |inner ℝ (θ - θ') (Y ω)| := by rw [inner_sub_left]
      _ ≤ ‖Y ω‖ * ‖θ - θ'‖ := by rw [mul_comm]; exact abs_real_inner_le_norm (θ - θ') (Y ω)
  calc |∫ ω, (φ (inner ℝ θ (Y ω)) - φ (inner ℝ θ' (Y ω))) ∂P|
      ≤ ∫ ω, ‖φ (inner ℝ θ (Y ω)) - φ (inner ℝ θ' (Y ω))‖ ∂P := abs_integral_le_integral_abs ..
    _ ≤ ∫ ω, ‖Y ω‖ * ‖θ - θ'‖ ∂P :=
        integral_mono_ae ((hint θ).sub (hint θ')).norm (hYint.norm.mul_const _)
          (Filter.Eventually.of_forall hbound)
    _ = (∫ ω, ‖Y ω‖ ∂P) * ‖θ - θ'‖ := integral_mul_const _ _

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
/-- The potential is continuous. -/
lemma continuous_potential (hYint : Integrable Y P) : Continuous (potential P Y) :=
  (lipschitzWith_integral_inner P Y lipschitzWith_softplus
    (integrable_softplus_inner P Y hYint) hYint).continuous

/-- `s ↦ max s 0` (positive part) is `1`-Lipschitz. -/
lemma lipschitzWith_posPart : LipschitzWith 1 (fun s : ℝ ↦ max s 0) :=
  LipschitzWith.id.max_const 0

omit [IsProbabilityMeasure P] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
/-- `max⟪θ,Y⟫ 0` is `P`-integrable (dominated by `‖θ‖‖Y‖`). -/
lemma integrable_posPart_inner (hYint : Integrable Y P) (θ : F) :
    Integrable (fun ω ↦ max (inner ℝ θ (Y ω)) 0) P := by
  have hmeas : AEStronglyMeasurable (fun ω ↦ max (inner ℝ θ (Y ω)) 0) P :=
    (continuous_id.max continuous_const).comp_aestronglyMeasurable
      ((continuous_const.inner continuous_id).comp_aestronglyMeasurable hYint.aestronglyMeasurable)
  refine Integrable.mono' (hYint.norm.const_mul ‖θ‖) hmeas (Filter.Eventually.of_forall fun ω ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), max_le_iff]
  exact ⟨(le_abs_self _).trans (abs_real_inner_le_norm θ (Y ω)), by positivity⟩

omit [IsProbabilityMeasure P] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
/-- The positive-gain average `g(θ) = ∫⟪θ,Y⟫⁺ ∂P` is continuous. It lower-bounds the
potential (`softplus s ≥ s⁺`) and drives the coercivity argument. -/
lemma continuous_gainsPos (hYint : Integrable Y P) :
    Continuous (fun θ ↦ ∫ ω, max (inner ℝ θ (Y ω)) 0 ∂P) :=
  (lipschitzWith_integral_inner P Y lipschitzWith_posPart
    (integrable_posPart_inner P Y hYint) hYint).continuous

/-! ### The gains kernel and coercivity over its complement

`N = {θ : ⟪θ,Y⟫ = 0 a.e.}` is the linear subspace of **redundant** portfolio directions.
The potential is constant along `N`, so the backward construction minimises it over the
orthogonal complement `Nᗮ`, where no arbitrage makes it coercive. A minimiser on `Nᗮ` is
automatically a *global* minimiser (the potential is `N`-translation-invariant), so no
non-redundancy hypothesis is required. -/

/-- The **gains kernel** `N = {θ : ⟪θ,Y⟫ = 0 a.e.}`: portfolios whose discounted gain is
a.e. zero. A linear subspace of `F`; the market is non-redundant iff `N = ⊥`. -/
def gainsKernel : Submodule ℝ F where
  carrier := {θ | (fun ω ↦ inner ℝ θ (Y ω)) =ᵐ[P] 0}
  zero_mem' := by
    change (fun ω ↦ inner ℝ (0 : F) (Y ω)) =ᵐ[P] 0
    filter_upwards with ω; simp
  add_mem' := by
    intro a b ha hb
    change (fun ω ↦ inner ℝ (a + b) (Y ω)) =ᵐ[P] 0
    have ha' : (fun ω ↦ inner ℝ a (Y ω)) =ᵐ[P] 0 := ha
    have hb' : (fun ω ↦ inner ℝ b (Y ω)) =ᵐ[P] 0 := hb
    filter_upwards [ha', hb'] with ω ea eb
    simp only [Pi.zero_apply] at ea eb ⊢
    rw [inner_add_left, ea, eb, add_zero]
  smul_mem' := by
    intro c b hb
    change (fun ω ↦ inner ℝ (c • b) (Y ω)) =ᵐ[P] 0
    have hb' : (fun ω ↦ inner ℝ b (Y ω)) =ᵐ[P] 0 := hb
    filter_upwards [hb'] with ω eb
    simp only [Pi.zero_apply] at eb ⊢
    rw [real_inner_smul_left, eb, mul_zero]

omit [IsProbabilityMeasure P] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
@[simp] lemma mem_gainsKernel {θ : F} :
    θ ∈ gainsKernel P Y ↔ (fun ω ↦ inner ℝ θ (Y ω)) =ᵐ[P] 0 := Iff.rfl

omit [MeasurableSpace F] [BorelSpace F] in
/-- **Coercivity** of the potential on `Nᗮ` (no arbitrage). The positive gain average
`g(θ) = ∫⟪θ,Y⟫⁺` is positive on `Nᗮ \ {0}` (no arbitrage, plus `N ⊓ Nᗮ = ⊥`), continuous
and positively homogeneous; its minimum `c` over the unit sphere of `Nᗮ` is positive, and
`softplus s ≥ s⁺` gives `c‖θ‖ ≤ f(θ)` for `θ ∈ Nᗮ`. -/
lemma exists_pos_lower_bound (hYint : Integrable Y P) (hNA : NoArbitrage P Y)
    (hNbot : (gainsKernel P Y)ᗮ ≠ ⊥) :
    ∃ c > 0, ∀ θ ∈ (gainsKernel P Y)ᗮ, c * ‖θ‖ ≤ potential P Y θ := by
  set N := gainsKernel P Y
  set g : F → ℝ := fun θ ↦ ∫ ω, max (inner ℝ θ (Y ω)) 0 ∂P with hg
  have hg_nonneg : ∀ θ, 0 ≤ g θ := fun θ ↦ integral_nonneg fun ω ↦ le_max_right _ _
  -- `g` is positive on `Nᗮ \ {0}`
  have hg_pos : ∀ θ ∈ Nᗮ, θ ≠ 0 → 0 < g θ := by
    intro θ hθK hθ
    refine (hg_nonneg θ).lt_of_ne fun h ↦ hθ ?_
    have hmax : (fun ω ↦ max (inner ℝ θ (Y ω)) 0) =ᵐ[P] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall fun ω ↦ le_max_right _ _)
        (integrable_posPart_inner P Y hYint θ)).mp h.symm
    have hnonpos : (fun ω ↦ inner ℝ θ (Y ω)) ≤ᵐ[P] 0 := by
      filter_upwards [hmax] with ω hm
      have hle : inner ℝ θ (Y ω) ≤ max (inner ℝ θ (Y ω)) 0 := le_max_left _ _
      simp only [Pi.zero_apply] at hm ⊢; rwa [hm] at hle
    have hneg := hNA (-θ) (by
      filter_upwards [hnonpos] with ω h
      simp only [Pi.zero_apply] at h ⊢; rw [inner_neg_left]; linarith)
    have hθN : θ ∈ N := by
      change (fun ω ↦ inner ℝ θ (Y ω)) =ᵐ[P] 0
      filter_upwards [hneg] with ω hh
      simp only [Pi.zero_apply, inner_neg_left] at hh ⊢; linarith
    exact inner_self_eq_zero.mp (N.inner_right_of_mem_orthogonal hθN hθK)
  -- `g` is positively homogeneous
  have hg_hom : ∀ (r : ℝ), 0 ≤ r → ∀ θ, g (r • θ) = r * g θ := by
    intro r hr θ
    simp only [hg]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
    change max (inner ℝ (r • θ) (Y ω)) 0 = r * max (inner ℝ θ (Y ω)) 0
    rw [real_inner_smul_left]
    rcases le_total 0 (inner ℝ θ (Y ω)) with hs | hs
    · rw [max_eq_left hs, max_eq_left (mul_nonneg hr hs)]
    · rw [max_eq_right hs, max_eq_right (mul_nonpos_of_nonneg_of_nonpos hr hs), mul_zero]
  -- minimum of `g` over the unit sphere of `Nᗮ` is positive
  have hScompact : IsCompact ((Nᗮ : Set F) ∩ Metric.sphere 0 1) :=
    (isCompact_sphere 0 1).inter_left Nᗮ.isClosed_of_finiteDimensional
  have hSne : ((Nᗮ : Set F) ∩ Metric.sphere 0 1).Nonempty := by
    obtain ⟨v, hvK, hv0⟩ := (Submodule.ne_bot_iff _).mp hNbot
    have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    refine ⟨(‖v‖⁻¹ : ℝ) • v, Nᗮ.smul_mem _ hvK, ?_⟩
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos hvnorm, inv_mul_cancel₀ hvnorm.ne']
  obtain ⟨u₀, hu₀mem, hu₀min⟩ :=
    hScompact.exists_isMinOn hSne (continuous_gainsPos P Y hYint).continuousOn
  obtain ⟨hu₀K, hu₀S⟩ := hu₀mem
  have hu₀ne : u₀ ≠ 0 := fun h ↦ by
    rw [Metric.mem_sphere, h, dist_self] at hu₀S; exact one_ne_zero hu₀S.symm
  refine ⟨g u₀, hg_pos u₀ hu₀K hu₀ne, fun θ hθK ↦ ?_⟩
  have hpg : g θ ≤ potential P Y θ := by
    rw [hg, potential]
    exact integral_mono_ae (integrable_posPart_inner P Y hYint θ)
      (integrable_softplus_inner P Y hYint θ)
      (Filter.Eventually.of_forall fun ω ↦ posPart_le_softplus _)
  refine le_trans ?_ hpg
  rcases eq_or_ne θ 0 with rfl | hθ
  · simpa using hg_nonneg 0
  · have hθ0 : (0 : ℝ) < ‖θ‖ := norm_pos_iff.mpr hθ
    have hunit : (‖θ‖⁻¹ : ℝ) • θ ∈ (Nᗮ : Set F) ∩ Metric.sphere 0 1 := by
      refine ⟨Nᗮ.smul_mem _ hθK, ?_⟩
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_pos hθ0, inv_mul_cancel₀ hθ0.ne']
    calc g u₀ * ‖θ‖ = ‖θ‖ * g u₀ := mul_comm _ _
      _ ≤ ‖θ‖ * g ((‖θ‖⁻¹ : ℝ) • θ) :=
          mul_le_mul_of_nonneg_left (isMinOn_iff.mp hu₀min _ hunit) hθ0.le
      _ = g θ := by
          rw [hg_hom ‖θ‖⁻¹ (inv_nonneg.mpr hθ0.le) θ, ← mul_assoc, mul_inv_cancel₀ hθ0.ne', one_mul]

omit [MeasurableSpace F] [BorelSpace F] in
/-- **The potential attains a global minimum** (no arbitrage). On `Nᗮ`, coercivity makes
the minimum over a large closed ball global; and the potential is constant along `N`
(`⟪n,Y⟫ = 0` a.e.), so a minimiser over `Nᗮ` minimises over all of `F` after the
decomposition `θ = n + z`, `n ∈ N`, `z ∈ Nᗮ`. -/
lemma exists_global_min_potential (hYint : Integrable Y P) (hNA : NoArbitrage P Y)
    (hNbot : (gainsKernel P Y)ᗮ ≠ ⊥) :
    ∃ θ₀, ∀ θ, potential P Y θ₀ ≤ potential P Y θ := by
  set N := gainsKernel P Y
  obtain ⟨c, hc, hlb⟩ := exists_pos_lower_bound P Y hYint hNA hNbot
  -- the potential is constant along `N`
  have hinv : ∀ ψ : F, ∀ n ∈ N, potential P Y (ψ + n) = potential P Y ψ := by
    intro ψ n hn
    have hn' : (fun ω ↦ inner ℝ n (Y ω)) =ᵐ[P] 0 := hn
    refine integral_congr_ae ?_
    filter_upwards [hn'] with ω he
    simp only [Pi.zero_apply] at he
    show softplus (inner ℝ (ψ + n) (Y ω)) = softplus (inner ℝ ψ (Y ω))
    rw [inner_add_left, he, add_zero]
  -- minimise over the compact set `Nᗮ ∩ closedBall 0 R`
  have hp0 : 0 ≤ potential P Y 0 := integral_nonneg fun ω ↦ softplus_nonneg _
  set R : ℝ := potential P Y 0 / c with hRdef
  have hR0 : 0 ≤ R := div_nonneg hp0 hc.le
  have hKcompact : IsCompact ((Nᗮ : Set F) ∩ Metric.closedBall 0 R) :=
    (isCompact_closedBall 0 R).inter_left Nᗮ.isClosed_of_finiteDimensional
  have hKne : ((Nᗮ : Set F) ∩ Metric.closedBall 0 R).Nonempty :=
    ⟨0, Nᗮ.zero_mem, Metric.mem_closedBall_self hR0⟩
  obtain ⟨θ₀, hθ₀mem, hθ₀min⟩ :=
    hKcompact.exists_isMinOn hKne (continuous_potential P Y hYint).continuousOn
  obtain ⟨hθ₀K, _⟩ := hθ₀mem
  have hcR : c * R = potential P Y 0 := by rw [hRdef]; field_simp
  -- θ₀ minimises over all of `Nᗮ` (coercivity escapes the ball)
  have hθ₀minK : ∀ θ ∈ Nᗮ, potential P Y θ₀ ≤ potential P Y θ := by
    intro θ hθK
    rcases le_or_gt ‖θ‖ R with hle | hlt
    · exact isMinOn_iff.mp hθ₀min θ ⟨hθK, by rw [Metric.mem_closedBall, dist_zero_right]; exact hle⟩
    · calc potential P Y θ₀
          ≤ potential P Y 0 := isMinOn_iff.mp hθ₀min 0 ⟨Nᗮ.zero_mem, Metric.mem_closedBall_self hR0⟩
        _ = c * R := hcR.symm
        _ ≤ c * ‖θ‖ := mul_le_mul_of_nonneg_left hlt.le hc.le
        _ ≤ potential P Y θ := hlb θ hθK
  -- lift to all of `F`: `f(θ) = f(z) ≥ f(θ₀)` for the `Nᗮ`-component `z` of `θ`
  refine ⟨θ₀, fun θ ↦ ?_⟩
  obtain ⟨n, hn, z, hz, hnz⟩ : ∃ n ∈ N, ∃ z ∈ Nᗮ, n + z = θ := by
    have hmem : θ ∈ N ⊔ Nᗮ := by
      rw [Submodule.sup_orthogonal_of_hasOrthogonalProjection]; trivial
    exact Submodule.mem_sup.mp hmem
  have hfθ : potential P Y θ = potential P Y z := by
    rw [← hnz, add_comm n z, hinv z n hn]
  rw [hfθ]; exact hθ₀minK z hz

/-- **First-order condition**. At a global minimiser `θ₀` of the potential, every
directional derivative vanishes (`IsLocalMin.hasDerivAt_eq_zero`), so the gradient
`∫ σ⟪θ₀,Y⟫ • Y` is the zero vector — the candidate density `z = σ⟪θ₀,Y⟫` makes `Y` fair. -/
lemma integral_logistic_smul_eq_zero (hY : Measurable Y) (hYint : Integrable Y P)
    {θ₀ : F} (hmin : ∀ θ, potential P Y θ₀ ≤ potential P Y θ) :
    ∫ ω, logistic (inner ℝ θ₀ (Y ω)) • Y ω ∂P = 0 := by
  -- every directional derivative at `θ₀` is `0`
  have hdir : ∀ u, ∫ ω, logistic (inner ℝ θ₀ (Y ω)) * inner ℝ u (Y ω) ∂P = 0 := by
    intro u
    have hmin0 : IsLocalMin (fun t : ℝ ↦ potential P Y (θ₀ + t • u)) 0 :=
      Filter.Eventually.of_forall fun t ↦ by simp only [zero_smul, add_zero]; exact hmin _
    exact hmin0.hasDerivAt_eq_zero (hasDerivAt_potential_dir P Y hY hYint θ₀ u)
  -- the gradient vector is `0`: it is `inner`-orthogonal to everything
  have hGint : Integrable (fun ω ↦ logistic (inner ℝ θ₀ (Y ω)) • Y ω) P := by
    refine Integrable.mono' hYint.norm
      ((continuous_logistic.comp_aestronglyMeasurable
        ((continuous_const.inner continuous_id).comp_aestronglyMeasurable
          hYint.aestronglyMeasurable)).smul hYint.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω ↦ ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (logistic_pos _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (logistic_lt_one _).le
  have hGu : ∀ u, inner ℝ (∫ ω, logistic (inner ℝ θ₀ (Y ω)) • Y ω ∂P) u = 0 := by
    intro u
    rw [real_inner_comm, ← integral_inner hGint]
    simp_rw [real_inner_smul_right]
    exact hdir u
  exact inner_self_eq_zero.mp (hGu _)

/-- **Integrable backward direction** (finite-dim market). For an integrable `Y`, no
arbitrage gives an equivalent martingale measure. If `Y =ᵐ 0` (every direction redundant)
then `Q = P`; otherwise the logistic density `z = σ⟪θ₀,Y⟫` at the potential's global
minimiser is strictly positive, bounded, and fair, so `Q = P.withDensity (z / ∫z)` is the
EMM. -/
theorem exists_isEMM_of_noArbitrage_integrable (hY : Measurable Y) (hYint : Integrable Y P)
    (hNA : NoArbitrage P Y) :
    ∃ Q, IsEMM P Y Q := by
  by_cases hY0 : (gainsKernel P Y)ᗮ = ⊥
  · -- `Nᗮ = ⊥ ⟹ N = ⊤`: `Y` is a.e. orthogonal to every `θ`, so `E[Y] = 0` and `Q = P`
    refine ⟨P, ⟨inferInstance, .rfl, .rfl⟩, hYint, ?_⟩
    have hNtop : gainsKernel P Y = ⊤ := by
      have hoo := Submodule.orthogonal_orthogonal (gainsKernel P Y)
      rw [hY0, Submodule.bot_orthogonal_eq_top] at hoo
      exact hoo.symm
    have hall : ∀ θ : F, inner ℝ θ (∫ ω, Y ω ∂P) = (0 : ℝ) := by
      intro θ
      have hmem : θ ∈ gainsKernel P Y := by rw [hNtop]; exact Submodule.mem_top
      have hθN : (fun ω ↦ inner ℝ θ (Y ω)) =ᵐ[P] 0 := (mem_gainsKernel P Y).mp hmem
      calc inner ℝ θ (∫ ω, Y ω ∂P)
          = ∫ ω, inner ℝ θ (Y ω) ∂P := (integral_inner hYint θ).symm
        _ = 0 := by rw [integral_congr_ae hθN]; simp
    exact inner_self_eq_zero.mp (hall _)
  · obtain ⟨θ₀, hmin⟩ := exists_global_min_potential P Y hYint hNA hY0
    have hfair := integral_logistic_smul_eq_zero P Y hY hYint hmin
    set z : Ω → ℝ := fun ω ↦ logistic (inner ℝ θ₀ (Y ω))
    have hzpos : ∀ ω, 0 < z ω := fun ω ↦ logistic_pos _
    have hzlt : ∀ ω, z ω < 1 := fun ω ↦ logistic_lt_one _
    have hzmeas : Measurable z := continuous_logistic.measurable.comp (measurable_const.inner hY)
    have hzint : Integrable z P :=
      ⟨hzmeas.aestronglyMeasurable, HasFiniteIntegral.of_bounded
        (Filter.Eventually.of_forall fun ω ↦ by
          rw [Real.norm_eq_abs, abs_of_pos (hzpos ω)]; exact (hzlt ω).le)⟩
    set ζ : ℝ := ∫ ω, z ω ∂P with hζ
    have hζpos : 0 < ζ := by
      rw [hζ, integral_pos_iff_support_of_nonneg_ae
          (Filter.Eventually.of_forall fun ω ↦ (hzpos ω).le) hzint,
        show Function.support z = Set.univ from Set.eq_univ_of_forall fun ω ↦ (hzpos ω).ne']
      rw [measure_univ]; exact one_pos
    set dens : Ω → ℝ := fun ω ↦ z ω / ζ with hdens
    have hdpos : ∀ ω, 0 < dens ω := fun ω ↦ div_pos (hzpos ω) hζpos
    have hdmeas : Measurable dens := hzmeas.div_const ζ
    have hdint : Integrable dens P := hzint.div_const ζ
    have hdsum : ∫ ω, dens ω ∂P = 1 := by
      simp only [hdens, div_eq_inv_mul]
      rw [integral_const_mul, ← hζ, inv_mul_cancel₀ hζpos.ne']
    have hdbound : ∀ ω, dens ω ≤ ζ⁻¹ := fun ω ↦ by
      rw [hdens, div_le_iff₀ hζpos, inv_mul_cancel₀ hζpos.ne']; exact (hzlt ω).le
    set Q : Measure Ω := P.withDensity (fun ω ↦ ENNReal.ofReal (dens ω)) with hQ
    have hofReal_meas : Measurable (fun ω ↦ ENNReal.ofReal (dens ω)) :=
      ENNReal.measurable_ofReal.comp hdmeas
    obtain ⟨hQprob, hQP, hPQ⟩ := isEquivProbMeasure_withDensity P hdpos hdint hdsum
    rw [← hQ] at hQprob hQP hPQ
    have := hQprob
    have hdY_int : Integrable (fun ω ↦ dens ω • Y ω) P := by
      refine Integrable.mono' (hYint.norm.const_mul ζ⁻¹)
        (hdmeas.aestronglyMeasurable.smul hYint.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun ω ↦ ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hdpos ω)]
      exact mul_le_mul_of_nonneg_right (hdbound ω) (norm_nonneg _)
    have hYintQ : Integrable Y Q := by
      rw [hQ, integrable_withDensity_iff_integrable_smul' hofReal_meas
        (Filter.Eventually.of_forall fun ω ↦ ENNReal.ofReal_lt_top)]
      refine hdY_int.congr (Filter.Eventually.of_forall fun ω ↦ ?_)
      change dens ω • Y ω = (ENNReal.ofReal (dens ω)).toReal • Y ω
      rw [ENNReal.toReal_ofReal (hdpos ω).le]
    have hQfair : ∫ ω, Y ω ∂Q = 0 := by
      rw [hQ, integral_withDensity_eq_integral_toReal_smul hofReal_meas
        (Filter.Eventually.of_forall fun ω ↦ ENNReal.ofReal_lt_top)]
      have heq : (fun ω ↦ (ENNReal.ofReal (dens ω)).toReal • Y ω)
          = fun ω ↦ ζ⁻¹ • (z ω • Y ω) := by
        funext ω
        show (ENNReal.ofReal (dens ω)).toReal • Y ω = ζ⁻¹ • (z ω • Y ω)
        rw [ENNReal.toReal_ofReal (hdpos ω).le]
        change (z ω / ζ) • Y ω = ζ⁻¹ • (z ω • Y ω)
        rw [div_eq_inv_mul, mul_smul]
      rw [heq, integral_smul, hfair, smul_zero]
    exact ⟨Q, ⟨hQprob, hQP, hPQ⟩, hYintQ, hQfair⟩

/-- **General backward direction** (finite-dim market, integrability dropped). For a
measurable `Y`, no arbitrage gives an EMM. Pass to the equivalent probability measure
`P_tilde = P.withDensity (w/κ)`, `w = (1+‖Y‖)⁻¹`, under which `Y` is integrable; no arbitrage is
an a.e. notion preserved by `P_tilde ~ P`, so the integrable backward direction applies, and
`Q ~ P_tilde ~ P` by transitivity. -/
theorem exists_isEMM_of_noArbitrage (hY : Measurable Y) (hNA : NoArbitrage P Y) :
    ∃ Q, IsEMM P Y Q := by
  set w : Ω → ℝ := fun ω ↦ (1 + ‖Y ω‖)⁻¹ with hwdef
  have hw_meas : Measurable w := (measurable_const.add hY.norm).inv
  have hden_pos : ∀ ω, (0 : ℝ) < 1 + ‖Y ω‖ := fun ω ↦ by positivity
  have hw_pos : ∀ ω, 0 < w ω := fun ω ↦ by simp only [hwdef]; exact inv_pos.mpr (hden_pos ω)
  have hw_le_one : ∀ ω, w ω ≤ 1 := fun ω ↦ by
    simp only [hwdef]; exact inv_le_one_of_one_le₀ (by linarith [norm_nonneg (Y ω)])
  have hw_int : Integrable w P :=
    ⟨hw_meas.aestronglyMeasurable, HasFiniteIntegral.of_bounded
      (Filter.Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_pos (hw_pos ω)]; exact hw_le_one ω)⟩
  set κ : ℝ := ∫ ω, w ω ∂P with hκdef
  have hκ_pos : 0 < κ := by
    rw [hκdef, integral_pos_iff_support_of_nonneg_ae
        (Filter.Eventually.of_forall fun ω ↦ (hw_pos ω).le) hw_int,
      show Function.support w = Set.univ from Set.eq_univ_of_forall fun ω ↦ (hw_pos ω).ne']
    rw [measure_univ]; exact one_pos
  set dens : Ω → ℝ := fun ω ↦ w ω / κ with hddef
  have hd_meas : Measurable dens := hw_meas.div_const κ
  have hd_pos : ∀ ω, 0 < dens ω := fun ω ↦ div_pos (hw_pos ω) hκ_pos
  have hd_int : Integrable dens P := hw_int.div_const κ
  have hd_sum : ∫ ω, dens ω ∂P = 1 := by
    simp only [hddef, div_eq_inv_mul]
    rw [integral_const_mul, ← hκdef, inv_mul_cancel₀ hκ_pos.ne']
  set Pt : Measure Ω := P.withDensity (fun ω ↦ ENNReal.ofReal (dens ω)) with hPtdef
  have hd_ofReal_meas : Measurable (fun ω ↦ ENNReal.ofReal (dens ω)) :=
    ENNReal.measurable_ofReal.comp hd_meas
  obtain ⟨hPt_prob, hPt_ll_P, hP_ll_Pt⟩ :=
    isEquivProbMeasure_withDensity P hd_pos hd_int hd_sum
  rw [← hPtdef] at hPt_prob hPt_ll_P hP_ll_Pt
  have := hPt_prob
  have hdY_int : Integrable (fun ω ↦ dens ω • Y ω) P := by
    refine ⟨(hd_meas.aestronglyMeasurable.smul hY.aestronglyMeasurable),
      HasFiniteIntegral.of_bounded (C := κ⁻¹) (Filter.Eventually.of_forall fun ω ↦ ?_)⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hd_pos ω)]
    have h1 : w ω * ‖Y ω‖ ≤ 1 := by
      simp only [hwdef, inv_mul_eq_div, div_le_one (hden_pos ω)]
      linarith [norm_nonneg (Y ω)]
    simp only [hddef, div_mul_eq_mul_div]
    rw [div_le_iff₀ hκ_pos, inv_mul_cancel₀ hκ_pos.ne']; exact h1
  have hYintPt : Integrable Y Pt := by
    rw [hPtdef, integrable_withDensity_iff_integrable_smul' hd_ofReal_meas
      (Filter.Eventually.of_forall fun ω ↦ ENNReal.ofReal_lt_top)]
    refine hdY_int.congr (Filter.Eventually.of_forall fun ω ↦ ?_)
    change dens ω • Y ω = (ENNReal.ofReal (dens ω)).toReal • Y ω
    rw [ENNReal.toReal_ofReal (hd_pos ω).le]
  have hNAt : NoArbitrage Pt Y := fun θ h ↦
    hPt_ll_P.ae_eq (hNA θ (hP_ll_Pt.ae_le h))
  obtain ⟨Q, hQ⟩ := exists_isEMM_of_noArbitrage_integrable Pt Y hY hYintPt hNAt
  exact ⟨Q, ⟨hQ.isProb, hQ.ac.trans hPt_ll_P, hP_ll_Pt.trans hQ.ac'⟩, hQ.int, hQ.fair⟩

/-- **One-period Fundamental Theorem of Asset Pricing**, finite-dimensional market, general
`Ω`. For a measurable `F`-valued discounted excess return `Y` (`F = EuclideanSpace ℝ (Fin
d)` is the `d`-asset case), no arbitrage holds iff there is an equivalent martingale
measure `Q ~ P` with `Y` integrable and `E_Q[Y] = 0`. The backward direction is
explicit: minimise the softplus potential over the gains kernel's orthogonal complement
(its logistic weight is the density), needing no Hahn–Banach, no L⁰-cone closedness,
no measurable selection, and **no non-redundancy hypothesis**. -/
theorem ftap_one_period_vector (hY : Measurable Y) :
    NoArbitrage P Y ↔ ∃ Q, IsEMM P Y Q :=
  ⟨fun hNA ↦ exists_isEMM_of_noArbitrage P Y hY hNA,
   fun ⟨_, hQ⟩ ↦ noArbitrage_of_isEMM P Y hY hQ⟩

end MathFin.OnePeriodVector

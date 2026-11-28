/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.DividendsGreeks
public import LeanPool.MathFin.Models.Jumps.JumpDiffusionMixing
public import LeanPool.MathFin.Models.Rates.VasicekZeroMeanReversionLimit

/-!
# The Ju–Zhong quadratic approximation at zero interest rate

The Ju–Zhong (1999) modified quadratic approximation prices an American option as
`V_E(S) + hA·(S/S*)^{q_QD}/(1 − χ)` with `χ = x(bx + c)`, `x = log(S/S*)`, where `S*` is the
Barone-Adesi–Whaley critical price. Its coefficients involve `α = 2r/σ²`, `h = 1 − e^{−rT}`,
`α/h`, `q_QD′(h)`, `1/h` and `∂V_E/∂h`. At `r = 0` the ratio `α/h` is `0/0` and the last three
are `O(1/r)`, but they only ever enter multiplied by `α = O(r)`. QuantLib's limit-stable rewrite
of `juquadraticengine.cpp` (the fix for a NaN at `r = 0`) computes `ρ = α/h`, extended by
`ρ(0) = 2/(σ²T)`, together with `α·q_QD′` and `α·∂V_E/∂h`, and adds a put early exit
(`DR ≥ 1 ∧ DR ≥ DQ` ⇒ European price). The formulas here are transcribed from that file and
from the source equations; `φ = 1` is a call, `φ = −1` a put.

## Main definitions

* `juAlpha`, `juBeta`, `juH`: `α = 2r/σ²`, `N = 2(r − q)/σ²` and `h = 1 − e^{−rT}`.
* `juRho`: `ρ = α/h`, extended at `r = 0` by its limit `2/(σ²T)`.
* `juRoot`, `juLambda`: `√((N − 1)² + 4ρ)` and `q_QD = (−(N − 1) + φ√((N − 1)² + 4ρ))/2`, with
  `φ = 1` for a call and `φ = −1` for a put.
* `juVE`: the European price `φ (S e^{−qT} Φ(φd₁) − K e^{−rT} Φ(φd₂))`; `juVE_one` and
  `juVE_neg_one` identify it with `bsVDiv` and `bsPDiv`.
* `juHA`: `hA = φ (S* − K) − V_E(S*)`.
* `juValueRaw`: the pre-fix Ju–Zhong price on the continuation region, with `α/h` computed
  directly; its coefficients are `juRootRaw`, `juLambdaRaw`, `juLambdaPrime`, `juVEhRaw`,
  `juBRaw`, `juCRaw`, `juChiRaw`.
* `juValue`: the post-fix, limit-stable price `V_E(S) + hA (S/S*)^{q_QD} / (1 − χ)`; its
  coefficients are `juAlphaLambdaPrime`, `juAlphaVEh`, `juB`, `juC`, `juChi`.

## Main results

* `tendsto_juAlpha_div_juH_zero_rate`, `continuousAt_juRho_zero` — the removable singularity
  `α/h → 2/(σ²T)` as `r → 0` (two-sided). `α/h = (2/σ²)/vasicekBondB r T`
  (`juAlpha_div_juH_eq`), and `vasicekBondB r T → T`
  (`tendsto_vasicekBondB_zero_meanReversion`).
* `juValueRaw_eq_juValue` — the fix preserves semantics: for every `r ≠ 0` the pre-fix price
  `juValueRaw` and the post-fix price `juValue` are equal, identically in `S*` and `S`.
* `tendsto_juValueRaw_zero_rate` — the headline, **conditional**: if `S*(r) → S*₀ > 0` as
  `r → 0⁺`, `hA(0, S*₀) ≠ 0` and `1 − χ(0, S*₀, S) ≠ 0`, the pre-fix price tends to the
  post-fix value at `r = 0`. The critical price and both nonvanishing conditions are
  hypotheses.
* `put_intrinsic_le_parityBound` — the pointwise half of the put exit: under `DR ≥ 1`,
  `DR ≥ DQ`, `0 < S ≤ K`, `K − S ≤ K·DR − S·DQ ≤ bsPDiv`.
* `bawPut_no_positive_root_zero_rate`, `bawPut_criticalPrice_eq_zero_zero_rate` — at `r = 0`
  with `q ≥ 0` the BAW put critical-price equation (as transcribed here) has no root `S > 0`:
  any `S* ≥ 0` solving it is `S* = 0`. This excludes a positive root of the `r = 0` equation;
  it does not assert that `S* = 0` solves it, and it does not show that the limit of the
  critical prices of the `r > 0` problems is such a root (that limit is not studied).
* `juVE_one`, `juVE_neg_one` — the European leg is `bsVDiv` / `bsPDiv`.

## Scoped out

* The BAW critical price as a function of `r`: existence, uniqueness and continuity of the
  Newton fixed point are not formalized; `S*` is an input.
* The put limit `r → 0⁺` when `q ≥ 0`: the behaviour of the critical prices `S*(r)` and of
  `hA` as `r → 0⁺`, and hence of the early-exercise premium, is not addressed.
* Any accuracy claim for the approximation, the derivation of its trial-solution ODE, and the
  identification of `juVEhRaw` with `∂V_E/∂h`: these are transcribed, not derived.
* The statement that American and European puts agree when `r ≤ 0` and `r ≤ q` (optional
  stopping).
* Floating point: QuantLib's `close(DR, 1, 1000)` switch is replaced by the exact branch
  `r = 0`, and nothing is stated about the raw formula *at* `r = 0`, where Lean's `x/0 = 0`
  makes it a junk value rather than NaN (so `juValueRaw_eq_juValue` compares two Lean
  transcriptions for `r ≠ 0`, not QuantLib's code).

## References

* [N. Ju and R. Zhong, *An approximate formula for pricing American options*][JuZhong1999].
* [G. Barone-Adesi and R. E. Whaley, *Efficient analytic approximation of American option
  values*][BaroneAdesiWhaley1987] (the critical-price equation).
* [M. Li, *Analytical approximations for the critical stock prices of American options: a
  performance comparison*][Li2009], §II.B, eqs. (27)–(34) with the notation of
  eqs. (1)–(13). This restatement is the one used for the formulas here.
* [QuantLib, `ql/pricingengines/vanilla/juquadraticengine.cpp`][QuantLibJuQuadratic].

## Tags

Ju–Zhong, quadratic approximation, American option approximation, Barone-Adesi–Whaley,
zero interest rate limit, MSC 91G20, MSC 35R35, JEL G13
-/

@[expose] public section

namespace MathFin

open Filter Topology ProbabilityTheory

/-! ### The closed-form scaffolding -/

/-- `M = 2r/σ²` (Li eq. (6); QuantLib's `alpha`). -/
noncomputable def juAlpha (σ r : ℝ) : ℝ := 2 * r / σ ^ 2

/-- `N = 2(r − q)/σ²` (Li eq. (6); QuantLib's `beta`). -/
noncomputable def juBeta (q σ r : ℝ) : ℝ := 2 * (r - q) / σ ^ 2

/-- `h = 1 − e^{−rT}` (QuantLib's `h = 1 − DR`). -/
noncomputable def juH (T r : ℝ) : ℝ := 1 - Real.exp (-(r * T))

/-- QuantLib's `alphaOverH`: `ρ = α/h`, extended at `r = 0` by its limit `2/(σ²T)`
(`tendsto_juAlpha_div_juH_zero_rate`). QuantLib switches branches when `DR` is within
1000 ulps of 1; that floating-point switch is not modelled, the branch here is `r = 0`. -/
noncomputable def juRho (σ T r : ℝ) : ℝ :=
  if r = 0 then 2 / (σ ^ 2 * T) else juAlpha σ r / juH T r

/-- `√((N − 1)² + 4ρ)`, the square root in `q_QD` (Li eq. (10); QuantLib's `temp_root`). -/
noncomputable def juRoot (q σ T r : ℝ) : ℝ :=
  Real.sqrt ((juBeta q σ r - 1) ^ 2 + 4 * juRho σ T r)

/-- `q_QD = (−(N − 1) + φ·√((N − 1)² + 4ρ))/2` (Li eq. (10); QuantLib's `lambda`);
`φ = 1` for a call, `−1` for a put. -/
noncomputable def juLambda (φ q σ T r : ℝ) : ℝ :=
  (-(juBeta q σ r - 1) + φ * juRoot q σ T r) / 2

/-- The pre-fix square root, with `α/h` computed directly (`0/0` at `r = 0`). -/
noncomputable def juRootRaw (q σ T r : ℝ) : ℝ :=
  Real.sqrt ((juBeta q σ r - 1) ^ 2 + 4 * (juAlpha σ r / juH T r))

/-- The pre-fix `q_QD`, built on `juRootRaw`. -/
noncomputable def juLambdaRaw (φ q σ T r : ℝ) : ℝ :=
  (-(juBeta q σ r - 1) + φ * juRootRaw q σ T r) / 2

/-- `q_QD′(h) = −φM/(h²√((N − 1)² + 4M/h))` (Li eq. (33); QuantLib's `lambda_prime`),
`O(1/r)` as `r → 0`. -/
noncomputable def juLambdaPrime (φ q σ T r : ℝ) : ℝ :=
  -(φ * juAlpha σ r) / (juH T r ^ 2 * juRootRaw q σ T r)

/-- The forward at the critical price, `F* = S*·DQ/DR` (QuantLib's `forwardSk`). -/
noncomputable def juFwd (q T r Sk : ℝ) : ℝ :=
  Sk * Real.exp (-(q * T)) / Real.exp (-(r * T))

/-- The European price `V_E(S) = φ·(S·DQ·Φ(φd₁) − K·DR·Φ(φd₂))`, `d₁ = bsd1 S K (r − q) σ T`
(QuantLib's `blackFormula(…)·DR`). `juVE_one` and `juVE_neg_one` identify it with `bsVDiv`
and `bsPDiv`. -/
noncomputable def juVE (φ K q σ T r S : ℝ) : ℝ :=
  φ * (S * Real.exp (-(q * T)) * Phi (φ * bsd1 S K (r - q) σ T)
    - K * Real.exp (-(r * T)) * Phi (φ * bsd2 S K (r - q) σ T))

/-- `hA = φ(S* − K) − V_E(S*)` (QuantLib's `hA`). -/
noncomputable def juHA (φ K q σ T r Sk : ℝ) : ℝ :=
  φ * (Sk - K) - juVE φ K q σ T r Sk

/-- The pre-fix `V_E_h = ∂V_E/∂h` at `S*` (QuantLib's `part1 + part2 + part3`), with
`part1 = F*·n(d₁)/(α√(σ²T))` and `part2 = −φF*Φ(φd₁)·log DQ/log DR`; both are `O(1/r)`. -/
noncomputable def juVEhRaw (φ K q σ T r Sk : ℝ) : ℝ :=
  juFwd q T r Sk * gaussianPDFReal 0 1 (bsd1 Sk K (r - q) σ T)
      / (juAlpha σ r * Real.sqrt (σ ^ 2 * T))
    - φ * juFwd q T r Sk * Phi (φ * bsd1 Sk K (r - q) σ T) * Real.log (Real.exp (-(q * T)))
      / Real.log (Real.exp (-(r * T)))
    + φ * K * Phi (φ * bsd2 Sk K (r - q) σ T)

/-- The pre-fix `b = (1 − h)·M·q_QD′/(2(2q_QD + N − 1))` (Li eq. (30)). -/
noncomputable def juBRaw (φ q σ T r : ℝ) : ℝ :=
  (1 - juH T r) * juAlpha σ r * juLambdaPrime φ q σ T r
    / (2 * (2 * juLambdaRaw φ q σ T r + juBeta q σ r - 1))

/-- The pre-fix `c = −(1 − h)M/(2q_QD + N − 1)·[V_E_h/hA + 1/h + q_QD′/(2q_QD + N − 1)]`
(Li eq. (32), `c₀`, with QuantLib's `V_E_h/hA` in place of Li's Θ-term). -/
noncomputable def juCRaw (φ K q σ T r Sk : ℝ) : ℝ :=
  -((1 - juH T r) * juAlpha σ r / (2 * juLambdaRaw φ q σ T r + juBeta q σ r - 1))
    * (juVEhRaw φ K q σ T r Sk / juHA φ K q σ T r Sk + 1 / juH T r
      + juLambdaPrime φ q σ T r / (2 * juLambdaRaw φ q σ T r + juBeta q σ r - 1))

/-- The pre-fix `χ = x(bx + c)`, `x = log(S/S*)`. -/
noncomputable def juChiRaw (φ K q σ T r Sk S : ℝ) : ℝ :=
  Real.log (S / Sk) * (juBRaw φ q σ T r * Real.log (S / Sk) + juCRaw φ K q σ T r Sk)

/-- The pre-fix Ju–Zhong price on the continuation region (Li eq. (29)):
`V_E(S) + hA·(S/S*)^{q_QD}/(1 − χ)`. -/
noncomputable def juValueRaw (φ K q σ T r Sk S : ℝ) : ℝ :=
  juVE φ K q σ T r S
    + juHA φ K q σ T r Sk * (S / Sk) ^ juLambdaRaw φ q σ T r / (1 - juChiRaw φ K q σ T r Sk S)

/-- The post-fix `α·λ′ = −φρ²/√((N − 1)² + 4ρ)`. -/
noncomputable def juAlphaLambdaPrime (φ q σ T r : ℝ) : ℝ :=
  -(φ * juRho σ T r ^ 2) / juRoot q σ T r

/-- The post-fix `α·V_E_h = F*n(d₁)/√(σ²T) + 2φF*Φ(φd₁)·log DQ/(σ²T) + φαKΦ(φd₂)`. -/
noncomputable def juAlphaVEh (φ K q σ T r Sk : ℝ) : ℝ :=
  juFwd q T r Sk * gaussianPDFReal 0 1 (bsd1 Sk K (r - q) σ T) / Real.sqrt (σ ^ 2 * T)
    + 2 * φ * juFwd q T r Sk * Phi (φ * bsd1 Sk K (r - q) σ T) * Real.log (Real.exp (-(q * T)))
      / (σ ^ 2 * T)
    + φ * juAlpha σ r * K * Phi (φ * bsd2 Sk K (r - q) σ T)

/-- The post-fix `b = (1 − h)·(αλ′)/(2(2λ + N − 1))`. -/
noncomputable def juB (φ q σ T r : ℝ) : ℝ :=
  (1 - juH T r) * juAlphaLambdaPrime φ q σ T r
    / (2 * (2 * juLambda φ q σ T r + juBeta q σ r - 1))

/-- The post-fix `c = −(1 − h)/(2λ + N − 1)·[αV_E_h/hA + ρ + αλ′/(2λ + N − 1)]`. -/
noncomputable def juC (φ K q σ T r Sk : ℝ) : ℝ :=
  -((1 - juH T r) / (2 * juLambda φ q σ T r + juBeta q σ r - 1))
    * (juAlphaVEh φ K q σ T r Sk / juHA φ K q σ T r Sk + juRho σ T r
      + juAlphaLambdaPrime φ q σ T r / (2 * juLambda φ q σ T r + juBeta q σ r - 1))

/-- The post-fix `χ = x(bx + c)`, `x = log(S/S*)`. -/
noncomputable def juChi (φ K q σ T r Sk S : ℝ) : ℝ :=
  Real.log (S / Sk) * (juB φ q σ T r * Real.log (S / Sk) + juC φ K q σ T r Sk)

/-- The post-fix Ju–Zhong price on the continuation region. -/
noncomputable def juValue (φ K q σ T r Sk S : ℝ) : ℝ :=
  juVE φ K q σ T r S
    + juHA φ K q σ T r Sk * (S / Sk) ^ juLambda φ q σ T r / (1 - juChi φ K q σ T r Sk S)

/-! ### The removable singularity `α/h → 2/(σ²T)` -/

/-- `α/h = (2/σ²)/B(r, T)`, the Vasicek bond coefficient at speed `r`. -/
lemma juAlpha_div_juH_eq (σ T r : ℝ) (hr : r ≠ 0) :
    juAlpha σ r / juH T r = 2 / σ ^ 2 / vasicekBondB r T := by
  rw [juAlpha, juH, vasicekBondB]
  field_simp

/-- **The removable singularity** (QuantLib's `alphaOverH` limit): `α/h → 2/(σ²T)` as
`r → 0`, from either side. -/
theorem tendsto_juAlpha_div_juH_zero_rate {σ T : ℝ} (hT : T ≠ 0) :
    Tendsto (fun r ↦ juAlpha σ r / juH T r) (𝓝[≠] 0) (𝓝 (2 / (σ ^ 2 * T))) := by
  have := (tendsto_const_nhds (x := 2 / σ ^ 2)).div
    (tendsto_vasicekBondB_zero_meanReversion T) hT
  rw [div_div] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (juAlpha_div_juH_eq σ T r hr).symm

/-- `ρ` is continuous at `r = 0`: the extension `ρ(0) = 2/(σ²T)` is the limit. -/
theorem continuousAt_juRho_zero {σ T : ℝ} (hT : T ≠ 0) : ContinuousAt (juRho σ T) 0 := by
  rw [← continuousWithinAt_compl_self, ContinuousWithinAt, juRho, ite_eq_left rfl]
  refine (tendsto_juAlpha_div_juH_zero_rate hT).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : r ≠ 0)
  rw [juRho, ite_eq_right hr]

/-! ### The fix preserves semantics: raw = stable for `r ≠ 0` -/

lemma juRootRaw_eq (q σ T : ℝ) {r : ℝ} (hr : r ≠ 0) : juRootRaw q σ T r = juRoot q σ T r := by
  rw [juRootRaw, juRoot, juRho, ite_eq_right hr]

lemma juLambdaRaw_eq (φ q σ T : ℝ) {r : ℝ} (hr : r ≠ 0) :
    juLambdaRaw φ q σ T r = juLambda φ q σ T r := by
  rw [juLambdaRaw, juLambda, juRootRaw_eq q σ T hr]

/-- `α·λ′ = −φρ²/√((N − 1)² + 4ρ)`: the `O(1/r)` factor `λ′` times `α = O(r)`. -/
lemma juAlpha_mul_juLambdaPrime (φ q σ T : ℝ) {r : ℝ} (hr : r ≠ 0) :
    juAlpha σ r * juLambdaPrime φ q σ T r = juAlphaLambdaPrime φ q σ T r := by
  rw [juLambdaPrime, juAlphaLambdaPrime, juRootRaw_eq q σ T hr, juRho, ite_eq_right hr]
  ring

/-- `α·V_E_h` in the stable form: `α·part1` cancels the `1/α`, and `α/log DR = −2/(σ²T)`. -/
lemma juAlpha_mul_juVEhRaw (φ K q : ℝ) {σ T r : ℝ} (hσ : σ ≠ 0) (hT : T ≠ 0) (hr : r ≠ 0)
    (Sk : ℝ) : juAlpha σ r * juVEhRaw φ K q σ T r Sk = juAlphaVEh φ K q σ T r Sk := by
  rw [juVEhRaw, juAlphaVEh, Real.log_exp (-(r * T)), juAlpha]
  field_simp
  ring

lemma juBRaw_eq (φ q σ T : ℝ) {r : ℝ} (hr : r ≠ 0) : juBRaw φ q σ T r = juB φ q σ T r := by
  rw [juBRaw, juB, juLambdaRaw_eq φ q σ T hr, ← juAlpha_mul_juLambdaPrime φ q σ T hr]
  ring

lemma juCRaw_eq (φ K q : ℝ) {σ T r : ℝ} (hσ : σ ≠ 0) (hT : T ≠ 0) (hr : r ≠ 0) (Sk : ℝ) :
    juCRaw φ K q σ T r Sk = juC φ K q σ T r Sk := by
  rw [juCRaw, juC, juLambdaRaw_eq φ q σ T hr, ← juAlpha_mul_juLambdaPrime φ q σ T hr,
    ← juAlpha_mul_juVEhRaw φ K q hσ hT hr, juRho, ite_eq_right hr]
  ring

/-- **The fix preserves semantics.** For every `σ ≠ 0`, `T ≠ 0` and `r ≠ 0` the post-fix
(limit-stable) Ju–Zhong price equals the pre-fix one, identically in `S*` and `S`. Pure
algebra: `α·(X/hA) = (αX)/hA` holds in Lean even when `hA = 0`, so no hypothesis on `hA` or
`1 − χ` is needed. This is an identity between the two Lean transcriptions `juValueRaw` and
`juValue`; it is not tied to an American option price or to QuantLib's code. -/
theorem juValueRaw_eq_juValue (φ K q : ℝ) {σ T r : ℝ} (hσ : σ ≠ 0) (hT : T ≠ 0) (hr : r ≠ 0)
    (Sk S : ℝ) : juValueRaw φ K q σ T r Sk S = juValue φ K q σ T r Sk S := by
  rw [juValueRaw, juValue, juChiRaw, juChi, juBRaw_eq φ q σ T hr, juCRaw_eq φ K q hσ hT hr,
    juLambdaRaw_eq φ q σ T hr]

/-! ### Continuity of the stable form at `r = 0`, and the headline limit -/

/-- `2q_QD + N − 1 = φ·√((N − 1)² + 4ρ)`: the denominator of `b` and `c` vanishes only with the
root. -/
lemma two_mul_juLambda_add_juBeta_sub_one (φ q σ T r : ℝ) :
    2 * juLambda φ q σ T r + juBeta q σ r - 1 = φ * juRoot q σ T r := by
  rw [juLambda]; ring

lemma juRoot_zero_pos (q : ℝ) {σ T : ℝ} (hσ : 0 < σ) (hT : 0 < T) : 0 < juRoot q σ T 0 := by
  rw [juRoot, juRho, ite_eq_left rfl]
  exact Real.sqrt_pos.2 (by positivity)

/-- **Headline: the pre-fix price tends to the post-fix price at `r = 0`** — conditionally.
Let `S*(r)` be *any* critical-price function with `S*(r) → S*₀ > 0` as `r → 0⁺`. If the two
side conditions `hA(0, S*₀) ≠ 0` and `1 − χ(0, S*₀, S) ≠ 0` hold, the pre-fix Ju–Zhong price
`juValueRaw` along `(r, S*(r))` tends to the post-fix value `juValue` at `(0, S*₀)`.

The critical price is a black box: its existence, uniqueness and continuity in `r` (the BAW
Newton fixed point) are hypotheses here, not derived. The two nonvanishing conditions are
hypotheses as well. `bawPut_no_positive_root_zero_rate` excludes a positive root of the `r = 0`
put critical-price equation for `q ≥ 0`; whether the limit `S*₀` of the critical prices of the
`r > 0` problems is such a root is not proved here. -/
theorem tendsto_juValueRaw_zero_rate {φ K q σ T S S₀ : ℝ} {Sk : ℝ → ℝ}
    (hφ : φ = 1 ∨ φ = -1) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) (hS : 0 < S)
    (hSk : Tendsto Sk (𝓝[>] 0) (𝓝 S₀)) (hS₀ : 0 < S₀)
    (hA₀ : juHA φ K q σ T 0 S₀ ≠ 0) (hχ₀ : 1 - juChi φ K q σ T 0 S₀ S ≠ 0) :
    Tendsto (fun r ↦ juValueRaw φ K q σ T r (Sk r) S) (𝓝[>] 0)
      (𝓝 (juValue φ K q σ T 0 S₀ S)) := by
  set L : Filter ℝ := 𝓝[>] 0
  have hφ0 : φ ≠ 0 := by rcases hφ with h | h <;> simp [h]
  refine Tendsto.congr' ?_ (show Tendsto (fun r ↦ juValue φ K q σ T r (Sk r) S) L _ from ?_)
  · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    exact (juValueRaw_eq_juValue φ K q hσ.ne' hT.ne' hr.ne' _ _).symm
  have hr : Tendsto (fun r : ℝ ↦ r) L (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hcont : ∀ f : ℝ → ℝ, ContinuousAt f 0 → Tendsto f L (𝓝 (f 0)) :=
    fun f hf ↦ hf.tendsto.mono_left nhdsWithin_le_nhds
  have hα := hcont (juAlpha σ) (by unfold juAlpha; fun_prop)
  have hβ := hcont (juBeta q σ) (by unfold juBeta; fun_prop)
  have hh := hcont (juH T) (by unfold juH; fun_prop)
  have hρ := hcont (juRho σ T) (continuousAt_juRho_zero hT.ne')
  have hroot0 := juRoot_zero_pos q hσ hT
  have hroot : Tendsto (fun r ↦ juRoot q σ T r) L (𝓝 (juRoot q σ T 0)) := by
    simp only [juRoot]; exact (((hβ.sub_const 1).pow 2).add (hρ.const_mul 4)).sqrt
  have hlam : Tendsto (fun r ↦ juLambda φ q σ T r) L (𝓝 (juLambda φ q σ T 0)) := by
    simp only [juLambda]; exact ((hβ.sub_const 1).neg.add (hroot.const_mul φ)).div_const 2
  have hD0 : 2 * juLambda φ q σ T 0 + juBeta q σ 0 - 1 ≠ 0 := by
    rw [two_mul_juLambda_add_juBeta_sub_one]; exact mul_ne_zero hφ0 hroot0.ne'
  have hD := ((hlam.const_mul 2).add hβ).sub_const 1
  have hd1 : ∀ {s : ℝ → ℝ} {s₀ : ℝ}, Tendsto s L (𝓝 s₀) → 0 < s₀ →
      Tendsto (fun r ↦ bsd1 (s r) K (r - q) σ T) L (𝓝 (bsd1 s₀ K (0 - q) σ T)) := by
    intro s s₀ hs hs₀
    simp only [bsd1]
    exact (((hs.div_const K).log (by positivity)).add
      (((hr.sub_const q).add_const _).mul_const T)).div_const _
  have hd2 : ∀ {s : ℝ → ℝ} {s₀ : ℝ}, Tendsto s L (𝓝 s₀) → 0 < s₀ →
      Tendsto (fun r ↦ bsd2 (s r) K (r - q) σ T) L (𝓝 (bsd2 s₀ K (0 - q) σ T)) :=
    fun hs hs₀ ↦ (hd1 hs hs₀).sub_const _
  have hΦ : ∀ {f : ℝ → ℝ} {x : ℝ}, Tendsto f L (𝓝 x) →
      Tendsto (fun r ↦ Phi (φ * f r)) L (𝓝 (Phi (φ * x))) :=
    fun hf ↦ (continuous_Phi.tendsto _).comp (hf.const_mul φ)
  have hDR := (hr.mul_const T).neg.rexp
  have hVE : ∀ {s : ℝ → ℝ} {s₀ : ℝ}, Tendsto s L (𝓝 s₀) → 0 < s₀ →
      Tendsto (fun r ↦ juVE φ K q σ T r (s r)) L (𝓝 (juVE φ K q σ T 0 s₀)) := by
    intro s s₀ hs hs₀
    simp only [juVE]
    exact (((hs.mul_const _).mul (hΦ (hd1 hs hs₀))).sub
      ((tendsto_const_nhds.mul hDR).mul (hΦ (hd2 hs hs₀)))).const_mul φ
  have hHA : Tendsto (fun r ↦ juHA φ K q σ T r (Sk r)) L (𝓝 (juHA φ K q σ T 0 S₀)) := by
    simp only [juHA]; exact ((hSk.sub_const K).const_mul φ).sub (hVE hSk hS₀)
  have hF : Tendsto (fun r ↦ juFwd q T r (Sk r)) L (𝓝 (juFwd q T 0 S₀)) := by
    simp only [juFwd]; exact (hSk.mul_const _).div hDR (Real.exp_pos _).ne'
  have hαVEh : Tendsto (fun r ↦ juAlphaVEh φ K q σ T r (Sk r)) L
      (𝓝 (juAlphaVEh φ K q σ T 0 S₀)) := by
    simp only [juAlphaVEh]
    exact (((hF.mul (((continuous_gaussianPDFReal 0 1).tendsto _).comp
      (hd1 hSk hS₀))).div_const _).add
      ((((hF.const_mul (2 * φ)).mul (hΦ (hd1 hSk hS₀))).mul_const _).div_const _)).add
      (((hα.const_mul φ).mul_const K).mul (hΦ (hd2 hSk hS₀)))
  have hαlp : Tendsto (fun r ↦ juAlphaLambdaPrime φ q σ T r) L
      (𝓝 (juAlphaLambdaPrime φ q σ T 0)) := by
    simp only [juAlphaLambdaPrime]; exact ((hρ.pow 2).const_mul φ).neg.div hroot hroot0.ne'
  have hB : Tendsto (fun r ↦ juB φ q σ T r) L (𝓝 (juB φ q σ T 0)) := by
    simp only [juB]
    exact ((tendsto_const_nhds.sub hh).mul hαlp).div (hD.const_mul 2)
      (mul_ne_zero two_ne_zero hD0)
  have hC : Tendsto (fun r ↦ juC φ K q σ T r (Sk r)) L (𝓝 (juC φ K q σ T 0 S₀)) := by
    simp only [juC]
    exact ((tendsto_const_nhds.sub hh).div hD hD0).neg.mul
      (((hαVEh.div hHA hA₀).add hρ).add (hαlp.div hD hD0))
  have hratio : Tendsto (fun r ↦ S / Sk r) L (𝓝 (S / S₀)) :=
    tendsto_const_nhds.div hSk hS₀.ne'
  have hx := hratio.log (by positivity)
  have hχ : Tendsto (fun r ↦ juChi φ K q σ T r (Sk r) S) L (𝓝 (juChi φ K q σ T 0 S₀ S)) := by
    simp only [juChi]; exact hx.mul ((hB.mul hx).add hC)
  simp only [juValue]
  exact (hVE tendsto_const_nhds hS).add ((hHA.mul (hratio.rpow hlam (Or.inl (by positivity)))).div
    (tendsto_const_nhds.sub hχ) hχ₀)

/-! ### `V_E` is the Black–Scholes–Merton price -/

/-- The call (`φ = 1`) European price is `bsVDiv`. -/
lemma juVE_one (K q σ T r S : ℝ) : juVE 1 K q σ T r S = bsVDiv K r q σ S T := by
  have hd : Real.exp (-(q * T)) * Real.exp (-((r - q) * T)) = Real.exp (-(r * T)) := by
    rw [← Real.exp_add]; ring_nf
  rw [juVE, bsVDiv, bsV, ← hd]
  ring_nf

/-- The put (`φ = −1`) European price is `bsPDiv`. -/
lemma juVE_neg_one (K q σ T r S : ℝ) : juVE (-1) K q σ T r S = bsPDiv K r q σ S T := by
  have hd : Real.exp (-(q * T)) * Real.exp (-((r - q) * T)) = Real.exp (-(r * T)) := by
    rw [← Real.exp_add]; ring_nf
  rw [juVE, bsPDiv, bsP, ← hd]
  simp only [neg_one_mul]
  ring

/-! ### The put side at `r = 0` -/

/-- **The pointwise half of the put "no early exercise" exit.** If `DR = e^{−rT} ≥ 1` and
`DR ≥ DQ = e^{−qT}`, then for `0 < S ≤ K` the intrinsic value is below the parity bound
`K·DR − S·DQ`, which is below the European put `bsPDiv`. This is the inequality behind
QuantLib's comment in `juquadraticengine.cpp` that holding is worth at least `K·DR − S·DQ`;
the optional-stopping half (American = European) is not formalized. -/
theorem put_intrinsic_le_parityBound {K r q σ S T : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T)
    (hS : 0 < S) (hSK : S ≤ K) (hDR : 1 ≤ Real.exp (-(r * T)))
    (hDRQ : Real.exp (-(q * T)) ≤ Real.exp (-(r * T))) :
    K - S ≤ K * Real.exp (-(r * T)) - S * Real.exp (-(q * T)) ∧
      K * Real.exp (-(r * T)) - S * Real.exp (-(q * T)) ≤ bsPDiv K r q σ S T := by
  refine ⟨?_, ?_⟩
  · rcases le_or_gt (Real.exp (-(q * T))) 1 with h | h <;> nlinarith
  · have := mul_nonneg (Real.exp_pos (-(q * T))).le (bsV_nonneg_of_pos hS hK hσ hT (r := r - q))
    rw [bsPDiv_eq_bsVDiv, bsVDiv]
    linarith

/-- At `r = 0` the put's `q_QD` (`φ = −1`) is negative, whatever `q`. -/
lemma juLambda_neg_one_zero_neg (q : ℝ) {σ T : ℝ} (hσ : 0 < σ) (hT : 0 < T) :
    juLambda (-1) q σ T 0 < 0 := by
  have h4 : 0 < 4 * juRho σ T 0 := by rw [juRho, ite_eq_left rfl]; positivity
  have : -(juBeta q σ 0 - 1) < juRoot q σ T 0 := by
    calc -(juBeta q σ 0 - 1) ≤ |juBeta q σ 0 - 1| := neg_le_abs _
      _ = Real.sqrt ((juBeta q σ 0 - 1) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ < juRoot q σ T 0 := Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  rw [juLambda]
  linarith

/-- **At `r = 0` with `q ≥ 0`, the BAW put critical-price equation has no positive root.**
The equation (Li eq. (9), with `q_QD` at its `r = 0` value `juLambda (-1) q σ T 0`) is
`K − S − p(S) = −S(1 − e^{−qT}Φ(−d₁(S)))/q_QD`. Its left side is `≤ 0` (parity at `r = 0` and
a nonnegative call give `p(S) ≥ K − S·e^{−qT} ≥ K − S`); its right side is `> 0`
(`q_QD < 0` and `1 − e^{−qT}Φ(−d₁) ≥ Φ(d₁) > 0`). This excludes a positive root; it does not
establish that `S = 0` itself solves the equation or that `hA = 0` there. -/
theorem bawPut_no_positive_root_zero_rate {K q σ T S : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    (hT : 0 < T) (hq : 0 ≤ q) (hS : 0 < S) :
    K - S - bsPDiv K 0 q σ S T ≠
      -S * (1 - Real.exp (-(q * T)) * Phi (-bsd1 S K (0 - q) σ T)) / juLambda (-1) q σ T 0 := by
  have hDQ : Real.exp (-(q * T)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hlhs : K - S - bsPDiv K 0 q σ S T ≤ 0 := by
    have := mul_nonneg (Real.exp_pos (-(q * T))).le
      (bsV_nonneg_of_pos hS hK hσ hT (r := 0 - q))
    rw [bsPDiv_eq_bsVDiv, bsVDiv]
    simp only [zero_mul, neg_zero, Real.exp_zero, mul_one]
    nlinarith
  have hΦ : 0 < Phi (bsd1 S K (0 - q) σ T) := by positivity
  have hnum : 0 < 1 - Real.exp (-(q * T)) * Phi (-bsd1 S K (0 - q) σ T) := by
    have h0 := Phi_nonneg (-bsd1 S K (0 - q) σ T)
    rw [Phi_neg] at h0 ⊢
    nlinarith
  have hrhs : 0 < -S * (1 - Real.exp (-(q * T)) * Phi (-bsd1 S K (0 - q) σ T)) /
      juLambda (-1) q σ T 0 :=
    div_pos_of_neg_of_neg (by nlinarith) (juLambda_neg_one_zero_neg q hσ hT)
  intro h
  linarith

/-- **Corollary: a positive put critical price at `r = 0`, `q ≥ 0` is excluded.** Any `S* ≥ 0`
solving the BAW put equation is `S* = 0` — this excludes a positive root, not asserts that
`S* = 0` itself solves the equation. Whether the limit of the critical prices of the `r > 0`
problems is such a root is not proved, so this does not by itself refute the hypothesis
`0 < S*₀` of `tendsto_juValueRaw_zero_rate` for such puts. -/
theorem bawPut_criticalPrice_eq_zero_zero_rate {K q σ T Sstar : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    (hT : 0 < T) (hq : 0 ≤ q) (hSstar : 0 ≤ Sstar)
    (heq : K - Sstar - bsPDiv K 0 q σ Sstar T =
      -Sstar * (1 - Real.exp (-(q * T)) * Phi (-bsd1 Sstar K (0 - q) σ T)) /
        juLambda (-1) q σ T 0) :
    Sstar = 0 :=
  hSstar.eq_or_lt.elim Eq.symm fun h ↦
    absurd heq (bawPut_no_positive_root_zero_rate hK hσ hT hq h)

end MathFin

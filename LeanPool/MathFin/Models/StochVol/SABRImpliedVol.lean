/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.ImpliedVolatility
public import LeanPool.MathFin.Models.Forwards.Black76

/-!
# The SABR lognormal implied-volatility asymptotic approximation

Hagan, Kumar, Lesniewski & Woodward, "Managing Smile Risk," *Wilmott Magazine*,
September 2002, pp. 84-108. Under the SABR stochastic-volatility model
`dF̂ = α̂F̂^β dW₁`, `dα̂ = να̂ dW₂`, `dW₁ dW₂ = ρ dt` (their eqs. 2.15a-c), singular
perturbation gives the price of European options via Black's formula with an
*explicit, closed-form asymptotic approximation* for the implied volatility
`σ_B(K, f)` as a function of today's forward `f` and strike `K` (eqs. 2.17a-c):

`σ_B(K,f) = α / [(fK)^((1-β)/2) · (1 + (1-β)²/24 · log²(f/K) + (1-β)⁴/1920 · log⁴(f/K) + ⋯)]
  · (z / x(z)) · (1 + [(1-β)²/24 · α²/(fK)^(1-β)
    + ρβνα/4/(fK)^((1-β)/2) + (2-3ρ²)/24 · ν²] t_ex + ⋯)`

where `z = (ν/α)(fK)^((1-β)/2) log(f/K)` and
`x(z) = log((√(1-2ρz+z²) + z - ρ)/(1-ρ))` (eqs. 2.17b-c).

**This is a closed-form asymptotic approximation, not an exact price** — the
paper derives it via a singular-perturbation (small vol-of-vol, short-maturity)
expansion and explicitly omits higher-order `⋯` terms (stated to be "much,
much smaller" than the displayed terms, but nonzero). Neither that derivation nor
any error bound against the true SABR implied volatility is formalized here: the
two-factor SDE's transition density and its short-time (heat-kernel /
geodesic-distance) asymptotics do not exist in this repo or in
Mathlib/BrownianMotion. The rigorous form of the expansion (an error bound against the
SABR model's implied volatility) is not formalized. What is proved concerns the *printed*
formulas
(eq. 2.17a-c with the `⋯` dropped, and eq. 2.18):

* At `K = f` the general formula is `0/0` in its `z / x(z)` factor (`z = 0`,
  `x(0) = 0`), and the paper says it "reduces to" eq. 2.18. We prove this as a
  limit: `sabrImpliedVol K f ⋯ → sabrATMVol f ⋯` as `K → f`, `K ≠ f`. The
  removable singularity is resolved by `x'(0) = 1` (`hasDerivAt_sabrX_zero`), so
  `z / x(z) → 1`.
* The *backbone law* (section 3): along the leading-order ATM curve
  `f ↦ α / f^(1-β)`, `d log σ / d log f = β - 1`, stated as the derivative of
  `v ↦ log (sabrBackbone (e^v))` in `v = log f`.

## Main definitions

* `sabrZ`, `sabrX` — Hagan's `z` and `x(z)` (eqs. 2.17b, 2.17c).
* `sabrImpliedVol` — the general implied vol `σ_B(K, f)` (eq. 2.17a, `⋯` dropped).
* `sabrATMVol` — the at-the-money implied vol (eq. 2.18).
* `sabrBackbone` — the leading-order ATM vol `α / f^(1-β)` ("the backbone" in the
  paper's section 3 terminology).

## Main results

* `tendsto_sabrImpliedVol_atm` — eq. 2.17a tends to eq. 2.18 as `K → f`
  (for `f > 0`, `α ≠ 0`, `ν ≠ 0`, `ρ ≠ 1`, any `β`, `t_ex`).
* `hasDerivAt_log_sabrBackbone` — `d/df log (α / f^(1-β)) = (β - 1) / f` (`f, α > 0`).
* `hasDerivAt_log_sabrBackbone_exp` — the backbone law in log-log form:
  `d/dv log (α / (e^v)^(1-β)) = β - 1` (`α > 0`).
* `sabrBackbone_pos` — the backbone is positive for `α, f > 0`.
* `sabrATMVol_bsV_gt_backbone_bsV` — whenever eq. 2.18's bracketed correction,
  scaled by `t_ex`, is positive, the ATM Black call (the statement's zero-rate,
  spot = strike = `f` instantiation, `0 < T`) priced at `sabrATMVol` is
  strictly above the same call priced at the backbone (via
  `bsV_strictMonoOn_sigma`, `Models/BlackScholes/ImpliedVolatility.lean`).
* `sabrATMVol_black_futures_price` — the ATM option priced, as the paper prescribes, by
  Black's formula at `σ_ATM = sabrATMVol`: under the Black-76 hypothesis at that vol,
  the discounted expected call payoff is `e^{−rT} · f · (2Φ(σ_ATM √T / 2) − 1)`. This
  is Black's formula evaluated at eq. 2.18's vol; it does not show that the SABR model
  itself produces this price.

## References

* [F. Black, *The pricing of commodity contracts*][Black1976]
* [Hagan et al., *Managing smile risk*][HaganKumarLesniewskiWoodward2002], eq. 2.18; eqs. 2.17a-c
  and 2.18; section 3 and eq. 2.18

## Tags

SABR model, Hagan formula, implied volatility asymptotics, managing smile risk, backbone,
stochastic volatility, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open Filter MeasureTheory Topology

/-- **The SABR "backbone"**: the leading-order at-the-money implied volatility
`α / f^(1-β)` (the dominant factor in Hagan-Kumar-Lesniewski-Woodward eq. 2.18;
called the *backbone* in their section 3, the curve traced by ATM vol as the
forward `f` varies). -/
noncomputable def sabrBackbone (f α β : ℝ) : ℝ := α / f ^ (1 - β)

/-- **The SABR at-the-money implied volatility** (Hagan-Kumar-Lesniewski-Woodward,
*Managing Smile Risk*, Wilmott Magazine 2002, eq. 2.18):

`σ_ATM = α/f^(1-β) · {1 + [(1-β)²/24 · α²/f^(2-2β) + ρβαν/4/f^(1-β) + (2-3ρ²)/24 · ν²] t_ex + ⋯}`

the `K = f` specialization of the general formula (eq. 2.17a), where the
`z/x(z)` factor's removable singularity at `z = 0` is already resolved. This is
the asymptotic truncation as printed in the paper (the omitted `⋯` terms are
higher order in the perturbation expansion, stated by the authors to be much
smaller than the displayed correction). -/
noncomputable def sabrATMVol (f α β ρ ν tex : ℝ) : ℝ :=
  sabrBackbone f α β *
    (1 + ((1 - β) ^ 2 / 24 * (α ^ 2 / f ^ (2 - 2 * β))
        + ρ * β * α * ν / 4 / f ^ (1 - β)
        + (2 - 3 * ρ ^ 2) / 24 * ν ^ 2) * tex)

/-- **The backbone is positive** for `α, f > 0`: `α / f^(1-β) > 0`. -/
theorem sabrBackbone_pos {f α : ℝ} (β : ℝ) (hf : 0 < f) (hα : 0 < α) :
    0 < sabrBackbone f α β :=
  div_pos hα (Real.rpow_pos_of_pos hf _)

/-- **A positive perturbation correction raises the ATM price**: whenever eq.
2.18's bracketed stochastic-vol correction `(1-β)²/24·α²/f^(2-2β) + ρβαν/4/f^(1-β)
+ (2-3ρ²)/24·ν²`, scaled by `t_ex`, is positive, the full ATM vol `sabrATMVol`
strictly exceeds the bare backbone `sabrBackbone` — and, by `bsV_strictMonoOn_sigma`
(`Models/BlackScholes/ImpliedVolatility.lean`, the strict monotonicity of the Black call
price in its vol input), the ATM Black call priced at `sabrATMVol` is strictly more
expensive than the same option priced at the backbone alone. The call compared is the
statement's `bsV f 0 σ f T` instantiation: spot and strike both the forward `f`, rate
`r = 0`, maturity `T` with `0 < T` (`hT`) — the same zero-rate, spot = strike = `f`
call `sabrATMVol_black_futures_price` below spells out in full. The positivity of
the correction is a hypothesis (`hbracket`), not proved; the conclusion is the strict
monotonicity of the Black call in its vol, applied to `backbone < backbone · (1 + c)`. -/
theorem sabrATMVol_bsV_gt_backbone_bsV {f α β ρ ν tex T : ℝ} (hf : 0 < f) (hα : 0 < α)
    (hT : 0 < T)
    (hbracket : 0 < ((1 - β) ^ 2 / 24 * (α ^ 2 / f ^ (2 - 2 * β))
        + ρ * β * α * ν / 4 / f ^ (1 - β) + (2 - 3 * ρ ^ 2) / 24 * ν ^ 2) * tex) :
    bsV f 0 (sabrBackbone f α β) f T < bsV f 0 (sabrATMVol f α β ρ ν tex) f T := by
  have hpos := sabrBackbone_pos β hf hα
  have hlt : sabrBackbone f α β < sabrATMVol f α β ρ ν tex := by
    unfold sabrATMVol
    nlinarith [mul_pos hpos hbracket]
  exact bsV_strictMonoOn_sigma hf hT hf hpos (hpos.trans hlt) hlt

/-- **The ATM price as Black-76 at `sabrATMVol`**: Hagan et al. price European options by
Black's formula with the implied vol `σ_B`; at the money that vol is eq. 2.18. The vol's own
`t_ex` argument is the option's time to expiry, so it is instantiated at the same `T` the
Black-76 price is computed for (not left as an independent free variable — eq. 2.18's ATM vol
is specifically the vol *for an option expiring at `t_ex`*, priced at that same expiry). Under
the Black-76 hypothesis at `σ_ATM = sabrATMVol f α β ρ ν T` (forward `f`, strike `f`, zero
drift), the discounted expected call payoff is `e^{−rT} · f · (2Φ(σ_ATM √T / 2) − 1)`
(`black_futures_formula_atm`). This is Black's formula at eq. 2.18's vol, not a
statement that the SABR dynamics produce this price. -/
theorem sabrATMVol_black_futures_price {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q] {f α β ρ ν T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q f f 0 (sabrATMVol f α β ρ ν T) T Z) (r : ℝ) :
    ∫ ω, Real.exp (-r * T) * max (bsTerminal f 0 (sabrATMVol f α β ρ ν T) T (Z ω) - f) 0 ∂Q
      = Real.exp (-r * T) * f * (2 * Phi (sabrATMVol f α β ρ ν T * Real.sqrt T / 2) - 1) :=
  black_futures_formula_atm h r

/-! ### The general formula (eq. 2.17) and its `K → f` limit -/

/-- **Hagan's `x(z)`** (Hagan-Kumar-Lesniewski-Woodward eq. 2.17c):
`x(z) = log((√(1 - 2ρz + z²) + z - ρ) / (1 - ρ))`. -/
noncomputable def sabrX (ρ z : ℝ) : ℝ :=
  Real.log ((Real.sqrt (1 - 2 * ρ * z + z ^ 2) + z - ρ) / (1 - ρ))

/-- **Hagan's `z`** (eq. 2.17b): `z = (ν/α) (fK)^((1-β)/2) log(f/K)`. -/
noncomputable def sabrZ (K f α β ν : ℝ) : ℝ :=
  ν / α * (f * K) ^ ((1 - β) / 2) * Real.log (f / K)

/-- **The SABR implied volatility `σ_B(K, f)`** (Hagan-Kumar-Lesniewski-Woodward eq. 2.17a),
the printed asymptotic formula with its `⋯` terms dropped:

`α / [(fK)^((1-β)/2) (1 + (1-β)²/24 log²(f/K) + (1-β)⁴/1920 log⁴(f/K))] · (z / x(z))
  · (1 + [(1-β)²/24 · α²/(fK)^(1-β) + ρβαν/4/(fK)^((1-β)/2) + (2-3ρ²)/24 · ν²] t_ex)`.

At `K = f` the factor `z / x(z)` is `0 / 0` (Lean's `0 / 0 = 0` makes the literal value
`0` there); `tendsto_sabrImpliedVol_atm` shows the formula tends to `sabrATMVol` as
`K → f`. -/
noncomputable def sabrImpliedVol (K f α β ρ ν tex : ℝ) : ℝ :=
  α / ((f * K) ^ ((1 - β) / 2) *
      (1 + (1 - β) ^ 2 / 24 * Real.log (f / K) ^ 2
        + (1 - β) ^ 4 / 1920 * Real.log (f / K) ^ 4)) *
    (sabrZ K f α β ν / sabrX ρ (sabrZ K f α β ν)) *
    (1 + ((1 - β) ^ 2 / 24 * (α ^ 2 / (f * K) ^ (1 - β))
        + ρ * β * α * ν / 4 / (f * K) ^ ((1 - β) / 2)
        + (2 - 3 * ρ ^ 2) / 24 * ν ^ 2) * tex)

/-- **`x(z)` has slope `1` at `z = 0`** (`ρ ≠ 1`). With `x(0) = 0`, this is what makes
`z = 0` a removable singularity of `z / x(z)`. -/
theorem hasDerivAt_sabrX_zero {ρ : ℝ} (hρ : ρ ≠ 1) : HasDerivAt (sabrX ρ) 1 0 := by
  have h1ρ : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  have hq : HasDerivAt (fun z : ℝ ↦ 1 - 2 * ρ * z + z ^ 2) (-(2 * ρ)) 0 :=
    ((((hasDerivAt_id' (0 : ℝ)).const_mul (2 * ρ)).const_sub 1).add
      (hasDerivAt_pow 2 (0 : ℝ))).congr_deriv (by norm_num)
  have hs := hq.sqrt (by norm_num)
  have hg := ((hs.add (hasDerivAt_id' (0 : ℝ))).sub_const ρ).div_const (1 - ρ)
  have hl := hg.log (by norm_num [h1ρ])
  unfold sabrX
  convert hl using 1
  simp only [Pi.add_apply]
  norm_num
  field_simp
  ring

/-- **`z / x(z) → 1` as `z → 0`, `z ≠ 0`** (`ρ ≠ 1`): the removable singularity of
eq. 2.17a's `z / x(z)` factor, from `x(0) = 0` and `x'(0) = 1`. -/
theorem tendsto_div_sabrX {ρ : ℝ} (hρ : ρ ≠ 1) :
    Tendsto (fun z ↦ z / sabrX ρ z) (𝓝[≠] 0) (𝓝 1) := by
  have h := (hasDerivAt_iff_tendsto_slope_zero.mp (hasDerivAt_sabrX_zero hρ)).inv₀ one_ne_zero
  have h0 : sabrX ρ 0 = 0 := by
    have h1ρ : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
    simp [sabrX, h1ρ]
  simpa [h0, div_eq_mul_inv, mul_comm] using h

/-- **`z → 0` through nonzero values as `K → f`, `K ≠ f`** (`f > 0`, `α ≠ 0`, `ν ≠ 0`):
`z(K)` is continuous at `K = f` with `z(f) = 0`, and `z(K) ≠ 0` for `K > 0`, `K ≠ f`,
since `log(f/K) ≠ 0` there. -/
theorem tendsto_sabrZ {f α β ν : ℝ} (hf : 0 < f) (hα : α ≠ 0) (hν : ν ≠ 0) :
    Tendsto (fun K ↦ sabrZ K f α β ν) (𝓝[≠] f) (𝓝[≠] 0) := by
  have hcont : ContinuousAt (fun K ↦ sabrZ K f α β ν) f := by
    unfold sabrZ
    have hff : f * f ≠ 0 := (mul_pos hf hf).ne'
    have hf0 : f ≠ 0 := hf.ne'
    have hdiv : f / f ≠ 0 := div_ne_zero hf0 hf0
    have hr : f * f ≠ 0 ∨ 0 ≤ (1 - β) / 2 := Or.inl hff
    fun_prop (disch := assumption)
  have hval : sabrZ f f α β ν = 0 := by simp [sabrZ, hf.ne']
  rw [tendsto_nhdsWithin_iff]
  refine ⟨hval ▸ hcont.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
  have hpos : ∀ᶠ K in 𝓝[≠] f, 0 < K := nhdsWithin_le_nhds (Ioi_mem_nhds hf)
  filter_upwards [hpos, self_mem_nhdsWithin] with K hK hKf
  have hfK : f / K ≠ 1 := fun h ↦ hKf ((div_eq_one_iff_eq hK.ne').mp h).symm
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, sabrZ]
  exact mul_ne_zero (mul_ne_zero (div_ne_zero hν hα) (Real.rpow_pos_of_pos (mul_pos hf hK) _).ne')
    (Real.log_ne_zero_of_pos_of_ne_one (div_pos hf hK) hfK)

/-- The factors of eq. 2.17a other than `z / x(z)` are continuous in `K` at `K = f`
(`f > 0`). -/
theorem sabrImpliedVol_rest_continuousAt {f α β ρ ν tex : ℝ} (hf : 0 < f) :
    ContinuousAt (fun K ↦ α / ((f * K) ^ ((1 - β) / 2) *
      (1 + (1 - β) ^ 2 / 24 * Real.log (f / K) ^ 2
        + (1 - β) ^ 4 / 1920 * Real.log (f / K) ^ 4)) *
    (1 + ((1 - β) ^ 2 / 24 * (α ^ 2 / (f * K) ^ (1 - β))
        + ρ * β * α * ν / 4 / (f * K) ^ ((1 - β) / 2)
        + (2 - 3 * ρ ^ 2) / 24 * ν ^ 2) * tex)) f := by
  have hff : f * f ≠ 0 := (mul_pos hf hf).ne'
  have hf0 : f ≠ 0 := hf.ne'
  have hdiv : f / f ≠ 0 := div_ne_zero hf0 hf0
  have hr : f * f ≠ 0 ∨ 0 ≤ (1 - β) / 2 := Or.inl hff
  have hr' : f * f ≠ 0 ∨ 0 ≤ 1 - β := Or.inl hff
  have h1 : (f * f) ^ ((1 - β) / 2) ≠ 0 := (Real.rpow_pos_of_pos (mul_pos hf hf) _).ne'
  have h2 : (f * f) ^ (1 - β) ≠ 0 := (Real.rpow_pos_of_pos (mul_pos hf hf) _).ne'
  have h3 : (f * f) ^ ((1 - β) / 2) * (1 + (1 - β) ^ 2 / 24 * Real.log (f / f) ^ 2
        + (1 - β) ^ 4 / 1920 * Real.log (f / f) ^ 4) ≠ 0 := by simpa [hf.ne'] using h1
  fun_prop (disch := assumption)

/-- **The general SABR formula tends to the ATM formula as `K → f`**
(Hagan-Kumar-Lesniewski-Woodward: eq. 2.17a "reduces to" eq. 2.18 at `K = f`): for
`f > 0`, `α ≠ 0`, `ν ≠ 0`, `ρ ≠ 1` and every `β`, `t_ex`, `σ_B(K, f) → σ_ATM(f)` as
`K → f` with `K ≠ f`. At `K = f` itself the printed formula is `0 / 0` in its `z / x(z)`
factor, so the limit, not evaluation, is the content. This concerns the two printed
truncations only; it says nothing about how well either approximates the true SABR
implied volatility. -/
theorem tendsto_sabrImpliedVol_atm {f α β ρ ν tex : ℝ} (hf : 0 < f) (hα : α ≠ 0) (hν : ν ≠ 0)
    (hρ : ρ ≠ 1) :
    Tendsto (fun K ↦ sabrImpliedVol K f α β ρ ν tex) (𝓝[≠] f)
      (𝓝 (sabrATMVol f α β ρ ν tex)) := by
  have hR := (sabrImpliedVol_rest_continuousAt (α := α) (β := β) (ρ := ρ) (ν := ν) (tex := tex)
    hf).tendsto.mono_left (nhdsWithin_le_nhds (s := {f}ᶜ))
  have hZX := (tendsto_div_sabrX hρ).comp (tendsto_sabrZ (β := β) hf hα hν)
  have hhalf : (f * f) ^ ((1 - β) / 2) = f ^ (1 - β) := by
    rw [Real.mul_rpow hf.le hf.le, ← Real.rpow_add hf]; ring_nf
  have hfull : (f * f) ^ (1 - β) = f ^ (2 - 2 * β) := by
    rw [Real.mul_rpow hf.le hf.le, ← Real.rpow_add hf]; ring_nf
  convert hR.mul hZX using 1
  · funext K
    simp only [sabrImpliedVol, Function.comp_apply]
    ring
  · simp only [sabrATMVol, sabrBackbone, hhalf, hfull, div_self hf.ne', Real.log_one]
    congr 1
    ring

/-! ### The backbone law -/

/-- Along the leading-order ATM curve `σ(f) = α / f^(1-β)`, `d log σ / df = (β - 1) / f`,
for `f > 0`, `α > 0`. The log-log form is `hasDerivAt_log_sabrBackbone_exp`. -/
theorem hasDerivAt_log_sabrBackbone {f α : ℝ} (β : ℝ) (hf : 0 < f) (hα : 0 < α) :
    HasDerivAt (fun x ↦ Real.log (sabrBackbone x α β)) ((β - 1) / f) f := by
  have hev : (fun x ↦ Real.log α - (1 - β) * Real.log x) =ᶠ[𝓝 f]
      fun x ↦ Real.log (sabrBackbone x α β) := by
    filter_upwards [Ioi_mem_nhds hf] with x hx
    rw [sabrBackbone, Real.log_div hα.ne' (Real.rpow_pos_of_pos hx _).ne', Real.log_rpow hx]
  have hd := ((Real.hasDerivAt_log hf.ne').const_mul (1 - β)).const_sub (Real.log α)
  refine (hd.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  field_simp
  ring

/-- **The SABR backbone law** (Hagan-Kumar-Lesniewski-Woodward section 3): along the
leading-order ATM curve `σ(f) = α / f^(1-β)`, `d log σ / d log f = β - 1`, i.e. the map
`v ↦ log σ(e^v)` has derivative `β - 1` at every `v` (`β = 1`: flat; `β = 0`: `σ ∝ 1/f`).
Holds for `α > 0`. -/
theorem hasDerivAt_log_sabrBackbone_exp (β : ℝ) {α : ℝ} (hα : 0 < α) (v : ℝ) :
    HasDerivAt (fun w ↦ Real.log (sabrBackbone (Real.exp w) α β)) (β - 1) v := by
  have h := (hasDerivAt_log_sabrBackbone β (Real.exp_pos v) hα).comp v (Real.hasDerivAt_exp v)
  rw [div_mul_cancel₀ _ (Real.exp_pos v).ne'] at h
  exact h

end MathFin

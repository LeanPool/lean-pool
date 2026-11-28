/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Gaussian.NormalTail
public import LeanPool.MathFin.Models.BlackScholes.Call
public import Mathlib.Algebra.Ring.IsFormallyReal

/-! # Endpoint limits of the QD+ fixed-point integrands

The fixed-point scheme of Andersen, Lake and Offengenden (QD+) for the American put exercise
boundary integrates, at a collocation node `τ` with trial boundary value `b`, explicit
integrands built from an interpolated boundary `B`. Here `B` is an arbitrary real function: the
integrands below are not tied to the American put's exercise boundary, and nothing in this file
connects them to it. With
`d₊(t, z) = bsd1 z 1 (r - q) σ t` and `d₋(t, z) = bsd2 z 1 (r - q) σ t`, they are

* equation A, after the substitution `m = τ (1 + y)² / 4`, `y ∈ [-1, 1]`:
  `K₁₂(y) = e^{q(τ-m)} (½ τ (1 + y) Φ(d₊(m, b/B(τ-m))) + (√τ/σ) φ(d₊(m, b/B(τ-m))))` and
  `K₃(y) = (√τ/σ) e^{r(τ-m)} φ(d₋(m, b/B(τ-m)))`;
* equation B, on `u ∈ [0, τ]`:
  `nᵢ(u) = e^{r u} Φ(d₋(τ-u, b/B(u)))` and `dᵢ(u) = e^{q u} Φ(d₊(τ-u, b/B(u)))`.

These are transcribed from QuantLib's `qdfpamericanengine.cpp`. At the endpoint `y = -1`
(respectively `u = τ`) the time argument vanishes, so `d±` is a `0/0` form when `b = B τ`.
A Gauss–Lobatto rule samples this endpoint, so it needs the one-sided limit. This file
computes it over an abstract boundary `B`, with no fixed-point or pricing content.

## Main definitions

* `qdfpK12`: fixed-point equation A, the `K₁ + K₂` integrand after the substitution
  `m = τ (1 + y)² / 4`, built from an arbitrary real function `B`.
* `qdfpK3`: fixed-point equation A, the `K₃` integrand after the same substitution.
* `qdfpNi`, `qdfpDi`: fixed-point equation B, the numerator and denominator integrands.

## Main results

* `b = B τ`, `B` differentiable at `τ` with `0 < B τ`: `K₁₂ → e^{qτ} (√τ/σ)/√(2π)`,
  `K₃ → e^{rτ} (√τ/σ)/√(2π)`, `nᵢ → ½ e^{rτ}`, `dᵢ → ½ e^{qτ}`
  (`tendsto_qdfpK12_endpoint` and siblings).
* `b ≠ B τ`, `B` only continuous at `τ`: `K₁₂, K₃ → 0`, and `nᵢ, dᵢ` tend to `e^{rτ}`,
  `e^{qτ}` when `B τ < b` and to `0` when `b < B τ` (`tendsto_qdfpK12_endpoint_ne` and
  siblings). The endpoint value is therefore discontinuous in `b` at `b = B τ`.
* Differentiability is sufficient for the limit above, but continuity alone is not: for the
  continuous boundary `B s = b e^{-c √(τ-s)}`, which has `B τ = b` and
  `log (b / B(τ - m)) = c √m`, `K₁₂ → e^{qτ} (√τ/σ) φ(c/σ)`, which differs from the value
  above when `c ≠ 0` (`tendsto_qdfpK12_endpoint_holder`, `not_tendsto_qdfpK12_endpoint_holder`).
  This counterexample is nondifferentiable at `τ`, so it shows continuity alone does not pin
  down the differentiable-case limit; it does not show differentiability is necessary for
  convergence as such.

## References

* [J. Healy, *Pricing American options under negative rates*][Healy2021], §5.1
  (restates the fixed-point equations and the substitution `y = -1 + 2 √((τ - u)/τ)`).
* [Andersen, Lake and Offengenden, *High-performance American option
  pricing*][AndersenLakeOffengenden2016]

## Tags

QD+ method, American put, exercise boundary, fixed-point integral equation, Gauss–Lobatto,
negative rates, MSC 91G60, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open Filter Set ProbabilityTheory
open scoped Topology Real

/-- Fixed-point equation A, the `K₁ + K₂` integrand after the substitution
`m = τ (1 + y)² / 4`. -/
noncomputable def qdfpK12 (B : ℝ → ℝ) (r q σ τ b y : ℝ) : ℝ :=
  Real.exp (q * (τ - τ * (1 + y) ^ 2 / 4)) *
    (τ * (1 + y) / 2 * Phi (bsd1 (b / B (τ - τ * (1 + y) ^ 2 / 4)) 1 (r - q) σ
        (τ * (1 + y) ^ 2 / 4)) +
      Real.sqrt τ / σ * gaussianPDFReal 0 1 (bsd1 (b / B (τ - τ * (1 + y) ^ 2 / 4)) 1
        (r - q) σ (τ * (1 + y) ^ 2 / 4)))

/-- Fixed-point equation A, the `K₃` integrand after the substitution `m = τ (1 + y)² / 4`. -/
noncomputable def qdfpK3 (B : ℝ → ℝ) (r q σ τ b y : ℝ) : ℝ :=
  Real.sqrt τ / σ * Real.exp (r * (τ - τ * (1 + y) ^ 2 / 4)) *
    gaussianPDFReal 0 1 (bsd2 (b / B (τ - τ * (1 + y) ^ 2 / 4)) 1 (r - q) σ
      (τ * (1 + y) ^ 2 / 4))

/-- Fixed-point equation B, the numerator integrand. -/
noncomputable def qdfpNi (B : ℝ → ℝ) (r q σ τ b u : ℝ) : ℝ :=
  Real.exp (r * u) * Phi (bsd2 (b / B u) 1 (r - q) σ (τ - u))

/-- Fixed-point equation B, the denominator integrand. -/
noncomputable def qdfpDi (B : ℝ → ℝ) (r q σ τ b u : ℝ) : ℝ :=
  Real.exp (q * u) * Phi (bsd1 (b / B u) 1 (r - q) σ (τ - u))

/-! ### The standard normal density at the origin and at infinity -/

theorem gaussianPDFReal_zero_one_zero : gaussianPDFReal 0 1 0 = 1 / Real.sqrt (2 * π) := by
  simp [gaussianPDFReal]

theorem tendsto_gaussianPDFReal_zero_one_atTop :
    Tendsto (gaussianPDFReal 0 1) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ ↦ -(x - 0) ^ 2 / (2 * ((1 : NNReal) : ℝ))) atTop atBot := by
    have : Tendsto (fun x : ℝ ↦ x ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
    simpa [neg_div] using (tendsto_neg_atTop_atBot.comp this).atBot_div_const two_pos
  have := (Real.tendsto_exp_atBot.comp h).const_mul (Real.sqrt (2 * π * ((1 : NNReal) : ℝ)))⁻¹
  rw [mul_zero] at this
  exact this

theorem tendsto_gaussianPDFReal_zero_one_atBot :
    Tendsto (gaussianPDFReal 0 1) atBot (𝓝 0) := by
  have := tendsto_gaussianPDFReal_zero_one_atTop.comp tendsto_neg_atBot_atTop
  simpa [Function.comp_def, gaussianPDFReal_zero_one_neg] using this

theorem gaussianPDFReal_zero_one_ne_zero_point {x : ℝ} (hx : x ≠ 0) :
    gaussianPDFReal 0 1 x ≠ gaussianPDFReal 0 1 0 := by
  intro h
  simp only [gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one,
    zero_pow two_ne_zero, neg_zero, zero_div, Real.exp_zero] at h
  have h2 : Real.exp (-x ^ 2 / 2) = 1 := by
    have hc : (Real.sqrt (2 * π))⁻¹ ≠ 0 := by positivity
    exact mul_left_cancel₀ hc (h.trans (mul_one _).symm)
  have : -x ^ 2 / 2 = 0 := by simpa using h2
  exact hx (by nlinarith [sq_nonneg x])

/-! ### The `d±` arguments near the endpoint -/

/-- The time change `m = τ (1 + y)² / 4` maps `y → -1⁺` to `m → 0⁺`. -/
theorem tendsto_qdfpTimeChange {τ : ℝ} (hτ : 0 < τ) :
    Tendsto (fun y : ℝ ↦ τ * (1 + y) ^ 2 / 4) (𝓝[>] (-1)) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have : Tendsto (fun y : ℝ ↦ τ * (1 + y) ^ 2 / 4) (𝓝 (-1)) (𝓝 (τ * (1 + -1) ^ 2 / 4)) :=
      (by fun_prop : Continuous fun y : ℝ ↦ τ * (1 + y) ^ 2 / 4).tendsto _
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y (hy : -1 < y)
    have : 0 < 1 + y := by linarith
    exact (by positivity : 0 < τ * (1 + y) ^ 2 / 4)

/-- `u ↦ τ - u` maps `u → τ⁻` to `m → 0⁺`. -/
theorem tendsto_sub_nhdsLT_nhdsGT_zero (τ : ℝ) :
    Tendsto (fun u : ℝ ↦ τ - u) (𝓝[<] τ) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have : Tendsto (fun u : ℝ ↦ τ - u) (𝓝 τ) (𝓝 (τ - τ)) :=
      (by fun_prop : Continuous fun u : ℝ ↦ τ - u).tendsto _
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with u (hu : u < τ)
    exact sub_pos.mpr hu

theorem tendsto_sqrt_nhdsGT_zero : Tendsto Real.sqrt (𝓝[>] 0) (𝓝 0) := by
  simpa using (Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds

/-- On the diagonal `b = B τ`, with `B` differentiable at `τ` and `0 < B τ`,
`d₊(m, B τ / B(τ - m)) → 0` as `m → 0⁺`. -/
theorem tendsto_bsd1_boundaryRatio_of_eq {B : ℝ → ℝ} {a σ τ : ℝ}
    (hB : DifferentiableAt ℝ B τ) (hBpos : 0 < B τ) (hσ : 0 < σ) :
    Tendsto (fun m ↦ bsd1 (B τ / B (τ - m)) 1 a σ m) (𝓝[>] 0) (𝓝 0) := by
  set g : ℝ → ℝ := fun s ↦ Real.log (B s)
  have hg : HasDerivAt g (deriv B τ / B τ) τ := hB.hasDerivAt.log hBpos.ne'
  -- the left difference quotient of `log ∘ B` at `τ`
  have hneg : Tendsto (fun m : ℝ ↦ -m) (𝓝[>] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using ((continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with m (hm : 0 < m)
      exact neg_ne_zero.mpr hm.ne'
  have hslope := hg.tendsto_slope_zero.comp hneg
  -- `B (τ - m)` is eventually positive
  have hBτ : Tendsto (fun m ↦ B (τ - m)) (𝓝[>] 0) (𝓝 (B τ)) := by
    have : Tendsto (fun m : ℝ ↦ τ - m) (𝓝[>] 0) (𝓝 τ) := by
      simpa using ((by fun_prop : Continuous fun m : ℝ ↦ τ - m).tendsto 0).mono_left
        nhdsWithin_le_nhds
    exact hB.continuousAt.tendsto.comp this
  have hpos : ∀ᶠ m in 𝓝[>] (0 : ℝ), 0 < B (τ - m) := hBτ.eventually (lt_mem_nhds hBpos)
  have hlim : Tendsto (fun m : ℝ ↦
      ((-m)⁻¹ • (g (τ + -m) - g τ)) * (Real.sqrt m / σ) + (a + σ ^ 2 / 2) * (Real.sqrt m / σ))
      (𝓝[>] 0) (𝓝 ((deriv B τ / B τ) * (0 / σ) + (a + σ ^ 2 / 2) * (0 / σ))) :=
    (hslope.mul (tendsto_sqrt_nhdsGT_zero.div_const σ)).add
      ((tendsto_sqrt_nhdsGT_zero.div_const σ).const_mul _)
  simp only [zero_div, mul_zero, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hpos] with m (hm : 0 < m) hBm
  simp only [g, bsd1, div_one, smul_eq_mul, ← sub_eq_add_neg]
  rw [Real.log_div hBpos.ne' hBm.ne']
  obtain ⟨s, hs0, rfl⟩ : ∃ s, 0 < s ∧ m = s ^ 2 :=
    ⟨Real.sqrt m, Real.sqrt_pos.mpr hm, (Real.sq_sqrt hm.le).symm⟩
  rw [Real.sqrt_sq hs0.le]
  field_simp
  ring

/-- The same as `tendsto_bsd1_boundaryRatio_of_eq` for `d₋ = d₊ - σ √m`. -/
theorem tendsto_bsd2_boundaryRatio_of_eq {B : ℝ → ℝ} {a σ τ : ℝ}
    (hB : DifferentiableAt ℝ B τ) (hBpos : 0 < B τ) (hσ : 0 < σ) :
    Tendsto (fun m ↦ bsd2 (B τ / B (τ - m)) 1 a σ m) (𝓝[>] 0) (𝓝 0) := by
  simpa [bsd2] using
    (tendsto_bsd1_boundaryRatio_of_eq (a := a) hB hBpos hσ).sub
      (tendsto_sqrt_nhdsGT_zero.const_mul σ)

/-- Off the diagonal, with `B` continuous at `τ` and `0 < B τ`, `d₊(m, b / B(τ - m))`
tends to `+∞` when `B τ < b` and to `-∞` when `b < B τ`, as `m → 0⁺`. -/
theorem tendsto_bsd1_boundaryRatio_of_ne {B : ℝ → ℝ} {a σ τ b : ℝ}
    (hB : ContinuousAt B τ) (hBpos : 0 < B τ) (hb : 0 < b) (hσ : 0 < σ) :
    (B τ < b → Tendsto (fun m ↦ bsd1 (b / B (τ - m)) 1 a σ m) (𝓝[>] 0) atTop) ∧
      (b < B τ → Tendsto (fun m ↦ bsd1 (b / B (τ - m)) 1 a σ m) (𝓝[>] 0) atBot) := by
  have hBτ : Tendsto (fun m ↦ B (τ - m)) (𝓝[>] 0) (𝓝 (B τ)) := by
    have : Tendsto (fun m : ℝ ↦ τ - m) (𝓝[>] 0) (𝓝 τ) := by
      simpa using ((by fun_prop : Continuous fun m : ℝ ↦ τ - m).tendsto 0).mono_left
        nhdsWithin_le_nhds
    exact hB.tendsto.comp this
  have hnum : Tendsto (fun m ↦ Real.log (b / B (τ - m) / 1) + (a + σ ^ 2 / 2) * m) (𝓝[>] 0)
      (𝓝 (Real.log (b / B τ))) := by
    have hlog := ((Real.continuousAt_log (div_pos hb hBpos).ne').tendsto.comp
      ((tendsto_const_nhds (x := b)).div hBτ hBpos.ne'))
    have hm : Tendsto (fun m : ℝ ↦ m) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    simpa [Function.comp_def] using hlog.add (hm.const_mul (a + σ ^ 2 / 2))
  have hden : Tendsto (fun m ↦ (σ * Real.sqrt m)⁻¹) (𝓝[>] 0) atTop := by
    refine tendsto_inv_nhdsGT_zero.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_)
    · simpa using tendsto_sqrt_nhdsGT_zero.const_mul σ
    · filter_upwards [self_mem_nhdsWithin] with m (hm : 0 < m)
      exact mul_pos hσ (Real.sqrt_pos.mpr hm)
  constructor
  · intro hlt
    have hc : 0 < Real.log (b / B τ) := Real.log_pos ((one_lt_div hBpos).mpr hlt)
    simpa [bsd1, div_eq_mul_inv] using hnum.pos_mul_atTop hc hden
  · intro hlt
    have hc : Real.log (b / B τ) < 0 :=
      Real.log_neg (div_pos hb hBpos) ((div_lt_one hBpos).mpr hlt)
    simpa [bsd1, div_eq_mul_inv] using hnum.neg_mul_atTop hc hden

/-- The same as `tendsto_bsd1_boundaryRatio_of_ne` for `d₋ = d₊ - σ √m`. -/
theorem tendsto_bsd2_boundaryRatio_of_ne {B : ℝ → ℝ} {a σ τ b : ℝ}
    (hB : ContinuousAt B τ) (hBpos : 0 < B τ) (hb : 0 < b) (hσ : 0 < σ) :
    (B τ < b → Tendsto (fun m ↦ bsd2 (b / B (τ - m)) 1 a σ m) (𝓝[>] 0) atTop) ∧
      (b < B τ → Tendsto (fun m ↦ bsd2 (b / B (τ - m)) 1 a σ m) (𝓝[>] 0) atBot) := by
  obtain ⟨h1, h2⟩ := tendsto_bsd1_boundaryRatio_of_ne (a := a) hB hBpos hb hσ
  have hs : Tendsto (fun m ↦ -(σ * Real.sqrt m)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_sqrt_nhdsGT_zero.const_mul σ).neg
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [bsd2, sub_eq_add_neg] using (h1 h).atTop_add hs
  · simpa [bsd2, sub_eq_add_neg] using (h2 h).atBot_add hs

/-! ### Equation A at `y = -1` -/

theorem tendsto_qdfpTimeChange_nhds {τ : ℝ} (hτ : 0 < τ) :
    Tendsto (fun y : ℝ ↦ τ * (1 + y) ^ 2 / 4) (𝓝[>] (-1)) (𝓝 0) :=
  tendsto_nhds_of_tendsto_nhdsWithin (tendsto_qdfpTimeChange hτ)

theorem tendsto_qdfpHalfJacobian (τ : ℝ) :
    Tendsto (fun y : ℝ ↦ τ * (1 + y) / 2) (𝓝[>] (-1)) (𝓝 0) := by
  simpa using ((by fun_prop : Continuous fun y : ℝ ↦ τ * (1 + y) / 2).tendsto (-1)).mono_left
    nhdsWithin_le_nhds

theorem tendsto_exp_qdfpDiscount (c : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    Tendsto (fun y : ℝ ↦ Real.exp (c * (τ - τ * (1 + y) ^ 2 / 4))) (𝓝[>] (-1))
      (𝓝 (Real.exp (c * τ))) := by
  simpa [Function.comp_def] using (Real.continuous_exp.tendsto _).comp
    (((tendsto_qdfpTimeChange_nhds hτ).const_sub τ).const_mul c)

/-- **Equation A, `K₁₂` at `y = -1`, on the diagonal.** With `b = B τ` and `B` differentiable
at `τ`, the integrand tends to `e^{qτ} (√τ/σ)/√(2π)`. -/
theorem tendsto_qdfpK12_endpoint {B : ℝ → ℝ} {r q σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ)
    (hB : DifferentiableAt ℝ B τ) (hBpos : 0 < B τ) :
    Tendsto (qdfpK12 B r q σ τ (B τ)) (𝓝[>] (-1))
      (𝓝 (Real.exp (q * τ) * (Real.sqrt τ / σ) / Real.sqrt (2 * π))) := by
  have hd := (tendsto_bsd1_boundaryRatio_of_eq (a := r - q) hB hBpos hσ).comp
    (tendsto_qdfpTimeChange hτ)
  have := (tendsto_exp_qdfpDiscount q hτ).mul
    (((tendsto_qdfpHalfJacobian τ).mul ((continuous_Phi.tendsto 0).comp hd)).add
      (((continuous_gaussianPDFReal 0 1).tendsto 0).comp
        hd |>.const_mul (Real.sqrt τ / σ)))
  rw [gaussianPDFReal_zero_one_zero] at this
  convert this using 2 <;> first | rfl | ring

/-- **Equation A, `K₃` at `y = -1`, on the diagonal.** -/
theorem tendsto_qdfpK3_endpoint {B : ℝ → ℝ} {r q σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ)
    (hB : DifferentiableAt ℝ B τ) (hBpos : 0 < B τ) :
    Tendsto (qdfpK3 B r q σ τ (B τ)) (𝓝[>] (-1))
      (𝓝 (Real.exp (r * τ) * (Real.sqrt τ / σ) / Real.sqrt (2 * π))) := by
  have hd := (tendsto_bsd2_boundaryRatio_of_eq (a := r - q) hB hBpos hσ).comp
    (tendsto_qdfpTimeChange hτ)
  have := ((tendsto_exp_qdfpDiscount r hτ).const_mul (Real.sqrt τ / σ)).mul
    (((continuous_gaussianPDFReal 0 1).tendsto 0).comp hd)
  rw [gaussianPDFReal_zero_one_zero] at this
  convert this using 2 <;> first | rfl | ring

/-- **Equation A, `K₁₂` at `y = -1`, off the diagonal.** With `b ≠ B τ` and `B` only
continuous at `τ`, the integrand tends to `0`. -/
theorem tendsto_qdfpK12_endpoint_ne {B : ℝ → ℝ} {r q σ τ b : ℝ} (hσ : 0 < σ) (hτ : 0 < τ)
    (hB : ContinuousAt B τ) (hBpos : 0 < B τ) (hb : 0 < b) (hne : b ≠ B τ) :
    Tendsto (qdfpK12 B r q σ τ b) (𝓝[>] (-1)) (𝓝 0) := by
  obtain ⟨hup, hdown⟩ := tendsto_bsd1_boundaryRatio_of_ne (a := r - q) hB hBpos hb hσ
  have hpdf : Tendsto (fun y : ℝ ↦ gaussianPDFReal 0 1 (bsd1 (b / B (τ - τ * (1 + y) ^ 2 / 4))
      1 (r - q) σ (τ * (1 + y) ^ 2 / 4))) (𝓝[>] (-1)) (𝓝 0) := by
    rcases hne.lt_or_gt with h | h
    · exact tendsto_gaussianPDFReal_zero_one_atBot.comp ((hdown h).comp
        (tendsto_qdfpTimeChange hτ))
    · exact tendsto_gaussianPDFReal_zero_one_atTop.comp ((hup h).comp
        (tendsto_qdfpTimeChange hτ))
  have hPhi : Tendsto (fun y : ℝ ↦ τ * (1 + y) / 2 * Phi (bsd1 (b / B (τ - τ * (1 + y) ^ 2 / 4))
      1 (r - q) σ (τ * (1 + y) ^ 2 / 4))) (𝓝[>] (-1)) (𝓝 0) :=
    (tendsto_qdfpHalfJacobian τ).zero_mul_isBoundedUnder_le
      (isBoundedUnder_of ⟨1, fun y ↦ by
        simpa [abs_of_nonneg (Phi_nonneg _)] using Phi_le_one _⟩)
  have := (tendsto_exp_qdfpDiscount q hτ).mul (hPhi.add (hpdf.const_mul (Real.sqrt τ / σ)))
  rw [mul_zero, add_zero, mul_zero] at this
  exact this

/-- **Equation A, `K₃` at `y = -1`, off the diagonal.** -/
theorem tendsto_qdfpK3_endpoint_ne {B : ℝ → ℝ} {r q σ τ b : ℝ} (hσ : 0 < σ) (hτ : 0 < τ)
    (hB : ContinuousAt B τ) (hBpos : 0 < B τ) (hb : 0 < b) (hne : b ≠ B τ) :
    Tendsto (qdfpK3 B r q σ τ b) (𝓝[>] (-1)) (𝓝 0) := by
  obtain ⟨hup, hdown⟩ := tendsto_bsd2_boundaryRatio_of_ne (a := r - q) hB hBpos hb hσ
  have hpdf : Tendsto (fun y : ℝ ↦ gaussianPDFReal 0 1 (bsd2 (b / B (τ - τ * (1 + y) ^ 2 / 4))
      1 (r - q) σ (τ * (1 + y) ^ 2 / 4))) (𝓝[>] (-1)) (𝓝 0) := by
    rcases hne.lt_or_gt with h | h
    · exact tendsto_gaussianPDFReal_zero_one_atBot.comp ((hdown h).comp
        (tendsto_qdfpTimeChange hτ))
    · exact tendsto_gaussianPDFReal_zero_one_atTop.comp ((hup h).comp
        (tendsto_qdfpTimeChange hτ))
  have := ((tendsto_exp_qdfpDiscount r hτ).const_mul (Real.sqrt τ / σ)).mul hpdf
  rw [mul_zero] at this
  exact this

/-! ### Equation B at `u = τ` -/

theorem tendsto_exp_mul_nhdsLT (c τ : ℝ) :
    Tendsto (fun u : ℝ ↦ Real.exp (c * u)) (𝓝[<] τ) (𝓝 (Real.exp (c * τ))) :=
  ((by fun_prop : Continuous fun u : ℝ ↦ Real.exp (c * u)).tendsto τ).mono_left
    nhdsWithin_le_nhds

/-- **Equation B, `nᵢ` at `u = τ`, on the diagonal.** -/
theorem tendsto_qdfpNi_endpoint {B : ℝ → ℝ} {r q σ τ : ℝ} (hσ : 0 < σ)
    (hB : DifferentiableAt ℝ B τ) (hBpos : 0 < B τ) :
    Tendsto (qdfpNi B r q σ τ (B τ)) (𝓝[<] τ) (𝓝 (Real.exp (r * τ) / 2)) := by
  have hd : Tendsto (fun u ↦ bsd2 (B τ / B u) 1 (r - q) σ (τ - u)) (𝓝[<] τ) (𝓝 0) := by
    simpa [Function.comp_def, sub_sub_cancel] using
      (tendsto_bsd2_boundaryRatio_of_eq (a := r - q) hB hBpos hσ).comp
        (tendsto_sub_nhdsLT_nhdsGT_zero τ)
  have := (tendsto_exp_mul_nhdsLT r τ).mul ((continuous_Phi.tendsto 0).comp hd)
  rw [Phi_zero, ← div_eq_mul_one_div] at this
  exact this

/-- **Equation B, `dᵢ` at `u = τ`, on the diagonal.** -/
theorem tendsto_qdfpDi_endpoint {B : ℝ → ℝ} {r q σ τ : ℝ} (hσ : 0 < σ)
    (hB : DifferentiableAt ℝ B τ) (hBpos : 0 < B τ) :
    Tendsto (qdfpDi B r q σ τ (B τ)) (𝓝[<] τ) (𝓝 (Real.exp (q * τ) / 2)) := by
  have hd : Tendsto (fun u ↦ bsd1 (B τ / B u) 1 (r - q) σ (τ - u)) (𝓝[<] τ) (𝓝 0) := by
    simpa [Function.comp_def, sub_sub_cancel] using
      (tendsto_bsd1_boundaryRatio_of_eq (a := r - q) hB hBpos hσ).comp
        (tendsto_sub_nhdsLT_nhdsGT_zero τ)
  have := (tendsto_exp_mul_nhdsLT q τ).mul ((continuous_Phi.tendsto 0).comp hd)
  rw [Phi_zero, ← div_eq_mul_one_div] at this
  exact this

/-- **Equation B, `nᵢ` at `u = τ`, off the diagonal.** The limit is `e^{rτ}` above the
boundary and `0` below it. -/
theorem tendsto_qdfpNi_endpoint_ne {B : ℝ → ℝ} {r q σ τ b : ℝ} (hσ : 0 < σ)
    (hB : ContinuousAt B τ) (hBpos : 0 < B τ) (hb : 0 < b) (hne : b ≠ B τ) :
    Tendsto (qdfpNi B r q σ τ b) (𝓝[<] τ)
      (𝓝 (if B τ < b then Real.exp (r * τ) else 0)) := by
  obtain ⟨hup, hdown⟩ := tendsto_bsd2_boundaryRatio_of_ne (a := r - q) hB hBpos hb hσ
  have hcomp := tendsto_sub_nhdsLT_nhdsGT_zero τ
  split_ifs with h
  · have hd : Tendsto (fun u ↦ bsd2 (b / B u) 1 (r - q) σ (τ - u)) (𝓝[<] τ) atTop := by
      simpa [Function.comp_def, sub_sub_cancel] using (hup h).comp hcomp
    have := (tendsto_exp_mul_nhdsLT r τ).mul (tendsto_Phi_atTop.comp hd)
    rw [mul_one] at this
    exact this
  · have hd : Tendsto (fun u ↦ bsd2 (b / B u) 1 (r - q) σ (τ - u)) (𝓝[<] τ) atBot := by
      simpa [Function.comp_def, sub_sub_cancel] using
        (hdown (lt_of_le_of_ne (not_lt.mp h) hne)).comp hcomp
    have := (tendsto_exp_mul_nhdsLT r τ).mul (tendsto_Phi_atBot.comp hd)
    rw [mul_zero] at this
    exact this

/-- **Equation B, `dᵢ` at `u = τ`, off the diagonal.** -/
theorem tendsto_qdfpDi_endpoint_ne {B : ℝ → ℝ} {r q σ τ b : ℝ} (hσ : 0 < σ)
    (hB : ContinuousAt B τ) (hBpos : 0 < B τ) (hb : 0 < b) (hne : b ≠ B τ) :
    Tendsto (qdfpDi B r q σ τ b) (𝓝[<] τ)
      (𝓝 (if B τ < b then Real.exp (q * τ) else 0)) := by
  obtain ⟨hup, hdown⟩ := tendsto_bsd1_boundaryRatio_of_ne (a := r - q) hB hBpos hb hσ
  have hcomp := tendsto_sub_nhdsLT_nhdsGT_zero τ
  split_ifs with h
  · have hd : Tendsto (fun u ↦ bsd1 (b / B u) 1 (r - q) σ (τ - u)) (𝓝[<] τ) atTop := by
      simpa [Function.comp_def, sub_sub_cancel] using (hup h).comp hcomp
    have := (tendsto_exp_mul_nhdsLT q τ).mul (tendsto_Phi_atTop.comp hd)
    rw [mul_one] at this
    exact this
  · have hd : Tendsto (fun u ↦ bsd1 (b / B u) 1 (r - q) σ (τ - u)) (𝓝[<] τ) atBot := by
      simpa [Function.comp_def, sub_sub_cancel] using
        (hdown (lt_of_le_of_ne (not_lt.mp h) hne)).comp hcomp
    have := (tendsto_exp_mul_nhdsLT q τ).mul (tendsto_Phi_atBot.comp hd)
    rw [mul_zero] at this
    exact this

/-! ### Continuity alone does not pin down the differentiable-case limit -/

/-- The boundary `B s = b e^{-c √(τ - s)}` used in `tendsto_qdfpK12_endpoint_holder` is
continuous. -/
theorem continuous_qdfpHolderBoundary (b c τ : ℝ) :
    Continuous fun s : ℝ ↦ b * Real.exp (-(c * Real.sqrt (τ - s))) := by
  fun_prop

/-- For the ½-Hölder boundary `B s = b e^{-c √(τ - s)}` (so `B τ = b`), the `K₁₂` endpoint
limit is `e^{qτ} (√τ/σ) φ(c/σ)`. -/
theorem tendsto_qdfpK12_endpoint_holder {r q σ τ b c : ℝ} (hσ : 0 < σ) (hτ : 0 < τ)
    (hb : 0 < b) :
    Tendsto (qdfpK12 (fun s ↦ b * Real.exp (-(c * Real.sqrt (τ - s)))) r q σ τ b) (𝓝[>] (-1))
      (𝓝 (Real.exp (q * τ) * (Real.sqrt τ / σ) * gaussianPDFReal 0 1 (c / σ))) := by
  have hcore : Tendsto (fun m ↦ bsd1 (b / (b * Real.exp (-(c * Real.sqrt (τ - (τ - m))))))
      1 (r - q) σ m) (𝓝[>] 0) (𝓝 (c / σ)) := by
    have hlim : Tendsto (fun m ↦ c / σ + (r - q + σ ^ 2 / 2) * (Real.sqrt m / σ)) (𝓝[>] 0)
        (𝓝 (c / σ + (r - q + σ ^ 2 / 2) * (0 / σ))) :=
      tendsto_const_nhds.add ((tendsto_sqrt_nhdsGT_zero.div_const σ).const_mul _)
    rw [zero_div, mul_zero, add_zero] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with m (hm : 0 < m)
    obtain ⟨s, hs0, rfl⟩ : ∃ s, 0 < s ∧ m = s ^ 2 :=
      ⟨Real.sqrt m, Real.sqrt_pos.mpr hm, (Real.sq_sqrt hm.le).symm⟩
    rw [sub_sub_cancel, Real.sqrt_sq hs0.le, bsd1, div_one, div_mul_cancel_left₀ hb.ne',
      ← Real.exp_neg, neg_neg, Real.log_exp, Real.sqrt_sq hs0.le]
    field_simp
  have hd := hcore.comp (tendsto_qdfpTimeChange hτ)
  have := (tendsto_exp_qdfpDiscount q hτ).mul
    (((tendsto_qdfpHalfJacobian τ).mul ((continuous_Phi.tendsto _).comp hd)).add
      (((continuous_gaussianPDFReal 0 1).tendsto _).comp
        hd |>.const_mul (Real.sqrt τ / σ)))
  convert this using 2 <;> first | rfl | ring

/-- **The endpoint value needs more than continuity.** For the continuous, ½-Hölder boundary
`B s = b e^{-c √(τ - s)}` with `c ≠ 0`, the `K₁₂` integrand on the diagonal `b = B τ` does
not tend to the value `e^{qτ} (√τ/σ)/√(2π)` of `tendsto_qdfpK12_endpoint`. -/
theorem not_tendsto_qdfpK12_endpoint_holder {r q σ τ b c : ℝ} (hσ : 0 < σ) (hτ : 0 < τ)
    (hb : 0 < b) (hc : c ≠ 0) :
    ¬ Tendsto (qdfpK12 (fun s ↦ b * Real.exp (-(c * Real.sqrt (τ - s)))) r q σ τ b) (𝓝[>] (-1))
      (𝓝 (Real.exp (q * τ) * (Real.sqrt τ / σ) / Real.sqrt (2 * π))) := by
  intro h
  have heq := tendsto_nhds_unique (tendsto_qdfpK12_endpoint_holder (r := r) (c := c) hσ hτ hb) h
  rw [div_eq_mul_one_div _ (Real.sqrt (2 * π)), ← gaussianPDFReal_zero_one_zero] at heq
  have hpos : Real.exp (q * τ) * (Real.sqrt τ / σ) ≠ 0 := by
    have := Real.sqrt_pos.mpr hτ
    positivity
  exact gaussianPDFReal_zero_one_ne_zero_point (div_ne_zero hc hσ.ne')
    (mul_left_cancel₀ hpos heq)

end MathFin

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.VarianceSwapFromQV

/-!
# Variance-swap equipartition sum from QV (phase 33)

Extends Phase 32's per-increment QV identity to the full **equipartition
sum** over `[0, T]`. For BS log-price `X_t := log S_0 + (r − σ²/2)·t +
σ·B_t` and a partition of `[0, T]` into `n + 1` equal subintervals:

  `E[Σ_{k=0}^{n} (X_{(k+1)T/(n+1)} − X_{kT/(n+1)})²]
    = σ²·T + (r − σ²/2)²·T²/(n+1)`.

The drift contribution `(r − σ²/2)² · T² / (n + 1)` vanishes as `n → ∞`,
so

  `lim_n E[Σ (X-increments)²] = σ²·T`,

the QV characterisation of the variance-swap fair strike. The limit
theorem proper requires `Filter.Tendsto` analysis and is left as a
follow-up; the finite-`n` closed form here makes the limit obvious.

## Main results

* `integrable_bsLogPrice_sq_increment`: integrability of each per-
  subinterval squared increment (needed to swap sum and integral).
* `expected_bsLogPrice_equipartition_sum` (main theorem): closed-form
  finite-`n` equipartition-sum identity.

## Tags

variance swap, realized variance, quadratic variation, log-price increments, equipartition sum,
fair strike, MSC 91G20, MSC 60J65, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ → Ω → ℝ}

/-- **Integrability of each squared log-price increment** under a finite
measure. Derived from the algebraic decomposition
`(X_t − X_s)² = a² + 2aσ(B_t − B_s) + σ²(B_t − B_s)²` (with `a = (r −
σ²/2)(t − s)`) and the integrability of constants, of `(B_t − B_s)`, and
of `(B_t − B_s)²`. -/
theorem integrable_bsLogPrice_sq_increment
    [IsFiniteMeasure μ]
    (hB : BrownianQuadraticVariation μ B) (S_0 r σ : ℝ)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Integrable (fun ω ↦ (bsLogPrice S_0 r σ B t ω -
                          bsLogPrice S_0 r σ B s ω) ^ 2) μ := by
  set a : ℝ := (r - σ ^ 2 / 2) * (t - s) with a_def
  have h_eq : (fun ω ↦ (bsLogPrice S_0 r σ B t ω -
                         bsLogPrice S_0 r σ B s ω) ^ 2)
            = (fun ω ↦ a ^ 2 + 2 * a * σ * (B t ω - B s ω) +
                        σ ^ 2 * (B t ω - B s ω) ^ 2) := by
    funext ω
    unfold bsLogPrice
    rw [a_def]; ring
  rw [h_eq]
  exact ((integrable_const _).add
    ((hB.integrable_increment hs hst).const_mul _)).add
    ((hB.integrable_sq_increment hs hst).const_mul _)

/-- **Variance-swap equipartition sum identity** (phase 33, main theorem).
For BS log-price `X_t := log S_0 + (r − σ²/2)·t + σ·B_t` under
`BrownianQuadraticVariation` hypothesis on `B` and a probability measure
`μ`, the expectation of the sum of squared increments along the
equipartition of `[0, T]` into `n + 1` equal subintervals is

  `E[Σ_{k=0}^{n} (X_{(k+1)T/(n+1)} − X_{kT/(n+1)})²]
    = σ²·T + (r − σ²/2)²·T²/(n+1)`.

Proof: apply Phase 32's per-increment identity to each summand (length
`T/(n+1)`), sum `n+1` identical contributions, and arithmetic.

The drift contribution vanishes as `n → ∞`, giving the QV characterisation
of the variance-swap fair strike (`lim_n (1/T) · E[Σ ...] = σ²`). -/
theorem expected_bsLogPrice_equipartition_sum
    [IsProbabilityMeasure μ]
    (hB : BrownianQuadraticVariation μ B) (S_0 r σ : ℝ)
    {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    ∫ ω, ∑ k ∈ Finset.range (n + 1),
        (bsLogPrice S_0 r σ B (((k : ℝ) + 1) * T / ((n : ℝ) + 1)) ω -
         bsLogPrice S_0 r σ B ((k : ℝ) * T / ((n : ℝ) + 1)) ω) ^ 2 ∂μ
      = σ ^ 2 * T + (r - σ ^ 2 / 2) ^ 2 * T ^ 2 / ((n : ℝ) + 1) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn_ne : ((n : ℝ) + 1) ≠ 0 := hn_pos.ne'
  have h_start_nonneg : ∀ k : ℕ, (0 : ℝ) ≤ (k : ℝ) * T / ((n : ℝ) + 1) :=
    fun k ↦ div_nonneg (mul_nonneg (Nat.cast_nonneg k) hT) hn_pos.le
  -- subinterval endpoint inequality
  have h_endpt_le : ∀ k : ℕ,
      (((k : ℝ) * T) / ((n : ℝ) + 1)) ≤
        ((((k : ℝ) + 1) * T) / ((n : ℝ) + 1)) := by
    intro k
    rw [div_le_div_iff_of_pos_right hn_pos]
    nlinarith
  -- subinterval length T/(n+1)
  have h_len : ∀ k : ℕ,
      (((k : ℝ) + 1) * T) / ((n : ℝ) + 1) -
        ((k : ℝ) * T) / ((n : ℝ) + 1) = T / ((n : ℝ) + 1) := by
    intro k
    field_simp
    ring
  -- swap sum and integral
  rw [integral_finsetSum _ (fun k _ ↦
    integrable_bsLogPrice_sq_increment hB S_0 r σ (h_start_nonneg k) (h_endpt_le k))]
  -- per-summand QV identity
  have h_each : ∀ k ∈ Finset.range (n + 1),
      ∫ ω, (bsLogPrice S_0 r σ B (((k : ℝ) + 1) * T / ((n : ℝ) + 1)) ω -
            bsLogPrice S_0 r σ B ((k : ℝ) * T / ((n : ℝ) + 1)) ω) ^ 2 ∂μ
      = σ ^ 2 * (T / ((n : ℝ) + 1)) +
        (r - σ ^ 2 / 2) ^ 2 * (T / ((n : ℝ) + 1)) ^ 2 := by
    intro k _
    rw [expected_bsLogPrice_sq_increment hB S_0 r σ (h_start_nonneg k) (h_endpt_le k)]
    rw [h_len k]
  rw [Finset.sum_congr rfl h_each, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  -- (n+1) · (σ²·h + drift²·h²) = σ²·T + drift²·T²/(n+1), h = T/(n+1)
  push_cast
  field_simp

end MathFin

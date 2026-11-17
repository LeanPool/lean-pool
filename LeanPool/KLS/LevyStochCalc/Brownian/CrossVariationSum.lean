/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.CrossVariation
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoIncrementMoment
public import LeanPool.KLS.LevyStochCalc.Probability.MartingaleDifference

/-!
# Weighted sums of cross increments

For two distinct Brownian coordinates the product of the increments of the Itô integrals across a
cell is conditionally centred at the cell's left endpoint, so a weighted sum of such products over
a partition is a sum of martingale differences whenever the weights are measurable at the left
endpoints. Its second moment is therefore the sum of the termwise second moments, and each of
those is bounded through the fourth moments of the two increments.

## Main statements

* `LevyStochCalc.Brownian.Ito.integrable_sq_mul_and_le` — the square of a product is integrable
  with second moment at most half the sum of the fourth moments.
* `LevyStochCalc.Brownian.Ito.crossIncrement` — the product of the increments of the Itô
  integrals against two coordinates across a cell.
* `LevyStochCalc.Brownian.Ito.integral_sq_crossIncrement_le` — its second moment is at most
  `(6 + c)·(C_H⁴ + C_K⁴)/2·(b − a)²`.
* `LevyStochCalc.Brownian.Ito.integral_sq_weighted_crossSum_le` — the second moment of a weighted
  sum over a grid is at most `D²·(6 + c)·(C_H⁴ + C_K⁴)/2·∑ᵢ (tᵢ₊₁ − tᵢ)²`.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

omit [IsProbabilityMeasure P] in
/-- The square of a product of two functions with integrable fourth powers is integrable, and its
integral is at most half the sum of the two fourth moments. -/
theorem integrable_sq_mul_and_le {A B : Ω → ℝ} (hAm : Measurable A) (hBm : Measurable B)
    (hA4 : Integrable (fun ω => A ω ^ 4) P) (hB4 : Integrable (fun ω => B ω ^ 4) P) :
    Integrable (fun ω => (A ω * B ω) ^ 2) P
      ∧ ∫ ω, (A ω * B ω) ^ 2 ∂P ≤ (∫ ω, A ω ^ 4 ∂P + ∫ ω, B ω ^ 4 ∂P) / 2 := by
  have hdom : Integrable (fun ω => (A ω ^ 4 + B ω ^ 4) / 2) P := (hA4.add hB4).div_const 2
  have hpt : ∀ ω, (A ω * B ω) ^ 2 ≤ (A ω ^ 4 + B ω ^ 4) / 2 := fun ω => by
    nlinarith [sq_nonneg (A ω ^ 2 - B ω ^ 2), sq_nonneg (A ω * B ω)]
  have hint : Integrable (fun ω => (A ω * B ω) ^ 2) P := by
    refine Integrable.mono' hdom ((hAm.mul hBm).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt ω
  refine ⟨hint, ?_⟩
  have hle : ∫ ω, (A ω * B ω) ^ 2 ∂P ≤ ∫ ω, (A ω ^ 4 + B ω ^ 4) / 2 ∂P :=
    MeasureTheory.integral_mono hint hdom hpt
  rwa [MeasureTheory.integral_div, MeasureTheory.integral_add hA4 hB4] at hle

section CrossSum

open LevyStochCalc.Brownian.Multidim

variable {d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
  {H K : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
  (hHp : Probability.ProgressivelyMeasurable ℱ H)
  (hHs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hKm : Measurable (Function.uncurry K))
  (hKp : Probability.ProgressivelyMeasurable ℱ K)
  (hKs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

/-- The product of the increments of the Itô integrals against the coordinates `i` and `j`
across `(a, b]`. -/
noncomputable def crossIncrement (i j : Fin d) (a b : ℝ) (ω : Ω) : ℝ :=
  (stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
      - stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs a ω)
    * (stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs b ω
      - stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs a ω)

/-- The cross increment is measurable. -/
theorem measurable_crossIncrement (i j : Fin d) (a b : ℝ) :
    Measurable (crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j a b) :=
  (measurable_sub_stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs a b).mul
    (measurable_sub_stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs a b)

/-- The cross increment across `(a, b]` is measurable for the σ-algebra at `b`. -/
theorem stronglyMeasurable_crossIncrement (i j : Fin d) {a b : ℝ} (hab : a ≤ b) :
    StronglyMeasurable[ℱ b] (crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j a b) := by
  have hib := stochasticIntegralBrownian_stronglyAdapted (W.W i) ℱ (hcoord i) H hHm hHp hHs b
  have hia := (stochasticIntegralBrownian_stronglyAdapted (W.W i) ℱ (hcoord i) H hHm hHp hHs
    a).mono (ℱ.mono hab)
  have hjb := stochasticIntegralBrownian_stronglyAdapted (W.W j) ℱ (hcoord j) K hKm hKp hKs b
  have hja := (stochasticIntegralBrownian_stronglyAdapted (W.W j) ℱ (hcoord j) K hKm hKp hKs
    a).mono (ℱ.mono hab)
  exact (hib.sub hia).mul (hjb.sub hja)

variable {CH CK : ℝ} (hCH0 : 0 ≤ CH) (hCH : ∀ ω s, |H ω s| ≤ CH)
  (hCK0 : 0 ≤ CK) (hCK : ∀ ω s, |K ω s| ≤ CK)

include hCH0 hCH hCK0 hCK in
/-- **Second moment of a cross increment.** Both increments have fourth moments bounded through
the integrand bounds, and the square of a product is dominated by half the sum of the fourth
powers. -/
theorem integrable_sq_crossIncrement_and_le (i j : Fin d) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Integrable (fun ω =>
        (crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j a b ω) ^ 2) P
      ∧ ∫ ω, (crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j a b ω) ^ 2 ∂P
        ≤ (6 + gaussianFourthMoment) * (CH ^ 4 + CK ^ 4) / 2 * (b - a) ^ 2 := by
  obtain ⟨hA4, hA4le⟩ :=
    integral_sub_pow_four_le (W.W i) ℱ (hcoord i) H hHm hHp hHs hCH0 hCH ha hab
  obtain ⟨hB4, hB4le⟩ :=
    integral_sub_pow_four_le (W.W j) ℱ (hcoord j) K hKm hKp hKs hCK0 hCK ha hab
  obtain ⟨hint, hle⟩ := integrable_sq_mul_and_le
    (measurable_sub_stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs a b)
    (measurable_sub_stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs a b) hA4 hB4
  refine ⟨hint, le_trans hle ?_⟩
  linarith [hA4le, hB4le]

include hCH0 hCH hCK0 hCK in
/-- The cross increment lies in `L²`. -/
theorem memLp_two_crossIncrement (i j : Fin d) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    MemLp (crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j a b) 2 P :=
  (memLp_two_iff_integrable_sq
      (measurable_crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j a b).aestronglyMeasurable).2
    (integrable_sq_crossIncrement_and_le W hcoord hHm hHp hHs hKm hKp hKs hCH0 hCH hCK0 hCK
      i j ha hab).1

/-- The cross increment is conditionally centred at the left endpoint of its cell. -/
theorem condExp_crossIncrement {i j : Fin d} (hij : i ≠ j) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    P[crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j a b | ℱ a] =ᵐ[P] 0 :=
  condExp_mul_cross_increment_eq_zero W hcoord hHm hHp hHs hKm hKp hKs hij ha hab

include hCH0 hCH hCK0 hCK in
/-- **Second moment of a weighted sum of cross increments.** The cross increments are martingale
differences for the weights at the left endpoints, so the weighted sum's second moment is
controlled by the sum of the squared cell lengths. -/
theorem integral_sq_weighted_crossSum_le {i j : Fin d} (hij : i ≠ j)
    (t : ℕ → ℝ) (h0 : 0 ≤ t 0) (ht : ∀ k, t k < t (k + 1))
    (g : ℕ → Ω → ℝ) (hg : ∀ k, StronglyMeasurable[ℱ (t k)] (g k))
    {D : ℝ} (hD0 : 0 ≤ D) (hgD : ∀ (k : ℕ) (ω : Ω), |g k ω| ≤ D) (n : ℕ) :
    ∫ ω, (∑ k ∈ Finset.range n, g k ω *
        crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (t k) (t (k + 1)) ω) ^ 2 ∂P
      ≤ D ^ 2 * ((6 + gaussianFourthMoment) * (CH ^ 4 + CK ^ 4) / 2)
        * ∑ k ∈ Finset.range n, (t (k + 1) - t k) ^ 2 := by
  have htmono : StrictMono t := strictMono_nat_of_lt_succ ht
  have ht0 : ∀ k, 0 ≤ t k := fun k => h0.trans (htmono.monotone (Nat.zero_le k))
  set 𝒢 : ℕ → MeasurableSpace Ω := fun k => ℱ (t k) with h𝒢
  have h𝒢le : ∀ k, 𝒢 k ≤ ‹MeasurableSpace Ω› := fun k => ℱ.le (t k)
  have h𝒢mono : Monotone 𝒢 := fun p q hpq => ℱ.mono (htmono.monotone hpq)
  set Y : ℕ → Ω → ℝ := fun k ω =>
    g k ω * crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (t k) (t (k + 1)) ω with hY
  have hζmem : ∀ k, MemLp
      (crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (t k) (t (k + 1))) 2 P :=
    fun k => memLp_two_crossIncrement W hcoord hHm hHp hHs hKm hKp hKs hCH0 hCH hCK0 hCK
      i j (ht0 k) (ht k)
  have hgmeas : ∀ k, Measurable (g k) := fun k => ((hg k).mono (h𝒢le k)).measurable
  have hYmem : ∀ k, MemLp (Y k) 2 P := by
    intro k
    refine MeasureTheory.MemLp.mono ((hζmem k).const_mul D)
      ((hgmeas k).aestronglyMeasurable.mul (hζmem k).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hD0]
    exact mul_le_mul_of_nonneg_right (hgD k ω) (abs_nonneg _)
  have hYmeas : ∀ k, @MeasureTheory.StronglyMeasurable Ω ℝ _ (𝒢 (k + 1)) (Y k) := fun k =>
    ((hg k).mono (h𝒢mono (Nat.le_succ k))).mul
      (stronglyMeasurable_crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (ht k).le)
  have hYcond : ∀ k, P[Y k | 𝒢 k] =ᵐ[P] 0 := by
    intro k
    have hprod : Integrable
        (g k * crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (t k) (t (k + 1))) P :=
      (hYmem k).integrable (by norm_num)
    have hkey := MeasureTheory.condExp_mul_of_stronglyMeasurable_left (m := 𝒢 k) (hg k)
      hprod ((hζmem k).integrable (by norm_num))
    have hfun : Y k
        = g k * crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (t k) (t (k + 1)) := rfl
    rw [hfun]
    filter_upwards [hkey, condExp_crossIncrement W hcoord hHm hHp hHs hKm hKp hKs hij
      (ht0 k) (ht k)] with ω hω hω'
    rw [hω, Pi.mul_apply, hω', Pi.zero_apply, mul_zero]
  rw [LevyStochCalc.Probability.integral_sq_sum_of_condExp_eq_zero 𝒢 h𝒢le h𝒢mono Y hYmem
    hYmeas hYcond n]
  have hterm : ∀ k ∈ Finset.range n, ∫ ω, (Y k ω) ^ 2 ∂P
      ≤ D ^ 2 * ((6 + gaussianFourthMoment) * (CH ^ 4 + CK ^ 4) / 2) * (t (k + 1) - t k) ^ 2 := by
    intro k _
    obtain ⟨hζint, hζle⟩ := integrable_sq_crossIncrement_and_le W hcoord hHm hHp hHs hKm hKp hKs
      hCH0 hCH hCK0 hCK i j (ht0 k) (ht k)
    have hYint : Integrable (fun ω => (Y k ω) ^ 2) P := by
      have hfun : (fun ω => (Y k ω) ^ 2) = Y k * Y k := by funext ω; rw [pow_two]; rfl
      rw [hfun]
      exact (hYmem k).integrable_mul (hYmem k)
    have hstep : ∫ ω, (Y k ω) ^ 2 ∂P ≤ D ^ 2 * ∫ ω,
        (crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (t k) (t (k + 1)) ω) ^ 2 ∂P := by
      have hle : ∫ ω, (Y k ω) ^ 2 ∂P ≤ ∫ ω, D ^ 2 *
          (crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (t k) (t (k + 1)) ω) ^ 2 ∂P := by
        refine MeasureTheory.integral_mono hYint (hζint.const_mul _) fun ω => ?_
        have hgi : (g k ω) ^ 2 ≤ D ^ 2 := by
          have h := pow_le_pow_left₀ (abs_nonneg (g k ω)) (hgD k ω) 2
          rwa [← abs_pow, abs_of_nonneg (sq_nonneg (g k ω))] at h
        have hsq : (Y k ω) ^ 2 = (g k ω) ^ 2
            * (crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (t k) (t (k + 1)) ω) ^ 2 := by
          simp only [hY]; ring
        rw [hsq]
        exact mul_le_mul_of_nonneg_right hgi (sq_nonneg _)
      rwa [MeasureTheory.integral_const_mul] at hle
    have hD2 : (0 : ℝ) ≤ D ^ 2 := sq_nonneg D
    calc ∫ ω, (Y k ω) ^ 2 ∂P
        ≤ D ^ 2 * ∫ ω,
            (crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (t k) (t (k + 1)) ω) ^ 2 ∂P :=
          hstep
      _ ≤ D ^ 2 * ((6 + gaussianFourthMoment) * (CH ^ 4 + CK ^ 4) / 2 * (t (k + 1) - t k) ^ 2) :=
          mul_le_mul_of_nonneg_left hζle hD2
      _ = D ^ 2 * ((6 + gaussianFourthMoment) * (CH ^ 4 + CK ^ 4) / 2)
            * (t (k + 1) - t k) ^ 2 := by ring
  calc ∑ k ∈ Finset.range n, ∫ ω, (Y k ω) ^ 2 ∂P
      ≤ ∑ k ∈ Finset.range n,
          D ^ 2 * ((6 + gaussianFourthMoment) * (CH ^ 4 + CK ^ 4) / 2)
            * (t (k + 1) - t k) ^ 2 := Finset.sum_le_sum hterm
    _ = D ^ 2 * ((6 + gaussianFourthMoment) * (CH ^ 4 + CK ^ 4) / 2)
          * ∑ k ∈ Finset.range n, (t (k + 1) - t k) ^ 2 := by rw [Finset.mul_sum]

end CrossSum

end LevyStochCalc.Brownian.Ito

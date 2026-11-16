/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system (module
-- header, public imports, exposed public section) for Lean/Mathlib v4.35.0; proofs use
-- `continuous_abs.measurable.comp` for the no longer reachable `Measurable.abs`.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.DriftIncrement
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoIncrementMoment
public import LeanPool.KLS.LevyStochCalc.Probability.AbsMoment

/-!
# Itô processes and the moments of their increments

An Itô process is `X_t = X₀ + ∫_{[0,t]} b_s ds + ∫_0^t H_s dW_s` for a bounded drift `b` and an
`L²` integrand `H`. Its increment across a window is the drift's window integral plus the Itô
integral's increment, so its moments follow from the drift bound and the increment moments of
the Itô integral.

## Main statements

* `LevyStochCalc.Brownian.Ito.itoProcess` — the process itself.
* `LevyStochCalc.Brownian.Ito.itoProcess_sub` — the increment splits into drift and martingale
  parts.
* `LevyStochCalc.Brownian.Ito.integral_sq_itoProcess_sub_le` — `𝔼|ΔX|² ≤ 2B²(Δt)² + 2C²Δt`.
* `LevyStochCalc.Brownian.Ito.integral_abs_sub_stochasticIntegral_le` — `𝔼|ΔM| ≤ C√(Δt)`.
* `LevyStochCalc.Brownian.Ito.integral_abs_itoProcess_sub_le` — `𝔼|ΔX| ≤ BΔt + C√(Δt)`.
* `LevyStochCalc.Brownian.Ito.integrable_abs_itoIncrement_pow_three` — the cube of the absolute
  increment is integrable.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- `(a + b)³ ≤ 4(a³ + b³)` for nonnegative reals. -/
theorem add_pow_three_le_four {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) := by
  nlinarith [sq_nonneg (a - b), mul_nonneg ha hb, sq_nonneg (a + b)]

section Drift

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- The `n`-th power of the absolute increment of a bounded drift's integral is integrable. -/
theorem integrable_abs_drift_pow
    (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (huv : u ≤ v) (n : ℕ) :
    MeasureTheory.Integrable
      (fun ω : Ω => |∫ s in Set.Ioc u v, bdrift ω s ∂volume| ^ n) P := by
  have hDmeas : Measurable fun ω : Ω => ∫ s in Set.Ioc u v, bdrift ω s ∂volume :=
    measurable_setIntegral_Ioc hbm _ _
  have hvu : (0 : ℝ) ≤ v - u := sub_nonneg.mpr huv
  refine (MeasureTheory.integrable_const ((B * (v - u)) ^ n)).mono
    (((continuous_abs.measurable.comp hDmeas).pow_const n).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (abs_nonneg _) n),
    abs_of_nonneg (pow_nonneg (mul_nonneg hB0 hvu) n)]
  exact pow_le_pow_left₀ (abs_nonneg _)
    (abs_setIntegral_Ioc_le (Measurable.of_uncurry_left hbm) (hB ω) huv) n

/-- The cube of the absolute increment of a bounded drift's integral is integrable. -/
theorem integrable_abs_drift_pow_three
    (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (huv : u ≤ v) :
    MeasureTheory.Integrable
      (fun ω : Ω => |∫ s in Set.Ioc u v, bdrift ω s ∂volume| ^ 3) P :=
  integrable_abs_drift_pow (P := P) bdrift hbm hB0 hB huv 3

/-- The absolute increment of a bounded drift's integral is integrable. -/
theorem integrable_abs_drift
    (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (huv : u ≤ v) :
    MeasureTheory.Integrable
      (fun ω : Ω => |∫ s in Set.Ioc u v, bdrift ω s ∂volume|) P := by
  simpa only [pow_one] using integrable_abs_drift_pow (P := P) bdrift hbm hB0 hB huv 1

/-- The square of the increment of a bounded drift's integral is integrable. -/
theorem integrable_drift_sq
    (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (huv : u ≤ v) :
    MeasureTheory.Integrable
      (fun ω : Ω => (∫ s in Set.Ioc u v, bdrift ω s ∂volume) ^ 2) P := by
  simpa only [sq_abs] using integrable_abs_drift_pow (P := P) bdrift hbm hB0 hB huv 2

/-- The first absolute moment of a bounded drift's increment is at most `B·(v − u)`. -/
theorem integral_abs_drift_le
    (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (huv : u ≤ v) :
    ∫ ω, |∫ s in Set.Ioc u v, bdrift ω s ∂volume| ∂P ≤ B * (v - u) := by
  calc ∫ ω, |∫ s in Set.Ioc u v, bdrift ω s ∂volume| ∂P
      ≤ ∫ _ω : Ω, B * (v - u) ∂P :=
        MeasureTheory.integral_mono (integrable_abs_drift (P := P) bdrift hbm hB0 hB huv)
          (MeasureTheory.integrable_const _)
          (fun ω => abs_setIntegral_Ioc_le (Measurable.of_uncurry_left hbm) (hB ω) huv)
    _ = B * (v - u) := by simp

/-- The second moment of a bounded drift's increment is at most `(B·(v − u))²`. -/
theorem integral_drift_sq_le
    (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (huv : u ≤ v) :
    ∫ ω, (∫ s in Set.Ioc u v, bdrift ω s ∂volume) ^ 2 ∂P ≤ (B * (v - u)) ^ 2 := by
  calc ∫ ω, (∫ s in Set.Ioc u v, bdrift ω s ∂volume) ^ 2 ∂P
      ≤ ∫ _ω : Ω, (B * (v - u)) ^ 2 ∂P := by
        refine MeasureTheory.integral_mono (integrable_drift_sq (P := P) bdrift hbm hB0 hB huv)
          (MeasureTheory.integrable_const _) fun ω => ?_
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _)
          (abs_setIntegral_Ioc_le (Measurable.of_uncurry_left hbm) (hB ω) huv) 2
    _ = (B * (v - u)) ^ 2 := by simp

end Drift

section Process

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

/-- The Itô process `X_t = X₀ + ∫_{[0,t]} b_s ds + ∫_0^t H_s dW_s`. -/
noncomputable def itoProcess (X₀ : Ω → ℝ) (bdrift : Ω → ℝ → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  X₀ ω + (∫ s in Set.Icc (0 : ℝ) t, bdrift ω s ∂volume)
    + stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω

include hℱ in
/-- An Itô process is measurable in the sample point at each time. -/
theorem measurable_itoProcess {X₀ : Ω → ℝ} (hX₀ : Measurable X₀) {bdrift : Ω → ℝ → ℝ}
    (hbm : Measurable (Function.uncurry bdrift)) (t : ℝ) :
    Measurable (itoProcess W ℱ hℱ H hm hp hq X₀ bdrift t) := by
  unfold itoProcess
  exact (hX₀.add (measurable_setIntegral hbm _)).add
    ((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq t).mono (ℱ.le t)).measurable

include hℱ in
/-- The increment of an Itô process is the drift's increment plus the Itô integral's. -/
theorem itoProcess_sub (X₀ : Ω → ℝ) (bdrift : Ω → ℝ → ℝ)
    (hbm : Measurable (Function.uncurry bdrift)) {B : ℝ}
    (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (ω : Ω) :
    itoProcess W ℱ hℱ H hm hp hq X₀ bdrift v ω
        - itoProcess W ℱ hℱ H hm hp hq X₀ bdrift u ω
      = (∫ s in Set.Ioc u v, bdrift ω s ∂volume)
        + (stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω) := by
  unfold itoProcess
  rw [← setIntegral_Icc_sub_Icc (Measurable.of_uncurry_left hbm) (hB ω) hu huv]
  ring

variable {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hℱ hC0 hCH in
/-- The cube of the absolute increment of an Itô process is integrable. -/
theorem integrable_abs_itoIncrement_pow_three
    (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    MeasureTheory.Integrable (fun ω : Ω =>
      |(∫ s in Set.Ioc u v, bdrift ω s ∂volume)
        + (stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω)| ^ 3) P := by
  have hDint := integrable_abs_drift_pow_three (P := P) bdrift hbm hB0 hB huv.le
  have hDmeas : Measurable fun ω : Ω => ∫ s in Set.Ioc u v, bdrift ω s ∂volume :=
    measurable_setIntegral_Ioc hbm _ _
  have hMint := (integral_abs_sub_pow_three_le W ℱ hℱ H hm hp hq hC0 hCH hu huv).1
  have hMmeas := measurable_sub_stochasticIntegralBrownian W ℱ hℱ H hm hp hq u v
  refine ((hDint.add hMint).const_mul 4).mono
    (((continuous_abs.measurable.comp (hDmeas.add hMmeas)).pow_const 3).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) 3)]
  refine le_trans ?_ (le_abs_self _)
  have h3 : |(∫ s in Set.Ioc u v, bdrift ω s ∂volume)
      + (stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω)| ^ 3
      ≤ (|∫ s in Set.Ioc u v, bdrift ω s ∂volume|
        + |stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω|) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg _) (abs_add_le _ _) 3
  exact h3.trans (add_pow_three_le_four (abs_nonneg _) (abs_nonneg _))

include hℱ hC0 hCH in
/-- **Second moment of an Itô process's increment.** `𝔼|X_v − X_u|² ≤ 2B²(v−u)² + 2C²(v−u)`. -/
theorem integral_sq_itoProcess_sub_le
    (X₀ : Ω → ℝ) (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    MeasureTheory.Integrable (fun ω : Ω =>
        (itoProcess W ℱ hℱ H hm hp hq X₀ bdrift v ω
          - itoProcess W ℱ hℱ H hm hp hq X₀ bdrift u ω) ^ 2) P
      ∧ ∫ ω, (itoProcess W ℱ hℱ H hm hp hq X₀ bdrift v ω
            - itoProcess W ℱ hℱ H hm hp hq X₀ bdrift u ω) ^ 2 ∂P
          ≤ 2 * (B * (v - u)) ^ 2 + 2 * (C ^ 2 * (v - u)) := by
  have key : ∀ ω : Ω, itoProcess W ℱ hℱ H hm hp hq X₀ bdrift v ω
      - itoProcess W ℱ hℱ H hm hp hq X₀ bdrift u ω
      = (∫ s in Set.Ioc u v, bdrift ω s ∂volume)
        + (stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω) := fun ω =>
    itoProcess_sub W ℱ hℱ H hm hp hq X₀ bdrift hbm hB hu huv.le ω
  simp_rw [key]
  obtain ⟨hMint, hMle⟩ := integral_sub_sq_le W ℱ hℱ H hm hp hq hC0 hCH hu huv
  have hDint := integrable_drift_sq (P := P) bdrift hbm hB0 hB huv.le
  have hDle := integral_drift_sq_le (P := P) bdrift hbm hB0 hB huv.le
  have hDmeas : Measurable fun ω : Ω => ∫ s in Set.Ioc u v, bdrift ω s ∂volume :=
    measurable_setIntegral_Ioc hbm _ _
  have hMmeas := measurable_sub_stochasticIntegralBrownian W ℱ hℱ H hm hp hq u v
  have hdom : MeasureTheory.Integrable (fun ω : Ω =>
      2 * (∫ s in Set.Ioc u v, bdrift ω s ∂volume) ^ 2
        + 2 * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω) ^ 2) P :=
    (hDint.const_mul 2).add (hMint.const_mul 2)
  have hpt : ∀ ω : Ω, ((∫ s in Set.Ioc u v, bdrift ω s ∂volume)
        + (stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω)) ^ 2
      ≤ 2 * (∫ s in Set.Ioc u v, bdrift ω s ∂volume) ^ 2
        + 2 * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω) ^ 2 := by
    intro ω
    nlinarith [sq_nonneg ((∫ s in Set.Ioc u v, bdrift ω s ∂volume)
      - (stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω))]
  have hXint : MeasureTheory.Integrable (fun ω : Ω =>
      ((∫ s in Set.Ioc u v, bdrift ω s ∂volume)
        + (stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω)) ^ 2) P := by
    refine hdom.mono (((hDmeas.add hMmeas).pow_const 2).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (hpt ω).trans (le_abs_self _)
  refine ⟨hXint, ?_⟩
  calc ∫ ω, ((∫ s in Set.Ioc u v, bdrift ω s ∂volume)
        + (stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω)) ^ 2 ∂P
      ≤ ∫ ω, (2 * (∫ s in Set.Ioc u v, bdrift ω s ∂volume) ^ 2
          + 2 * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω) ^ 2) ∂P :=
        MeasureTheory.integral_mono hXint hdom hpt
    _ = 2 * (∫ ω, (∫ s in Set.Ioc u v, bdrift ω s ∂volume) ^ 2 ∂P)
        + 2 * ∫ ω, (stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω) ^ 2 ∂P := by
        rw [MeasureTheory.integral_add (hDint.const_mul 2) (hMint.const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ ≤ 2 * (B * (v - u)) ^ 2 + 2 * (C ^ 2 * (v - u)) := by
        have h1 : 2 * (∫ ω, (∫ s in Set.Ioc u v, bdrift ω s ∂volume) ^ 2 ∂P)
            ≤ 2 * (B * (v - u)) ^ 2 := by linarith
        have h2 : 2 * ∫ ω, (stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
              - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω) ^ 2 ∂P
            ≤ 2 * (C ^ 2 * (v - u)) := by linarith
        linarith

include hℱ hC0 hCH in
/-- **First absolute moment of an increment of the Itô integral.** `𝔼|M_v − M_u| ≤ C√(v−u)`. -/
theorem integral_abs_sub_stochasticIntegral_le {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    MeasureTheory.Integrable (fun ω : Ω =>
        |stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω|) P
      ∧ ∫ ω, |stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω| ∂P
          ≤ C * Real.sqrt (v - u) := by
  obtain ⟨hMsq, hMle⟩ := integral_sub_sq_le W ℱ hℱ H hm hp hq hC0 hCH hu huv
  have hMmeas := measurable_sub_stochasticIntegralBrownian W ℱ hℱ H hm hp hq u v
  have hyoung : ∀ x : ℝ, |x| ≤ (x ^ 2 + 1) / 2 := by
    intro x
    nlinarith [sq_nonneg (|x| - 1), sq_abs x]
  have hMabs : MeasureTheory.Integrable (fun ω : Ω =>
      |stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω|) P := by
    refine ((hMsq.add (MeasureTheory.integrable_const 1)).div_const 2).mono
      (continuous_abs.measurable.comp hMmeas).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
    exact (hyoung _).trans (le_abs_self _)
  refine ⟨hMabs, ?_⟩
  have hsqrt : Real.sqrt (C ^ 2 * (v - u)) = C * Real.sqrt (v - u) := by
    rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC0]
  rw [← hsqrt]
  exact integral_abs_le_sqrt_of_integral_sq_le hMabs hMsq hMle

include hℱ hC0 hCH in
/-- **First absolute moment of an Itô process's increment.** `𝔼|X_v − X_u| ≤ B(v−u) + C√(v−u)`. -/
theorem integral_abs_itoProcess_sub_le
    (X₀ : Ω → ℝ) (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    MeasureTheory.Integrable (fun ω : Ω =>
        |itoProcess W ℱ hℱ H hm hp hq X₀ bdrift v ω
          - itoProcess W ℱ hℱ H hm hp hq X₀ bdrift u ω|) P
      ∧ ∫ ω, |itoProcess W ℱ hℱ H hm hp hq X₀ bdrift v ω
            - itoProcess W ℱ hℱ H hm hp hq X₀ bdrift u ω| ∂P
          ≤ B * (v - u) + C * Real.sqrt (v - u) := by
  have key : ∀ ω : Ω, itoProcess W ℱ hℱ H hm hp hq X₀ bdrift v ω
      - itoProcess W ℱ hℱ H hm hp hq X₀ bdrift u ω
      = (∫ s in Set.Ioc u v, bdrift ω s ∂volume)
        + (stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω) := fun ω =>
    itoProcess_sub W ℱ hℱ H hm hp hq X₀ bdrift hbm hB hu huv.le ω
  simp_rw [key]
  obtain ⟨hMabs, hMabsle⟩ :=
    integral_abs_sub_stochasticIntegral_le W ℱ hℱ H hm hp hq hC0 hCH hu huv
  have hMmeas := measurable_sub_stochasticIntegralBrownian W ℱ hℱ H hm hp hq u v
  have hDmeas : Measurable fun ω : Ω => ∫ s in Set.Ioc u v, bdrift ω s ∂volume :=
    measurable_setIntegral_Ioc hbm _ _
  have hDabs := integrable_abs_drift (P := P) bdrift hbm hB0 hB huv.le
  have hDle := integral_abs_drift_le (P := P) bdrift hbm hB0 hB huv.le
  have hpt : ∀ ω : Ω, |(∫ s in Set.Ioc u v, bdrift ω s ∂volume)
        + (stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω)|
      ≤ |∫ s in Set.Ioc u v, bdrift ω s ∂volume|
        + |stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω| := fun ω => abs_add_le _ _
  have hXabs : MeasureTheory.Integrable (fun ω : Ω =>
      |(∫ s in Set.Ioc u v, bdrift ω s ∂volume)
        + (stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω)|) P := by
    refine (hDabs.add hMabs).mono
      ((continuous_abs.measurable.comp (hDmeas.add hMmeas)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
    exact (hpt ω).trans (le_abs_self _)
  refine ⟨hXabs, ?_⟩
  calc ∫ ω, |(∫ s in Set.Ioc u v, bdrift ω s ∂volume)
        + (stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω)| ∂P
      ≤ ∫ ω, (|∫ s in Set.Ioc u v, bdrift ω s ∂volume|
          + |stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω|) ∂P :=
        MeasureTheory.integral_mono hXabs (hDabs.add hMabs) hpt
    _ = (∫ ω, |∫ s in Set.Ioc u v, bdrift ω s ∂volume| ∂P)
        + ∫ ω, |stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω| ∂P :=
        MeasureTheory.integral_add hDabs hMabs
    _ ≤ B * (v - u) + C * Real.sqrt (v - u) := add_le_add hDle hMabsle

end Process

end LevyStochCalc.Brownian.Ito

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoTimeRiemann
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoQuadVarSum

/-!
# The quadratic-variation Riemann sum of the Itô formula

Squaring the increments of a continuous Itô process across a uniform grid and weighting them by
a bounded Lipschitz function of the process gives a Riemann sum for `∫_0^T φ(X_s)·H_s² ds`. The
drift square and the cross term are `O(1/m)` and `O(m^{-1/2})`, the compensated squares are
`O(m^{-1/2})` by the martingale-difference bound, and the compensator itself is a frozen-weight
Riemann sum for the density `H²`.

## Main statements

* `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_sum_drift_sq_le` — the drift-square sum.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_sum_cross_le` — the cross term.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_sum_quadVar_le` — the compensated
  squares.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_quadVarRiemann_sub_le` — the four
  pieces together.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section QuadVarRiemann

variable {P : Measure Ω} [IsProbabilityMeasure P] {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {H : Ω → ℝ → ℝ} {hm : Measurable (Function.uncurry H)}
  {hp : Probability.ProgressivelyMeasurable ℱ H}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → ℝ} {bdrift : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

/-- **The drift-square sum is `O(1/m)`.** -/
theorem IsItoVersion.integral_abs_sum_drift_sq_le
    (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (_hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {φ : ℝ → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hKφ0 : 0 ≤ Kφ) (hφbd : ∀ x, |φ x| ≤ Kφ)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    MeasureTheory.Integrable (fun ω : Ω => ∑ i ∈ Finset.range m,
        φ (X (unifGrid T m i) ω)
          * (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
              bdrift ω s ∂volume) ^ 2) P
      ∧ ∫ ω, |∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
              bdrift ω s ∂volume) ^ 2| ∂P
        ≤ (m : ℝ) * (Kφ * (B * (T / (m : ℝ))) ^ 2) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hTm0 : (0 : ℝ) ≤ T / (m : ℝ) := (div_pos hT hm').le
  have hmeas : Measurable fun ω : Ω => ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
      * (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift ω s ∂volume) ^ 2 :=
    Finset.measurable_sum _ fun i _ =>
      (hφc.measurable.comp (h.measurable (unifGrid T m i))).mul
        ((measurable_setIntegral_Ioc hbm _ _).pow_const 2)
  have hDbd : ∀ (ω : Ω) (i : ℕ),
      |∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift ω s ∂volume|
        ≤ B * (T / (m : ℝ)) := by
    intro ω i
    have hle := abs_setIntegral_Ioc_le (Measurable.of_uncurry_left hbm) (hB ω)
      (unifGrid_lt_succ hT hm0 i).le
    rwa [unifGrid_succ_sub hm0 i] at hle
  have hbound : ∀ ω : Ω, |∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
      * (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift ω s ∂volume) ^ 2|
      ≤ (m : ℝ) * (Kφ * (B * (T / (m : ℝ))) ^ 2) := by
    intro ω
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ i ∈ Finset.range m, |φ (X (unifGrid T m i) ω)
        * (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
            bdrift ω s ∂volume) ^ 2| ≤ Kφ * (B * (T / (m : ℝ))) ^ 2 := by
      intro i _
      rw [abs_mul, abs_pow]
      refine mul_le_mul (hφbd _) (pow_le_pow_left₀ (abs_nonneg _) (hDbd ω i) 2)
        (by positivity) hKφ0
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact integral_abs_le_of_bounded hmeas (by positivity) hbound

include hC0 hCH in
/-- **The drift–martingale cross term is `O(m^{-1/2})`.** -/
theorem IsItoVersion.integral_abs_sum_cross_le
    (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {φ : ℝ → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hKφ0 : 0 ≤ Kφ) (hφbd : ∀ x, |φ x| ≤ Kφ)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    MeasureTheory.Integrable (fun ω : Ω => ∑ i ∈ Finset.range m,
        φ (X (unifGrid T m i) ω)
          * (2 * (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift ω s ∂volume)
            * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
              - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω))) P
      ∧ ∫ ω, |∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * (2 * (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift ω s ∂volume)
            * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
              - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω))| ∂P
        ≤ (m : ℝ) * (2 * Kφ * (B * (T / (m : ℝ))) * (C * Real.sqrt (T / (m : ℝ)))) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hTm0 : (0 : ℝ) ≤ T / (m : ℝ) := (div_pos hT hm').le
  have hMdata : ∀ i : ℕ,
      MeasureTheory.Integrable (fun ω : Ω =>
          |stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω|) P
        ∧ ∫ ω, |stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω| ∂P
          ≤ C * Real.sqrt (T / (m : ℝ)) := by
    intro i
    obtain ⟨hint, hle⟩ := integral_abs_sub_stochasticIntegral_le W ℱ hℱ H hm hp hq hC0 hCH
      (unifGrid_nonneg hT.le m i) (unifGrid_lt_succ hT hm0 i)
    rw [unifGrid_succ_sub hm0 i] at hle
    exact ⟨hint, hle⟩
  have hDbd : ∀ (ω : Ω) (i : ℕ),
      |∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift ω s ∂volume|
        ≤ B * (T / (m : ℝ)) := by
    intro ω i
    have hle := abs_setIntegral_Ioc_le (Measurable.of_uncurry_left hbm) (hB ω)
      (unifGrid_lt_succ hT hm0 i).le
    rwa [unifGrid_succ_sub hm0 i] at hle
  have hmeas : Measurable fun ω : Ω => ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
      * (2 * (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift ω s ∂volume)
        * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω)) :=
    Finset.measurable_sum _ fun i _ =>
      (hφc.measurable.comp (h.measurable (unifGrid T m i))).mul
        ((measurable_const.mul (measurable_setIntegral_Ioc hbm _ _)).mul
          (measurable_sub_stochasticIntegralBrownian W ℱ hℱ H hm hp hq
            (unifGrid T m i) (unifGrid T m (i + 1))))
  set g : Ω → ℝ := fun ω => ∑ i ∈ Finset.range m, 2 * Kφ * (B * (T / (m : ℝ)))
    * |stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
      - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω| with hgdef
  have hgint : MeasureTheory.Integrable g P :=
    MeasureTheory.integrable_finsetSum _ fun i _ => ((hMdata i).1.const_mul _)
  have hbound : ∀ ω : Ω, |∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
      * (2 * (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift ω s ∂volume)
        * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω))| ≤ g ω := by
    intro ω
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_mul, abs_mul, abs_two]
    calc |φ (X (unifGrid T m i) ω)|
          * (2 * |∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
              bdrift ω s ∂volume|
            * |stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
              - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω|)
        ≤ Kφ * (2 * (B * (T / (m : ℝ)))
            * |stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
              - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω|) := by
          gcongr
          · exact hφbd _
          · exact hDbd ω i
      _ = 2 * Kφ * (B * (T / (m : ℝ)))
            * |stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
              - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω| := by ring
  have hLint : MeasureTheory.Integrable (fun ω : Ω =>
      ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
        * (2 * (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift ω s ∂volume)
          * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω))) P := by
    refine hgint.mono hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact (hbound ω).trans (le_abs_self _)
  refine ⟨hLint, ?_⟩
  calc ∫ ω, |∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
        * (2 * (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift ω s ∂volume)
          * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω))| ∂P
      ≤ ∫ ω, g ω ∂P := MeasureTheory.integral_mono hLint.abs hgint hbound
    _ = ∑ i ∈ Finset.range m, 2 * Kφ * (B * (T / (m : ℝ)))
          * ∫ ω, |stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω| ∂P := by
        rw [hgdef, MeasureTheory.integral_finsetSum _ fun i _ => ((hMdata i).1.const_mul _)]
        exact Finset.sum_congr rfl fun i _ => MeasureTheory.integral_const_mul _ _
    _ ≤ ∑ _i ∈ Finset.range m, 2 * Kφ * (B * (T / (m : ℝ))) * (C * Real.sqrt (T / (m : ℝ))) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hc : (0 : ℝ) ≤ 2 * Kφ * (B * (T / (m : ℝ))) := by positivity
        exact mul_le_mul_of_nonneg_left (hMdata i).2 hc
    _ = (m : ℝ) * (2 * Kφ * (B * (T / (m : ℝ))) * (C * Real.sqrt (T / (m : ℝ)))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

include hC0 hCH in
/-- **The compensated squares sum to `O(m^{-1/2})`.** -/
theorem IsItoVersion.integral_abs_sum_quadVar_le
    (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    {φ : ℝ → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hKφ0 : 0 ≤ Kφ) (hφbd : ∀ x, |φ x| ≤ Kφ)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    MeasureTheory.Integrable (fun ω : Ω => ∑ i ∈ Finset.range m,
        φ (X (unifGrid T m i) ω)
          * quadVarIncrement W ℱ hℱ H hm hp hq (unifGrid T m i)
              (unifGrid T m (i + 1)) ω) P
      ∧ ∫ ω, |∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * quadVarIncrement W ℱ hℱ H hm hp hq (unifGrid T m i)
              (unifGrid T m (i + 1)) ω| ∂P
        ≤ Real.sqrt (Kφ ^ 2 * ((2 * (6 + gaussianFourthMoment) + 2) * C ^ 4)
            * ((m : ℝ) * (T / (m : ℝ)) ^ 2)) := by
  have hgadapt : ∀ k : ℕ, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ.rightCont (unifGrid T m k)) (fun ω => φ (X (unifGrid T m k) ω)) := fun k =>
    hφc.comp_stronglyMeasurable ((h.adapted (unifGrid T m k)).mono (ℱ.le_rightCont _))
  have hquad := integral_sq_weighted_quadVarSum_le W ℱ hℱ H hm hp hq hC0 hCH
    (unifGrid T m) (by simp) (unifGrid_lt_succ hT hm0)
    (fun k ω => φ (X (unifGrid T m k) ω)) hgadapt hKφ0 (fun k ω => hφbd _) m
  have hmesh : ∑ i ∈ Finset.range m, (unifGrid T m (i + 1) - unifGrid T m i) ^ 2
      = (m : ℝ) * (T / (m : ℝ)) ^ 2 := by
    simp_rw [unifGrid_succ_sub hm0]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hmesh] at hquad
  have hζmem : ∀ k : ℕ, MeasureTheory.MemLp (quadVarIncrement W ℱ hℱ H hm hp hq
      (unifGrid T m k) (unifGrid T m (k + 1))) 2 P := fun k =>
    memLp_two_quadVarIncrement W ℱ hℱ H hm hp hq hC0 hCH (unifGrid_nonneg hT.le m k)
      (unifGrid_lt_succ hT hm0 k)
  have hYmem : ∀ k : ℕ, MeasureTheory.MemLp (fun ω => φ (X (unifGrid T m k) ω)
      * quadVarIncrement W ℱ hℱ H hm hp hq (unifGrid T m k)
          (unifGrid T m (k + 1)) ω) 2 P := by
    intro k
    refine MeasureTheory.MemLp.mono ((hζmem k).const_mul Kφ)
      ((hφc.measurable.comp (h.measurable (unifGrid T m k))).aestronglyMeasurable.mul
        (hζmem k).aestronglyMeasurable) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hKφ0]
    exact mul_le_mul_of_nonneg_right (hφbd _) (abs_nonneg _)
  have hsummem : MeasureTheory.MemLp (fun ω => ∑ i ∈ Finset.range m,
      φ (X (unifGrid T m i) ω) * quadVarIncrement W ℱ hℱ H hm hp hq (unifGrid T m i)
          (unifGrid T m (i + 1)) ω) 2 P :=
    MeasureTheory.memLp_finsetSum _ fun i _ => hYmem i
  have hint1 : MeasureTheory.Integrable (fun ω => |∑ i ∈ Finset.range m,
      φ (X (unifGrid T m i) ω) * quadVarIncrement W ℱ hℱ H hm hp hq (unifGrid T m i)
          (unifGrid T m (i + 1)) ω|) P := (hsummem.integrable (by norm_num)).abs
  have hint2 : MeasureTheory.Integrable (fun ω => (∑ i ∈ Finset.range m,
      φ (X (unifGrid T m i) ω) * quadVarIncrement W ℱ hℱ H hm hp hq (unifGrid T m i)
          (unifGrid T m (i + 1)) ω) ^ 2) P := by
    have hmul := hsummem.integrable_mul hsummem
    have hfun : (fun ω => (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
        * quadVarIncrement W ℱ hℱ H hm hp hq (unifGrid T m i)
            (unifGrid T m (i + 1)) ω) ^ 2)
        = (fun ω => ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * quadVarIncrement W ℱ hℱ H hm hp hq (unifGrid T m i)
              (unifGrid T m (i + 1)) ω)
          * fun ω => ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * quadVarIncrement W ℱ hℱ H hm hp hq (unifGrid T m i)
              (unifGrid T m (i + 1)) ω := by
      funext ω
      simp [pow_two]
    rw [hfun]
    exact hmul
  exact ⟨hsummem.integrable (by norm_num),
    integral_abs_le_sqrt_of_integral_sq_le hint1 hint2 hquad⟩

include hCH in
/-- The square of a version's increment splits into the drift square, the cross term, the
compensated square, and the compensator. -/
theorem IsItoVersion.sq_sub_ae
    (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    ∀ᵐ ω ∂P, (X v ω - X u ω) ^ 2
      = (∫ s in Set.Ioc u v, bdrift ω s ∂volume) ^ 2
        + 2 * (∫ s in Set.Ioc u v, bdrift ω s ∂volume)
            * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
              - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω)
        + quadVarIncrement W ℱ hℱ H hm hp hq u v ω
        + ∫ s in Set.Ioc u v, H ω s ^ 2 ∂volume := by
  filter_upwards [h.ae_eq v (hu.trans huv), h.ae_eq u hu] with ω hv hu'
  have hHsq : (∫ s in Set.Icc (0 : ℝ) v, H ω s ^ 2 ∂volume)
      - ∫ s in Set.Icc (0 : ℝ) u, H ω s ^ 2 ∂volume
      = ∫ s in Set.Ioc u v, H ω s ^ 2 ∂volume := by
    refine setIntegral_Icc_sub_Icc (B := C ^ 2)
      ((Measurable.of_uncurry_left hm).pow_const 2) (fun s => ?_) hu huv
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hCH ω s) 2
  rw [hv, hu', itoProcess_sub W ℱ hℱ H hm hp hq X₀ bdrift hbm hB hu huv ω]
  unfold quadVarIncrement
  rw [hHsq]
  ring

include hC0 hCH in
/-- **The weighted quadratic-variation Riemann sum converges in `L¹` at rate `√(T/m)`.** -/
theorem IsItoVersion.integral_abs_quadVarRiemann_sub_le
    (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {φ : ℝ → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hKφ0 : 0 ≤ Kφ) (hφbd : ∀ x, |φ x| ≤ Kφ)
    {L : ℝ} (hL0 : 0 ≤ L) (hφlip : ∀ x y : ℝ, |φ x - φ y| ≤ L * |x - y|)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    MeasureTheory.Integrable (fun ω : Ω => (∑ i ∈ Finset.range m,
          φ (X (unifGrid T m i) ω)
            * (X (unifGrid T m (i + 1)) ω - X (unifGrid T m i) ω) ^ 2)
        - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * H ω s ^ 2 ∂volume) P
      ∧ ∫ ω, |(∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * (X (unifGrid T m (i + 1)) ω - X (unifGrid T m i) ω) ^ 2)
          - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * H ω s ^ 2 ∂volume| ∂P
        ≤ (m : ℝ) * (Kφ * (B * (T / (m : ℝ))) ^ 2)
        + (m : ℝ) * (2 * Kφ * (B * (T / (m : ℝ))) * (C * Real.sqrt (T / (m : ℝ))))
        + Real.sqrt (Kφ ^ 2 * ((2 * (6 + gaussianFourthMoment) + 2) * C ^ 4)
            * ((m : ℝ) * (T / (m : ℝ)) ^ 2))
        + L * C ^ 2 * (T * (B * (T / (m : ℝ)) + C * Real.sqrt (T / (m : ℝ)))) := by
  have hHsqbd : ∀ (ω : Ω) (s : ℝ), |H ω s ^ 2| ≤ C ^ 2 := by
    intro ω s
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hCH ω s) 2
  obtain ⟨hAint, hAle⟩ :=
    h.integral_abs_sum_drift_sq_le hbm hB0 hB hφc hKφ0 hφbd hT hm0
  obtain ⟨hBint, hBle⟩ :=
    h.integral_abs_sum_cross_le hC0 hCH hbm hB0 hB hφc hKφ0 hφbd hT hm0
  obtain ⟨hCint, hCle⟩ := h.integral_abs_sum_quadVar_le hC0 hCH hφc hKφ0 hφbd hT hm0
  obtain ⟨hDint, hDle⟩ := h.integral_abs_frozenRiemann_sub_le hC0 hCH hbm hB0 hB
    (fun ω s => H ω s ^ 2) (hm.pow_const 2) (by positivity) hHsqbd hφc hφbd hL0 hφlip hT hm0
  have hae : ∀ᵐ ω ∂P, ∀ i : ℕ,
      (X (unifGrid T m (i + 1)) ω - X (unifGrid T m i) ω) ^ 2
        = (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift ω s ∂volume) ^ 2
          + 2 * (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift ω s ∂volume)
              * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
                - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω)
          + quadVarIncrement W ℱ hℱ H hm hp hq (unifGrid T m i)
              (unifGrid T m (i + 1)) ω
          + ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
              H ω s ^ 2 ∂volume :=
    MeasureTheory.ae_all_iff.mpr fun i => h.sq_sub_ae hCH hbm hB
      (unifGrid_nonneg hT.le m i) (unifGrid_lt_succ hT hm0 i).le
  have hsplit : (fun ω : Ω => (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * (X (unifGrid T m (i + 1)) ω - X (unifGrid T m i) ω) ^ 2)
        - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * H ω s ^ 2 ∂volume)
      =ᵐ[P] fun ω => (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
                bdrift ω s ∂volume) ^ 2)
          + (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * (2 * (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
                bdrift ω s ∂volume)
              * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
                - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω)))
          + (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * quadVarIncrement W ℱ hℱ H hm hp hq (unifGrid T m i)
                (unifGrid T m (i + 1)) ω)
          + ((∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
              * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
                  H ω s ^ 2 ∂volume)
            - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * H ω s ^ 2 ∂volume) := by
    filter_upwards [hae] with ω hω
    have hterm : ∀ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
        * (X (unifGrid T m (i + 1)) ω - X (unifGrid T m i) ω) ^ 2
        = φ (X (unifGrid T m i) ω)
            * (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
                bdrift ω s ∂volume) ^ 2
          + φ (X (unifGrid T m i) ω)
            * (2 * (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
                bdrift ω s ∂volume)
              * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
                - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω))
          + φ (X (unifGrid T m i) ω)
            * quadVarIncrement W ℱ hℱ H hm hp hq (unifGrid T m i)
                (unifGrid T m (i + 1)) ω
          + φ (X (unifGrid T m i) ω)
            * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
                H ω s ^ 2 ∂volume := by
      intro i _
      rw [hω i]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib]
    ring
  have hsplitabs : (fun ω : Ω => |(∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * (X (unifGrid T m (i + 1)) ω - X (unifGrid T m i) ω) ^ 2)
        - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * H ω s ^ 2 ∂volume|)
      =ᵐ[P] fun ω => |(∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
                bdrift ω s ∂volume) ^ 2)
          + (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * (2 * (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
                bdrift ω s ∂volume)
              * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
                - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω)))
          + (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * quadVarIncrement W ℱ hℱ H hm hp hq (unifGrid T m i)
                (unifGrid T m (i + 1)) ω)
          + ((∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
              * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
                  H ω s ^ 2 ∂volume)
            - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * H ω s ^ 2 ∂volume)| := by
    filter_upwards [hsplit] with ω hω
    rw [hω]
  refine ⟨(((hAint.add hBint).add hCint).add hDint).congr hsplit.symm, ?_⟩
  rw [MeasureTheory.integral_congr_ae hsplitabs]
  exact integral_abs_add_four_le hAint hBint hCint hDint hAle hBle hCle hDle

end QuadVarRiemann

end LevyStochCalc.Brownian.Ito

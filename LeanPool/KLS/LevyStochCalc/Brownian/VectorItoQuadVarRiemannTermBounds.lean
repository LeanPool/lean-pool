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

public import LeanPool.KLS.LevyStochCalc.Brownian.VectorItoTimeRiemann
public import LeanPool.KLS.LevyStochCalc.Brownian.CrossVariationSum
public import LeanPool.KLS.LevyStochCalc.Brownian.PolarisedQuadVar
public import LeanPool.KLS.LevyStochCalc.Probability.AbsMoment

/-!
# Cell sums and the error terms of the quadratic-variation Riemann sum

Summing terms attached to the cells of a uniform grid against weights bounded by `Kw` multiplies
a common bound on their first absolute moments by `N·Kw`. Applied to the increments of two
coordinates of a continuous vector Itô process across a grid of `m` cells, weighted by a bounded
function of the process, this bounds the drift–drift term by `O(1/m)` and the drift–martingale
terms, the compensated products on the diagonal in the Brownian index and the cross terms off
that diagonal by `O(m^{-1/2})`.

## Main statements

* `LevyStochCalc.Brownian.Ito.integral_abs_weighted_cellSum_le` — the `L¹` bound for a weighted
  sum of cell terms with a common first-absolute-moment bound.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_sum_drift_sq_le` — the
  drift–drift term.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_sum_driftCross_le` — a
  drift–martingale term.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section CellSums

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- **`L¹` bound for a weighted sum of cell terms.** With weights bounded by `Kw` and cell terms
whose first absolute moments are all at most `ρ`, the weighted sum has first absolute moment at
most `N·Kw·ρ`. -/
theorem integral_abs_weighted_cellSum_le (N : ℕ) (w R : ℕ → Ω → ℝ)
    (hwm : ∀ i, Measurable (w i)) (hRm : ∀ i, Measurable (R i))
    {Kw : ℝ} (hKw0 : 0 ≤ Kw) (hwb : ∀ (i : ℕ) (ω : Ω), |w i ω| ≤ Kw)
    (hRint : ∀ i, Integrable (fun ω => |R i ω|) P)
    {ρ : ℝ} (hRle : ∀ i, ∫ ω, |R i ω| ∂P ≤ ρ) :
    Integrable (fun ω => ∑ i ∈ Finset.range N, w i ω * R i ω) P
      ∧ ∫ ω, |∑ i ∈ Finset.range N, w i ω * R i ω| ∂P ≤ (N : ℝ) * (Kw * ρ) := by
  have hdom : Integrable (fun ω => ∑ i ∈ Finset.range N, Kw * |R i ω|) P :=
    MeasureTheory.integrable_finsetSum _ fun i _ => (hRint i).const_mul _
  have hmeas : Measurable fun ω => ∑ i ∈ Finset.range N, w i ω * R i ω :=
    Finset.measurable_sum _ fun i _ => (hwm i).mul (hRm i)
  have hpt : ∀ ω, |∑ i ∈ Finset.range N, w i ω * R i ω|
      ≤ ∑ i ∈ Finset.range N, Kw * |R i ω| := by
    intro ω
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hwb i ω) (abs_nonneg _)
  have hint : Integrable (fun ω => ∑ i ∈ Finset.range N, w i ω * R i ω) P := by
    refine hdom.mono hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact (hpt ω).trans (le_abs_self _)
  refine ⟨hint, ?_⟩
  calc ∫ ω, |∑ i ∈ Finset.range N, w i ω * R i ω| ∂P
      ≤ ∫ ω, ∑ i ∈ Finset.range N, Kw * |R i ω| ∂P :=
        MeasureTheory.integral_mono hint.abs hdom hpt
    _ = ∑ i ∈ Finset.range N, Kw * ∫ ω, |R i ω| ∂P := by
        rw [MeasureTheory.integral_finsetSum _ fun i _ => (hRint i).const_mul _]
        exact Finset.sum_congr rfl fun i _ => MeasureTheory.integral_const_mul _ _
    _ ≤ ∑ _i ∈ Finset.range N, Kw * ρ :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hRle i) hKw0
    _ = (N : ℝ) * (Kw * ρ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The squared cell lengths of the uniform grid sum to `T²/m`. -/
theorem sum_unifGrid_sq_diff {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    ∑ i ∈ Finset.range m, (unifGrid T m (i + 1) - unifGrid T m i) ^ 2 = T ^ 2 / (m : ℝ) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hterm : ∀ i ∈ Finset.range m,
      (unifGrid T m (i + 1) - unifGrid T m i) ^ 2 = (T / (m : ℝ)) ^ 2 :=
    fun i _ => by rw [unifGrid_succ_sub hm0 i]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

omit [IsProbabilityMeasure P] in
/-- The first absolute moment of a sum is at most the sum of the bounds. -/
theorem integral_abs_add_le {f g : Ω → ℝ} (hf : Integrable f P) (hg : Integrable g P)
    {a b : ℝ} (ha : ∫ ω, |f ω| ∂P ≤ a) (hb : ∫ ω, |g ω| ∂P ≤ b) :
    ∫ ω, |f ω + g ω| ∂P ≤ a + b := by
  calc ∫ ω, |f ω + g ω| ∂P ≤ ∫ ω, (|f ω| + |g ω|) ∂P :=
        MeasureTheory.integral_mono (hf.add hg).abs (hf.abs.add hg.abs)
          (fun ω => abs_add_le _ _)
    _ = (∫ ω, |f ω| ∂P) + ∫ ω, |g ω| ∂P := MeasureTheory.integral_add hf.abs hg.abs
    _ ≤ a + b := add_le_add ha hb

omit [IsProbabilityMeasure P] in
/-- The first absolute moment of a finite sum is at most the sum of the bounds. -/
theorem integral_abs_finsetSum_le {ι : Type*} (s : Finset ι) (F : ι → Ω → ℝ)
    (hF : ∀ j ∈ s, Integrable (F j) P) (c : ι → ℝ) (hc : ∀ j ∈ s, ∫ ω, |F j ω| ∂P ≤ c j) :
    ∫ ω, |∑ j ∈ s, F j ω| ∂P ≤ ∑ j ∈ s, c j := by
  have hsum : Integrable (fun ω => ∑ j ∈ s, F j ω) P :=
    MeasureTheory.integrable_finsetSum _ hF
  have habs : Integrable (fun ω => ∑ j ∈ s, |F j ω|) P :=
    MeasureTheory.integrable_finsetSum _ fun j hj => (hF j hj).abs
  calc ∫ ω, |∑ j ∈ s, F j ω| ∂P ≤ ∫ ω, ∑ j ∈ s, |F j ω| ∂P :=
        MeasureTheory.integral_mono hsum.abs habs fun ω => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ s, ∫ ω, |F j ω| ∂P :=
        MeasureTheory.integral_finsetSum _ fun j hj => (hF j hj).abs
    _ ≤ ∑ j ∈ s, c j := Finset.sum_le_sum hc

end CellSums

section VectorQuadVar

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ m k, Measurable (Function.uncurry (H m k))}
  {hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k)}
  {hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)

/-- **The drift–drift term is `O(1/m)`.** -/
theorem IsVectorItoVersion.integral_abs_sum_drift_sq_le
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) (p q : Fin n)
    {φ : (Fin n → ℝ) → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hKφ0 : 0 ≤ Kφ)
    (hφbd : ∀ x, |φ x| ≤ Kφ) {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω => ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
        * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
          * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
              bdrift q ω s ∂volume)) P
      ∧ ∫ ω, |∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
            * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
                bdrift q ω s ∂volume)| ∂P
        ≤ (m : ℝ) * (Kφ * (B * (T / (m : ℝ))) ^ 2) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hTm0 : (0 : ℝ) ≤ T / (m : ℝ) := (div_pos hT hm').le
  have hDbd : ∀ (r : Fin n) (ω : Ω) (i : ℕ),
      |∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift r ω s ∂volume|
        ≤ B * (T / (m : ℝ)) := by
    intro r ω i
    have hle := abs_setIntegral_Ioc_le (Measurable.of_uncurry_left (hbm r)) (hB r ω)
      (unifGrid_lt_succ hT hm0 i).le
    rwa [unifGrid_succ_sub hm0 i] at hle
  have hRm : ∀ i : ℕ, Measurable fun ω : Ω =>
      (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
        * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift q ω s ∂volume :=
    fun i => (measurable_setIntegral_Ioc (hbm p) _ _).mul
      (measurable_setIntegral_Ioc (hbm q) _ _)
  have hRb : ∀ (i : ℕ) (ω : Ω),
      |(∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
        * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift q ω s ∂volume|
      ≤ (B * (T / (m : ℝ))) ^ 2 := by
    intro i ω
    rw [abs_mul, pow_two]
    exact mul_le_mul (hDbd p ω i) (hDbd q ω i) (abs_nonneg _) (by positivity)
  have hRdata : ∀ i : ℕ, Integrable (fun ω : Ω =>
        |(∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
          * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift q ω s ∂volume|) P
      ∧ ∫ ω, |(∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
              bdrift p ω s ∂volume)
            * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
                bdrift q ω s ∂volume| ∂P
        ≤ (B * (T / (m : ℝ))) ^ 2 := by
    intro i
    obtain ⟨hi, hle⟩ := integral_abs_le_of_bounded (P := P) (hRm i) (by positivity) (hRb i ·)
    exact ⟨hi.abs, hle⟩
  exact integral_abs_weighted_cellSum_le m (fun i ω => φ (X (unifGrid T m i) ω)) _
    (fun i => hφc.measurable.comp (h.measurable (unifGrid T m i))) hRm hKφ0
    (fun i ω => hφbd _) (fun i => (hRdata i).1) (fun i => (hRdata i).2)

include hC0 hCH in
/-- **A drift–martingale term is `O(m^{-1/2})`.** -/
theorem IsVectorItoVersion.integral_abs_sum_driftCross_le
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) (p q : Fin n)
    {φ : (Fin n → ℝ) → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hKφ0 : 0 ≤ Kφ)
    (hφbd : ∀ x, |φ x| ≤ Kφ) {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω => ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
        * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
          * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
            - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω))) P
      ∧ ∫ ω, |∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
            * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
              - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω))| ∂P
        ≤ (m : ℝ) * (Kφ * (B * (T / (m : ℝ)) * ((d : ℝ) * (C * Real.sqrt (T / (m : ℝ)))))) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hTm0 : (0 : ℝ) ≤ T / (m : ℝ) := (div_pos hT hm').le
  have hDbd : ∀ (ω : Ω) (i : ℕ),
      |∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume|
        ≤ B * (T / (m : ℝ)) := by
    intro ω i
    have hle := abs_setIntegral_Ioc_le (Measurable.of_uncurry_left (hbm p)) (hB p ω)
      (unifGrid_lt_succ hT hm0 i).le
    rwa [unifGrid_succ_sub hm0 i] at hle
  have hMdata : ∀ i : ℕ,
      Integrable (fun ω : Ω =>
          |vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
            - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω|) P
        ∧ ∫ ω, |vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
              - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω| ∂P
            ≤ (d : ℝ) * (C * Real.sqrt (T / (m : ℝ))) := by
    intro i
    obtain ⟨hint, hle⟩ := integral_abs_vectorItoMartingale_sub_le W ℱ hcoord H hHm hHp hHs
      hC0 hCH q (unifGrid_nonneg hT.le m i) (unifGrid_lt_succ hT hm0 i)
    rw [unifGrid_succ_sub hm0 i] at hle
    exact ⟨hint, hle⟩
  have hRm : ∀ i : ℕ, Measurable fun ω : Ω =>
      (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
        * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
          - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω) :=
    fun i => (measurable_setIntegral_Ioc (hbm p) _ _).mul
      ((measurable_vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1))).sub
        (measurable_vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i)))
  have hRdata : ∀ i : ℕ, Integrable (fun ω : Ω =>
        |(∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
          * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
            - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω)|) P
      ∧ ∫ ω, |(∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
            * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
              - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω)| ∂P
        ≤ B * (T / (m : ℝ)) * ((d : ℝ) * (C * Real.sqrt (T / (m : ℝ)))) := by
    intro i
    have hpt : ∀ ω : Ω,
        |(∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
          * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
            - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω)|
        ≤ B * (T / (m : ℝ))
          * |vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
            - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω| := by
      intro ω
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hDbd ω i) (abs_nonneg _)
    have hdom : Integrable (fun ω : Ω => B * (T / (m : ℝ))
        * |vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
          - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω|) P :=
      (hMdata i).1.const_mul _
    have hint : Integrable (fun ω : Ω =>
        |(∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
          * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
            - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω)|) P := by
      refine hdom.mono (continuous_abs.measurable.comp (hRm i)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
      exact (hpt ω).trans (le_abs_self _)
    refine ⟨hint, ?_⟩
    calc ∫ ω, |(∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
          * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
            - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω)| ∂P
        ≤ ∫ ω, B * (T / (m : ℝ))
            * |vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
              - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω| ∂P :=
          MeasureTheory.integral_mono hint hdom hpt
      _ = B * (T / (m : ℝ))
            * ∫ ω, |vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
              - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω| ∂P :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ B * (T / (m : ℝ)) * ((d : ℝ) * (C * Real.sqrt (T / (m : ℝ)))) :=
          mul_le_mul_of_nonneg_left (hMdata i).2 (by positivity)
  exact integral_abs_weighted_cellSum_le m (fun i ω => φ (X (unifGrid T m i) ω)) _
    (fun i => hφc.measurable.comp (h.measurable (unifGrid T m i))) hRm hKφ0
    (fun i ω => hφbd _) (fun i => (hRdata i).1) (fun i => (hRdata i).2)

include hC0 hCH in
/-- **The compensated products on the diagonal in the Brownian index sum to `O(m^{-1/2})`.** -/
theorem IsVectorItoVersion.integral_abs_sum_polarQuadVar_le
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) (p q : Fin n) (k : Fin d)
    (hma : Measurable (Function.uncurry fun ω s => H p k ω s + H q k ω s))
    (hpa : Probability.ProgressivelyMeasurable ℱ fun ω s => H p k ω s + H q k ω s)
    (hqa : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s + H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {φ : (Fin n → ℝ) → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hKφ0 : 0 ≤ Kφ)
    (hφbd : ∀ x, |φ x| ≤ Kφ) {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω => ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
        * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
            (hHp p k) (hHp q k) (hHs p k) (hHs q k)
            (unifGrid T m i) (unifGrid T m (i + 1)) ω) P
      ∧ ∫ ω, |∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
              (hHp p k) (hHp q k) (hHs p k) (hHs q k)
              (unifGrid T m i) (unifGrid T m (i + 1)) ω| ∂P
        ≤ Real.sqrt (Kφ ^ 2 * (3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4))
          * (T ^ 2 / (m : ℝ))) := by
  have h0 : (0 : ℝ) ≤ unifGrid T m 0 := le_of_eq (unifGrid_zero T m).symm
  have hgrid : ∀ i : ℕ, unifGrid T m i < unifGrid T m (i + 1) := unifGrid_lt_succ hT hm0
  have hg : ∀ i : ℕ, @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont (unifGrid T m i))
      (fun ω => φ (X (unifGrid T m i) ω)) := fun i =>
    (hφc.comp_stronglyMeasurable (h.adapted (unifGrid T m i))).mono (ℱ.le_rightCont _)
  have hζmem : ∀ i : ℕ, MemLp (polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k)
      (hHm p k) (hHm q k) (hHp p k) (hHp q k) (hHs p k) (hHs q k)
      (unifGrid T m i) (unifGrid T m (i + 1))) 2 P := fun i =>
    memLp_two_polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
      (hHp p k) (hHp q k) (hHs p k) (hHs q k) hma hpa hqa hC0 (hCH p k) (hCH q k)
      (unifGrid_nonneg hT.le m i) (hgrid i)
  have hζmeas : ∀ i : ℕ, Measurable (polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k)
      (hHm p k) (hHm q k) (hHp p k) (hHp q k) (hHs p k) (hHs q k)
      (unifGrid T m i) (unifGrid T m (i + 1))) := fun i =>
    ((stronglyMeasurable_polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k)
      (hHm q k) (hHp p k) (hHp q k) (hHs p k) (hHs q k) (hgrid i).le).mono
        (ℱ.rightCont.le _)).measurable
  have hYmem : ∀ i : ℕ, MemLp (fun ω => φ (X (unifGrid T m i) ω)
      * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
          (hHp p k) (hHp q k) (hHs p k) (hHs q k)
          (unifGrid T m i) (unifGrid T m (i + 1)) ω) 2 P := by
    intro i
    refine MeasureTheory.MemLp.mono ((hζmem i).const_mul Kφ)
      (((hφc.measurable.comp (h.measurable (unifGrid T m i))).mul
        (hζmeas i)).aestronglyMeasurable) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hKφ0]
    exact mul_le_mul_of_nonneg_right (hφbd _) (abs_nonneg _)
  have hSmem := memLp_finsetSum (Finset.range m) fun i _ => hYmem i
  have hbound := integral_sq_weighted_polarQuadVarSum_le (W.W k) ℱ (hcoord k) (H p k) (H q k)
    (hHm p k) (hHm q k) (hHp p k) (hHp q k) (hHs p k) (hHs q k) hma hpa hqa hC0
    (hCH p k) (hCH q k) (unifGrid T m) h0 hgrid (fun i ω => φ (X (unifGrid T m i) ω)) hg
    hKφ0 (fun i ω => hφbd _) m
  rw [sum_unifGrid_sq_diff hT hm0] at hbound
  exact ⟨hSmem.integrable (by norm_num),
    integral_abs_le_sqrt_of_integral_sq_le ((hSmem.integrable (by norm_num)).abs)
      hSmem.integrable_sq hbound⟩

include hC0 hCH in
/-- **The cross terms off the diagonal in the Brownian index sum to `O(m^{-1/2})`.** -/
theorem IsVectorItoVersion.integral_abs_sum_offDiagCross_le
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (p q : Fin n)
    {k l : Fin d} (hkl : k ≠ l)
    {φ : (Fin n → ℝ) → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hKφ0 : 0 ≤ Kφ)
    (hφbd : ∀ x, |φ x| ≤ Kφ) {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω => ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
        * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l) (hHs q l)
            k l (unifGrid T m i) (unifGrid T m (i + 1)) ω) P
      ∧ ∫ ω, |∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l) (hHs q l)
              k l (unifGrid T m i) (unifGrid T m (i + 1)) ω| ∂P
        ≤ Real.sqrt (Kφ ^ 2 * ((6 + gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2)
          * (T ^ 2 / (m : ℝ))) := by
  have h0 : (0 : ℝ) ≤ unifGrid T m 0 := le_of_eq (unifGrid_zero T m).symm
  have hgrid : ∀ i : ℕ, unifGrid T m i < unifGrid T m (i + 1) := unifGrid_lt_succ hT hm0
  have hg : ∀ i : ℕ, @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ (unifGrid T m i))
      (fun ω => φ (X (unifGrid T m i) ω)) := fun i =>
    hφc.comp_stronglyMeasurable (h.adapted (unifGrid T m i))
  have hζmem : ∀ i : ℕ, MemLp (crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k)
      (hHm q l) (hHp q l) (hHs q l) k l (unifGrid T m i) (unifGrid T m (i + 1))) 2 P := fun i =>
    memLp_two_crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
      (hHs q l) hC0 (hCH p k) hC0 (hCH q l) k l (unifGrid_nonneg hT.le m i) (hgrid i)
  have hζmeas : ∀ i : ℕ, Measurable (crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k)
      (hHm q l) (hHp q l) (hHs q l) k l (unifGrid T m i) (unifGrid T m (i + 1))) := fun i =>
    measurable_crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
      (hHs q l) k l _ _
  have hYmem : ∀ i : ℕ, MemLp (fun ω => φ (X (unifGrid T m i) ω)
      * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l) (hHs q l)
          k l (unifGrid T m i) (unifGrid T m (i + 1)) ω) 2 P := by
    intro i
    refine MeasureTheory.MemLp.mono ((hζmem i).const_mul Kφ)
      (((hφc.measurable.comp (h.measurable (unifGrid T m i))).mul
        (hζmeas i)).aestronglyMeasurable) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hKφ0]
    exact mul_le_mul_of_nonneg_right (hφbd _) (abs_nonneg _)
  have hSmem := memLp_finsetSum (Finset.range m) fun i _ => hYmem i
  have hbound := integral_sq_weighted_crossSum_le W hcoord (hHm p k) (hHp p k) (hHs p k)
    (hHm q l) (hHp q l) (hHs q l) hC0 (hCH p k) hC0 (hCH q l) hkl (unifGrid T m) h0 hgrid
    (fun i ω => φ (X (unifGrid T m i) ω)) hg hKφ0 (fun i ω => hφbd _) m
  rw [sum_unifGrid_sq_diff hT hm0] at hbound
  exact ⟨hSmem.integrable (by norm_num),
    integral_abs_le_sqrt_of_integral_sq_le ((hSmem.integrable (by norm_num)).abs)
      hSmem.integrable_sq hbound⟩

end VectorQuadVar

end LevyStochCalc.Brownian.Ito

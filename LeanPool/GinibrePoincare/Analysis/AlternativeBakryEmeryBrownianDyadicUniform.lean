/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryBrownianDyadicUniform.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianDyadicCoordinates
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
/-!
# Alternative Bakry Emery Brownian dyadic uniform

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryBrownianDyadicPath_aemeasurable`, `bakryBrownianDyadicPath_endpoints`.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous paths `C(Icc 0 1, ℝ)`, used locally in this file. -/
local instance bakryBrownianDyadicUniformPathMeasurable :
    MeasurableSpace C(Icc (0 : ℝ) 1, ℝ) := borel _
local instance bakryBrownianDyadicUniform_pathBorel :
    BorelSpace C(Icc (0 : ℝ) 1, ℝ) := ⟨rfl⟩

/-- The identity path `t ↦ t` on the unit interval, as a continuous map. -/
def bakryBrownianDyadicLinearPath : C(Icc (0 : ℝ) 1, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩

/-- The `N`-th partial sum of the Faber–Schauder series of Brownian motion on `[0, 1]`: the
linear term `ω none • t` plus the dyadic levels `n < N` with coefficients from `ω`. -/
def bakryBrownianDyadicPartialPath (N : ℕ) (ω : BakryBrownianDyadicSample) : C(Icc (0 : ℝ) 1, ℝ) :=
  ω none • bakryBrownianDyadicLinearPath + ∑ n ∈ Finset.range N,
    bakryBrownianDyadicLevel n (fun k => ω (some ⟨n, k⟩))

/-- The dyadic Brownian path on `[0, 1]`: the linear term `ω none • t` plus the `tsum` in
`C(Icc 0 1, ℝ)` of all dyadic levels of the Faber–Schauder series. -/
def bakryBrownianDyadicPath (ω : BakryBrownianDyadicSample) : C(Icc (0 : ℝ) 1, ℝ) :=
  ω none • bakryBrownianDyadicLinearPath + ∑' n,
    bakryBrownianDyadicLevel n (fun k => ω (some ⟨n, k⟩))

/-- The fourth absolute moment `∫⁻ |x|^4` of the standard Gaussian `gaussianReal 0 1`. -/
def bakryBrownianDyadicFourthMoment : ℝ≥0∞ :=
  ∫⁻ x : ℝ, ENNReal.ofReal (|x|^4) ∂gaussianReal 0 1

theorem bakryBrownianDyadicFourthMoment_ne_top : bakryBrownianDyadicFourthMoment ≠ ∞ := by
  have hI : Integrable (fun x : ℝ => |x|^4) (gaussianReal 0 1) := by
    simpa only [Real.norm_eq_abs, id_eq] using
      (memLp_id_gaussianReal (μ := 0) (v := 1) (4 : ℝ≥0)).integrable_norm_pow (p := 4) (by decide)
  unfold bakryBrownianDyadicFourthMoment
  rw [← ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall (fun x => by
      positivity))]
  exact ENNReal.ofReal_ne_top

theorem bakryBrownianDyadic_coordinate_tail (i : BakryBrownianDyadicIndex) (A : ℝ) (hA : 0 < A) :
    bakryBrownianDyadicMeasure {ω | A ≤ |ω i|} ≤
      bakryBrownianDyadicFourthMoment / ENNReal.ofReal (A^4) := by
  let f : BakryBrownianDyadicSample → ℝ≥0∞ := fun ω => ENNReal.ofReal (|ω i|^4)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hs : {ω : BakryBrownianDyadicSample | A ≤ |ω i|} ⊆
      {ω | ENNReal.ofReal (A^4) ≤ f ω} := by
    intro ω hω
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hA.le hω 4)
  have hi : (∫⁻ ω, f ω ∂bakryBrownianDyadicMeasure) = bakryBrownianDyadicFourthMoment := by
    exact ((bakryBrownianDyadic_coordinate_law i).lintegral_comp
      (by fun_prop : Measurable (fun x : ℝ => ENNReal.ofReal (|x|^4))).aemeasurable)
  exact (measure_mono hs).trans (by
    rw [← hi]
    exact meas_ge_le_lintegral_div hf.aemeasurable (by positivity) ENNReal.ofReal_ne_top)

/-- The event that some level-`n` coefficient of the sample has absolute value at least
`(4/3)^n`. -/
def bakryBrownianDyadicBadLevel (n : ℕ) : Set BakryBrownianDyadicSample :=
  {ω | ∃ k : Fin (2^n), (4/3 : ℝ)^n ≤ |ω (some ⟨n, k⟩)|}

theorem bakryBrownianDyadicBadLevel_bound (n : ℕ) :
    bakryBrownianDyadicMeasure (bakryBrownianDyadicBadLevel n) ≤
      ENNReal.ofReal (bakryBrownianDyadicFourthMoment.toReal * (81/128 : ℝ)^n) := by
  have hset : bakryBrownianDyadicBadLevel n =
      ⋃ k : Fin (2^n), {ω : BakryBrownianDyadicSample | (4/3 : ℝ)^n ≤ |ω (some ⟨n, k⟩)|} := by
    ext ω
    simp [bakryBrownianDyadicBadLevel]
  rw [hset]
  calc
    bakryBrownianDyadicMeasure (⋃ k : Fin (2^n), {ω | (4/3 : ℝ)^n ≤ |ω (some ⟨n, k⟩)|}) ≤
      ∑ k : Fin (2^n), bakryBrownianDyadicMeasure {ω | (4/3 : ℝ)^n ≤ |ω (some ⟨n, k⟩)|} :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _k : Fin (2^n), bakryBrownianDyadicFourthMoment / ENNReal.ofReal (((4/3 : ℝ)^n)^4) :=
      Finset.sum_le_sum (fun k _ => bakryBrownianDyadic_coordinate_tail (some ⟨n, k⟩) _ (by
          positivity))
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← ENNReal.ofReal_toReal bakryBrownianDyadicFourthMoment_ne_top,
        ← ENNReal.ofReal_natCast,← ENNReal.ofReal_div_of_pos (by positivity),
        ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2^n : ℕ))]
      congr 1
      rw [Nat.cast_pow, Nat.cast_ofNat, ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
      have he : (2 : ℝ)^n / (((4/3 : ℝ)^n)^4) = (81/128 : ℝ)^n := by
        rw [← pow_mul, Nat.mul_comm n 4, pow_mul, ← div_pow]
        norm_num
      rw [← mul_div_assoc, mul_comm ((2 : ℝ)^n) _, mul_div_assoc, he]

theorem bakryBrownianDyadic_eventually_bounded :
    ∀ᵐ ω ∂bakryBrownianDyadicMeasure, ∀ᶠ n in atTop,
      ∀ k : Fin (2^n), |ω (some ⟨n, k⟩)| ≤ (4/3 : ℝ)^n := by
  have hS : Summable (fun n : ℕ => bakryBrownianDyadicFourthMoment.toReal * (81/128 : ℝ)^n) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 81/128) (by norm_num)).mul_left _
  have hFinite : (∑' n, ENNReal.ofReal
      (bakryBrownianDyadicFourthMoment.toReal * (81/128 : ℝ)^n)) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hS]
    exact ENNReal.ofReal_ne_top
  have hBad : (∑' n, bakryBrownianDyadicMeasure (bakryBrownianDyadicBadLevel n)) ≠ ∞ :=
    ne_top_of_le_ne_top hFinite (ENNReal.tsum_le_tsum bakryBrownianDyadicBadLevel_bound)
  filter_upwards [ae_eventually_notMem hBad] with ω hω
  filter_upwards [hω] with n hn
  intro k
  apply le_of_lt
  by_contra hh
  exact hn ⟨k, le_of_not_gt hh⟩

theorem bakryBrownianDyadic_series_summable :
    ∀ᵐ ω ∂bakryBrownianDyadicMeasure,
      Summable (fun n => bakryBrownianDyadicLevel n (fun k => ω (some ⟨n, k⟩))) := by
  have hr : (4/3 : ℝ)/Real.sqrt 2 < 1 := by
    have hsq : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
    have hn := Real.sqrt_nonneg (2 : ℝ)
    have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    rw [div_lt_one hpos]
    nlinarith
  have hG : Summable (fun n : ℕ => ((4/3 : ℝ)/Real.sqrt 2)^n / 2) :=
    (summable_geometric_of_lt_one (by positivity) hr).div_const 2
  filter_upwards [bakryBrownianDyadic_eventually_bounded] with ω hω
  apply hG.of_norm_bounded_eventually_nat
  filter_upwards [hω] with n hn
  have he := bakryBrownianDyadicLevel_norm_le n (fun k => ω (some ⟨n, k⟩)) ((4/3 : ℝ)^n)
    (by positivity) hn
  have hpow : (1/Real.sqrt 2)^n*(4/3 : ℝ)^n = ((4/3 : ℝ)/Real.sqrt 2)^n := by
    rw [← mul_pow]
    congr 1
    ring
  simpa only [hpow] using he

theorem bakryBrownianDyadicPartialPath_tendsto :
    ∀ᵐ ω ∂bakryBrownianDyadicMeasure,
      Tendsto (fun N => bakryBrownianDyadicPartialPath N ω) atTop
        (𝓝 (bakryBrownianDyadicPath ω)) := by
  filter_upwards [bakryBrownianDyadic_series_summable] with ω hω
  exact tendsto_const_nhds.add hω.hasSum.tendsto_sum_nat

theorem bakryBrownianDyadicPartialPath_measurable (N : ℕ) :
    Measurable (bakryBrownianDyadicPartialPath N) := by
  have hc : Continuous (bakryBrownianDyadicPartialPath N) := by
    unfold bakryBrownianDyadicPartialPath bakryBrownianDyadicLevel
    fun_prop
  exact hc.measurable

theorem bakryBrownianDyadicPath_aemeasurable :
    AEMeasurable bakryBrownianDyadicPath bakryBrownianDyadicMeasure :=
  aemeasurable_of_tendsto_metrizable_ae' (fun N =>
    (bakryBrownianDyadicPartialPath_measurable N).aemeasurable)
    bakryBrownianDyadicPartialPath_tendsto

theorem bakryBrownianDyadicPath_endpoints (ω : BakryBrownianDyadicSample) :
    bakryBrownianDyadicPath ω ⟨0, by norm_num, by norm_num⟩ = 0 ∧
    bakryBrownianDyadicPath ω ⟨1, by norm_num, by norm_num⟩ = ω none := by
  have ht0 (n : ℕ) (k : Fin (2^n)) :
      bakryBrownianDyadicTent n k ⟨0, by norm_num, by norm_num⟩ = 0 := by
    unfold bakryBrownianDyadicTent
    simp only [ContinuousMap.coe_mk, mul_zero, zero_sub]
    apply max_eq_left
    exact (min_le_left _ _).trans (neg_nonpos.mpr (Nat.cast_nonneg _))
  have ht1 (n : ℕ) (k : Fin (2^n)) :
      bakryBrownianDyadicTent n k ⟨1, by norm_num, by norm_num⟩ = 0 := by
    unfold bakryBrownianDyadicTent
    simp only [ContinuousMap.coe_mk, mul_one]
    apply max_eq_left
    have hk : ((k.val+1 : ℕ) : ℝ) ≤ (2 : ℝ)^n := by exact_mod_cast k.isLt
    exact (min_le_right _ _).trans (sub_nonpos.mpr hk)
  have he (t : Icc (0 : ℝ) 1) (ht : ∀ n k, bakryBrownianDyadicTent n k t = 0) :
      (∑' n, bakryBrownianDyadicLevel n (fun k => ω (some ⟨n, k⟩))) t = 0 := by
    by_cases hS : Summable (fun n => bakryBrownianDyadicLevel n (fun k => ω (some ⟨n, k⟩)))
    · have hh := (ContinuousMap.evalCLM (R := ℝ) t).map_tsum hS
      change (∑' n, bakryBrownianDyadicLevel n (fun k => ω (some ⟨n, k⟩))) t = _ at hh
      rw [hh]
      simp [bakryBrownianDyadicLevel, ht]
    · rw [tsum_eq_zero_of_not_summable hS]
      rfl
  constructor
  · simp [bakryBrownianDyadicPath, bakryBrownianDyadicLinearPath, he _ ht0]
  · simp [bakryBrownianDyadicPath, bakryBrownianDyadicLinearPath, he _ ht1]

end
end GinibrePoincare

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoProcess
public import LeanPool.KLS.LevyStochCalc.Brownian.RiemannSum
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoIncrementMoment

/-!
# The uniform grid and the third-moment remainder

The uniform partition of `[0, T]` into `m` cells, and the bound it gives for the sum of third
absolute moments of the increments of an Itô process — the size of the Taylor remainder in
Itô's formula.

## Main statements

* `LevyStochCalc.Brownian.Ito.unifGrid` — the uniform grid on `[0, T]`.
* `LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid` — the simple integrand carried by
  the uniform grid.
* `LevyStochCalc.Brownian.Ito.sum_integral_abs_sub_pow_three_le` — the sum of third absolute
  moments of the Itô-integral increments across the grid, of order `m^{-1/2}`.
* `LevyStochCalc.Brownian.Ito.sum_integral_abs_itoIncrement_pow_three_le` — the same for the
  increments of a full Itô process, drift included.
* `LevyStochCalc.Brownian.Ito.tendsto_riemann_weighted_unifGrid` — the Riemann sums of a
  continuous weight against a bounded density converge as the grid refines.
* `LevyStochCalc.Brownian.Ito.exists_unifGrid_cell` — every time in `(0, T]` lies in a cell.
* `LevyStochCalc.Brownian.Ito.abs_ofUnifGrid_eval_sub_le` — the grid step weight is within the
  weight's modulus of continuity at the mesh.
* `LevyStochCalc.Brownian.Ito.lintegral_sq_sub_le_of_bound` — a uniform pathwise bound on
  `(0, T]` gives the `L²` distance over the window.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The uniform grid on `[0, T]` with `m` cells. -/
noncomputable def unifGrid (T : ℝ) (m : ℕ) (i : ℕ) : ℝ := (i : ℝ) * T / (m : ℝ)

@[simp] theorem unifGrid_zero (T : ℝ) (m : ℕ) : unifGrid T m 0 = 0 := by simp [unifGrid]

theorem unifGrid_self {T : ℝ} {m : ℕ} (hm : m ≠ 0) : unifGrid T m m = T := by
  rw [unifGrid]
  field_simp

theorem unifGrid_succ_sub {T : ℝ} {m : ℕ} (hm : m ≠ 0) (i : ℕ) :
    unifGrid T m (i + 1) - unifGrid T m i = T / (m : ℝ) := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [unifGrid, unifGrid]
  push_cast
  field_simp
  ring

theorem unifGrid_nonneg {T : ℝ} (hT : 0 ≤ T) (m i : ℕ) : 0 ≤ unifGrid T m i := by
  rw [unifGrid]
  positivity

theorem unifGrid_lt_succ {T : ℝ} (hT : 0 < T) {m : ℕ} (hm : m ≠ 0) (i : ℕ) :
    unifGrid T m i < unifGrid T m (i + 1) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  have h := unifGrid_succ_sub (T := T) hm i
  have : 0 < T / (m : ℝ) := div_pos hT hm'
  linarith

theorem unifGrid_le {T : ℝ} (hT : 0 ≤ T) {m i : ℕ} (hi : i ≤ m) (hm : m ≠ 0) :
    unifGrid T m i ≤ T := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  rw [unifGrid, div_le_iff₀ hm']
  have : (i : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hi
  nlinarith


/-- Every time in `(0, T]` lies in exactly one cell of the uniform grid. -/
theorem exists_unifGrid_cell {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) {s : ℝ}
    (hs : 0 < s) (hsT : s ≤ T) :
    ∃ i : ℕ, i < m ∧ unifGrid T m i < s ∧ s ≤ unifGrid T m (i + 1) := by
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  set x : ℝ := s * (m : ℝ) / T with hxdef
  have hx0 : 0 < x := by rw [hxdef]; positivity
  have hxm : x ≤ (m : ℝ) := by
    rw [hxdef, div_le_iff₀ hT]
    nlinarith [hmR.le]
  set k : ℕ := ⌈x⌉₊ with hkdef
  have hk1 : 1 ≤ k := Nat.ceil_pos.mpr hx0
  have hkm : k ≤ m := Nat.ceil_le.mpr (by exact_mod_cast hxm)
  refine ⟨k - 1, by omega, ?_, ?_⟩
  · have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      have : (1 : ℕ) ≤ k := hk1
      push_cast [Nat.cast_sub this]
      ring
    rw [unifGrid, hcast, div_lt_iff₀ hmR]
    have hlt : (k : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0.le
    have hxs : x * T = s * (m : ℝ) := by
      rw [hxdef]; field_simp
    nlinarith [hT, hmR]
  · have hcast : (((k - 1 : ℕ) + 1 : ℕ) : ℝ) = (k : ℝ) := by
      have : (1 : ℕ) ≤ k := hk1
      push_cast [Nat.cast_sub this]
      ring
    rw [unifGrid, hcast, le_div_iff₀ hmR]
    have hle : x ≤ (k : ℝ) := Nat.le_ceil x
    have hxs : x * T = s * (m : ℝ) := by
      rw [hxdef]; field_simp
    nlinarith [hT, hmR]

/-- The simple integrand on the uniform grid of `[0, T]` with the given cell coefficients. -/
noncomputable def SimplePredictable.ofUnifGrid {T : ℝ} (hT : 0 < T) {m : ℕ} (hm : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i)) : SimplePredictable Ω T where
  N := m
  partition := fun i => unifGrid T m (i : ℕ)
  partition_zero := by simp
  partition_le_T := le_of_eq (by simpa using unifGrid_self (T := T) hm)
  partition_strictMono := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    simpa using unifGrid_lt_succ hT hm (i : ℕ)
  ξ := ξ
  ξ_bounded := hbdd
  ξ_measurable := hmeas

@[simp] theorem SimplePredictable.ofUnifGrid_partition {T : ℝ} (hT : 0 < T) {m : ℕ} (hm : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i)) (i : Fin (m + 1)) :
    (SimplePredictable.ofUnifGrid hT hm ξ hbdd hmeas).partition i = unifGrid T m (i : ℕ) := rfl

@[simp] theorem SimplePredictable.ofUnifGrid_xi {T : ℝ} (hT : 0 < T) {m : ℕ} (hm : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i)) (i : Fin m) :
    (SimplePredictable.ofUnifGrid hT hm ξ hbdd hmeas).ξ i = ξ i := rfl

theorem SimplePredictable.ofUnifGrid_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i))
    (hadapt : ∀ i : Fin m, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (unifGrid T m (i : ℕ))) (ξ i)) :
    ∀ i : Fin (SimplePredictable.ofUnifGrid hT hm ξ hbdd hmeas).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ ((SimplePredictable.ofUnifGrid hT hm ξ hbdd hmeas).partition i.castSucc))
        ((SimplePredictable.ofUnifGrid hT hm ξ hbdd hmeas).ξ i) := hadapt

/-- The grid integrand evaluates to the cell coefficient on each cell. -/
theorem SimplePredictable.ofUnifGrid_eval {T : ℝ} (hT : 0 < T) {m : ℕ} (hm : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i)) (i : Fin m) {s : ℝ}
    (hs : unifGrid T m (i : ℕ) < s ∧ s ≤ unifGrid T m ((i : ℕ) + 1)) (ω : Ω) :
    (SimplePredictable.ofUnifGrid hT hm ξ hbdd hmeas).eval s ω = ξ i ω :=
  (SimplePredictable.ofUnifGrid hT hm ξ hbdd hmeas).eval_of_mem_Ioc i hs ω

section ThirdMomentSum

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hℱ hC0 hCH in
/-- **The third absolute moments of the Itô-integral increments across a uniform grid sum to
`O(m^{-1/2})`.** -/
theorem sum_integral_abs_sub_pow_three_le {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    ∑ i ∈ Finset.range m,
        ∫ ω, |stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω| ^ 3 ∂P
      ≤ (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2 * (T * Real.sqrt (T / (m : ℝ))) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hstep : ∀ i : ℕ, unifGrid T m (i + 1) - unifGrid T m i = T / (m : ℝ) :=
    unifGrid_succ_sub hm0
  have hK0 : (0 : ℝ) ≤ (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2 := by
    have := gaussianFourthMoment_nonneg
    have h1 : (0 : ℝ) ≤ (6 + gaussianFourthMoment) * C ^ 4 :=
      mul_nonneg (by linarith) (by positivity)
    have h2 : (0 : ℝ) ≤ C ^ 2 := sq_nonneg C
    linarith
  have hterm : ∀ i ∈ Finset.range m,
      ∫ ω, |stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω| ^ 3 ∂P
        ≤ (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
          * (T / (m : ℝ) * Real.sqrt (T / (m : ℝ))) := by
    intro i _
    have h := (integral_abs_sub_pow_three_le W ℱ hℱ H hm hp hq hC0 hCH
      (unifGrid_nonneg hT.le m i) (unifGrid_lt_succ hT hm0 i)).2
    rwa [hstep i] at h
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hTm : (m : ℝ) * (T / (m : ℝ)) = T := by field_simp
  calc (m : ℝ) * ((C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
        * (T / (m : ℝ) * Real.sqrt (T / (m : ℝ))))
      = (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
        * (((m : ℝ) * (T / (m : ℝ))) * Real.sqrt (T / (m : ℝ))) := by ring
    _ = (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2 * (T * Real.sqrt (T / (m : ℝ))) := by
        rw [hTm]
    _ ≤ (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2 * (T * Real.sqrt (T / (m : ℝ))) :=
        le_rfl

end ThirdMomentSum


/-- `∫|u + v|³ ≤ 4(∫|u|³ + ∫|v|³)`. -/
theorem integral_abs_add_pow_three_le {P : Measure Ω} {u v : Ω → ℝ}
    (hu : MeasureTheory.Integrable (fun ω => |u ω| ^ 3) P)
    (hv : MeasureTheory.Integrable (fun ω => |v ω| ^ 3) P)
    (huv : MeasureTheory.Integrable (fun ω => |u ω + v ω| ^ 3) P) :
    ∫ ω, |u ω + v ω| ^ 3 ∂P ≤ 4 * ((∫ ω, |u ω| ^ 3 ∂P) + ∫ ω, |v ω| ^ 3 ∂P) := by
  have hpt : ∀ ω : Ω, |u ω + v ω| ^ 3 ≤ 4 * (|u ω| ^ 3 + |v ω| ^ 3) := by
    intro ω
    have h3 : |u ω + v ω| ^ 3 ≤ (|u ω| + |v ω|) ^ 3 :=
      pow_le_pow_left₀ (abs_nonneg _) (abs_add_le _ _) 3
    have h2 : (|u ω| + |v ω|) ^ 3 ≤ 4 * (|u ω| ^ 3 + |v ω| ^ 3) :=
      add_pow_three_le_four (abs_nonneg _) (abs_nonneg _)
    linarith
  calc ∫ ω, |u ω + v ω| ^ 3 ∂P ≤ ∫ ω, 4 * (|u ω| ^ 3 + |v ω| ^ 3) ∂P :=
        MeasureTheory.integral_mono huv ((hu.add hv).const_mul 4) hpt
    _ = 4 * ((∫ ω, |u ω| ^ 3 ∂P) + ∫ ω, |v ω| ^ 3 ∂P) := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hu hv]


/-- **The grid step weight is uniformly close to a uniformly continuous weight.** If the cell
coefficients are the weight frozen at the left endpoints, the step process differs from the
weight by at most the weight's modulus of continuity at the mesh. -/
theorem abs_ofUnifGrid_eval_sub_le {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i)) (g : Ω → ℝ → ℝ) {ε : ℝ}
    (hξg : ∀ (i : Fin m) (ω : Ω), ξ i ω = g ω (unifGrid T m (i : ℕ)))
    (hmod : ∀ ω : Ω, ∀ x ∈ Set.Icc (0 : ℝ) T, ∀ y ∈ Set.Icc (0 : ℝ) T,
      |x - y| ≤ T / (m : ℝ) → |g ω x - g ω y| ≤ ε)
    (ω : Ω) {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) T) :
    |(SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω - g ω s| ≤ ε := by
  obtain ⟨i, hi, hlt, hle⟩ := exists_unifGrid_cell hT hm0 hs.1 hs.2
  have heval : (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω = ξ ⟨i, hi⟩ ω :=
    SimplePredictable.ofUnifGrid_eval hT hm0 ξ hbdd hmeas ⟨i, hi⟩ ⟨hlt, hle⟩ ω
  rw [heval, hξg ⟨i, hi⟩ ω]
  refine hmod ω _ ⟨unifGrid_nonneg hT.le m i, unifGrid_le hT.le hi.le hm0⟩ s
    ⟨hs.1.le, hs.2⟩ ?_
  have hstep : unifGrid T m (i + 1) - unifGrid T m i = T / (m : ℝ) := unifGrid_succ_sub hm0 i
  rw [abs_of_nonpos (by linarith : unifGrid T m i - s ≤ 0)]
  linarith

/-- **`L²` distance between the grid step weight and the weight.** A uniform pathwise bound on
`(0, T]` gives an `L²` bound over the window. -/
theorem lintegral_sq_sub_le_of_bound {P : Measure Ω} [IsProbabilityMeasure P]
    (u v : Ω → ℝ → ℝ) {ε T : ℝ} (hε0 : 0 ≤ ε)
    (hbound : ∀ (ω : Ω), ∀ s ∈ Set.Ioc (0 : ℝ) T, |u ω s - v ω s| ≤ ε) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖u ω s - v ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ENNReal.ofReal (ε ^ 2 * T) := by
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖u ω s - v ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume
      ≤ ENNReal.ofReal (ε ^ 2 * T) := by
    intro ω
    have hset : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖u ω s - v ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume
        = ∫⁻ s in Set.Ioc (0 : ℝ) T, (‖u ω s - v ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
      by rw [MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioc_ae_eq_Icc)]
    rw [hset]
    have hptw : ∀ s ∈ Set.Ioc (0 : ℝ) T,
        (‖u ω s - v ω s‖₊ : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal (ε ^ 2) := by
      intro s hs
      have h1 : (‖u ω s - v ω s‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_eq_coe_nnreal hε0]
        refine ENNReal.coe_le_coe.mpr ?_
        rw [← NNReal.coe_le_coe]
        simpa [Real.norm_eq_abs] using hbound ω s hs
      calc (‖u ω s - v ω s‖₊ : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal ε ^ 2 := pow_le_pow_left' h1 2
        _ = ENNReal.ofReal (ε ^ 2) := (ENNReal.ofReal_pow hε0 2).symm
    calc ∫⁻ s in Set.Ioc (0 : ℝ) T, (‖u ω s - v ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume
        ≤ ∫⁻ _s in Set.Ioc (0 : ℝ) T, ENNReal.ofReal (ε ^ 2) ∂volume :=
          MeasureTheory.setLIntegral_mono' measurableSet_Ioc hptw
      _ = ENNReal.ofReal (ε ^ 2) * volume (Set.Ioc (0 : ℝ) T) := by
          rw [MeasureTheory.setLIntegral_const]
      _ = ENNReal.ofReal (ε ^ 2 * T) := by
          rw [Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (by positivity)]
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖u ω s - v ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ _ω : Ω, ENNReal.ofReal (ε ^ 2 * T) ∂P := lintegral_mono hinner
    _ = ENNReal.ofReal (ε ^ 2 * T) := by simp

section RiemannLimit

/-- **The Riemann sums of a continuous weight against a bounded density converge.** On the
uniform grid of `[0, T]`, freezing `g` at each cell's left endpoint converges to the integral
of `g·h`. -/
theorem tendsto_riemann_weighted_unifGrid {g h : ℝ → ℝ} (hgc : Continuous g)
    (hh : Measurable h) {M : ℝ} (hM0 : 0 ≤ M) (hhM : ∀ s, |h s| ≤ M) {T : ℝ} (hT : 0 < T) :
    Filter.Tendsto (fun m : ℕ => ∑ i ∈ Finset.range m,
        g (unifGrid T m i) * ∫ s in unifGrid T m i..unifGrid T m (i + 1), h s)
      Filter.atTop (nhds (∫ s in (0 : ℝ)..T, g s * h s)) := by
  obtain ⟨Kg, hKg⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hgc.continuousOn
  have hgb : ∀ s ∈ Set.Icc (0 : ℝ) T, |g s| ≤ Kg := fun s hs => by
    simpa [Real.norm_eq_abs] using hKg s hs
  rw [Metric.tendsto_atTop]
  intro ε' hε'
  have hMT1 : (0 : ℝ) < M * T + 1 := by positivity
  set ε : ℝ := ε' / (2 * (M * T + 1)) with hεdef
  have hε0 : 0 < ε := by positivity
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc (a := (0 : ℝ)) (b := T)).uniformContinuousOn_of_continuous
      hgc.continuousOn) ε hε0
  obtain ⟨N, hN⟩ := exists_nat_gt (T / δ)
  refine ⟨max N 1, fun m hm => ?_⟩
  have hm1 : 1 ≤ m := le_trans (le_max_right N 1) hm
  have hm0 : m ≠ 0 := Nat.one_le_iff_ne_zero.mp hm1
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hmesh : T / (m : ℝ) < δ := by
    have hNm : (N : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr (le_trans (le_max_left N 1) hm)
    have h1 : T / δ < (m : ℝ) := lt_of_lt_of_le hN hNm
    rw [div_lt_iff₀ hmR]
    rw [div_lt_iff₀ hδ0] at h1
    linarith
  -- the modulus of continuity at the mesh
  have hgmod : ∀ x ∈ Set.Icc (0 : ℝ) T, ∀ y ∈ Set.Icc (0 : ℝ) T,
      |x - y| ≤ T / (m : ℝ) → |g x - g y| ≤ ε := by
    intro x hx y hy hxy
    have hdist : dist x y < δ := lt_of_le_of_lt (by simpa [Real.dist_eq] using hxy) hmesh
    exact le_of_lt (by simpa [Real.dist_eq] using hδ x hx y hy hdist)
  have hbound := abs_riemann_weighted_sub_integral_le (T := T) (ε := ε) (δ := T / (m : ℝ))
    (M := M) (Kg := Kg) hε0.le hgc hh hhM hgb hgmod (unifGrid T m)
    (unifGrid_zero T m) (unifGrid_self hm0)
    (fun i _ => (unifGrid_lt_succ hT hm0 i).le)
    (fun i _ => le_of_eq (unifGrid_succ_sub hm0 i))
    (fun i _ => ⟨unifGrid_nonneg hT.le m i, unifGrid_le hT.le (by omega) hm0⟩)
  rw [Real.dist_eq]
  refine lt_of_le_of_lt hbound ?_
  have hlt : ε * (M * T) < ε' := by
    rw [hεdef]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * (M * T + 1))]
    nlinarith [mul_nonneg hM0 hT.le]
  calc ε * M * T = ε * (M * T) := by ring
    _ < ε' := hlt

end RiemannLimit

section ItoIncrement

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hℱ hC0 hCH in
/-- **The third absolute moments of an Itô process's increments across a uniform grid sum to
`O(m^{-1/2})`.** The drift contributes `O(m^{-2})` and the martingale part `O(m^{-1/2})`. -/
theorem sum_integral_abs_itoIncrement_pow_three_le
    (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    ∑ i ∈ Finset.range m, ∫ ω,
        |(∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift ω s ∂volume)
          + (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω)| ^ 3 ∂P
      ≤ 4 * ((m : ℝ) * (B * (T / (m : ℝ))) ^ 3
        + (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
          * (T * Real.sqrt (T / (m : ℝ)))) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hstep : ∀ i : ℕ, unifGrid T m (i + 1) - unifGrid T m i = T / (m : ℝ) :=
    unifGrid_succ_sub hm0
  have hTm0 : (0 : ℝ) ≤ T / (m : ℝ) := le_of_lt (div_pos hT hm')
  have hK0 : (0 : ℝ) ≤ (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2 := by
    have h1 : (0 : ℝ) ≤ (6 + gaussianFourthMoment) * C ^ 4 :=
      mul_nonneg (by linarith [gaussianFourthMoment_nonneg]) (by positivity)
    linarith [sq_nonneg C]
  have hterm : ∀ i ∈ Finset.range m, ∫ ω,
      |(∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift ω s ∂volume)
        + (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω)| ^ 3 ∂P
      ≤ 4 * ((B * (T / (m : ℝ))) ^ 3
        + (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
          * (T / (m : ℝ) * Real.sqrt (T / (m : ℝ)))) := by
    intro i _
    have hle : unifGrid T m i ≤ unifGrid T m (i + 1) := (unifGrid_lt_succ hT hm0 i).le
    -- the drift increment
    have hDbd : ∀ ω : Ω,
        |∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift ω s ∂volume|
          ≤ B * (T / (m : ℝ)) := by
      intro ω
      have h := abs_setIntegral_Ioc_le (Measurable.of_uncurry_left hbm) (hB ω) hle
      rwa [hstep i] at h
    have hDint := integrable_abs_drift_pow_three (P := P) bdrift hbm hB0 hB hle
    have hDle : ∫ ω, |∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
        bdrift ω s ∂volume| ^ 3 ∂P ≤ (B * (T / (m : ℝ))) ^ 3 := by
      calc ∫ ω, |∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
            bdrift ω s ∂volume| ^ 3 ∂P
          ≤ ∫ _ω : Ω, (B * (T / (m : ℝ))) ^ 3 ∂P :=
            MeasureTheory.integral_mono hDint (MeasureTheory.integrable_const _)
              (fun ω => pow_le_pow_left₀ (abs_nonneg _) (hDbd ω) 3)
        _ = (B * (T / (m : ℝ))) ^ 3 := by simp
    -- the martingale increment
    obtain ⟨hMint, hMle⟩ := integral_abs_sub_pow_three_le W ℱ hℱ H hm hp hq hC0 hCH
      (unifGrid_nonneg hT.le m i) (unifGrid_lt_succ hT hm0 i)
    rw [hstep i] at hMle
    -- the sum
    have hsumint := integrable_abs_itoIncrement_pow_three W ℱ hℱ H hm hp hq hC0 hCH
      bdrift hbm hB0 hB (unifGrid_nonneg hT.le m i) (unifGrid_lt_succ hT hm0 i)
    refine (integral_abs_add_pow_three_le hDint hMint hsumint).trans ?_
    have h4 : (0 : ℝ) ≤ 4 := by norm_num
    exact mul_le_mul_of_nonneg_left (add_le_add hDle hMle) h4
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hTm : (m : ℝ) * (T / (m : ℝ)) = T := by field_simp
  calc (m : ℝ) * (4 * ((B * (T / (m : ℝ))) ^ 3
        + (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
          * (T / (m : ℝ) * Real.sqrt (T / (m : ℝ)))))
      = 4 * ((m : ℝ) * (B * (T / (m : ℝ))) ^ 3
        + (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
          * (((m : ℝ) * (T / (m : ℝ))) * Real.sqrt (T / (m : ℝ)))) := by ring
    _ = 4 * ((m : ℝ) * (B * (T / (m : ℝ))) ^ 3
        + (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
          * (T * Real.sqrt (T / (m : ℝ)))) := by rw [hTm]
    _ ≤ 4 * ((m : ℝ) * (B * (T / (m : ℝ))) ^ 3
        + (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
          * (T * Real.sqrt (T / (m : ℝ)))) := le_rfl

end ItoIncrement

end LevyStochCalc.Brownian.Ito

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-27 by the KLS formalization project: update deprecated aliases and
-- proof-local bindings for warning-free Lean v4.33.0 builds; see vendor/port.patch.

-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoSimple
public import LeanPool.KLS.LevyStochCalc.Probability.Progressive

/-!
# Truncation in `L²` and dyadic cell averages

Truncation of an `L²(Ω × [0,T])` integrand at level `M` together with the `L²` error it
incurs, the dyadic partition of `[0,T]`, the cell averages of an integrand over the
partition intervals, and the simple predictable process whose values on the `n`-th dyadic
grid are those averages.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Pointwise truncation tendsto** (Brownian, mirror of Compensated). -/
private lemma truncation_pointwise_tendsto_brownian (x : ℝ) :
    Filter.Tendsto
      (fun M : ℕ => (‖x - max (-(M : ℝ)) (min (M : ℝ) x)‖₊ : ℝ≥0∞) ^ 2)
      Filter.atTop (nhds 0) := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  refine Filter.eventually_atTop.mpr ⟨⌈|x|⌉₊, fun M hM => ?_⟩
  have h_M_ge : (M : ℝ) ≥ |x| := by
    calc (M : ℝ) ≥ (⌈|x|⌉₊ : ℝ) := by exact_mod_cast hM
      _ ≥ |x| := Nat.le_ceil _
  have h_clip : max (-(M : ℝ)) (min (M : ℝ) x) = x := by
    have h_min : min (M : ℝ) x = x := min_eq_right (le_trans (le_abs_self _) h_M_ge)
    rw [h_min]
    exact max_eq_right (by linarith [neg_abs_le x])
  change (0 : ℝ≥0∞) = (‖x - max (-(M : ℝ)) (min (M : ℝ) x)‖₊ : ℝ≥0∞) ^ 2
  rw [h_clip, sub_self]
  simp

/-- **Pointwise truncation dominated** (Brownian, mirror of Compensated). -/
private lemma truncation_dominated_brownian (x : ℝ) (M : ℕ) :
    (‖x - max (-(M : ℝ)) (min (M : ℝ) x)‖₊ : ℝ≥0∞) ^ 2
      ≤ (‖x‖₊ : ℝ≥0∞) ^ 2 := by
  have h_M_nn : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have h_abs : |x - max (-(M : ℝ)) (min (M : ℝ) x)| ≤ |x| := by
    by_cases hx : 0 ≤ x
    · by_cases hxM : x ≤ M
      · rw [min_eq_right hxM, max_eq_right (by linarith)]
        simp [abs_nonneg]
      · push Not at hxM
        rw [min_eq_left (le_of_lt hxM), max_eq_right (by linarith : -(M : ℝ) ≤ M)]
        rw [abs_of_nonneg (by linarith : 0 ≤ x - M), abs_of_nonneg hx]
        linarith
    · push Not at hx
      by_cases hxM : -(M : ℝ) ≤ x
      · rw [min_eq_right (by linarith : x ≤ M), max_eq_right hxM]
        simp
      · push Not at hxM
        rw [min_eq_right (by linarith : x ≤ M), max_eq_left (le_of_lt hxM)]
        rw [show x - -(M : ℝ) = x + M from by ring]
        rw [abs_of_nonpos (by linarith : x + (M : ℝ) ≤ 0), abs_of_neg hx]
        linarith
  have h_nn : ‖x - max (-(M : ℝ)) (min (M : ℝ) x)‖₊ ≤ ‖x‖₊ := by
    rw [← NNReal.coe_le_coe]
    simp only [coe_nnNorm, Real.norm_eq_abs]
    exact h_abs
  exact pow_le_pow_left' (ENNReal.coe_le_coe.mpr h_nn) 2

-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Truncation L² convergence (Brownian).** Mirror of Compensated. -/
lemma truncation_L2_converges_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ}
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    Filter.Tendsto
      (fun M : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - max (-(M : ℝ)) (min (M : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P)
      Filter.atTop (nhds 0) := by
  rw [show (0 : ℝ≥0∞) = ∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂P from by simp]
  refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
    (bound := fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) ?_ ?_ h_sq_int.ne ?_
  · -- AEMeasurable via Measurable.lintegral_prod_right'.
    intro M
    have h_F_joint : Measurable (fun (p : Ω × ℝ) =>
        (‖H p.1 p.2 - max (-(M : ℝ)) (min (M : ℝ) (H p.1 p.2))‖₊ : ℝ≥0∞) ^ 2) := by
      have h_clip : Measurable (fun x : ℝ => max (-(M : ℝ)) (min (M : ℝ) x)) := by fun_prop
      have h_sub : Measurable (fun (p : Ω × ℝ) =>
          H p.1 p.2 - max (-(M : ℝ)) (min (M : ℝ) (H p.1 p.2))) :=
        h_meas.sub (h_clip.comp h_meas)
      exact (ENNReal.continuous_coe.measurable.comp h_sub.nnNorm).pow_const 2
    refine Measurable.aemeasurable ?_
    exact Measurable.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0:ℝ) T)) h_F_joint
  · -- Bound: F_M ω ≤ G ω everywhere.
    intro M
    refine Filter.Eventually.of_forall (fun ω => ?_)
    refine MeasureTheory.lintegral_mono (fun s => ?_)
    exact truncation_dominated_brownian _ _
  · -- Pointwise: F_M ω → 0 for a.e. ω with finite inner integral.
    have h_finite_inner : ∀ᵐ ω ∂P,
        ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤ := by
      have h_bound_h : Measurable (fun ω =>
          ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) :=
        Measurable.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0:ℝ) T))
          ((ENNReal.continuous_coe.measurable.comp h_meas.nnNorm).pow_const 2)
      exact MeasureTheory.ae_lt_top h_bound_h h_sq_int.ne
    filter_upwards [h_finite_inner] with ω h_ω_finite
    -- For this ω, apply DCT on the s-integral.
    rw [show (0 : ℝ≥0∞)
        = ∫⁻ _ : ℝ, (0 : ℝ≥0∞) ∂(volume.restrict (Set.Icc (0:ℝ) T)) from by simp]
    refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
      (bound := fun s => (‖H ω s‖₊ : ℝ≥0∞) ^ 2) ?_ ?_ h_ω_finite.ne ?_
    · intro M
      refine Measurable.aemeasurable ?_
      have h_clip : Measurable (fun x : ℝ => max (-(M : ℝ)) (min (M : ℝ) x)) := by fun_prop
      have h_meas_slice : Measurable (fun s : ℝ => H ω s) :=
        h_meas.comp (by fun_prop : Measurable (fun s : ℝ => (ω, s)))
      exact (ENNReal.continuous_coe.measurable.comp
        (h_meas_slice.sub (h_clip.comp h_meas_slice)).nnNorm).pow_const 2
    · intro M
      refine Filter.Eventually.of_forall (fun s => ?_)
      exact truncation_dominated_brownian _ _
    · refine Filter.Eventually.of_forall (fun s => ?_)
      exact truncation_pointwise_tendsto_brownian _

/-- Triangle inequality lifted to ENNReal:
`(‖x + y‖₊)² ≤ 2 · ((‖x‖₊)² + (‖y‖₊)²)`. Used to lift pointwise
bounds to lintegral bounds in the diagonal selection of
`simplePredictable_dense_L2`. -/
lemma sq_nnnorm_add_le_two_mul_brownian (x y : ℝ) :
    (‖x + y‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖x‖₊ : ℝ≥0∞) ^ 2 + (‖y‖₊ : ℝ≥0∞) ^ 2) := by
  have h_norm_sq : ∀ z : ℝ, (‖z‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (z ^ 2) :=
    fun z => by
    rw [show (‖z‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ from ofReal_norm z |>.symm]
    rw [← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [show ‖z‖ ^ 2 = z ^ 2 from by rw [Real.norm_eq_abs, sq_abs]]
  rw [h_norm_sq, h_norm_sq, h_norm_sq]
  have h_real : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by nlinarith [sq_nonneg (x - y)]
  have h_nn_x : 0 ≤ x ^ 2 := sq_nonneg _
  have h_nn_y : 0 ≤ y ^ 2 := sq_nonneg _
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by simp [ENNReal.ofReal_ofNat]]
  rw [← ENNReal.ofReal_add h_nn_x h_nn_y, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  exact ENNReal.ofReal_le_ofReal h_real

/-- **Step 1 of the density chain (Brownian, no mark dimension):** Bounded measurable
`g : Ω × [0, T] → ℝ` lies in `MemLp 2 (P × volume.restrict [0, T])`.

This gives access to Mathlib's `MeasureTheory.MemLp.exists_simpleFunc_eLpNorm_sub_lt`
which produces a Mathlib `SimpleFunc` approximation in L². The output, however, is
a Mathlib SimpleFunc (with constant range, indicator of measurable rectangles),
not yet our `SimplePredictable` form (with adapted ω-dependent coefficients on time
intervals only). Step 2 bridges this gap. -/
private lemma bounded_memLp_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (_hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    MeasureTheory.MemLp (Function.uncurry g)
      2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
  -- Volume.restrict (Icc 0 T) is finite (volume(Icc 0 T) = T < ∞).
  have : MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    ⟨by simp [Real.volume_Icc, ENNReal.ofReal_lt_top]⟩
  have : MeasureTheory.IsFiniteMeasure
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := inferInstance
  refine MeasureTheory.MemLp.of_bound h_meas.aestronglyMeasurable M ?_
  refine Filter.Eventually.of_forall (fun p => ?_)
  rw [Real.norm_eq_abs]
  exact h_bound p.1 p.2

/-- **Step 1.5 of the density chain (Brownian):** Mathlib SimpleFunc convergence on
the finite product space. Given `g ∈ MemLp 2` (from `bounded_memLp_brownian`), we
extract a sequence `(φ_n)` of Mathlib `SimpleFunc` such that `eLpNorm (g - φ_n) → 0`. -/
private lemma exists_simpleFunc_seq_tendsto_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    ∃ φ : ℕ → MeasureTheory.SimpleFunc (Ω × ℝ) ℝ,
      Filter.Tendsto
        (fun n => MeasureTheory.eLpNorm (Function.uncurry g - ⇑(φ n))
          2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))))
        Filter.atTop (nhds 0) := by
  have h_memLp : MeasureTheory.MemLp (Function.uncurry g)
      2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
    bounded_memLp_brownian hT g h_meas M h_bound
  -- For each n, get a SimpleFunc with eLpNorm-distance ≤ 1/(n+1).
  have h_choice : ∀ n : ℕ, ∃ φ : MeasureTheory.SimpleFunc (Ω × ℝ) ℝ,
      MeasureTheory.eLpNorm (Function.uncurry g - ⇑φ)
        2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) < ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    have h_eps_ne : ((n : ℝ≥0∞) + 1)⁻¹ ≠ 0 := by
      apply ENNReal.inv_ne_zero.mpr
      simp
    obtain ⟨φ, hφ_lt, _⟩ := MeasureTheory.MemLp.exists_simpleFunc_eLpNorm_sub_lt
      h_memLp (by simp : (2 : ℝ≥0∞) ≠ ⊤) h_eps_ne
    exact ⟨φ, hφ_lt⟩
  choose φ hφ using h_choice
  refine ⟨φ, ?_⟩
  -- Squeeze: ‖g - φ_n‖ ≤ (n+1)⁻¹ → 0.
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε_pos
  have h_inv_tendsto : Filter.Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹)
      Filter.atTop (nhds 0) := by
    have h := ENNReal.tendsto_inv_nat_nhds_zero
    have hcomp :
        Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) Filter.atTop (nhds 0) :=
      h.comp (Filter.tendsto_add_atTop_nat 1)
    simpa [Nat.cast_add, Nat.cast_one] using hcomp
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_atTop_zero.mp h_inv_tendsto) ε hε_pos
  refine ⟨N, fun n hn => ?_⟩
  exact (hφ n).le.trans (hN n hn)

/-- **Dyadic partition** of `[0, T]` at refinement level `n`:
`partition i = i * T / 2^n` for `i = 0, ..., 2^n`. -/
noncomputable def dyadicPartitionBrownian (T : ℝ) (n : ℕ) :
    Fin (2 ^ n + 1) → ℝ :=
  fun i => (i : ℝ) * T / (2 ^ n : ℕ)

lemma dyadicPartition_brownian_zero (T : ℝ) (n : ℕ) :
    dyadicPartitionBrownian T n 0 = 0 := by
  simp [dyadicPartitionBrownian]

lemma dyadicPartition_brownian_last (T : ℝ) (n : ℕ) :
    dyadicPartitionBrownian T n (Fin.last (2 ^ n)) = T := by
  unfold dyadicPartitionBrownian
  rw [Fin.val_last]
  field_simp

lemma dyadicPartition_brownian_strictMono {T : ℝ} (hT : 0 < T) (n : ℕ) :
    StrictMono (dyadicPartitionBrownian T n) := by
  intro i j hij
  unfold dyadicPartitionBrownian
  have h_pos : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
  have h_lt : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
  rw [div_lt_div_iff_of_pos_right h_pos]
  exact mul_lt_mul_of_pos_right h_lt hT

lemma dyadicPartition_brownian_le_T {T : ℝ} (_hT : 0 < T) (n : ℕ) :
    dyadicPartitionBrownian T n (Fin.last (2 ^ n)) ≤ T :=
  le_of_eq (dyadicPartition_brownian_last T n)

/-- **Dyadic averaging coefficient**: the average of `g(ω, ·)` over the `i`-th
dyadic interval `(t_i, t_{i+1}]` of `[0, T]` at refinement level `n`.

Used as the ξ-coefficient of the dyadic SimplePredictable approximation. -/
noncomputable def dyadicAvgBrownian
    {T : ℝ} (g : Ω → ℝ → ℝ) (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) : ℝ :=
  ((2 ^ n : ℕ) / T) *
    ∫ s in Set.Ioc (dyadicPartitionBrownian T n i.castSucc)
                    (dyadicPartitionBrownian T n i.succ),
      g ω s

/-- Measurability of `dyadicAvgBrownian` in `ω` (Bochner integral commutes with
measurability via Fubini). -/
lemma dyadicAvg_brownian_measurable
    (T : ℝ) (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (n : ℕ) (i : Fin (2 ^ n)) :
    Measurable (dyadicAvgBrownian (T := T) g n i) := by
  unfold dyadicAvgBrownian
  refine Measurable.const_mul ?_ _
  -- The Bochner integral ∫ s in S, g ω s ∂volume = ∫ s, g ω s ∂(volume.restrict S)
  -- is measurable in ω by `StronglyMeasurable.integral_prod_right`.
  refine MeasureTheory.StronglyMeasurable.measurable ?_
  exact MeasureTheory.StronglyMeasurable.integral_prod_right
    (ν := volume.restrict (Set.Ioc (dyadicPartitionBrownian T n i.castSucc)
                                    (dyadicPartitionBrownian T n i.succ)))
    h_meas.stronglyMeasurable

/-- Length of dyadic interval at refinement level `n`: `T/2^n`. -/
lemma dyadicPartition_brownian_diff {T : ℝ} (n : ℕ) (i : Fin (2 ^ n)) :
    dyadicPartitionBrownian T n i.succ - dyadicPartitionBrownian T n i.castSucc
      = T / (2 ^ n : ℕ) := by
  unfold dyadicPartitionBrownian
  have hi_succ : ((i.succ : Fin (2 ^ n + 1)) : ℝ) = (i : ℝ) + 1 := by
    simp [Fin.val_succ]
  have hi_castSucc : ((i.castSucc : Fin (2 ^ n + 1)) : ℝ) = (i : ℝ) := by
    simp [Fin.val_castSucc]
  rw [hi_succ, hi_castSucc]
  ring

-- `omit` the unused `[MeasurableSpace Ω]` section variable (this lemma's
-- `g : Ω → ℝ → ℝ` does not need it).
omit [MeasurableSpace Ω] in
/-- Boundedness of `dyadicAvgBrownian`: if `|g| ≤ M`, then `|dyadicAvg ω| ≤ M`. -/
lemma dyadicAvg_brownian_bounded
    (T : ℝ) (hT : 0 < T) (g : Ω → ℝ → ℝ)
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M)
    (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) :
    |dyadicAvgBrownian (T := T) g n i ω| ≤ M := by
  unfold dyadicAvgBrownian
  set t_i := dyadicPartitionBrownian T n i.castSucc with ht_i
  set t_succ := dyadicPartitionBrownian T n i.succ with ht_succ
  have h_lt : t_i < t_succ :=
    dyadicPartition_brownian_strictMono hT n Fin.castSucc_lt_succ
  have h_le : t_i ≤ t_succ := le_of_lt h_lt
  have h_diff : t_succ - t_i = T / (2 ^ n : ℕ) := by
    rw [ht_i, ht_succ]
    exact dyadicPartition_brownian_diff n i
  have h_M_nn : (0 : ℝ) ≤ M := le_trans (abs_nonneg (g ω 0)) (h_bound ω 0)
  have h_volume_eq : volume (Set.Ioc t_i t_succ) = ENNReal.ofReal (t_succ - t_i) :=
    Real.volume_Ioc
  -- ∫ s in (t_i, t_succ], g ω s = ∫ s, (Ioc t_i t_succ).indicator (g ω) s.
  -- ‖g ω s‖ ≤ M everywhere, so the indicator ‖g ω s‖ ≤ M·𝟙_{Ioc} a.e.
  have h_integral_norm_bound :
      ‖∫ s in Set.Ioc t_i t_succ, g ω s‖ ≤ M * (t_succ - t_i) := by
    have h_norm_le : ∀ᵐ s ∂(volume.restrict (Set.Ioc t_i t_succ)),
        ‖g ω s‖ ≤ M := by
      refine Filter.Eventually.of_forall (fun s => ?_)
      rw [Real.norm_eq_abs]
      exact h_bound ω s
    have h_finite_restrict :
        MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Ioc t_i t_succ)) := by
      refine ⟨?_⟩
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          h_volume_eq]
      exact ENNReal.ofReal_lt_top
    have h_M_integrable : MeasureTheory.Integrable
        (fun _ => M) (volume.restrict (Set.Ioc t_i t_succ)) :=
      MeasureTheory.integrable_const M
    calc ‖∫ s in Set.Ioc t_i t_succ, g ω s‖
        ≤ ∫ _ in Set.Ioc t_i t_succ, M ∂volume :=
          MeasureTheory.norm_integral_le_of_norm_le h_M_integrable h_norm_le
      _ = M * (t_succ - t_i) := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul]
          have h_real : volume.real (Set.Ioc t_i t_succ) = t_succ - t_i := by
            unfold MeasureTheory.Measure.real
            rw [h_volume_eq, ENNReal.toReal_ofReal (by linarith)]
          rw [h_real]
          ring
  rw [Real.norm_eq_abs] at h_integral_norm_bound
  -- Combine.
  have h_pow_pos : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
  have h_coeff_pos : (0 : ℝ) < (2 ^ n : ℕ) / T := div_pos h_pow_pos hT
  rw [abs_mul, abs_of_pos h_coeff_pos]
  calc ((2 ^ n : ℕ) / T) * |∫ s in Set.Ioc t_i t_succ, g ω s|
      ≤ ((2 ^ n : ℕ) / T) * (M * (t_succ - t_i)) :=
        mul_le_mul_of_nonneg_left h_integral_norm_bound (le_of_lt h_coeff_pos)
    _ = ((2 ^ n : ℕ) / T) * (M * (T / (2 ^ n : ℕ))) := by rw [h_diff]
    _ = M := by
        have h_T_ne : T ≠ 0 := ne_of_gt hT
        have h_pow_ne : ((2 ^ n : ℕ) : ℝ) ≠ 0 := ne_of_gt h_pow_pos
        field_simp

/-- **Dyadic SimplePredictable (Brownian):** the SimplePredictable obtained by
dyadic refinement of `g` at level `n`. Partition `t_i = i T / 2^n`; coefficient
`ξ_i ω = (2^n/T) · ∫_{t_i}^{t_{i+1}} g(ω, s) ds`.

This SimplePredictable converges to `g` in L²(P × volume) as `n → ∞`. The
convergence is the substantive sub-result (Lévy upward / L² martingale convergence
on the dyadic σ-algebra). -/
noncomputable def dyadicSimplePredictableBrownian
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) (n : ℕ) :
    SimplePredictable Ω T where
  N := 2 ^ n
  partition := dyadicPartitionBrownian T n
  partition_zero := dyadicPartition_brownian_zero T n
  partition_le_T := dyadicPartition_brownian_le_T hT n
  partition_strictMono := dyadicPartition_brownian_strictMono hT n
  ξ := dyadicAvgBrownian (T := T) g n
  ξ_bounded := fun i =>
    ⟨M, fun ω => dyadicAvg_brownian_bounded T hT g M h_bound n i ω⟩
  ξ_measurable := dyadicAvg_brownian_measurable T g h_meas n
end LevyStochCalc.Brownian.Ito

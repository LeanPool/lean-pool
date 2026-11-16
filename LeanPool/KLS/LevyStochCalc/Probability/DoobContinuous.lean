/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import Mathlib.Probability.Martingale.Basic
public import LeanPool.KLS.LevyStochCalc.Probability.ProgressiveCadlag
public import LeanPool.KLS.MathFin.Foundations.DoobLpMaximalInequality

/-!
# Doob's `L²` maximal inequality in continuous time

For a right-continuous martingale on `[0, T]`, the supremum of the paths over the window is
square integrable, with `𝔼[sup_{t ≤ T} |M_t|²] ≤ 4 𝔼[|M_T|²]`.

The discrete inequality is `MeasureTheory.Martingale.eLpNorm_norm_runMax_le`; the passage to
continuous time samples the martingale along the dyadic partition of `[0, T]`, whose points are
increasing in the level, and uses right-continuity to identify the supremum over the window with
the supremum of the sampled maxima.

## Main statements

* `Filtration.compMono`, `martingale_compMono` — sampling along a monotone time map.
* `dyadicTime` — the dyadic partition points of `[0, T]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Sampling along a monotone time map -/

variable (mΩ) in
/-- The filtration sampled along a monotone time map. -/
def Filtration.compMono {ι ι' : Type*} [Preorder ι] [Preorder ι']
    (ℱ : Filtration ι' mΩ) (τ : ι → ι') (hτ : Monotone τ) : Filtration ι mΩ where
  seq i := ℱ (τ i)
  mono' _ _ hij := ℱ.mono' (hτ hij)
  le' i := ℱ.le' (τ i)

@[simp] theorem Filtration.compMono_apply {ι ι' : Type*} [Preorder ι] [Preorder ι']
    (ℱ : Filtration ι' mΩ) (τ : ι → ι') (hτ : Monotone τ) (i : ι) :
    Filtration.compMono mΩ ℱ τ hτ i = ℱ (τ i) := rfl

/-- A martingale sampled along a monotone time map is a martingale for the sampled
filtration. -/
theorem martingale_compMono {ι ι' : Type*} [Preorder ι] [Preorder ι']
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure Ω} {ℱ : Filtration ι' mΩ} {f : ι' → Ω → E}
    (hf : MeasureTheory.Martingale f ℱ μ) (τ : ι → ι') (hτ : Monotone τ) :
    MeasureTheory.Martingale (fun i => f (τ i)) (Filtration.compMono mΩ ℱ τ hτ) μ :=
  ⟨fun i => hf.1 (τ i), fun i j hij => hf.2 (τ i) (τ j) (hτ hij)⟩

/-! ### The dyadic partition of `[0, T]` -/

/-- The `k`-th dyadic partition point of `[0, T]` at level `n`, frozen at the horizon. -/
noncomputable def dyadicTime (T : ℝ) (n k : ℕ) : ℝ := min ((k : ℝ) * T / 2 ^ n) T

theorem dyadicTime_monotone {T : ℝ} (hT : 0 ≤ T) (n : ℕ) : Monotone (dyadicTime T n) := by
  intro k l hkl
  refine min_le_min ?_ le_rfl
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hkl) hT

theorem dyadicTime_nonneg {T : ℝ} (hT : 0 ≤ T) (n k : ℕ) : 0 ≤ dyadicTime T n k :=
  le_min (by positivity) hT

theorem dyadicTime_le {T : ℝ} (n k : ℕ) : dyadicTime T n k ≤ T := min_le_right _ _

theorem dyadicTime_mem_Icc {T : ℝ} (hT : 0 ≤ T) (n k : ℕ) :
    dyadicTime T n k ∈ Set.Icc (0 : ℝ) T :=
  ⟨dyadicTime_nonneg hT n k, dyadicTime_le n k⟩

@[simp] theorem dyadicTime_top {T : ℝ} (n : ℕ) :
    dyadicTime T n (2 ^ n) = T := by
  have h : ((2 ^ n : ℕ) : ℝ) * T / 2 ^ n = T := by
    push_cast
    field_simp
  rw [dyadicTime, h, min_self]

/-- Refining the level does not move the partition points: level `n`'s point `k` is level
`n + 1`'s point `2 * k`. -/
theorem dyadicTime_succ_two_mul {T : ℝ} (n k : ℕ) :
    dyadicTime T (n + 1) (2 * k) = dyadicTime T n k := by
  unfold dyadicTime
  congr 1
  push_cast
  rw [pow_succ]
  ring

/-! ### The sampled running maxima -/

variable {M : ℝ → Ω → ℝ} {T : ℝ}

/-- The running maximum of the sampled path over the dyadic partition of level `n`. -/
noncomputable def dyadicRunMax (M : ℝ → Ω → ℝ) (T : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (2 ^ n + 1)).sup' Finset.nonempty_range_add_one
    fun k => ‖M (dyadicTime T n k) ω‖

theorem dyadicRunMax_nonneg (M : ℝ → Ω → ℝ) (T : ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ dyadicRunMax M T n ω :=
  le_trans (norm_nonneg _)
    (Finset.le_sup' (f := fun k => ‖M (dyadicTime T n k) ω‖)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.zero_le _))))

/-- The sampled running maximum, as an extended non-negative real, is the supremum over the
partition points. -/
theorem enorm_dyadicRunMax (M : ℝ → Ω → ℝ) (T : ℝ) (n : ℕ) (ω : Ω) :
    (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞)
      = ⨆ k : Fin (2 ^ n + 1), (‖M (dyadicTime T n (k : ℕ)) ω‖₊ : ℝ≥0∞) := by
  have hcoe : ∀ x : ℝ, 0 ≤ x → ((‖x‖₊ : ℝ≥0) : ℝ) = x := fun x hx => by
    simp [Real.norm_eq_abs, abs_of_nonneg hx]
  refine le_antisymm ?_ ?_
  · rcases Finset.exists_mem_eq_sup' (Finset.nonempty_range_add_one (n := 2 ^ n))
      (fun k => ‖M (dyadicTime T n k) ω‖) with ⟨k, hk, hkeq⟩
    refine le_iSup_of_le ⟨k, Finset.mem_range.mp hk⟩ (le_of_eq ?_)
    rw [dyadicRunMax, hkeq]
    congr 1
    exact NNReal.eq (by simp [Real.norm_eq_abs])
  · refine iSup_le fun k => ?_
    refine ENNReal.coe_le_coe.mpr ?_
    refine NNReal.coe_le_coe.mp ?_
    rw [hcoe _ (dyadicRunMax_nonneg M T n ω), coe_nnnorm]
    exact Finset.le_sup' (f := fun j => ‖M (dyadicTime T n j) ω‖)
      (Finset.mem_range.mpr k.isLt)

/-- Refining the level can only increase the sampled running maximum. -/
theorem enorm_dyadicRunMax_mono (M : ℝ → Ω → ℝ) (T : ℝ) (ω : Ω) :
    Monotone fun n => (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞) := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [enorm_dyadicRunMax, enorm_dyadicRunMax]
  refine iSup_le fun k => ?_
  refine le_iSup_of_le ⟨2 * (k : ℕ), ?_⟩ (le_of_eq ?_)
  · have hk : (k : ℕ) ≤ 2 ^ n := Nat.lt_succ_iff.mp k.isLt
    calc 2 * (k : ℕ) ≤ 2 * 2 ^ n := by omega
      _ < 2 ^ (n + 1) + 1 := by rw [pow_succ]; omega
  · rw [dyadicTime_succ_two_mul]

/-- Each sampled running maximum is measurable when the sampled slices are. -/
theorem measurable_enorm_dyadicRunMax (hM : ∀ t : ℝ, Measurable (M t)) (T : ℝ) (n : ℕ) :
    Measurable fun ω => (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞) := by
  have heq : (fun ω => (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞))
      = fun ω => ⨆ k : Fin (2 ^ n + 1), (‖M (dyadicTime T n (k : ℕ)) ω‖₊ : ℝ≥0∞) :=
    funext fun ω => enorm_dyadicRunMax M T n ω
  rw [heq]
  exact Measurable.iSup fun k =>
    ENNReal.continuous_coe.measurable.comp (hM (dyadicTime T n (k : ℕ))).nnnorm

/-! ### The supremum over the window -/

/-- The dyadic index whose partition point is the first at or after `t`. -/
noncomputable def dyadicIndex (T t : ℝ) (n : ℕ) : ℕ := ⌈t * 2 ^ n / T⌉₊

theorem dyadicIndex_le {T t : ℝ} (hT : 0 < T) (ht : t ≤ T) (n : ℕ) :
    dyadicIndex T t n ≤ 2 ^ n := by
  refine Nat.ceil_le.mpr ?_
  rw [div_le_iff₀ hT]
  push_cast
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) n]

theorem le_dyadicTime_dyadicIndex {T t : ℝ} (hT : 0 < T) (htT : t ≤ T) (n : ℕ) :
    t ≤ dyadicTime T n (dyadicIndex T t n) := by
  have hpow : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have hceil : t * 2 ^ n / T ≤ (dyadicIndex T t n : ℝ) := Nat.le_ceil _
  have h1 : t * 2 ^ n ≤ (dyadicIndex T t n : ℝ) * T := (div_le_iff₀ hT).mp hceil
  have hmul : t ≤ (dyadicIndex T t n : ℝ) * T / 2 ^ n := (le_div_iff₀ hpow).mpr h1
  exact le_min hmul htT

theorem dyadicTime_dyadicIndex_le_add {T t : ℝ} (hT : 0 < T) (ht : 0 ≤ t) (n : ℕ) :
    dyadicTime T n (dyadicIndex T t n) ≤ t + T / 2 ^ n := by
  have hpow : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have hlt : (dyadicIndex T t n : ℝ) < t * 2 ^ n / T + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  refine le_trans (min_le_left _ _) ?_
  rw [div_le_iff₀ hpow]
  have hexp : (t + T / 2 ^ n) * 2 ^ n = t * 2 ^ n + T := by field_simp
  rw [hexp]
  have : (dyadicIndex T t n : ℝ) * T ≤ (t * 2 ^ n / T + 1) * T :=
    mul_le_mul_of_nonneg_right hlt.le hT.le
  calc (dyadicIndex T t n : ℝ) * T ≤ (t * 2 ^ n / T + 1) * T := this
    _ = t * 2 ^ n + T := by field_simp

/-- The dyadic points chosen by `dyadicIndex` approach `t` from the right. -/
theorem tendsto_dyadicTime_dyadicIndex {T t : ℝ} (hT : 0 < T) (ht : 0 ≤ t) (htT : t ≤ T) :
    Filter.Tendsto (fun n => dyadicTime T n (dyadicIndex T t n)) Filter.atTop
      (nhdsWithin t (Set.Ici t)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
    (Filter.Eventually.of_forall fun n => le_dyadicTime_dyadicIndex hT htT n)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ : ℕ => t) (h := fun n => t + T / 2 ^ n) tendsto_const_nhds ?_
    (fun n => le_dyadicTime_dyadicIndex hT htT n)
    (fun n => dyadicTime_dyadicIndex_le_add hT ht n)
  have hhalf : Filter.Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hd : ∀ n : ℕ, T / 2 ^ n = T * ((1 : ℝ) / 2) ^ n := fun n => by
    rw [div_pow, one_pow]
    ring
  have htend0 : Filter.Tendsto (fun n : ℕ => T / 2 ^ n) Filter.atTop (nhds 0) := by
    simp only [hd]
    simpa using hhalf.const_mul T
  simpa using tendsto_const_nhds.add htend0

/-- **Right-continuity identifies the supremum over the window with the supremum of the sampled
running maxima.** -/
theorem iSup_enorm_eq_iSup_dyadicRunMax (hT : 0 ≤ T) {ω : Ω}
    (hcad : ∀ t : ℝ, Filter.Tendsto (fun s => M s ω) (nhdsWithin t (Set.Ioi t))
      (nhds (M t ω))) :
    (⨆ t : Set.Icc (0 : ℝ) T, (‖M (t : ℝ) ω‖₊ : ℝ≥0∞))
      = ⨆ n, (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞) := by
  refine le_antisymm (iSup_le fun t => ?_) (iSup_le fun n => ?_)
  · rcases eq_or_lt_of_le hT with hT0 | hTpos
    · have ht0 : (t : ℝ) = 0 := le_antisymm (hT0 ▸ t.2.2) t.2.1
      refine le_iSup_of_le 0 ?_
      rw [enorm_dyadicRunMax]
      refine le_iSup_of_le ⟨0, Nat.succ_pos _⟩ (le_of_eq ?_)
      have hd0 : dyadicTime T 0 0 = 0 := by
        simp [dyadicTime, ← hT0]
      rw [hd0, ht0]
    · have hbd : ∀ n : ℕ, (‖M (dyadicTime T n (dyadicIndex T (t : ℝ) n)) ω‖₊ : ℝ≥0∞)
          ≤ ⨆ m, (‖dyadicRunMax M T m ω‖₊ : ℝ≥0∞) := by
        intro n
        refine le_iSup_of_le n ?_
        rw [enorm_dyadicRunMax]
        exact le_iSup_of_le
          ⟨dyadicIndex T (t : ℝ) n, Nat.lt_succ_of_le (dyadicIndex_le hTpos t.2.2 n)⟩ le_rfl
      have hMs : Filter.Tendsto
          (fun n => M (dyadicTime T n (dyadicIndex T (t : ℝ) n)) ω) Filter.atTop
          (nhds (M (t : ℝ) ω)) :=
        (tendsto_nhdsGE_of_nhdsGT (hcad (t : ℝ))).comp
          (tendsto_dyadicTime_dyadicIndex hTpos t.2.1 t.2.2)
      have hconv : Filter.Tendsto
          (fun n => (‖M (dyadicTime T n (dyadicIndex T (t : ℝ) n)) ω‖₊ : ℝ≥0∞))
          Filter.atTop (nhds ((‖M (t : ℝ) ω‖₊ : ℝ≥0∞))) :=
        (ENNReal.continuous_coe.tendsto _).comp hMs.nnnorm
      exact le_of_tendsto hconv (Filter.Eventually.of_forall hbd)
  · rw [enorm_dyadicRunMax]
    exact iSup_le fun k =>
      le_iSup_of_le ⟨dyadicTime T n (k : ℕ), dyadicTime_mem_Icc hT n (k : ℕ)⟩ le_rfl

/-! ### Doob's `L²` inequality in continuous time -/

/-- Squaring commutes with the supremum of a monotone sequence. -/
theorem iSup_sq_of_monotone {a : ℕ → ℝ≥0∞} (ha : Monotone a) :
    (⨆ n, a n) ^ 2 = ⨆ n, a n ^ 2 := by
  refine le_antisymm ?_ (iSup_le fun n => pow_le_pow_left' (le_iSup a n) 2)
  rw [pow_two, ENNReal.iSup_mul]
  refine iSup_le fun n => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun m => le_iSup_of_le (max n m) ?_
  rw [pow_two]
  exact mul_le_mul' (ha (le_max_left n m)) (ha (le_max_right n m))

/-- The `L²` seminorm as a `lintegral`. The measurability premise is required because
Mathlib v4.35's `eLpNorm` is `∞` for functions that are not a.e. strongly measurable. -/
theorem eLpNorm_two_eq {μ : Measure Ω} (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ = (∫⁻ ω, (‖f ω‖₊ : ℝ≥0∞) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  simp only [ENNReal.toReal_ofNat]
  congr 1
  refine lintegral_congr fun ω => ?_
  rw [← ENNReal.rpow_natCast _ 2]
  norm_num
  simp [enorm_eq_nnnorm]

/-- **Doob's `L²` maximal inequality at a dyadic level.** -/
theorem lintegral_sq_dyadicRunMax_le {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ mΩ} (hM : MeasureTheory.Martingale M ℱ μ) (hT : 0 ≤ T) (n : ℕ) :
    ∫⁻ ω, (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞) ^ 2 ∂μ
      ≤ 4 * ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  have hsamp := martingale_compMono hM (dyadicTime T n) (dyadicTime_monotone hT n)
  have hdoob := MeasureTheory.Martingale.eLpNorm_norm_runMax_le hsamp
    (by norm_num : (1 : ℝ) < 2) (2 ^ n)
  have hp : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by
    simp
  have hc : ENNReal.ofReal ((2 : ℝ) / (2 - 1)) = (2 : ℝ≥0∞) := by
    norm_num
  rw [hp, hc, dyadicTime_top n] at hdoob
  have hlhs : eLpNorm (fun ω => (Finset.range (2 ^ n + 1)).sup' Finset.nonempty_range_add_one
      fun k => ‖M (dyadicTime T n k) ω‖) 2 μ = eLpNorm (dyadicRunMax M T n) 2 μ := rfl
  have hmeas_max : AEStronglyMeasurable (dyadicRunMax M T n) μ := by
    unfold dyadicRunMax
    exact (Finset.measurable_range_sup'' fun k _ =>
      ((hM.stronglyMeasurable _).mono (ℱ.le _)).measurable.norm).aestronglyMeasurable
  rw [hlhs, eLpNorm_two_eq _ hmeas_max, eLpNorm_two_eq _ (hM.integrable T).aestronglyMeasurable]
    at hdoob
  have hsq := ENNReal.rpow_le_rpow hdoob (by norm_num : (0 : ℝ) ≤ 2)
  rw [← ENNReal.rpow_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.rpow_mul] at hsq
  norm_num at hsq
  calc ∫⁻ ω, (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞) ^ 2 ∂μ
      = (∫⁻ ω, (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞) ^ 2 ∂μ) ^ (1 : ℝ) := by
        rw [ENNReal.rpow_one]
    _ ≤ 4 * ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
        simpa using hsq

/-- **Doob's `L²` inequality over the dyadic points.** No path regularity is needed: the
supremum runs over the countable family of partition points. -/
theorem lintegral_iSup_dyadicRunMax_sq_le {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ mΩ} (hM : MeasureTheory.Martingale M ℱ μ) (hT : 0 ≤ T) :
    ∫⁻ ω, (⨆ n, (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞)) ^ 2 ∂μ
      ≤ 4 * ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  have hMm : ∀ t : ℝ, Measurable (M t) := fun t => ((hM.1 t).mono (ℱ.le t)).measurable
  have heq : (fun ω => (⨆ n, (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞)) ^ 2)
      = fun ω => ⨆ n, (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞) ^ 2 :=
    funext fun ω => iSup_sq_of_monotone (enorm_dyadicRunMax_mono M T ω)
  rw [heq, lintegral_iSup (fun n => (measurable_enorm_dyadicRunMax hMm T n).pow_const 2)
    (fun m n hmn ω => pow_le_pow_left' (enorm_dyadicRunMax_mono M T ω hmn) 2)]
  exact iSup_le fun n => lintegral_sq_dyadicRunMax_le hM hT n

/-- **Doob's `L²` maximal inequality in continuous time.** For a right-continuous martingale, the
supremum of the path over `[0, T]` has second moment at most four times that of the terminal
value. -/
theorem lintegral_iSup_sq_le_of_martingale {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ mΩ} (hM : MeasureTheory.Martingale M ℱ μ) (hT : 0 ≤ T)
    (hcad : ∀ᵐ ω ∂μ, ∀ t : ℝ, Filter.Tendsto (fun s => M s ω) (nhdsWithin t (Set.Ioi t))
      (nhds (M t ω))) :
    ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, (‖M (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂μ
      ≤ 4 * ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  have hcongr : ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, (‖M (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂μ
      = ∫⁻ ω, (⨆ n, (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞)) ^ 2 ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hcad] with ω hω
    rw [iSup_enorm_eq_iSup_dyadicRunMax hT hω]
  rw [hcongr]
  exact lintegral_iSup_dyadicRunMax_sq_le hM hT

/-! ### Bounding the supremum over the window -/

/-- The sampled running maximum is subadditive. -/
theorem enorm_dyadicRunMax_add_le (A B : ℝ → Ω → ℝ) (T : ℝ) (n : ℕ) (ω : Ω) :
    (‖dyadicRunMax (fun t ω => A t ω + B t ω) T n ω‖₊ : ℝ≥0∞)
      ≤ (‖dyadicRunMax A T n ω‖₊ : ℝ≥0∞) + (‖dyadicRunMax B T n ω‖₊ : ℝ≥0∞) := by
  rw [enorm_dyadicRunMax, enorm_dyadicRunMax, enorm_dyadicRunMax]
  refine iSup_le fun k => ?_
  have hpt : (‖A (dyadicTime T n (k : ℕ)) ω + B (dyadicTime T n (k : ℕ)) ω‖₊ : ℝ≥0∞)
      ≤ (‖A (dyadicTime T n (k : ℕ)) ω‖₊ : ℝ≥0∞)
        + (‖B (dyadicTime T n (k : ℕ)) ω‖₊ : ℝ≥0∞) := by
    rw [← ENNReal.coe_add]
    exact ENNReal.coe_le_coe.mpr (nnnorm_add_le _ _)
  exact le_trans hpt (add_le_add
    (le_iSup (fun j : Fin (2 ^ n + 1) => (‖A (dyadicTime T n (j : ℕ)) ω‖₊ : ℝ≥0∞)) k)
    (le_iSup (fun j : Fin (2 ^ n + 1) => (‖B (dyadicTime T n (j : ℕ)) ω‖₊ : ℝ≥0∞)) k))

/-- The supremum of the sampled running maxima is subadditive. -/
theorem iSup_dyadicRunMax_add_le (A B : ℝ → Ω → ℝ) (T : ℝ) (ω : Ω) :
    (⨆ n, (‖dyadicRunMax (fun t ω => A t ω + B t ω) T n ω‖₊ : ℝ≥0∞))
      ≤ (⨆ n, (‖dyadicRunMax A T n ω‖₊ : ℝ≥0∞))
        + ⨆ n, (‖dyadicRunMax B T n ω‖₊ : ℝ≥0∞) :=
  iSup_le fun n => le_trans (enorm_dyadicRunMax_add_le A B T n ω)
    (add_le_add (le_iSup (fun m => (‖dyadicRunMax A T m ω‖₊ : ℝ≥0∞)) n)
      (le_iSup (fun m => (‖dyadicRunMax B T m ω‖₊ : ℝ≥0∞)) n))

/-- A pathwise bound over the window bounds the supremum of the sampled running maxima. -/
theorem iSup_dyadicRunMax_le_of_bound {A : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 ≤ T) {ω : Ω} {c : ℝ≥0∞}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, (‖A t ω‖₊ : ℝ≥0∞) ≤ c) :
    (⨆ n, (‖dyadicRunMax A T n ω‖₊ : ℝ≥0∞)) ≤ c := by
  refine iSup_le fun n => ?_
  rw [enorm_dyadicRunMax]
  exact iSup_le fun k => h _ (dyadicTime_mem_Icc hT n (k : ℕ))

/-- The supremum over the window of a sum of squared coordinates is bounded by the sum of the
squared coordinatewise suprema. -/
theorem iSup_sum_sq_le {n' : ℕ} (A : ℝ → Ω → (Fin n' → ℝ)) (T : ℝ) (ω : Ω) :
    (⨆ t : Set.Icc (0 : ℝ) T, ∑ i, (‖A (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2)
      ≤ ∑ i, (⨆ t : Set.Icc (0 : ℝ) T, (‖A (t : ℝ) ω i‖₊ : ℝ≥0∞)) ^ 2 := by
  refine iSup_le fun t => Finset.sum_le_sum fun i _ => ?_
  exact pow_le_pow_left' (le_iSup (fun u : Set.Icc (0 : ℝ) T =>
    (‖A (u : ℝ) ω i‖₊ : ℝ≥0∞)) t) 2

/-! ### Finite sums -/

/-- A square of a finite sum is bounded by the sum of squares, up to the squared cardinality. -/
theorem sq_sum_le_card_sq_mul {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ≥0∞) ^ 2 * ∑ i ∈ s, f i ^ 2 := by
  have h1 : ∑ i ∈ s, f i ≤ (s.card : ℝ≥0∞) * s.sup f := by
    calc ∑ i ∈ s, f i ≤ ∑ _i ∈ s, s.sup f :=
          Finset.sum_le_sum fun i hi => Finset.le_sup hi
      _ = (s.card : ℝ≥0∞) * s.sup f := by rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : s.sup f ^ 2 ≤ ∑ i ∈ s, f i ^ 2 := by
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp
    · obtain ⟨i, hi, hieq⟩ := Finset.exists_mem_eq_sup s hne f
      rw [hieq]
      exact Finset.single_le_sum (f := fun j => f j ^ 2) (fun _ _ => zero_le) hi
  calc (∑ i ∈ s, f i) ^ 2 ≤ ((s.card : ℝ≥0∞) * s.sup f) ^ 2 := pow_le_pow_left' h1 2
    _ = (s.card : ℝ≥0∞) ^ 2 * s.sup f ^ 2 := by rw [mul_pow]
    _ ≤ (s.card : ℝ≥0∞) ^ 2 * ∑ i ∈ s, f i ^ 2 := mul_le_mul' le_rfl h2

/-- The sampled running maximum of a finite sum is bounded by the sum of the running maxima. -/
theorem enorm_dyadicRunMax_sum_le {ι : Type*} (s : Finset ι) (A : ι → ℝ → Ω → ℝ) (T : ℝ)
    (n : ℕ) (ω : Ω) :
    (‖dyadicRunMax (fun t ω => ∑ j ∈ s, A j t ω) T n ω‖₊ : ℝ≥0∞)
      ≤ ∑ j ∈ s, (‖dyadicRunMax (A j) T n ω‖₊ : ℝ≥0∞) := by
  rw [enorm_dyadicRunMax]
  refine iSup_le fun k => ?_
  have hpt : (‖∑ j ∈ s, A j (dyadicTime T n (k : ℕ)) ω‖₊ : ℝ≥0∞)
      ≤ ∑ j ∈ s, (‖A j (dyadicTime T n (k : ℕ)) ω‖₊ : ℝ≥0∞) := by
    rw [← ENNReal.ofNNReal_finsetSum]
    exact ENNReal.coe_le_coe.mpr (nnnorm_sum_le _ _)
  refine le_trans hpt (Finset.sum_le_sum fun j _ => ?_)
  rw [enorm_dyadicRunMax]
  exact le_iSup (fun m : Fin (2 ^ n + 1) =>
    (‖A j (dyadicTime T n (m : ℕ)) ω‖₊ : ℝ≥0∞)) k

/-- The supremum of the sampled running maxima of a finite sum is bounded by the sum of the
suprema. -/
theorem iSup_dyadicRunMax_sum_le {ι : Type*} (s : Finset ι) (A : ι → ℝ → Ω → ℝ) (T : ℝ)
    (ω : Ω) :
    (⨆ n, (‖dyadicRunMax (fun t ω => ∑ j ∈ s, A j t ω) T n ω‖₊ : ℝ≥0∞))
      ≤ ∑ j ∈ s, ⨆ n, (‖dyadicRunMax (A j) T n ω‖₊ : ℝ≥0∞) :=
  iSup_le fun n => le_trans (enorm_dyadicRunMax_sum_le s A T n ω)
    (Finset.sum_le_sum fun j _ => le_iSup (fun m => (‖dyadicRunMax (A j) T m ω‖₊ : ℝ≥0∞)) n)

end LevyStochCalc.Probability

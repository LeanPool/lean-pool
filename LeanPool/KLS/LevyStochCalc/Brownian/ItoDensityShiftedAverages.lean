/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0, with
-- source adaptations (deprecated names, proof-context visibility) listed in vendor/port.patch.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoDensityDyadicAverages

/-!
# Left-shifted dyadic averages and cell-average identities

The left-shifted dyadic cell averages, which on the interval `(t_{i-1}, t_i]` take the
average over the previous cell and are therefore adapted, the simple predictable process
they define, and the identification of a cell average with an average of the integrand
over a closed ball, through the dyadic index of a time `s ∈ (0, T]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Predictable shifted dyadic ξ.** For `i = 0`, returns `0`; for
`i ≥ 1`, returns the dyadic average over the PREVIOUS interval
`(t_{i-1}, t_i]` (so the value depends only on `g` up to time `t_i`,
hence is `ℱ_{t_i}`-measurable when `g` is adapted).

Used to construct `predictableDyadicSimple_brownian`, the analogue of
`dyadicSimplePredictable_brownian` whose ξ is predictable. -/
noncomputable def dyadicAvg_shifted_brownian
    (T : ℝ) (g : Ω → ℝ → ℝ) (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) : ℝ :=
  if h : i.val = 0 then 0
  else
    have h_lt : i.val - 1 < 2 ^ n := by omega
    dyadicAvg_brownian (T := T) g n ⟨i.val - 1, h_lt⟩ ω

-- `omit` the unused `[MeasurableSpace Ω]` section variable.
omit [MeasurableSpace Ω] in
/-- Boundedness of the shifted dyadic average. Bounded by `max M 0` to
handle the case `i = 0` (which is constant 0) uniformly. -/
lemma dyadicAvg_shifted_brownian_bounded
    (T : ℝ) (hT : 0 < T) (g : Ω → ℝ → ℝ) (M : ℝ)
    (h_bound : ∀ ω s, |g ω s| ≤ M) (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) :
    |dyadicAvg_shifted_brownian T g n i ω| ≤ max M 0 := by
  unfold dyadicAvg_shifted_brownian
  by_cases h : i.val = 0
  · rw [dite_eq_left h]
    rw [abs_zero]
    exact le_max_right _ _
  · rw [dite_eq_right h]
    have h_lt : i.val - 1 < 2 ^ n := by omega
    exact (dyadicAvg_brownian_bounded T hT g M h_bound n
      ⟨i.val - 1, h_lt⟩ ω).trans (le_max_left _ _)

/-- Measurability of the shifted dyadic average in `ω`. -/
lemma dyadicAvg_shifted_brownian_measurable
    (T : ℝ) (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (n : ℕ) (i : Fin (2 ^ n)) :
    Measurable (dyadicAvg_shifted_brownian T g n i) := by
  unfold dyadicAvg_shifted_brownian
  by_cases h : i.val = 0
  · simp only [h, ↓reduceDIte]
    exact measurable_const
  · simp only [h, ↓reduceDIte]
    have h_lt : i.val - 1 < 2 ^ n := by omega
    exact dyadicAvg_brownian_measurable T g h_meas n ⟨i.val - 1, h_lt⟩

/-- **Predictable shifted dyadic SimplePredictable.** Same partition as
`dyadicSimplePredictable_brownian`, but with ξ values from the
PREVIOUS dyadic interval (and ξ_0 = 0). When `g` is progressively
measurable for a filtration `ℱ`, this construction is predictable: each
`ξ_i` is `ℱ_{t_i}`-measurable (`predictableDyadicSimple_brownian_adapted`).

The L² convergence `(.eval) → g` for bounded measurable `g` is
`predictableDyadicSimple_brownian_L2_converges`. -/
noncomputable def predictableDyadicSimple_brownian
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) (n : ℕ) :
    SimplePredictable Ω T where
  N := 2 ^ n
  partition := dyadicPartition_brownian T n
  partition_zero := dyadicPartition_brownian_zero T n
  partition_le_T := dyadicPartition_brownian_le_T hT n
  partition_strictMono := dyadicPartition_brownian_strictMono hT n
  ξ := dyadicAvg_shifted_brownian T g n
  ξ_bounded := fun i =>
    ⟨max M 0, fun ω =>
      dyadicAvg_shifted_brownian_bounded T hT g M h_bound n i ω⟩
  ξ_measurable := dyadicAvg_shifted_brownian_measurable T g h_meas n

/-- **Predictability of `dyadicAvg_shifted_brownian`.** When `g` is
jointly measurable wrt `ℱ_t × Borel(ℝ)` for each `t` (i.e., progressively
measurable up to each time `t`), `dyadicAvg_shifted_brownian g n i` is
`ℱ_{t_i}`-StronglyMeasurable, where `t_i = dyadicPartition T n i.castSucc`.

Proof: for `i = 0`, ξ_0 = 0 (constant, trivially measurable). For `i ≥ 1`,
ξ_i is the dyadic average over `(t_{i-1}, t_i]`, which is the Bochner
integral of `g(·, s)` over `s ∈ (t_{i-1}, t_i]`. By
`MeasureTheory.StronglyMeasurable.integral_prod_right'`, the integral
inherits `ℱ_{t_i}`-measurability from the integrand's joint measurability. -/
lemma dyadicAvg_shifted_brownian_adapted
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (T : ℝ) (g : Ω → ℝ → ℝ)
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ g)
    (n : ℕ) (i : Fin (2 ^ n)) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (dyadicPartition_brownian T n i.castSucc))
      (dyadicAvg_shifted_brownian T g n i) := by
  unfold dyadicAvg_shifted_brownian
  by_cases h_i_zero : i.val = 0
  · -- Case i = 0: ξ_0 = 0, constant, StronglyMeasurable wrt anything.
    simp only [h_i_zero, ↓reduceDIte]
    exact MeasureTheory.stronglyMeasurable_const
  · -- Case i ≥ 1: ξ_i = dyadicAvg over (t_{i-1}, t_i], use integral_prod_right'.
    simp only [h_i_zero, ↓reduceDIte]
    -- The integrand: f(p) = g p.1 p.2 is StronglyMeas wrt ℱ_{t_i} × Borel.
    set t_i : ℝ := dyadicPartition_brownian T n i.castSucc with h_ti_def
    have h_succ_eq : dyadicPartition_brownian T n (⟨i.val - 1, by omega⟩ : Fin (2 ^ n)).succ
        = t_i := by
      rw [h_ti_def]
      congr 1
      ext
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    -- The average over `(t_{i-1}, t_i] ⊆ (-∞, t_i]` is `ℱ t_i`-measurable.
    have h_int_step : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ t_i)
        (fun ω => ∫ s in Set.Ioc
          (dyadicPartition_brownian T n (⟨i.val - 1, by omega⟩ : Fin (2 ^ n)).castSucc)
          (dyadicPartition_brownian T n (⟨i.val - 1, by omega⟩ : Fin (2 ^ n)).succ),
          g ω s) :=
      h_progMeas.stronglyMeasurable_setIntegral measurableSet_Ioc
        (Set.Ioc_subset_Iic_self.trans (Set.Iic_subset_Iic.mpr h_succ_eq.le)) volume
    -- Multiply by constant.
    have h_const_meas := h_int_step.const_mul ((2 ^ n : ℕ) / T : ℝ)
    -- This is exactly dyadicAvg_brownian g n ⟨i.val - 1, _⟩ ω.
    convert h_const_meas using 1
    rfl

/-- **Boundedness of the eval of `predictableDyadicSimple_brownian`.**
The eval at any (s, ω) is bounded by `max M 0`. -/
lemma predictableDyadicSimple_brownian_eval_bounded
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) (n : ℕ) (s : ℝ) (ω : Ω) :
    |(predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval s ω|
      ≤ max M 0 := by
  set H := predictableDyadicSimple_brownian hT g h_meas M h_bound n
  unfold SimplePredictable.eval
  by_cases h_any : ∃ i : Fin H.N,
      H.partition i.castSucc < s ∧ s ≤ H.partition i.succ
  · obtain ⟨i₀, hi₀⟩ := h_any
    have h_unique : ∀ j : Fin H.N, j ≠ i₀ →
        ¬(H.partition j.castSucc < s ∧ s ≤ H.partition j.succ) := by
      intro j hj hj_active
      rcases lt_or_gt_of_ne hj with hlt | hgt
      · have h_le : H.partition j.succ ≤ H.partition i₀.castSucc :=
          H.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr hlt)
        linarith [hj_active.2, hi₀.1]
      · have h_le : H.partition i₀.succ ≤ H.partition j.castSucc :=
          H.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr hgt)
        linarith [hi₀.2, hj_active.1]
    have h_sum_eq : (∑ i : Fin H.N,
        if H.partition i.castSucc < s ∧ s ≤ H.partition i.succ then H.ξ i ω else 0)
        = H.ξ i₀ ω := by
      rw [Finset.sum_eq_single i₀]
      · simp [hi₀]
      · intro j _ hj
        simp [h_unique j hj]
      · intro h_not; exact absurd (Finset.mem_univ _) h_not
    rw [h_sum_eq]
    exact dyadicAvg_shifted_brownian_bounded T hT g M h_bound n i₀ ω
  · have h_sum_zero : (∑ i : Fin H.N,
        if H.partition i.castSucc < s ∧ s ≤ H.partition i.succ then H.ξ i ω else 0)
        = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : H.partition i.castSucc < s ∧ s ≤ H.partition i.succ
      · exact absurd ⟨i, hi⟩ h_any
      · simp [hi]
    rw [h_sum_zero, abs_zero]
    exact le_max_right _ _

/-- **Predictability of `predictableDyadicSimple_brownian`.** Each `ξ_i`
is `ℱ_{t_i}`-StronglyMeasurable when `g` is progressively measurable. -/
lemma predictableDyadicSimple_brownian_adapted
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M)
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ g)
    (n : ℕ)
    (i : Fin (predictableDyadicSimple_brownian hT g h_meas M h_bound n).N) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((predictableDyadicSimple_brownian hT g h_meas M h_bound n).partition
          i.castSucc))
      ((predictableDyadicSimple_brownian hT g h_meas M h_bound n).ξ i) := by
  change @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (dyadicPartition_brownian T n i.castSucc))
    (dyadicAvg_shifted_brownian T g n i)
  exact dyadicAvg_shifted_brownian_adapted ℱ T g h_progMeas n i

/-- **Doubling measure instance for `(volume : Measure ℝ)`.** Mathlib's
`IsUnifLocDoublingMeasure` is not auto-inferred for `ℝ`; we provide it explicitly
via `Real.volume_closedBall` and the trivial doubling constant `K = 2`.

Once available, this unlocks `IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub`,
which gives the Lebesgue differentiation theorem in the form needed for
sub-lemma A (a.e. convergence of dyadic averages). -/
instance instIsUnifLocDoublingMeasureRealVolume :
    IsUnifLocDoublingMeasure (volume : Measure ℝ) := by
  refine ⟨(2 : NNReal), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε hε x
  rw [Real.volume_closedBall, Real.volume_closedBall]
  rw [ENNReal.coe_ofNat]
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by
    rw [show (2 : ℝ≥0∞) = ((2 : ℕ) : ℝ≥0∞) from by norm_cast]
    simp [ENNReal.ofReal_ofNat]]
  rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]

/-- **Auxiliary: Bounded measurable functions on `ℝ` are locally integrable.**
Used to invoke `IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub` on each
slice `g(ω, ·)`. -/
lemma bounded_locallyIntegrable
    (g : ℝ → ℝ) (h_meas : Measurable g) (M : ℝ) (h_bound : ∀ s, |g s| ≤ M) :
    MeasureTheory.LocallyIntegrable g volume := by
  intro x
  refine ⟨Set.Ioo (x - 1) (x + 1), isOpen_Ioo.mem_nhds (by simp), ?_⟩
  refine ⟨h_meas.aestronglyMeasurable, ?_⟩
  refine MeasureTheory.HasFiniteIntegral.restrict_of_bounded_enorm
    (C := ENNReal.ofReal M) ?_ ?_ ?_
  · simp
  · rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  · refine Filter.Eventually.of_forall (fun s => ?_)
    rw [show ‖g s‖ₑ = ENNReal.ofReal ‖g s‖ from (ofReal_norm _).symm]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.norm_eq_abs]
    exact h_bound s

/-- **Sub-lemma B (uniform L² boundedness):** The eval of dyadic SimplePredictable
is bounded by `M` everywhere, hence its L²(P × volume.restrict[0,T]) norm is
uniformly bounded by `M · √T`. Combined with `g`'s L² bound, ensures uniform
integrability. -/
lemma dyadicSimplePredictable_brownian_eval_bounded
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M)
    (n : ℕ) (s : ℝ) (ω : Ω) :
    |(dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval s ω| ≤ M := by
  set φ := dyadicSimplePredictable_brownian hT g h_meas M h_bound n with hφ
  have h_M_nn : (0 : ℝ) ≤ M := le_trans (abs_nonneg (g ω 0)) (h_bound ω 0)
  -- ξ bound for each i: dyadicAvg bounded by M.
  have h_each_bound : ∀ i : Fin φ.N, |φ.ξ i ω| ≤ M := fun i => by
    change |dyadicAvg_brownian (T := T) g n i ω| ≤ M
    exact dyadicAvg_brownian_bounded T hT g M h_bound n i ω
  -- At most one index i has `partition i.castSucc < s ∧ s ≤ partition i.succ`.
  have h_at_most_one : ∀ i j : Fin φ.N, i ≠ j →
      ¬((φ.partition i.castSucc < s ∧ s ≤ φ.partition i.succ) ∧
        (φ.partition j.castSucc < s ∧ s ≤ φ.partition j.succ)) := by
    intro i j hij ⟨⟨hi1, hi2⟩, ⟨hj1, hj2⟩⟩
    rcases lt_trichotomy i j with hlt | heq | hgt
    · -- i < j, so i.succ ≤ j.castSucc. Then s ≤ partition i.succ ≤ partition j.castSucc < s.
      have h_succ_le : i.succ ≤ j.castSucc := Fin.succ_le_castSucc_iff.mpr hlt
      have h_part_le : φ.partition i.succ ≤ φ.partition j.castSucc :=
        φ.partition_strictMono.monotone h_succ_le
      linarith
    · exact hij heq
    · have h_succ_le : j.succ ≤ i.castSucc := Fin.succ_le_castSucc_iff.mpr hgt
      have h_part_le : φ.partition j.succ ≤ φ.partition i.castSucc :=
        φ.partition_strictMono.monotone h_succ_le
      linarith
  unfold SimplePredictable.eval
  -- The sum `∑ i, (if cond_i then ξ_i ω else 0)` has at most one nonzero term.
  -- Case 1: some i fires. Sum = ξ i ω, |·| ≤ M.
  -- Case 2: no i fires. Sum = 0, |·| = 0 ≤ M.
  by_cases h_exists : ∃ i : Fin φ.N,
      φ.partition i.castSucc < s ∧ s ≤ φ.partition i.succ
  · obtain ⟨i, hi⟩ := h_exists
    have h_sum_eq : (∑ j : Fin φ.N,
        if φ.partition j.castSucc < s ∧ s ≤ φ.partition j.succ
        then φ.ξ j ω else 0) = φ.ξ i ω := by
      rw [Finset.sum_eq_single i]
      · exact ite_eq_left hi
      · intro j _ hji
        refine ite_eq_right ?_
        intro hj
        exact h_at_most_one i j (Ne.symm hji) ⟨hi, hj⟩
      · intro h_not_mem
        exact absurd (Finset.mem_univ i) h_not_mem
    rw [h_sum_eq]
    exact h_each_bound i
  · have h_sum_eq : (∑ j : Fin φ.N,
        if φ.partition j.castSucc < s ∧ s ≤ φ.partition j.succ
        then φ.ξ j ω else 0) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      refine ite_eq_right ?_
      intro hj
      exact h_exists ⟨j, hj⟩
    rw [h_sum_eq, abs_zero]
    exact h_M_nn

/-- **Sub-lemma C (uniform L² bound on Mathlib product space).** The eval functions
of the dyadic SimplePredictable, viewed as functions on `Ω × ℝ`, are uniformly
bounded by `M` (and hence L²-norm uniformly bounded by `M · √(P × T)`). -/
private lemma dyadicSimplePredictable_brownian_uncurried_bounded
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M)
    (n : ℕ) (p : Ω × ℝ) :
    |(dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1| ≤ M :=
  dyadicSimplePredictable_brownian_eval_bounded hT g h_meas M h_bound n p.2 p.1

/-- **Helper: closedBall = Icc on `ℝ`.** For `a ≤ b`, the closed ball with center
`(a+b)/2` and radius `(b-a)/2` equals `[a, b]`. Used in the dyadic-bridge to
identify `closedBall (midpoint) (half-length)` with the dyadic interval `[t_i, t_{i+1}]`. -/
private lemma closedBall_eq_Icc (a b : ℝ) :
    Metric.closedBall ((a + b) / 2) ((b - a) / 2) = Set.Icc a b := by
  ext x
  simp only [Metric.mem_closedBall, Real.dist_eq, Set.mem_Icc]
  constructor
  · intro h
    have h_abs : |x - (a + b) / 2| ≤ (b - a) / 2 := h
    have := abs_le.mp h_abs
    refine ⟨by linarith [this.1], by linarith [this.2]⟩
  · intro ⟨h1, h2⟩
    rw [abs_le]
    refine ⟨by linarith, by linarith⟩

/-- **Dyadic index function:** for `s ∈ (0, T]`, the index `i ∈ Fin (2^n)` such
that `s ∈ (i*T/2^n, (i+1)*T/2^n]`. Defined via the ceiling function. -/
noncomputable def dyadicIndex (n : ℕ) (T : ℝ) (hT : 0 < T) (s : ℝ)
    (hs : 0 < s ∧ s ≤ T) : Fin (2 ^ n) :=
  ⟨⌈s * (2 ^ n : ℕ) / T⌉₊ - 1, by
    have h_pos : (0 : ℝ) < s * (2 ^ n : ℕ) / T :=
      div_pos (mul_pos hs.1 (by positivity)) hT
    have h_le : s * (2 ^ n : ℕ) / T ≤ (2 ^ n : ℕ) := by
      rw [div_le_iff₀ hT]
      have : s * (2 ^ n : ℕ) ≤ T * (2 ^ n : ℕ) :=
        mul_le_mul_of_nonneg_right hs.2 (by positivity)
      linarith
    have h_ceil_le : ⌈s * (2 ^ n : ℕ) / T⌉₊ ≤ 2 ^ n := by
      rw [Nat.ceil_le]; exact_mod_cast h_le
    have h_ceil_pos : 0 < ⌈s * (2 ^ n : ℕ) / T⌉₊ := Nat.ceil_pos.mpr h_pos
    omega⟩

/-- **Dyadic index membership:** `s ∈ (t_{i_n(s)}, t_{i_n(s)+1}]` where
`t_i := i * T / 2^n`. -/
lemma dyadicIndex_mem (n : ℕ) (T : ℝ) (hT : 0 < T) (s : ℝ)
    (hs : 0 < s ∧ s ≤ T) :
    ((dyadicIndex n T hT s hs : ℕ) : ℝ) * T / (2 ^ n : ℕ) < s ∧
    s ≤ (((dyadicIndex n T hT s hs : ℕ) + 1) : ℝ) * T / (2 ^ n : ℕ) := by
  simp only [dyadicIndex]
  set k := ⌈s * (2 ^ n : ℕ) / T⌉₊ with hk_def
  have h_pos : (0 : ℝ) < s * (2 ^ n : ℕ) / T :=
    div_pos (mul_pos hs.1 (by positivity)) hT
  have hk_pos : 0 < k := Nat.ceil_pos.mpr h_pos
  have hk_ge : (s * (2 ^ n : ℕ) / T : ℝ) ≤ k := Nat.le_ceil _
  have hk_lt : (k : ℝ) - 1 < s * (2 ^ n : ℕ) / T := by
    have := Nat.ceil_lt_add_one (le_of_lt h_pos); linarith
  have h_pow : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
  have h_sub : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk_pos]; push_cast; ring
  refine ⟨?_, ?_⟩
  · rw [h_sub, div_lt_iff₀ h_pow]
    rw [lt_div_iff₀ hT] at hk_lt
    linarith
  · rw [show ((((k : ℕ) - 1 : ℕ) : ℝ) + 1) = (k : ℝ) by rw [h_sub]; ring]
    rw [le_div_iff₀ h_pow]
    rw [div_le_iff₀ hT] at hk_ge
    linarith

-- `omit` the unused `[MeasurableSpace Ω]` section variable.
omit [MeasurableSpace Ω] in
/-- **Average bridge:**
`dyadicAvg n i ω = ⨍ y in closedBall(midpoint, halfLen), g(ω, y) ∂volume`.

Here `midpoint := (t_i + t_{i+1})/2`, `halfLen := (t_{i+1} - t_i)/2 = T/2^(n+1)`.
The bridge uses:
- `closedBall_eq_Icc`: `closedBall(midpoint, halfLen) = Icc t_i t_{i+1}`.
- `Ioc_ae_eq_Icc`: a.e.-equality of `Ioc` and `Icc` (boundary `{t_i}` has measure 0).
- `Real.volume_Icc`: `vol(Icc t_i t_{i+1}) = T/2^n`. -/
lemma dyadicAvg_brownian_eq_average_closedBall
    {T : ℝ} (hT : 0 < T) (g : Ω → ℝ → ℝ) (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) :
    dyadicAvg_brownian (T := T) g n i ω =
      ⨍ y in Metric.closedBall
        ((dyadicPartition_brownian T n i.castSucc + dyadicPartition_brownian T n i.succ) / 2)
        ((dyadicPartition_brownian T n i.succ - dyadicPartition_brownian T n i.castSucc) / 2),
        g ω y ∂volume := by
  set t_i := dyadicPartition_brownian T n i.castSucc with ht_i
  set t_succ := dyadicPartition_brownian T n i.succ with ht_succ
  have h_lt : t_i < t_succ :=
    dyadicPartition_brownian_strictMono hT n Fin.castSucc_lt_succ
  have h_diff : t_succ - t_i = T / (2 ^ n : ℕ) :=
    dyadicPartition_brownian_diff n i
  have h_pow_pos : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
  -- closedBall (midpoint) (halfLen) = Icc t_i t_succ.
  have h_ball_eq : Metric.closedBall ((t_i + t_succ) / 2) ((t_succ - t_i) / 2) =
      Set.Icc t_i t_succ := closedBall_eq_Icc t_i t_succ
  rw [h_ball_eq]
  -- ⨍ Icc = ⨍ Ioc (since vol({t_i}) = 0).
  rw [show (volume.restrict (Set.Icc t_i t_succ) : Measure ℝ)
        = volume.restrict (Set.Ioc t_i t_succ)
      from MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc.symm]
  -- Now ⨍ over Ioc = (1/vol(Ioc)) * ∫ over Ioc.
  rw [MeasureTheory.average_eq]
  -- dyadicAvg = (2^n/T) * ∫ over Ioc.
  unfold dyadicAvg_brownian
  rw [show ((volume.restrict (Set.Ioc t_i t_succ) : Measure ℝ).real Set.univ)
      = t_succ - t_i from by
    unfold MeasureTheory.Measure.real
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    rw [Real.volume_Ioc]
    rw [ENNReal.toReal_ofReal (by linarith)]]
  rw [h_diff]
  -- (T/2^n)⁻¹ * ∫ ... = (2^n/T) * ∫ ...
  have h_T_ne : T ≠ 0 := ne_of_gt hT
  have h_pow_ne : ((2 ^ n : ℕ) : ℝ) ≠ 0 := ne_of_gt h_pow_pos
  rw [smul_eq_mul]
  field_simp
  ring

/-- **Eval at `s` equals `dyadicAvg` at `dyadicIndex n s`.** For `s ∈ (0, T]`,
`eval s ω = dyadicAvg n (i_n(s)) ω`, by collapsing the indicator sum to the
unique nonzero term. -/
lemma dyadicSimplePredictable_brownian_eval_eq_dyadicAvg
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M)
    (n : ℕ) (s : ℝ) (hs : 0 < s ∧ s ≤ T) (ω : Ω) :
    (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval s ω =
      dyadicAvg_brownian (T := T) g n (dyadicIndex n T hT s hs) ω := by
  let φ := dyadicSimplePredictable_brownian hT g h_meas M h_bound n
  let i := dyadicIndex n T hT s hs
  -- s ∈ (t_i, t_{i+1}], so the i-th indicator fires.
  have hi_mem := dyadicIndex_mem n T hT s hs
  have h_partition_castSucc : φ.partition i.castSucc =
      ((i : ℕ) : ℝ) * T / (2 ^ n : ℕ) := by
    change dyadicPartition_brownian T n i.castSucc = _
    unfold dyadicPartition_brownian
    push_cast
    simp [Fin.val_castSucc]
  have h_partition_succ : φ.partition i.succ =
      (((i : ℕ) + 1) : ℝ) * T / (2 ^ n : ℕ) := by
    change dyadicPartition_brownian T n i.succ = _
    unfold dyadicPartition_brownian
    push_cast
    simp [Fin.val_succ]
  -- The i-th indicator fires: t_i < s ≤ t_{i+1}.
  have h_i_fires : φ.partition i.castSucc < s ∧ s ≤ φ.partition i.succ := by
    rw [h_partition_castSucc, h_partition_succ]
    exact hi_mem
  -- For j ≠ i, the j-th indicator does NOT fire (partition strictly monotone).
  have h_j_not_fires : ∀ j : Fin (2 ^ n), j ≠ i →
      ¬(φ.partition j.castSucc < s ∧ s ≤ φ.partition j.succ) := by
    intro j hji ⟨hj1, hj2⟩
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have h_succ_le : i.succ ≤ j.castSucc := Fin.succ_le_castSucc_iff.mpr hlt
      have h_part_le : φ.partition i.succ ≤ φ.partition j.castSucc :=
        φ.partition_strictMono.monotone h_succ_le
      have hi_le : s ≤ φ.partition i.succ := h_i_fires.2
      linarith
    · exact hji heq.symm
    · have h_succ_le : j.succ ≤ i.castSucc := Fin.succ_le_castSucc_iff.mpr hgt
      have h_part_le : φ.partition j.succ ≤ φ.partition i.castSucc :=
        φ.partition_strictMono.monotone h_succ_le
      have hi_lt : φ.partition i.castSucc < s := h_i_fires.1
      linarith
  -- Now collapse the sum.
  change (∑ j : Fin φ.N, if φ.partition j.castSucc < s ∧ s ≤ φ.partition j.succ
                       then φ.ξ j ω else 0) = dyadicAvg_brownian g n i ω
  change (∑ j : Fin (2 ^ n), if φ.partition j.castSucc < s ∧ s ≤ φ.partition j.succ
                            then φ.ξ j ω else 0) = dyadicAvg_brownian g n i ω
  rw [Finset.sum_eq_single i]
  · rw [ite_eq_left h_i_fires]
    change dyadicAvg_brownian (T := T) g n i ω = dyadicAvg_brownian g n i ω
    rfl
  · intro j _ hji
    refine ite_eq_right ?_
    intro hj
    exact h_j_not_fires j hji hj
  · intro h_not_mem
    exact absurd (Finset.mem_univ i) h_not_mem

/-- **Eval of `predictableDyadicSimple_brownian` at `s` equals
`dyadicAvg_shifted_brownian`.** For `s ∈ (0, T]`, eval at `s` equals the
shifted dyadic average at index `dyadicIndex n s`. -/
lemma predictableDyadicSimple_brownian_eval_eq_shifted
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M)
    (n : ℕ) (s : ℝ) (hs : 0 < s ∧ s ≤ T) (ω : Ω) :
    (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval s ω =
      dyadicAvg_shifted_brownian (T := T) g n (dyadicIndex n T hT s hs) ω := by
  let φ := predictableDyadicSimple_brownian hT g h_meas M h_bound n
  let i := dyadicIndex n T hT s hs
  -- s ∈ (t_i, t_{i+1}], so the i-th indicator fires.
  have hi_mem := dyadicIndex_mem n T hT s hs
  have h_partition_castSucc : φ.partition i.castSucc =
      ((i : ℕ) : ℝ) * T / (2 ^ n : ℕ) := by
    change dyadicPartition_brownian T n i.castSucc = _
    unfold dyadicPartition_brownian
    push_cast
    simp [Fin.val_castSucc]
  have h_partition_succ : φ.partition i.succ =
      (((i : ℕ) + 1) : ℝ) * T / (2 ^ n : ℕ) := by
    change dyadicPartition_brownian T n i.succ = _
    unfold dyadicPartition_brownian
    push_cast
    simp [Fin.val_succ]
  have h_i_fires : φ.partition i.castSucc < s ∧ s ≤ φ.partition i.succ := by
    rw [h_partition_castSucc, h_partition_succ]
    exact hi_mem
  have h_j_not_fires : ∀ j : Fin (2 ^ n), j ≠ i →
      ¬(φ.partition j.castSucc < s ∧ s ≤ φ.partition j.succ) := by
    intro j hji ⟨hj1, hj2⟩
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have h_succ_le : i.succ ≤ j.castSucc := Fin.succ_le_castSucc_iff.mpr hlt
      have h_part_le : φ.partition i.succ ≤ φ.partition j.castSucc :=
        φ.partition_strictMono.monotone h_succ_le
      have hi_le : s ≤ φ.partition i.succ := h_i_fires.2
      linarith
    · exact hji heq.symm
    · have h_succ_le : j.succ ≤ i.castSucc := Fin.succ_le_castSucc_iff.mpr hgt
      have h_part_le : φ.partition j.succ ≤ φ.partition i.castSucc :=
        φ.partition_strictMono.monotone h_succ_le
      have hi_lt : φ.partition i.castSucc < s := h_i_fires.1
      linarith
  change (∑ j : Fin φ.N, if φ.partition j.castSucc < s ∧ s ≤ φ.partition j.succ
                       then φ.ξ j ω else 0) = dyadicAvg_shifted_brownian T g n i ω
  change (∑ j : Fin (2 ^ n), if φ.partition j.castSucc < s ∧ s ≤ φ.partition j.succ
                            then φ.ξ j ω else 0) = dyadicAvg_shifted_brownian T g n i ω
  rw [Finset.sum_eq_single i]
  · rw [ite_eq_left h_i_fires]
    change dyadicAvg_shifted_brownian T g n i ω = dyadicAvg_shifted_brownian T g n i ω
    rfl
  · intro j _ hji
    refine ite_eq_right ?_
    intro hj
    exact h_j_not_fires j hji hj
  · intro h_not_mem
    exact absurd (Finset.mem_univ i) h_not_mem
end LevyStochCalc.Brownian.Ito

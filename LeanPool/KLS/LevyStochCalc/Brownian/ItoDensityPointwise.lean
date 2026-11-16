/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-27 by the KLS formalization project: update deprecated aliases and
-- proof-local bindings for warning-free Lean v4.33.0 builds; see vendor/port.patch.

-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0, with
-- source adaptations (deprecated names, proof-context visibility) listed in vendor/port.patch.
-- Modified 2026-10-31 by the KLS formalization project: add an explicit public import of
-- Mathlib.MeasureTheory.Covering.DensityTheorem, which provides
-- `IsUnifLocDoublingMeasure.ae_tendsto_average` and is no longer reachable transitively in
-- Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoDensityShiftedAverages
public import Mathlib.MeasureTheory.Covering.DensityTheorem

/-!
# Almost-everywhere convergence of the dyadic averages

Lebesgue differentiation for a bounded jointly measurable integrand: the dyadic cell
averages, shifted and unshifted, converge to the integrand at almost every point of
`Ω × [0,T]`, and for the unshifted family the convergence also holds in `L²`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Step A1.0: Apply IsUnifLocDoublingMeasure.ae_tendsto_average to `g(ω, ·)`.**
For each ω, the average of g(ω, ·) over shrinking closed balls converges to g(ω, ·)
at almost every point.

This is the direct invocation of the Mathlib Lebesgue differentiation theorem,
made available by `instIsUnifLocDoublingMeasureRealVolume`. -/
private lemma g_omega_ae_tendsto_average
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M)
    (ω : Ω) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      ∀ {ι : Type} {l : Filter ι} (w : ι → ℝ) (δ : ι → ℝ),
        Filter.Tendsto δ l (nhdsWithin 0 (Set.Ioi 0)) →
        (∀ᶠ j in l, x ∈ Metric.closedBall (w j) (1 * δ j)) →
        Filter.Tendsto
          (fun j => ⨍ y in Metric.closedBall (w j) (δ j), g ω y ∂volume)
            l (nhds (g ω x)) := by
  have h_loc_int : MeasureTheory.LocallyIntegrable (g ω) volume :=
    bounded_locallyIntegrable (g ω)
      (h_meas.comp (by fun_prop : Measurable (fun s : ℝ => (ω, s))))
      M (h_bound ω)
  exact IsUnifLocDoublingMeasure.ae_tendsto_average volume h_loc_int 1

/-- **Sub-sub-lemma A1: per-ω a.e. dyadic convergence.** For each fixed `ω`, the
dyadic averages of `g(ω, ·)` converge to `g(ω, ·)` a.e. on `[0, T]`.

The substantive remaining step is the dyadic-bridge: showing that for a.e. `s`,
the dyadic eval `eval n s ω` (= `(2^n/T) ∫_{(t_i, t_{i+1}]} g(ω, y) dy` for the
dyadic piece containing `s`) coincides with the Mathlib closed-ball average
`⨍ y in closedBall (midpoint) (half-length), g(ω, y) ∂volume`.

The closed-ball-to-dyadic-interval bridge:
- For dyadic level `n`, piece `i`: `t_i := i*T/2^n`, `t_{i+1} := (i+1)*T/2^n`.
- `midpoint := (t_i + t_{i+1})/2 = ((2i+1)*T/2^(n+1))`.
- `half-length := T/2^(n+1)`.
- `closedBall midpoint half-length = [t_i, t_{i+1}]`.
- `volume [t_i, t_{i+1}] = T/2^n = volume (t_i, t_{i+1}]` (boundary `{t_i}` has measure 0).
- Therefore `⨍ y in closedBall = (2^n/T) ∫_{[t_i, t_{i+1}]} g(ω, y) dy
                              = (2^n/T) ∫_{(t_i, t_{i+1}]} g(ω, y) dy = dyadicAvg`.
- And `eval s ω = dyadicAvg n i_n(s) ω` where `i_n(s)` is the dyadic index of `s`. -/
private lemma dyadic_pointwise_tendsto_per_omega
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M)
    (ω : Ω) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto
        (fun n => (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval s ω)
        Filter.atTop (nhds (g ω s)) := by
  -- Filter into volume.restrict-a.e. and exclude {0} which has volume 0.
  have h_lebesgue := g_omega_ae_tendsto_average g h_meas M h_bound ω
  -- Restrict the volume-a.e. property to volume.restrict (Icc 0 T)-a.e.
  have h_lebesgue_restrict : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∀ {ι : Type} {l : Filter ι} (w : ι → ℝ) (δ : ι → ℝ),
        Filter.Tendsto δ l (nhdsWithin 0 (Set.Ioi 0)) →
        (∀ᶠ j in l, x ∈ Metric.closedBall (w j) (1 * δ j)) →
        Filter.Tendsto
          (fun j => ⨍ y in Metric.closedBall (w j) (δ j), g ω y ∂volume) l (nhds (g ω x)) :=
    MeasureTheory.ae_restrict_of_ae h_lebesgue
  -- Exclude {0} via measure-zero set on the full measure.
  have h_pos_ae : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    have : {x : ℝ | ¬(x ≠ 0)} = {(0 : ℝ)} := by ext; simp
    rw [this, Real.volume_singleton]
  -- Restrict in domain to s ∈ Icc 0 T explicitly.
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc] at h_lebesgue_restrict
  filter_upwards [h_lebesgue_restrict, h_pos_ae] with x h_lebesgue_at_x hx_ne_zero hx_mem
  -- For x ∈ Icc 0 T with x ≠ 0, x > 0 (since x ≥ 0 from Icc).
  have hx_strict_pos : 0 < x := lt_of_le_of_ne hx_mem.1 (Ne.symm hx_ne_zero)
  have hx : 0 < x ∧ x ≤ T := ⟨hx_strict_pos, hx_mem.2⟩
  -- Apply Mathlib lemma with dyadic sequence.
  set w : ℕ → ℝ := fun n =>
    (dyadicPartition_brownian T n (dyadicIndex n T hT x hx).castSucc +
     dyadicPartition_brownian T n (dyadicIndex n T hT x hx).succ) / 2
  set δ : ℕ → ℝ := fun n =>
    (dyadicPartition_brownian T n (dyadicIndex n T hT x hx).succ -
     dyadicPartition_brownian T n (dyadicIndex n T hT x hx).castSucc) / 2
  have h_delta_eq : ∀ n, δ n = T / (2 * (2 ^ n : ℕ)) := by
    intro n
    change (dyadicPartition_brownian T n (dyadicIndex n T hT x hx).succ -
          dyadicPartition_brownian T n (dyadicIndex n T hT x hx).castSucc) / 2 = _
    rw [dyadicPartition_brownian_diff n (dyadicIndex n T hT x hx)]
    ring
  -- δ n → 0 in nhdsWithin 0 (Ioi 0).
  have h_delta_pos : ∀ n, 0 < δ n := by
    intro n
    rw [h_delta_eq]
    have : (0 : ℝ) < 2 * (2 ^ n : ℕ) := by positivity
    exact div_pos hT this
  have h_delta_to_zero : Filter.Tendsto δ Filter.atTop (nhds 0) := by
    have h_eq : δ = fun n => T / (2 * (2 ^ n : ℕ)) := funext h_delta_eq
    rw [h_eq]
    -- 2 * (2^n : ℕ) → ∞ as n → ∞.
    have h_2pow : Filter.Tendsto (fun n : ℕ => 2 * ((2 ^ n : ℕ) : ℝ))
        Filter.atTop Filter.atTop := by
      have h_pow_atTop : Filter.Tendsto (fun n : ℕ => ((2 ^ n : ℕ) : ℝ))
          Filter.atTop Filter.atTop := by
        have : Filter.Tendsto (fun n : ℕ => (2 ^ n : ℕ)) Filter.atTop Filter.atTop :=
          tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2)
        exact tendsto_natCast_atTop_iff.mpr this
      exact h_pow_atTop.atTop_mul_const' (by norm_num : (0 : ℝ) < 2) |>.congr
        (fun n => by ring)
    -- T / (2 * 2^n) → T / ∞ = 0.
    exact Filter.Tendsto.div_atTop tendsto_const_nhds h_2pow
  have h_delta_tendsto : Filter.Tendsto δ Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨h_delta_to_zero, ?_⟩
    exact Filter.Eventually.of_forall h_delta_pos
  -- x ∈ closedBall (w n) (1 * δ n) for all n.
  have h_x_in_ball : ∀ n, x ∈ Metric.closedBall (w n) (1 * δ n) := by
    intro n
    rw [one_mul]
    change |x - w n| ≤ δ n
    have h_mem := dyadicIndex_mem n T hT x hx
    set t_i := dyadicPartition_brownian T n (dyadicIndex n T hT x hx).castSucc with ht_i
    set t_succ := dyadicPartition_brownian T n (dyadicIndex n T hT x hx).succ with ht_succ
    have h_x1 : t_i < x := by
      have h := h_mem.1
      change dyadicPartition_brownian T n (dyadicIndex n T hT x hx).castSucc < x
      unfold dyadicPartition_brownian
      push_cast at h ⊢
      simpa [Fin.val_castSucc] using h
    have h_x2 : x ≤ t_succ := by
      have h := h_mem.2
      change x ≤ dyadicPartition_brownian T n (dyadicIndex n T hT x hx).succ
      unfold dyadicPartition_brownian
      push_cast at h ⊢
      simpa [Fin.val_succ] using h
    change |x - (t_i + t_succ) / 2| ≤ (t_succ - t_i) / 2
    rw [abs_le]
    refine ⟨by linarith, by linarith⟩
  -- Apply the Mathlib lemma.
  have h_avg_to_g := h_lebesgue_at_x hx_mem (l := Filter.atTop) w δ h_delta_tendsto
    (Filter.Eventually.of_forall h_x_in_ball)
  -- Bridge: ⨍ over closedBall = dyadicAvg = eval.
  have h_bridge : ∀ n,
      (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval x ω =
      ⨍ y in Metric.closedBall (w n) (δ n), g ω y ∂volume := by
    intro n
    rw [dyadicSimplePredictable_brownian_eval_eq_dyadicAvg hT g h_meas M h_bound n x hx ω]
    exact dyadicAvg_brownian_eq_average_closedBall hT g n (dyadicIndex n T hT x hx) ω
  -- Combine.
  have h_eq_seq : (fun n => (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval x ω)
      = fun n => ⨍ y in Metric.closedBall (w n) (δ n), g ω y ∂volume :=
    funext h_bridge
  rw [h_eq_seq]
  exact h_avg_to_g

/-- **Joint measurability of the convergence set.** The set
`{(ω, s) | Tendsto (eval n s ω) atTop (𝓝 (g ω s))}` is measurable.

Proof: `Tendsto _ atTop (𝓝 (g ω s))` is equivalent to
`Tendsto (eval n - g ω s) atTop (𝓝 0)`,
i.e., convergence to the fixed limit 0 of a jointly measurable sequence. By
`measurableSet_tendsto`, this set is measurable. -/
private lemma convergence_set_measurable
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    MeasurableSet
      {p : Ω × ℝ | Filter.Tendsto
        (fun n => (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds (g p.1 p.2))} := by
  -- Rewrite convergence to (g ω s) as convergence of difference to 0.
  have h_eq : {p : Ω × ℝ | Filter.Tendsto
        (fun n => (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds (g p.1 p.2))}
      = {p : Ω × ℝ | Filter.Tendsto
        (fun n => (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1
          - g p.1 p.2)
        Filter.atTop (nhds 0)} := by
    ext p
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hp
      have h_const : Filter.Tendsto (fun _ : ℕ => g p.1 p.2)
        Filter.atTop (nhds (g p.1 p.2)) := tendsto_const_nhds
      simpa using hp.sub h_const
    · intro hp
      have h_const : Filter.Tendsto (fun _ : ℕ => g p.1 p.2)
        Filter.atTop (nhds (g p.1 p.2)) := tendsto_const_nhds
      simpa using hp.add h_const
  rw [h_eq]
  -- The sequence is jointly measurable in (ω, s).
  have h_seq_meas : ∀ n, Measurable (fun (p : Ω × ℝ) =>
      (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1
        - g p.1 p.2) := by
    intro n
    have h_eval_meas : Measurable (fun p : Ω × ℝ =>
        (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1) := by
      unfold SimplePredictable.eval
      refine Finset.measurable_sum _ ?_
      intro i _
      refine Measurable.ite ?_ ?_ measurable_const
      · refine MeasurableSet.inter ?_ ?_
        · exact measurable_snd (measurableSet_Ioi
            (a := (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).partition i.castSucc))
        · exact measurable_snd (measurableSet_Iic
            (a := (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).partition i.succ))
      · exact (dyadicAvg_brownian_measurable T g h_meas n i).comp measurable_fst
    exact h_eval_meas.sub
      (h_meas.comp (by fun_prop : Measurable (fun (p : Ω × ℝ) => (p.1, p.2))))
  exact measurableSet_tendsto (nhds (0 : ℝ)) h_seq_meas

private lemma dyadicSimplePredictable_brownian_ae_tendsto
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      Filter.Tendsto
        (fun n => (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds (g p.1 p.2)) := by
  -- Use `MeasureTheory.Measure.ae_prod_iff_ae_ae` to lift "for each ω, ∀ᵐ s" to
  -- "∀ᵐ (ω, s) ∂(P × volume.restrict)".
  rw [MeasureTheory.Measure.ae_prod_iff_ae_ae
    (convergence_set_measurable hT g h_meas M h_bound)]
  refine Filter.Eventually.of_forall (fun ω => ?_)
  exact dyadic_pointwise_tendsto_per_omega hT g h_meas M h_bound ω

lemma dyadicSimplePredictable_brownian_L2_converges
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖g ω s - (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval s ω‖₊
          : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (nhds 0) := by
  -- Setup: finite measure on the product.
  have h_finite_vol : MeasureTheory.IsFiniteMeasure
      (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    refine ⟨?_⟩
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have h_finite_prod : MeasureTheory.IsFiniteMeasure
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := inferInstance
  -- The constant bound: 2(|M|+1) ≥ |g - eval| everywhere (using triangle ineq + boundedness).
  set CC : ℝ := 2 * (|M| + 1) with hCC
  have hCC_pos : (0 : ℝ) < CC := by
    have : (0 : ℝ) ≤ |M| := abs_nonneg _
    rw [hCC]; linarith
  have hCC_nn : (0 : ℝ) ≤ CC := le_of_lt hCC_pos
  -- Integrand on product space.
  set F : ℕ → Ω × ℝ → ℝ≥0∞ := fun n p =>
    (‖g p.1 p.2 -
       (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞) ^ 2 with hF_def
  -- F n p ≤ ENNReal.ofReal (CC²) everywhere.
  have h_F_bound : ∀ n p, F n p ≤ ENNReal.ofReal (CC ^ 2) := by
    intro n p
    have h_norm_le : ‖g p.1 p.2 -
        (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖ ≤ CC := by
      rw [Real.norm_eq_abs]
      have h1 : |g p.1 p.2| ≤ M := h_bound p.1 p.2
      have h2 : |(dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1| ≤ M :=
        dyadicSimplePredictable_brownian_eval_bounded hT g h_meas M h_bound n p.2 p.1
      have h_abs_M : M ≤ |M| := le_abs_self _
      have h12 : |g p.1 p.2 -
          (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1|
          ≤ |g p.1 p.2|
            + |(dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1| :=
        abs_sub _ _
      rw [hCC]; linarith
    have h_norm_nn : 0 ≤ ‖g p.1 p.2 -
        (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖ := norm_nonneg _
    change (‖g p.1 p.2 -
       (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal (CC ^ 2)
    have : ((‖g p.1 p.2 -
       (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞)) = ENNReal.ofReal ‖g p.1 p.2 -
       (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖ :=
      (ofReal_norm _).symm
    rw [this, ← ENNReal.ofReal_pow h_norm_nn]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_nonneg (g p.1 p.2 -
       (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1)]
  -- AEMeasurable of F n on the product.
  have h_F_meas : ∀ n, Measurable (F n) := by
    intro n
    change Measurable (fun (p : Ω × ℝ) => (‖g p.1 p.2 -
       (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞) ^ 2)
    have h_eval_meas : Measurable (fun p : Ω × ℝ =>
        (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1) := by
      unfold SimplePredictable.eval
      refine Finset.measurable_sum _ ?_
      intro i _
      refine Measurable.ite ?_ ?_ measurable_const
      · refine MeasurableSet.inter ?_ ?_
        · exact measurable_snd (measurableSet_Ioi
            (a := (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).partition i.castSucc))
        · exact measurable_snd (measurableSet_Iic
            (a := (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).partition i.succ))
      · exact (dyadicAvg_brownian_measurable T g h_meas n i).comp measurable_fst
    have h_diff : Measurable (fun p : Ω × ℝ =>
        g p.1 p.2 -
        (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1) :=
      (h_meas.comp (by fun_prop : Measurable (fun (p : Ω × ℝ) => (p.1, p.2)))).sub h_eval_meas
    exact ((ENNReal.continuous_coe.measurable.comp h_diff.nnnorm)).pow_const 2
  -- Bound is integrable (constant on finite measure space).
  have h_bound_integrable : ∫⁻ _ : Ω × ℝ, ENNReal.ofReal (CC ^ 2)
      ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) ≠ ⊤ := by
    rw [MeasureTheory.lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (MeasureTheory.measure_ne_top _ _)
  -- a.e. convergence on the product (consumes sub-lemma A).
  have h_F_ae : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      Filter.Tendsto (fun n => F n p) Filter.atTop (nhds 0) := by
    have h_ae := dyadicSimplePredictable_brownian_ae_tendsto (P := P) hT g h_meas M h_bound
    filter_upwards [h_ae] with p hp
    -- F n p = ‖g - eval‖² → 0 since ‖g - eval‖ → 0 (from eval → g).
    change Filter.Tendsto (fun n => (‖g p.1 p.2 -
       (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞) ^ 2) Filter.atTop (nhds 0)
    have h_diff_zero : Filter.Tendsto
        (fun n => g p.1 p.2 -
       (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds 0) := by
      have hp' : Filter.Tendsto
        (fun n => (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds (g p.1 p.2)) := hp
      have h_const : Filter.Tendsto (fun _ : ℕ => g p.1 p.2)
        Filter.atTop (nhds (g p.1 p.2)) := tendsto_const_nhds
      simpa using h_const.sub hp'
    have h_norm_zero : Filter.Tendsto
        (fun n => ‖g p.1 p.2 -
       (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊)
        Filter.atTop (nhds 0) := by
      rw [show (0 : ℝ≥0) = ‖(0 : ℝ)‖₊ from by simp]
      exact (continuous_nnnorm.tendsto _).comp h_diff_zero
    have h_enorm_zero : Filter.Tendsto
        (fun n => ((‖g p.1 p.2 -
       (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞)))
        Filter.atTop (nhds 0) := by
      rw [show (0 : ℝ≥0∞) = ((0 : ℝ≥0) : ℝ≥0∞) from by simp]
      exact (ENNReal.continuous_coe.tendsto _).comp h_norm_zero
    -- Compose: (·)² is continuous on ℝ≥0∞, so tendsto preserves it.
    have h_sq_continuous : Continuous (fun x : ℝ≥0∞ => x ^ 2) := by
      exact ENNReal.continuous_pow 2
    have : Filter.Tendsto (fun n => ((‖g p.1 p.2 -
       (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞)) ^ 2) Filter.atTop (nhds ((0 : ℝ≥0∞) ^ 2)) :=
      (h_sq_continuous.tendsto _).comp h_enorm_zero
    simpa using this
  -- Apply DCT on the product space.
  have h_DCT : Filter.Tendsto
      (fun n => ∫⁻ p, F n p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))))
      Filter.atTop (nhds 0) := by
    have h_target : Filter.Tendsto (fun n => ∫⁻ p, F n p
          ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))))
        Filter.atTop
        (nhds (∫⁻ _ : Ω × ℝ, (0 : ℝ≥0∞)
          ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))))) := by
      refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
        (bound := fun _ => ENNReal.ofReal (CC ^ 2))
        (fun n => (h_F_meas n).aemeasurable)
        ?_ h_bound_integrable h_F_ae
      intro n
      exact Filter.Eventually.of_forall (fun p => h_F_bound n p)
    simpa using h_target
  -- Convert iterated to product via Fubini.
  -- The iterated form ∫⁻ ω, ∫⁻ s in Icc 0 T, F p_swapped ∂vol ∂P equals
  -- ∫⁻ p, F p ∂(P × vol.restrict (Icc 0 T)).
  have h_eq : ∀ n, (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖g ω s - (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval s ω‖₊
          : ℝ≥0∞) ^ 2 ∂volume ∂P)
      = ∫⁻ p, F n p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
    intro n
    rw [MeasureTheory.lintegral_prod _ (h_F_meas n).aemeasurable]
  simp_rw [h_eq]
  exact h_DCT

/-- **Pointwise convergence for predictable shifted dyadic.** For each `ω`, the
predictable shifted dyadic SimplePredictable converges to `g(ω, ·)` a.e. on `[0, T]`.

The key difference from `dyadic_pointwise_tendsto_per_omega`: the eval uses the
LEFT-tangent interval `(t_{i-1}, t_i]` instead of the containing interval
`(t_i, t_{i+1}]`. Apply Vitali's differentiation theorem with K = 3 since the
tangent interval is at distance ≤ 3·δ from `s`. -/
lemma predictable_pointwise_tendsto_per_omega
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M)
    (ω : Ω) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto
        (fun n => (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval s ω)
        Filter.atTop (nhds (g ω s)) := by
  -- K = 3 Vitali on g(ω, ·).
  have h_loc_int : MeasureTheory.LocallyIntegrable (g ω) volume :=
    bounded_locallyIntegrable (g ω)
      (h_meas.comp (by fun_prop : Measurable (fun s : ℝ => (ω, s))))
      M (h_bound ω)
  have h_vitali_K3 := IsUnifLocDoublingMeasure.ae_tendsto_average volume h_loc_int 3
  have h_vitali_restrict : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∀ {ι : Type} {l : Filter ι} (w : ι → ℝ) (δ : ι → ℝ),
        Filter.Tendsto δ l (nhdsWithin 0 (Set.Ioi 0)) →
        (∀ᶠ j in l, x ∈ Metric.closedBall (w j) (3 * δ j)) →
        Filter.Tendsto
          (fun j => ⨍ y in Metric.closedBall (w j) (δ j), g ω y ∂volume) l
            (nhds (g ω x)) :=
    MeasureTheory.ae_restrict_of_ae h_vitali_K3
  -- Exclude {0}.
  have h_pos_ae : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    have : {x : ℝ | ¬(x ≠ 0)} = {(0 : ℝ)} := by ext; simp
    rw [this, Real.volume_singleton]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc] at h_vitali_restrict
  filter_upwards [h_vitali_restrict, h_pos_ae] with x h_vitali_at_x hx_ne_zero hx_mem
  have hx_strict_pos : 0 < x := lt_of_le_of_ne hx_mem.1 (Ne.symm hx_ne_zero)
  have hx : 0 < x ∧ x ≤ T := ⟨hx_strict_pos, hx_mem.2⟩
  -- Half-width δ_n = T/2^{n+1}.
  set δ : ℕ → ℝ := fun n => T / (2 * (2 ^ n : ℕ)) with hδ_def
  -- Center w_n = (i - 1/2) * T/2^n.  For i ≥ 1, this is the midpoint of (t_{i-1}, t_i].
  -- For i = 0 (which is eventually false), this is a dummy value.
  set w : ℕ → ℝ := fun n =>
    (((dyadicIndex n T hT x hx).val : ℝ) - 1/2) * (T / ((2 ^ n : ℕ) : ℝ))
    with hw_def
  -- δ → 0 in nhdsWithin 0 (Ioi 0).
  have h_delta_pos : ∀ n, 0 < δ n := fun n => by
    change 0 < T / (2 * (2 ^ n : ℕ))
    have : (0 : ℝ) < 2 * (2 ^ n : ℕ) := by positivity
    exact div_pos hT this
  have h_delta_to_zero : Filter.Tendsto δ Filter.atTop (nhds 0) := by
    have h_2pow : Filter.Tendsto (fun n : ℕ => 2 * ((2 ^ n : ℕ) : ℝ))
        Filter.atTop Filter.atTop := by
      have h_pow_atTop : Filter.Tendsto (fun n : ℕ => ((2 ^ n : ℕ) : ℝ))
          Filter.atTop Filter.atTop := by
        have : Filter.Tendsto (fun n : ℕ => (2 ^ n : ℕ)) Filter.atTop Filter.atTop :=
          tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2)
        exact tendsto_natCast_atTop_iff.mpr this
      exact h_pow_atTop.atTop_mul_const' (by norm_num : (0 : ℝ) < 2) |>.congr
        (fun n => by ring)
    exact Filter.Tendsto.div_atTop tendsto_const_nhds h_2pow
  have h_delta_tendsto : Filter.Tendsto δ Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨h_delta_to_zero, ?_⟩
    exact Filter.Eventually.of_forall h_delta_pos
  -- Eventually 0 < (dyadicIndex n s).val (i.e., for n large, i ≥ 1).
  have h_eventually_i_pos :
      ∀ᶠ n in Filter.atTop, 0 < (dyadicIndex n T hT x hx).val := by
    -- For n large enough, T/2^n < x → t_1 ≤ x → i ≥ 1.
    have h_pow_to_inf : Filter.Tendsto (fun n : ℕ => ((2 ^ n : ℕ) : ℝ))
        Filter.atTop Filter.atTop := by
      have : Filter.Tendsto (fun n : ℕ => (2 ^ n : ℕ)) Filter.atTop Filter.atTop :=
        tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2)
      exact tendsto_natCast_atTop_iff.mpr this
    have h_T_div_pow : Filter.Tendsto (fun n : ℕ => T / ((2 ^ n : ℕ) : ℝ))
        Filter.atTop (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds h_pow_to_inf
    have h_evnt : ∀ᶠ n in Filter.atTop, T / ((2 ^ n : ℕ) : ℝ) < x := by
      have := h_T_div_pow.eventually_lt_const hx_strict_pos
      exact this
    filter_upwards [h_evnt] with n hn
    -- (dyadicIndex n T hT x hx).val > 0: from dyadicIndex_mem, t_i < x ≤ t_{i+1}.
    -- If i.val = 0, then t_i = 0 and t_{i+1} = T/2^n. Since t_{i+1} ≥ x means
    -- T/2^n ≥ x, contradicting hn.
    by_contra h_not_pos
    push Not at h_not_pos
    have h_i_zero : (dyadicIndex n T hT x hx).val = 0 := Nat.eq_zero_of_le_zero h_not_pos
    have hi_mem := dyadicIndex_mem n T hT x hx
    have h_x_le : x ≤ T / ((2 ^ n : ℕ) : ℝ) := by
      have := hi_mem.2
      simp only [h_i_zero, Nat.cast_zero, zero_add, one_mul] at this
      exact this
    linarith
  -- For n with i ≥ 1, x ∈ closedBall(w_n, 3 δ_n).
  have h_x_in_ball_eventually : ∀ᶠ n in Filter.atTop,
      x ∈ Metric.closedBall (w n) (3 * δ n) := by
    filter_upwards [h_eventually_i_pos] with n hn_i_pos
    change |x - w n| ≤ 3 * δ n
    have hi_mem := dyadicIndex_mem n T hT x hx
    have h_x_lower : ((dyadicIndex n T hT x hx).val : ℝ) * T / ((2 ^ n : ℕ) : ℝ) < x :=
      hi_mem.1
    have h_x_upper :
        x ≤ (((dyadicIndex n T hT x hx).val : ℝ) + 1) * T / ((2 ^ n : ℕ) : ℝ) := by
      exact_mod_cast hi_mem.2
    set i_val : ℝ := ((dyadicIndex n T hT x hx).val : ℝ) with hi_val
    have h_pos_real : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
    have h_pow_ne : ((2 ^ n : ℕ) : ℝ) ≠ 0 := ne_of_gt h_pos_real
    change |x - (i_val - 1/2) * (T / ((2 ^ n : ℕ) : ℝ))| ≤ 3 * (T / (2 * (2 ^ n : ℕ)))
    rw [abs_le]
    constructor
    · -- Lower bound: x - w_n ≥ -(3 * δ_n).
      have h_x_lower' : i_val * T / ((2 ^ n : ℕ) : ℝ) ≤ x := le_of_lt h_x_lower
      have h_alg : i_val * T / ((2 ^ n : ℕ) : ℝ) - (i_val - 1/2) * (T / ((2 ^ n : ℕ) : ℝ)) =
          T / (2 * ((2 ^ n : ℕ) : ℝ)) := by
        field_simp; ring
      have h_3delta_pos : 0 < 3 * (T / (2 * ((2 ^ n : ℕ) : ℝ))) := by positivity
      linarith
    · -- Upper: x - w_n ≤ 3 δ_n.
      have h_alg :
          (i_val + 1) * T / ((2 ^ n : ℕ) : ℝ)
            - (i_val - 1/2) * (T / ((2 ^ n : ℕ) : ℝ))
            = 3 * (T / (2 * ((2 ^ n : ℕ) : ℝ))) := by
        field_simp; ring
      linarith
  -- Apply Vitali theorem.
  have h_avg_to_g := h_vitali_at_x hx_mem (l := Filter.atTop) w δ
    h_delta_tendsto h_x_in_ball_eventually
  -- Bridge: ⨍ over closedBall = predictable.eval (eventually).
  have h_bridge : ∀ᶠ n in Filter.atTop,
      (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval x ω =
      ⨍ y in Metric.closedBall (w n) (δ n), g ω y ∂volume := by
    filter_upwards [h_eventually_i_pos] with n hn_i_pos
    rw [predictableDyadicSimple_brownian_eval_eq_shifted hT g h_meas M h_bound n x hx ω]
    -- dyadicAvg_shifted T g n i ω = dyadicAvg_brownian g n ⟨i.val - 1, _⟩ ω (since i ≥ 1)
    -- = ⨍ over closedBall(midpt of (t_{i-1}, t_i], T/2^{n+1}) g(ω, ·)
    unfold dyadicAvg_shifted_brownian
    rw [dite_eq_right (by omega : ¬ (dyadicIndex n T hT x hx).val = 0)]
    have h_lt : (dyadicIndex n T hT x hx).val - 1 < 2 ^ n := by
      have := (dyadicIndex n T hT x hx).isLt; omega
    set i' : Fin (2 ^ n) := ⟨(dyadicIndex n T hT x hx).val - 1, h_lt⟩
    rw [dyadicAvg_brownian_eq_average_closedBall hT g n i' ω]
    -- Now match w_n and δ_n with the closedBall arguments.
    have h_w_eq : w n =
        (dyadicPartition_brownian T n i'.castSucc +
          dyadicPartition_brownian T n i'.succ) / 2 := by
      change (((dyadicIndex n T hT x hx).val : ℝ) - 1/2) *
          (T / ((2 ^ n : ℕ) : ℝ)) = _
      unfold dyadicPartition_brownian
      simp only [Fin.val_succ, Fin.val_castSucc]
      have h_pow_pos : (0 : ℝ) < ((2 ^ n : ℕ) : ℝ) := by positivity
      have h_pow_ne : ((2 ^ n : ℕ) : ℝ) ≠ 0 := ne_of_gt h_pow_pos
      have h_sub_cast :
          (((dyadicIndex n T hT x hx).val - 1 : ℕ) : ℝ) =
            ((dyadicIndex n T hT x hx).val : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ (dyadicIndex n T hT x hx).val)]
        simp
      rw [h_sub_cast]
      have h_add_one_cast :
          ((((dyadicIndex n T hT x hx).val - 1 : ℕ) + 1 : ℕ) : ℝ) =
            ((dyadicIndex n T hT x hx).val : ℝ) := by
        rw [show ((dyadicIndex n T hT x hx).val - 1 : ℕ) + 1 = (dyadicIndex n T hT x hx).val from
          by omega]
      rw [h_add_one_cast]
      field_simp
      ring
    have h_delta_eq : δ n = (dyadicPartition_brownian T n i'.succ -
        dyadicPartition_brownian T n i'.castSucc) / 2 := by
      rw [dyadicPartition_brownian_diff n i']
      change T / (2 * ((2 ^ n : ℕ) : ℝ)) = T / ((2 ^ n : ℕ) : ℝ) / 2
      field_simp
    rw [h_w_eq, h_delta_eq]
  refine Filter.Tendsto.congr' ?_ h_avg_to_g
  filter_upwards [h_bridge] with n hn
  exact hn.symm
end LevyStochCalc.Brownian.Ito

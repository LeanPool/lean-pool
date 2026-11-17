/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Real
public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.Trace.Algebra

/-!
# Finite moments and linear images of Borel laws

Continuous linear images preserve finite fourth moments.
`memLp_id_two_iff_lintegral_enorm_rpow_lt_top` characterises finite second moments. The section
`ThirdMomentContraction` proves `Σ_{ijk} (∫ x_i x_j x_k dν)² ≤ ∫ ‖x‖⁶ dν` for a probability law on
`ℝⁿ` with
integrable sixth moment (no centering or log-concavity), a deterministic support of the proposed
log-determinant non-explosion route for the BKL localization equations (67).
The section `MomentTails` holds the eighth-moment tail bounds on a normed group with Borel
structure: for a
probability law with integrable `‖x‖⁸` and `R > 0`, `ν(ball(0,R)ᶜ) ≤ M₈/R⁸` (Markov) and `‖x‖⁴`
together with its
tail restriction are integrable with `∫ 1_{ball(0,R)ᶜ} ‖x‖⁴ ≤ M₈/R⁴`, `M₈` the actual eighth moment.
They are the first
supports of the ball-conditioning stage of the moment-potential producer.
The section `MixedLinearMoments` expands mixed linear moments `∫ ∏ᵢ ⟪vᵢ, x⟫` on `EuclideanSpace ℝ
(Fin n)` into
coordinate monomials and passes convergence of all coordinate monomials of one degree to every mixed
linear moment
of that degree (`tendsto_integral_prod_inner_of_coord`).
-/

@[expose] public section

open MeasureTheory

namespace FunctionalInequalities.Probability

section LinearImages

/-- A continuous linear image preserves a finite fourth moment. -/
theorem memLp_four_map_linear {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) (S : E →L[ℝ] E)
    (hμ4 : MemLp id 4 μ) : MemLp id 4 (μ.map S) := by
  apply
    (memLp_map_measure_iff continuous_id.aestronglyMeasurable
        S.continuous.measurable.aemeasurable).2
  exact S.comp_memLp' hμ4

end LinearImages

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- The identity has finite second moment exactly when its extended squared norm has finite
lower integral. This includes real laws and needs no Hilbert or finite-dimensional structure. -/
theorem memLp_id_two_iff_lintegral_enorm_rpow_lt_top (ν : Measure E) :
    MemLp (id : E → E) 2 ν ↔ ∫⁻ x, ‖x‖ₑ ^ (2 : ℝ) ∂ν < ⊤ := by
  have h := eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (f := (id : E → E)) (μ := ν)
    (p := 2) two_ne_zero ENNReal.ofNat_ne_top aestronglyMeasurable_id
  simp only [id_eq, ENNReal.toReal_ofNat] at h
  rw [memLp_iff]
  exact h

section ThirdMomentContraction

private lemma integral_sq_le_of_integrable
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {g : α → ℝ} (hg : Integrable g μ)
    (hg2 : Integrable (fun x => g x ^ 2) μ) :
    (∫ x, g x ∂μ) ^ 2 ≤ ∫ x, g x ^ 2 ∂μ := by
  have hmem : MemLp g 2 μ :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 hg2
  have hv : 0 ≤ ProbabilityTheory.variance g μ :=
    ProbabilityTheory.variance_nonneg g μ
  rw [ProbabilityTheory.variance_eq_sub hmem] at hv
  have hv' :
      0 ≤ (∫ x, g x ^ 2 ∂μ) - (∫ x, g x ∂μ) ^ 2 := by
    simpa [Pi.pow_apply] using hv
  linarith

private lemma third_power_sum_sq
    {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (x i * x j * x k) ^ 2) = ‖x‖ ^ 6 := by
  rw [show (‖x‖ : ℝ) ^ 6 = (‖x‖ ^ 2) ^ 3 by ring,
    EuclideanSpace.real_norm_sq_eq]
  rw [pow_three, Finset.sum_mul_sum, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/--
**Third-moment contraction**: `Σ_{ijk} (∫ x_i x_j x_k dν)² ≤ ∫ ‖x‖⁶ dν` for a probability law with
integrable
sixth moment. -/
theorem sum_sq_integral_mul_mul_le_integral_norm_pow_six {n : ℕ}
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (h6 :
      Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 6)
        (ν : Measure (EuclideanSpace ℝ (Fin n)))) :
    (∑ i : Fin n,
        ∑ j : Fin n,
          ∑ k : Fin n, (∫ x, x i * x j * x k ∂(ν : Measure (EuclideanSpace ℝ (Fin n)))) ^ 2) ≤
      ∫ x, ‖x‖ ^ 6 ∂(ν : Measure (EuclideanSpace ℝ (Fin n))) := by
  let μ : Measure (EuclideanSpace ℝ (Fin n)) := (ν : Measure (EuclideanSpace ℝ (Fin n)))
  change
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, (∫ x, x i * x j * x k ∂μ) ^ 2) ≤ ∫ x, ‖x‖ ^ 6 ∂μ
  have hbase : Integrable (fun x : EuclideanSpace ℝ (Fin n) => 1 + ‖x‖ ^ 6) μ :=
    (integrable_const (μ := μ) (1 : ℝ)).add (by simpa [μ] using h6)
  have hterm :
    ∀ i j k : Fin n, Integrable (fun x : EuclideanSpace ℝ (Fin n) => x i * x j * x k) μ := by
    intro i j k
    have hm : AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin n) => x i * x j * x k) μ := by
      fun_prop
    apply hbase.mono' hm
    filter_upwards [] with x
    have hi : |x i| ≤ ‖x‖ := PiLp.norm_apply_le x i
    have hj : |x j| ≤ ‖x‖ := PiLp.norm_apply_le x j
    have hk : |x k| ≤ ‖x‖ := PiLp.norm_apply_le x k
    have hprod : ‖x i * x j * x k‖ ≤ ‖x‖ ^ 3 := by
      calc
        ‖x i * x j * x k‖ = |x i| * |x j| * |x k| := by simp [Real.norm_eq_abs]
        _ ≤ ‖x‖ * ‖x‖ * ‖x‖ := by gcongr
        _ = ‖x‖ ^ 3 := by ring
    nlinarith [sq_nonneg (‖x‖ ^ 3 - 1)]
  have hterm_sq :
    ∀ i j k : Fin n, Integrable (fun x : EuclideanSpace ℝ (Fin n) => (x i * x j * x k) ^ 2) μ := by
    intro i j k
    have hm :
      AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin n) => (x i * x j * x k) ^ 2) μ := by
      fun_prop
    have hm6 : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 6) μ := by
      simpa [μ] using h6
    refine hm6.mono' hm ?_
    filter_upwards [] with x
    have hi : |x i| ≤ ‖x‖ := PiLp.norm_apply_le x i
    have hj : |x j| ≤ ‖x‖ := PiLp.norm_apply_le x j
    have hk : |x k| ≤ ‖x‖ := PiLp.norm_apply_le x k
    have hprod : ‖x i * x j * x k‖ ≤ ‖x‖ ^ 3 := by
      calc
        ‖x i * x j * x k‖ = |x i| * |x j| * |x k| := by simp [Real.norm_eq_abs]
        _ ≤ ‖x‖ * ‖x‖ * ‖x‖ := by gcongr
        _ = ‖x‖ ^ 3 := by ring
    have ha : 0 ≤ ‖x i * x j * x k‖ := norm_nonneg _
    have hb : 0 ≤ ‖x‖ ^ 3 := by positivity
    have hdiff : 0 ≤ ‖x‖ ^ 3 - ‖x i * x j * x k‖ := sub_nonneg.mpr hprod
    have hsum : 0 ≤ ‖x‖ ^ 3 + ‖x i * x j * x k‖ := add_nonneg hb ha
    have hmul : 0 ≤ (‖x‖ ^ 3 - ‖x i * x j * x k‖) * (‖x‖ ^ 3 + ‖x i * x j * x k‖) :=
      mul_nonneg hdiff hsum
    have hs : ‖x i * x j * x k‖ ^ 2 ≤ (‖x‖ ^ 3) ^ 2 := by nlinarith
    calc
      ‖(x i * x j * x k) ^ 2‖ = ‖x i * x j * x k‖ ^ 2 := by rw [norm_pow]
      _ ≤ (‖x‖ ^ 3) ^ 2 := hs
      _ = ‖x‖ ^ 6 := by ring
  have hineq : ∀ i j k : Fin n, (∫ x, x i * x j * x k ∂μ) ^ 2 ≤ ∫ x, (x i * x j * x k) ^ 2 ∂μ := by
    intro i j k
    exact integral_sq_le_of_integrable (hterm i j k) (hterm_sq i j k)
  have hsumk :
    ∀ i j : Fin n,
      Integrable (fun x : EuclideanSpace ℝ (Fin n) => ∑ k : Fin n, (x i * x j * x k) ^ 2) μ := by
    intro i j
    exact integrable_finsetSum _ (fun k _ => hterm_sq i j k)
  have hsumj :
    ∀ i : Fin n,
      Integrable
        (fun x : EuclideanSpace ℝ (Fin n) => ∑ j : Fin n, ∑ k : Fin n, (x i * x j * x k) ^ 2)
        μ := by
    intro i
    exact integrable_finsetSum _ (fun j _ => hsumk i j)
  calc
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, (∫ x, x i * x j * x k ∂μ) ^ 2) ≤
        ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∫ x, (x i * x j * x k) ^ 2 ∂μ := by
      gcongr
      exact hineq _ _ _
    _ = ∫ x, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, (x i * x j * x k) ^ 2 ∂μ := by
      rw [integral_finsetSum _ (fun i _ => hsumj i)]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum _ (fun j _ => hsumk i j)]
      apply Finset.sum_congr rfl
      intro j hj
      rw [integral_finsetSum _ (fun k _ => hterm_sq i j k)]
    _ = ∫ x, ‖x‖ ^ 6 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact third_power_sum_sq x

/--
Third-moment contraction for an a.e.-measurable random vector: `Σ_{ijk} (∫ Y_i Y_j Y_k)² ≤ ∫ ‖Y‖⁶`,
no centering. -/
theorem sum_sq_integral_comp_mul_mul_le_integral_norm_pow_six {X : Type*} [MeasurableSpace X]
    {n : ℕ} (ν : ProbabilityMeasure X) (Y : X → EuclideanSpace ℝ (Fin n))
    (hY : AEMeasurable Y (ν : Measure X))
    (h6 : Integrable (fun x => ‖Y x‖ ^ 6) (ν : Measure X)) :
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, (∫ x, Y x i * Y x j * Y x k ∂(ν : Measure X)) ^ 2) ≤
      ∫ x, ‖Y x‖ ^ 6 ∂(ν : Measure X) := by
  let η : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) := ν.map Y
  have hnorm_cont : Continuous (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 6) := by fun_prop
  have h6' :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 6)
      (η : Measure (EuclideanSpace ℝ (Fin n))) := by
    change
      Integrable (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 6) (Measure.map Y (ν : Measure X))
    exact
      (integrable_map_measure hnorm_cont.aestronglyMeasurable hY).mpr
        (by simpa [Function.comp_def] using h6)
  have htriple_cont (i j k : Fin n) :
    Continuous (fun y : EuclideanSpace ℝ (Fin n) => y i * y j * y k) := by fun_prop
  have htriple (i j k : Fin n) :
    (∫ y, y i * y j * y k ∂(η : Measure (EuclideanSpace ℝ (Fin n)))) =
      ∫ x, Y x i * Y x j * Y x k ∂(ν : Measure X) := by
    change
      (∫ y, y i * y j * y k ∂Measure.map Y (ν : Measure X)) =
        ∫ x, Y x i * Y x j * Y x k ∂(ν : Measure X)
    exact integral_map hY (htriple_cont i j k).aestronglyMeasurable
  have hnorm :
    (∫ y, ‖y‖ ^ 6 ∂(η : Measure (EuclideanSpace ℝ (Fin n)))) =
      ∫ x, ‖Y x‖ ^ 6 ∂(ν : Measure X) := by
    change (∫ y, ‖y‖ ^ 6 ∂Measure.map Y (ν : Measure X)) = ∫ x, ‖Y x‖ ^ 6 ∂(ν : Measure X)
    exact integral_map hY hnorm_cont.aestronglyMeasurable
  have hmain := sum_sq_integral_mul_mul_le_integral_norm_pow_six η h6'
  simpa only [htriple, hnorm] using hmain

end ThirdMomentContraction

section MomentTails

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- **Eighth-moment tail (Markov)**: `ν(ball(0,R)ᶜ) ≤ (∫ ‖x‖⁸ dν) / R⁸` for `R > 0`. -/
theorem measure_ball_compl_toReal_le_integral_norm_pow_eight_div (ν : ProbabilityMeasure E)
    {R : ℝ} (hR : 0 < R) (h8 : Integrable (fun x : E => ‖x‖ ^ 8) (ν : Measure E)) :
    ((ν : Measure E) (Metric.ball (0 : E) R)ᶜ).toReal ≤
      (∫ x, ‖x‖ ^ 8 ∂(ν : Measure E)) / R ^ 8 := by
  let hb : MeasurableSet (Metric.ball (0 : E) R) := measurableSet_ball
  have hnonneg : 0 ≤ᵐ[(ν : Measure E)] (fun x : E => ‖x‖ ^ 8) :=
    Filter.Eventually.of_forall (fun x => by positivity)
  have hmarkov :
    R ^ 8 * (ν : Measure E).real {x : E | R ^ 8 ≤ ‖x‖ ^ 8} ≤ ∫ x, ‖x‖ ^ 8 ∂(ν : Measure E) :=
    MeasureTheory.mul_meas_ge_le_integral_of_nonneg hnonneg h8 (R ^ 8)
  have hsub : (Metric.ball (0 : E) R)ᶜ ⊆ {x : E | R ^ 8 ≤ ‖x‖ ^ 8} := by
    intro x hx
    simp only [Set.mem_compl_iff, mem_ball_zero_iff, not_lt] at hx
    have hp : ∀ n : ℕ, R ^ n ≤ ‖x‖ ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, pow_succ]
        exact mul_le_mul ih hx hR.le (by positivity)
    exact hp 8
  have hmeasure :
    (ν : Measure E).real (Metric.ball (0 : E) R)ᶜ ≤
      (ν : Measure E).real {x : E | R ^ 8 ≤ ‖x‖ ^ 8} :=
    measureReal_mono hsub
  have hresult :
    ((ν : Measure E) (Metric.ball (0 : E) R)ᶜ).toReal ≤
      (∫ x, ‖x‖ ^ 8 ∂(ν : Measure E)) / R ^ 8 := by
    rw [← measureReal_def]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < R ^ 8)).2
    calc
      (ν : Measure E).real (Metric.ball (0 : E) R)ᶜ * R ^ 8 ≤
          (ν : Measure E).real {x : E | R ^ 8 ≤ ‖x‖ ^ 8} * R ^ 8 :=
        mul_le_mul_of_nonneg_right hmeasure (by positivity)
      _ = R ^ 8 * (ν : Measure E).real {x : E | R ^ 8 ≤ ‖x‖ ^ 8} := by ring
      _ ≤ ∫ x, ‖x‖ ^ 8 ∂(ν : Measure E) := hmarkov
  have hwrap :
    hb = measurableSet_ball →
      (((ν : Measure E) (Metric.ball (0 : E) R)ᶜ).toReal ≤
        (∫ x, ‖x‖ ^ 8 ∂(ν : Measure E)) / R ^ 8) :=
    fun _ => hresult
  exact hwrap rfl

/--
**Fourth-moment tail**: with `∫ ‖x‖⁸ < ∞` and `R > 0`, `‖x‖⁴` and its tail restriction are
integrable and
`∫ 1_{ball(0,R)ᶜ} ‖x‖⁴ dν ≤ (∫ ‖x‖⁸ dν) / R⁴`. -/
theorem integrable_norm_pow_four_and_tail_le_of_integrable_pow_eight (ν : ProbabilityMeasure E)
    {R : ℝ} (hR : 0 < R) (h8 : Integrable (fun x : E => ‖x‖ ^ 8) (ν : Measure E)) :
    Integrable (fun x : E => ‖x‖ ^ 4) (ν : Measure E) ∧
      Integrable ((Metric.ball (0 : E) R)ᶜ.indicator (fun x : E => ‖x‖ ^ 4)) (ν : Measure E) ∧
        (∫ x, (Metric.ball (0 : E) R)ᶜ.indicator (fun y : E => ‖y‖ ^ 4) x ∂(ν : Measure E)) ≤
          (∫ x, ‖x‖ ^ 8 ∂(ν : Measure E)) / R ^ 4 := by
  have h4 : Integrable (fun x : E => ‖x‖ ^ 4) (ν : Measure E) := by
    apply ((integrable_const (1 : ℝ)).add h8).mono'
    · fun_prop
    · filter_upwards [] with x
      have hineq : ‖x‖ ^ 4 ≤ (1 : ℝ) + ‖x‖ ^ 8 := by nlinarith [sq_nonneg (‖x‖ ^ 4 - 1)]
      simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖x‖ ^ 4),
        abs_of_nonneg (by positivity : 0 ≤ (1 : ℝ) + ‖x‖ ^ 8)] using hineq
  have ht :
    Integrable ((Metric.ball (0 : E) R)ᶜ.indicator (fun x : E => ‖x‖ ^ 4)) (ν : Measure E) :=
    h4.indicator measurableSet_ball.compl
  have hpointwise :
    ∀ x : E, (Metric.ball (0 : E) R)ᶜ.indicator (fun y : E => ‖y‖ ^ 4) x ≤ ‖x‖ ^ 8 / R ^ 4 := by
    intro x
    by_cases hx : x ∈ (Metric.ball (0 : E) R)ᶜ
    · have hxnot : x ∉ Metric.ball (0 : E) R := hx
      have hle : R ≤ ‖x‖ := by
        apply le_of_not_gt
        intro h
        apply hxnot
        exact (mem_ball_zero_iff).2 h
      rw [Set.indicator_of_mem hx]
      have hpow : R ^ 4 ≤ ‖x‖ ^ 4 := by gcongr
      apply (le_div_iff₀ (by positivity : 0 < R ^ 4)).2
      calc
        ‖x‖ ^ 4 * R ^ 4 ≤ ‖x‖ ^ 4 * ‖x‖ ^ 4 := mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = ‖x‖ ^ 8 := by ring
    · simp only [Set.indicator, hx, ↓reduceIte]
      positivity
  refine ⟨h4, ht, ?_⟩
  calc
    (∫ x, (Metric.ball (0 : E) R)ᶜ.indicator (fun y : E => ‖y‖ ^ 4) x ∂(ν : Measure E)) ≤
        ∫ x, ‖x‖ ^ 8 / R ^ 4 ∂(ν : Measure E) :=
      integral_mono ht (h8.div_const (R ^ 4)) hpointwise
    _ = (∫ x, ‖x‖ ^ 8 ∂(ν : Measure E)) / R ^ 4 := by rw [integral_div]

/-- **Half mass**: `2 ∫ ‖x‖⁸ dν ≤ R⁸` and `R > 0` give `ν(ball(0,R)) ≥ 1/2 > 0`. -/
theorem one_half_le_measure_ball_toReal_of_integral_norm_pow_eight (ν : ProbabilityMeasure E)
    {R : ℝ} (hR : 0 < R) (h8 : Integrable (fun x : E => ‖x‖ ^ 8) (ν : Measure E))
    (hthr : 2 * (∫ x, ‖x‖ ^ 8 ∂(ν : Measure E)) ≤ R ^ 8) :
    (1 / 2 : ℝ) ≤ ((ν : Measure E) (Metric.ball (0 : E) R)).toReal ∧
      0 < (ν : Measure E) (Metric.ball (0 : E) R) := by
  have htail :
    ((ν : Measure E) (Metric.ball (0 : E) R)ᶜ).toReal ≤
      (∫ x, ‖x‖ ^ 8 ∂(ν : Measure E)) / R ^ 8 :=
    measure_ball_compl_toReal_le_integral_norm_pow_eight_div ν hR h8
  have hdiv : (∫ x, ‖x‖ ^ 8 ∂(ν : Measure E)) / R ^ 8 ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < R ^ 8)).2
    nlinarith [hthr]
  have hcomp : ((ν : Measure E) (Metric.ball (0 : E) R)ᶜ).toReal ≤ (1 / 2 : ℝ) :=
    htail.trans hdiv
  have hsum :
    ((ν : Measure E) (Metric.ball (0 : E) R)).toReal +
        ((ν : Measure E) (Metric.ball (0 : E) R)ᶜ).toReal =
      1 := by
    calc
      ((ν : Measure E) (Metric.ball (0 : E) R)).toReal +
            ((ν : Measure E) (Metric.ball (0 : E) R)ᶜ).toReal =
          (((ν : Measure E) (Metric.ball (0 : E) R)) +
              (ν : Measure E) (Metric.ball (0 : E) R)ᶜ).toReal := by
        rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      _ = 1 := by
        rw [measure_add_measure_compl measurableSet_ball]
        simp
  have hball : (1 / 2 : ℝ) ≤ ((ν : Measure E) (Metric.ball (0 : E) R)).toReal := by
    linarith [hsum, hcomp]
  have hne : (ν : Measure E) (Metric.ball (0 : E) R) ≠ 0 := by
    intro hz
    have hz' : ((ν : Measure E) (Metric.ball (0 : E) R)).toReal = 0 := by simp [hz]
    linarith [hball]
  exact ⟨hball, pos_iff_ne_zero.mpr hne⟩

end MomentTails

section CoordinateMonomials

/--
Under a finite measure a.e. supported in `‖x − a‖ ≤ R`, every cubic coordinate monomial of `x − a`
is integrable. -/
theorem integrable_coord_mul_coord_mul_coord_of_ae_norm_sub_le {n : ℕ}
    {ν : Measure (EuclideanSpace ℝ (Fin n))} [IsFiniteMeasure ν] (a : EuclideanSpace ℝ (Fin n))
    (R : ℝ) (hR : ∀ᵐ x ∂ν, ‖x - a‖ ≤ R) (p q r : Fin n) :
    Integrable (fun x => (x - a) p * (x - a) q * (x - a) r) ν := by
  refine (integrable_const (μ := ν) (c := R ^ 3)).mono' ?_ ?_
  · have hcont :
      Continuous (fun x : EuclideanSpace ℝ (Fin n) => (x - a) p * (x - a) q * (x - a) r) := by
      fun_prop
    exact hcont.aestronglyMeasurable
  · filter_upwards [hR] with x hx
    have hnonneg : 0 ≤ R := (norm_nonneg (x - a)).trans hx
    have h1 : ∀ s : Fin n, |(x - a) s| ≤ R := by
      intro s
      calc
        |(x - a) s| = ‖(x - a) s‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖x - a‖ := PiLp.norm_apply_le (x - a) s
        _ ≤ R := hx
    have hmul : |(x - a) p| * |(x - a) q| * |(x - a) r| ≤ R * R * R := by
      exact
        mul_le_mul (mul_le_mul (h1 p) (h1 q) (abs_nonneg _) hnonneg) (h1 r) (abs_nonneg _)
          (mul_nonneg hnonneg hnonneg)
    calc
      ‖(x - a) p * (x - a) q * (x - a) r‖ = |(x - a) p| * |(x - a) q| * |(x - a) r| := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
      _ ≤ R * R * R := hmul
      _ = R ^ 3 := by ring

/-- A weighted finite double sum of integrable functions commutes with the Bochner integral. -/
theorem integral_sum_sum_const_mul {α ι κ : Type*} [MeasurableSpace α] {ν : Measure α}
    (S : Finset ι) (K : Finset κ) (c : ι → κ → ℝ) (F : ι → κ → α → ℝ)
    (hF : ∀ s t, Integrable (F s t) ν) :
    ∫ x, (∑ s ∈ S, ∑ t ∈ K, c s t * F s t x) ∂ν = ∑ s ∈ S, ∑ t ∈ K, c s t * ∫ x, F s t x ∂ν := by
  rw [integral_finsetSum S
      (fun s _ => integrable_finsetSum K (fun t _ => (hF s t).const_mul (c s t)))]
  refine Finset.sum_congr rfl ?_
  intro s hs
  rw [integral_finsetSum K (fun t _ => (hF s t).const_mul (c s t))]
  refine Finset.sum_congr rfl ?_
  intro t ht
  exact integral_const_mul (c s t) (F s t)

end CoordinateMonomials

end FunctionalInequalities.Probability

section FiniteVarianceSum

open MeasureTheory

namespace FunctionalInequalities.Probability

private theorem sum_variance_eq_integral_sum_sq_sub_sum_integral_sq {alpha I : Type*}
    [MeasurableSpace alpha] [Fintype I] (mu : Measure alpha) [IsProbabilityMeasure mu]
    (F : I → alpha → ℝ) (hF : ∀ i, MemLp (F i) 2 mu) :
    (∑ i, ProbabilityTheory.variance (F i) mu) =
      (∫ x, ∑ i, F i x ^ 2 ∂mu) - ∑ i, (∫ x, F i x ∂mu) ^ 2 := by
  classical
  calc
    _ = ∑ i, ((∫ x, F i x ^ 2 ∂mu) - (∫ x, F i x ∂mu) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      exact ProbabilityTheory.variance_eq_sub (hF i)
    _ = (∑ i, ∫ x, F i x ^ 2 ∂mu) - ∑ i, (∫ x, F i x ∂mu) ^ 2 := by
      rw [Finset.sum_sub_distrib]
    _ = _ := by rw [integral_finsetSum _ (fun i _ => (hF i).integrable_sq)]

end FunctionalInequalities.Probability

end FiniteVarianceSum

section MatrixVarianceTrace

open MeasureTheory Matrix

namespace FunctionalInequalities.Probability

/--
For an almost-everywhere symmetric random matrix `H` with L2 entries and symmetric mean `M` under a
probability
measure, the entry variances sum to `∫ tr(H H) - tr(M M)`; all finite dimensions. -/
theorem sum_variance_entries_eq_integral_trace_sub_trace_mean {alpha : Type*}
    [MeasurableSpace alpha] {n : ℕ} (mu : Measure alpha) [IsProbabilityMeasure mu]
    (H : alpha → Matrix (Fin n) (Fin n) ℝ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm)
    (hH : ∀ᵐ x ∂mu, (H x).IsSymm) (hH2 : ∀ i j, MemLp (fun x => H x i j) 2 mu)
    (hmean : ∀ i j, (∫ x, H x i j ∂mu) = M i j) :
    (∑ p : Fin n × Fin n, ProbabilityTheory.variance (fun x => H x p.1 p.2) mu) =
      (∫ x, (H x * H x).trace ∂mu) - (M * M).trace := by
  classical
  have hI : (1 : Matrix (Fin n) (Fin n) ℝ).IsSymm := by
    change (1 : Matrix (Fin n) (Fin n) ℝ).transpose = 1
    simp only [Matrix.transpose_one]
  have htrace :
    (fun x => ∑ p : Fin n × Fin n, H x p.1 p.2 ^ 2) =ᵐ[mu] (fun x => (H x * H x).trace) := by
    filter_upwards [hH] with x hx
    simpa only [Matrix.one_mul, Matrix.mul_one, pow_two] using
      Analysis.sum_matrix_product_entry_mul_eq_trace (1 : Matrix (Fin n) (Fin n) ℝ) (H x) (H x)
        hI hx
  have hMtrace : (∑ p : Fin n × Fin n, M p.1 p.2 ^ 2) = (M * M).trace := by
    simpa only [Matrix.one_mul, Matrix.mul_one, pow_two] using
      Analysis.sum_matrix_product_entry_mul_eq_trace (1 : Matrix (Fin n) (Fin n) ℝ) M M hI hM
  rw [sum_variance_eq_integral_sum_sq_sub_sum_integral_sq mu
      (fun p : Fin n × Fin n => fun x => H x p.1 p.2) (fun p => hH2 p.1 p.2)]
  rw [integral_congr_ae htrace]
  simp_rw [hmean]
  rw [hMtrace]

end FunctionalInequalities.Probability

end MatrixVarianceTrace

/-! ### Quadratic forms of a fourth-moment vector

If `f` is in `L⁴`, then `⟪A f, f⟫` is in `L²` for every continuous linear `A`. -/

section
open MeasureTheory
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Probability

theorem memLp_quadratic_of_memLp_four {alpha E : Type*} [MeasurableSpace alpha]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {mu : Measure alpha}
    {f : alpha → E} (hf : MemLp f 4 mu) (A : E →L[ℝ] E) :
    MemLp (fun x => ⟪A (f x), f x⟫) 2 mu := by
  have ht : ENNReal.HolderTriple (4 : ENNReal) 4 2 := by
    constructor
    rw [← ENNReal.coe_ofNat 4, ← ENNReal.coe_ofNat 2,
      ← ENNReal.coe_inv (by norm_num : (4 : NNReal) ≠ 0),
      ← ENNReal.coe_inv (by norm_num : (2 : NNReal) ≠ 0),
      ← ENNReal.coe_add]
    norm_num
  have hp := hf.norm.mul hf.norm (hpqr := ht)
  apply hp.of_le_mul (c := ‖A‖)
    ((hf.continuousLinearMap_comp A).aestronglyMeasurable.inner hf.aestronglyMeasurable)
  filter_upwards [] with x
  calc
    ‖⟪A (f x), f x⟫‖ ≤ ‖A (f x)‖ * ‖f x‖ := norm_inner_le_norm _ _
    _ ≤ (‖A‖ * ‖f x‖) * ‖f x‖ :=
      mul_le_mul_of_nonneg_right (A.le_opNorm (f x)) (norm_nonneg _)
    _ = ‖A‖ * ‖‖f x‖ * ‖f x‖‖ := by
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      ring

end FunctionalInequalities.Probability

end

section MixedLinearMoments

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Probability

variable {n : ℕ}

/-- Coordinate expansion of a mixed linear moment integrand on `EuclideanSpace ℝ (Fin n)`. -/
theorem prod_inner_eq_sum_prod_coord {d : ℕ} (v : Fin d → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    ∏ i, ⟪v i, x⟫ = ∑ c : Fin d → Fin n, (∏ i, v i (c i)) * ∏ i, x (c i) := by
  have h (i : Fin d) : ⟪v i, x⟫ = ∑ a, v i a * x a := by
    simp [PiLp.inner_apply, mul_comm]
  simp_rw [h, Finset.prod_univ_sum, ← Finset.prod_mul_distrib]
  rfl

/--
Coordinate expansion of a mixed linear moment, given integrability of each coordinate monomial. -/
theorem integral_prod_inner_eq_sum (ρ : Measure (EuclideanSpace ℝ (Fin n))) {d : ℕ}
    (hint :
      ∀ c : Fin d → Fin n, Integrable (fun x : EuclideanSpace ℝ (Fin n) => ∏ i, x (c i)) ρ)
    (v : Fin d → EuclideanSpace ℝ (Fin n)) :
    ∫ x, ∏ i, ⟪v i, x⟫ ∂ρ = ∑ c : Fin d → Fin n, (∏ i, v i (c i)) * ∫ x, ∏ i, x (c i) ∂ρ := by
  simp_rw [prod_inner_eq_sum_prod_coord v]
  rw [integral_finsetSum _ fun c _ => (hint c).const_mul _]
  simp_rw [integral_const_mul]

/--
Convergence of all coordinate monomials of degree `d` gives convergence of every mixed linear moment
of
degree `d`. -/
theorem tendsto_integral_prod_inner_of_coord (ρ : ℕ → Measure (EuclideanSpace ℝ (Fin n)))
    (σ : Measure (EuclideanSpace ℝ (Fin n))) {d : ℕ}
    (hint :
      ∀ k (c : Fin d → Fin n),
        Integrable (fun x : EuclideanSpace ℝ (Fin n) => ∏ i, x (c i)) (ρ k))
    (hintσ :
      ∀ c : Fin d → Fin n, Integrable (fun x : EuclideanSpace ℝ (Fin n) => ∏ i, x (c i)) σ)
    (hcoord :
      ∀ c : Fin d → Fin n,
        Tendsto (fun k => ∫ x, ∏ i, x (c i) ∂(ρ k)) atTop (𝓝 (∫ x, ∏ i, x (c i) ∂σ)))
    (v : Fin d → EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun k => ∫ x, ∏ i, ⟪v i, x⟫ ∂(ρ k)) atTop (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂σ)) := by
  simp_rw [integral_prod_inner_eq_sum _ (hint _) v, integral_prod_inner_eq_sum σ hintσ v]
  exact tendsto_finsetSum _ fun c _ => (hcoord c).const_mul _

/-- Coordinate monomials are mixed linear moments of standard basis vectors. -/
theorem prod_coord_eq_prod_inner_single {d : ℕ} (c : Fin d → Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    ∏ i, x (c i) = ∏ i, ⟪EuclideanSpace.single (c i) (1 : ℝ), x⟫ := by
  simp [EuclideanSpace.inner_single_left]

end FunctionalInequalities.Probability

end MixedLinearMoments

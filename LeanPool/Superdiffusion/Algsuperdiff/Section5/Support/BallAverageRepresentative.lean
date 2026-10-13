/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.BallAverageHolder

/-!
# BallAverageRepresentative

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# A finite ball-average Hölder gauge produces a continuous representative

The converse half of the identification of the localized regularity.  If the
countable supremum of difference quotients of ball averages is finite, then the
almost-everywhere class has a representative continuous on the open set — so the
gauge is `⊤` exactly when no continuous representative exists, which is the
reading the infimum convention of the localized regularity asks for.

Three steps.  The bound over the countable set of centres extends to *all*
centres, by continuity of the average in the centre, at the price of asking the
doubled ball to fit inside the open set.  The ball averages then form a Cauchy
sequence at every point of the open set: comparing with a nearby point where
Lebesgue differentiation applies controls the tail.  The limit is Hölder on the
open set, hence continuous there, and agrees with the function at every point
where Lebesgue differentiation applies, hence almost everywhere.

## Main results

* `continuousOn_of_holderSeminormBoundOn` — a Hölder bound is continuity.
* `abs_setAverage_ball_sub_le_toReal` — the bound at arbitrary centres.
* `ballAverageLimit` — the candidate representative.
* `exists_continuousOn_of_ballAverageHolderOn_lt_top`.

## References

* ABK26, the localized regularity of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open HCPolySupport MeasureTheory Filter
open Algsuperdiff.Section4.Support
open scoped ENNReal Topology

noncomputable section

variable {d : ℕ}

/-! ## 1. A Hölder bound is continuity -/

theorem continuousOn_of_holderSeminormBoundOn {E : Type*} [NormedAddCommGroup E]
    {U : Set (Vec d)} {alpha K : ℝ} (hK : 0 ≤ K) (halpha : 0 < alpha) {f : Vec d → E}
    (hf : HolderSeminormBoundOn U alpha K f) : ContinuousOn f U := by
  rw [Metric.continuousOn_iff]
  intro b hb eps heps
  have hK1 : (0 : ℝ) < K + 1 := by linarith
  have hq : (0 : ℝ) < eps / (K + 1) := div_pos heps hK1
  refine ⟨(eps / (K + 1)) ^ (1 / alpha), by positivity, fun a ha hab => ?_⟩
  have hnorm : ‖a - b‖ < (eps / (K + 1)) ^ (1 / alpha) := by
    rwa [← dist_eq_norm]
  have hpow : ‖a - b‖ ^ alpha ≤ eps / (K + 1) := by
    refine le_of_lt ?_
    calc ‖a - b‖ ^ alpha < ((eps / (K + 1)) ^ (1 / alpha)) ^ alpha :=
          Real.rpow_lt_rpow (norm_nonneg _) hnorm halpha
      _ = eps / (K + 1) := by
          rw [← Real.rpow_mul hq.le, one_div_mul_cancel halpha.ne', Real.rpow_one]
  have hbd := hf a ha b hb
  have hstep : K * ‖a - b‖ ^ alpha ≤ K * (eps / (K + 1)) :=
    mul_le_mul_of_nonneg_left hpow hK
  have hfrac : K * (eps / (K + 1)) < eps := by
    have hle : K / (K + 1) < 1 := (div_lt_one hK1).2 (by linarith)
    calc K * (eps / (K + 1)) = eps * (K / (K + 1)) := by ring
      _ < eps * 1 := by
          exact mul_lt_mul_of_pos_left hle heps
      _ = eps := mul_one eps
  rw [dist_eq_norm]
  linarith [hbd, hstep, hfrac]

/-! ## 2. The gauges do not see the values outside the open set -/

theorem ballAverageHolderOn_indicator {U D : Set (Vec d)} (f : Vec d → ℝ) :
    ballAverageHolderOn U D (U.indicator f) = ballAverageHolderOn U D f := by
  have hcongr : ∀ (p : Vec d) (r : ℝ), Metric.ball p r ⊆ U →
      (⨍ w in Metric.ball p r, U.indicator f w ∂volume) =
        ⨍ w in Metric.ball p r, f w ∂volume := by
    intro p r hBU
    rw [setAverage_eq, setAverage_eq,
      setIntegral_congr_fun measurableSet_ball fun w hw => Set.indicator_of_mem (hBU hw) f]
  refine le_antisymm ?_ ?_ <;>
    refine iSup_le fun x => iSup_le fun hx => iSup_le fun z => iSup_le fun hz =>
      iSup_le fun hne => iSup_le fun k => iSup_le fun hbx => iSup_le fun hbz => ?_
  · rw [hcongr x _ hbx, hcongr z _ hbz]
    exact le_ballAverageHolderOn hx hz hne k hbx hbz
  · rw [← hcongr x _ hbx, ← hcongr z _ hbz]
    exact le_ballAverageHolderOn hx hz hne k hbx hbz

/-! ## 3. The bound at arbitrary centres -/

/-- **The difference quotient bound holds at every pair of centres whose doubled
balls fit inside the open set**, not only at the centres of the countable
family: the average is continuous in the centre, and a centre of the countable
family within one radius of a given centre has its ball inside the doubled
ball. -/
theorem abs_setAverage_ball_sub_le_toReal [NeZero d] {U D : Set (Vec d)} (hD : Dense D)
    {f : Vec d → ℝ} (hf : Integrable f volume)
    (hS : ballAverageHolderOn U D f < ⊤) {p q : Vec d} {k : ℕ}
    (hp : Metric.ball p (2 * (1 / (k + 1 : ℝ))) ⊆ U)
    (hq : Metric.ball q (2 * (1 / (k + 1 : ℝ))) ⊆ U) :
    |(⨍ w in Metric.ball p (1 / (k + 1 : ℝ)), f w ∂volume) -
        ⨍ w in Metric.ball q (1 / (k + 1 : ℝ)), f w ∂volume| ≤
      (ballAverageHolderOn U D f).toReal * ‖p - q‖ ^ (1 / 2 : ℝ) := by
  set S : ℝ := (ballAverageHolderOn U D f).toReal with hSdef
  have hSnn : (0 : ℝ) ≤ S := ENNReal.toReal_nonneg
  have hrpos : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
  rcases eq_or_ne p q with rfl | hpq
  · simp only [sub_self, abs_zero, norm_zero]
    positivity
  have hpqpos : (0 : ℝ) < ‖p - q‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.2 hpq
  refine le_of_forall_pos_le_add fun eps heps => ?_
  -- continuity of the average in the centre, at the two centres
  have hcont := continuous_setAverage_ball hf (1 / (k + 1 : ℝ))
  obtain ⟨eta1, heta1, hc1⟩ := Metric.continuous_iff.1 hcont p (eps / 3) (by linarith)
  obtain ⟨eta2, heta2, hc2⟩ := Metric.continuous_iff.1 hcont q (eps / 3) (by linarith)
  -- continuity of the Hölder factor
  have hfac : ContinuousAt (fun t : ℝ => S * t ^ (1 / 2 : ℝ)) ‖p - q‖ :=
    (Real.continuousAt_rpow_const _ _ (Or.inr (by norm_num))).const_mul S
  obtain ⟨eta3, heta3, hc3⟩ := Metric.continuousAt_iff.1 hfac (eps / 3) (by linarith)
  set eta : ℝ := min (min eta1 eta2) (min (eta3 / 3) (min (1 / (k + 1 : ℝ)) (‖p - q‖ / 3)))
    with hetadef
  have hetapos : 0 < eta := by
    refine lt_min (lt_min heta1 heta2) (lt_min (by linarith) (lt_min hrpos ?_))
    linarith
  obtain ⟨p', hp'D, hp'dist0⟩ := Metric.mem_closure_iff.1 (hD p) eta hetapos
  obtain ⟨q', hq'D, hq'dist0⟩ := Metric.mem_closure_iff.1 (hD q) eta hetapos
  have hp'dist : dist p' p < eta := by rwa [dist_comm] at hp'dist0
  have hq'dist : dist q' q < eta := by rwa [dist_comm] at hq'dist0
  have hple : eta ≤ 1 / (k + 1 : ℝ) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hball : ∀ {a b : Vec d}, dist a b < eta →
      Metric.ball b (2 * (1 / (k + 1 : ℝ))) ⊆ U →
      Metric.ball a (1 / (k + 1 : ℝ)) ⊆ U := by
    intro a b hab hbU w hw
    refine hbU ?_
    have h1 : dist w a < 1 / (k + 1 : ℝ) := Metric.mem_ball.1 hw
    refine Metric.mem_ball.2 ?_
    calc dist w b ≤ dist w a + dist a b := dist_triangle _ _ _
      _ < 1 / (k + 1 : ℝ) + 1 / (k + 1 : ℝ) := by
          have := lt_of_lt_of_le hab hple
          linarith
      _ = 2 * (1 / (k + 1 : ℝ)) := by ring
  have hp'ball : Metric.ball p' (1 / (k + 1 : ℝ)) ⊆ U := hball hp'dist hp
  have hq'ball : Metric.ball q' (1 / (k + 1 : ℝ)) ⊆ U := hball hq'dist hq
  -- the two centres of the countable family are distinct
  have hetalt : eta ≤ ‖p - q‖ / 3 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hnormdiff : |‖p' - q'‖ - ‖p - q‖| ≤ ‖p' - p‖ + ‖q' - q‖ := by
    have hbase := abs_norm_sub_norm_le (p' - q') (p - q)
    have hrw : (p' - q') - (p - q) = (p' - p) - (q' - q) := by abel
    rw [hrw] at hbase
    exact le_trans hbase (norm_sub_le _ _)
  have hpp : ‖p' - p‖ < eta := by rwa [← dist_eq_norm]
  have hqq : ‖q' - q‖ < eta := by rwa [← dist_eq_norm]
  have hp'q'pos : (0 : ℝ) < ‖p' - q'‖ := by
    have habs := abs_le.1 hnormdiff
    linarith [habs.1, hetalt]
  have hp'q'ne : p' ≠ q' := by
    intro hcon
    rw [hcon, sub_self, norm_zero] at hp'q'pos
    exact lt_irrefl 0 hp'q'pos
  -- the bound at the two centres of the countable family
  have hquot : |(⨍ w in Metric.ball p' (1 / (k + 1 : ℝ)), f w ∂volume) -
      ⨍ w in Metric.ball q' (1 / (k + 1 : ℝ)), f w ∂volume| ≤ S * ‖p' - q'‖ ^ (1 / 2 : ℝ) := by
    have hle := le_ballAverageHolderOn (U := U) (D := D) (f := f) hp'D hq'D hp'q'ne k
      hp'ball hq'ball
    have h := ENNReal.toReal_mono hS.ne hle
    rw [ENNReal.toReal_ofReal (by positivity)] at h
    have hNpos : (0 : ℝ) < ‖p' - q'‖ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hp'q'pos _
    rwa [div_le_iff₀ hNpos] at h
  -- compare the Hölder factors
  have hfacbd : S * ‖p' - q'‖ ^ (1 / 2 : ℝ) ≤ S * ‖p - q‖ ^ (1 / 2 : ℝ) + eps / 3 := by
    have hdist : |‖p' - q'‖ - ‖p - q‖| < eta3 := by
      have heta3' : eta ≤ eta3 / 3 :=
        le_trans (min_le_right _ _) (le_trans (min_le_left _ _) le_rfl)
      have habs := abs_le.1 hnormdiff
      rw [abs_lt]
      constructor <;> linarith [habs.1, habs.2]
    have := hc3 hdist
    rw [Real.dist_eq] at this
    have habs := abs_lt.1 this
    linarith [habs.2]
  -- compare the two centres with the two centres of the countable family
  have hcp := hc1 p' (lt_of_lt_of_le hp'dist (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hcq := hc2 q' (lt_of_lt_of_le hq'dist (le_trans (min_le_left _ _) (min_le_right _ _)))
  rw [Real.dist_eq] at hcp hcq
  have habsp := abs_lt.1 hcp
  have habsq := abs_lt.1 hcq
  have hmain := abs_le.1 hquot
  rw [abs_le]
  constructor <;> linarith [hmain.1, hmain.2, habsp.1, habsp.2, habsq.1, habsq.2, hfacbd]

/-! ## 4. The candidate representative -/

/-- **The limit of the ball averages**, where it exists.  On an open set where
the ball-average Hölder gauge is finite this is a representative continuous
there. -/
def ballAverageLimit (f : Vec d → ℝ) (x : Vec d) : ℝ :=
  limUnder atTop fun k : ℕ => ⨍ w in Metric.ball x (1 / (k + 1 : ℝ)), f w ∂volume

private theorem eventually_double_ball_subset {U : Set (Vec d)} (hU : IsOpen U) {x : Vec d}
    (hx : x ∈ U) :
    ∀ᶠ k : ℕ in atTop, Metric.ball x (2 * (1 / (k + 1 : ℝ))) ⊆ U := by
  obtain ⟨delta, hdelta, hball⟩ := Metric.isOpen_iff.1 hU x hx
  have hr0 : Tendsto (fun k : ℕ => 2 * (1 / (k + 1 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ))
  filter_upwards [Filter.Tendsto.eventually_lt_const hdelta hr0] with k hk
  exact subset_trans (Metric.ball_subset_ball hk.le) hball

/-- **A finite ball-average Hölder gauge produces a representative continuous on
the open set.**  In particular the gauge is `⊤` whenever no continuous
representative exists. -/
theorem exists_continuousOn_of_ballAverageHolderOn_lt_top [NeZero d] {U D : Set (Vec d)}
    (hU : IsOpen U) (hD : Dense D) {f : Vec d → ℝ} (hf : IntegrableOn f U volume)
    (hS : ballAverageHolderOn U D f < ⊤) :
    ∃ g : Vec d → ℝ, g =ᵐ[volume.restrict U] f ∧ ContinuousOn g U := by
  have hUmeas : MeasurableSet U := hU.measurableSet
  have hFint : Integrable (U.indicator f) volume := hf.integrable_indicator hUmeas
  have hSF : ballAverageHolderOn U D (U.indicator f) < ⊤ := by
    rw [ballAverageHolderOn_indicator]
    exact hS
  have hSnn : (0 : ℝ) ≤ (ballAverageHolderOn U D (U.indicator f)).toReal :=
    ENNReal.toReal_nonneg
  have hleb := ae_tendsto_setAverage_ball hFint
  have hbd : ∀ (x y : Vec d) (k : ℕ), Metric.ball x (2 * (1 / (k + 1 : ℝ))) ⊆ U →
      Metric.ball y (2 * (1 / (k + 1 : ℝ))) ⊆ U →
      |(⨍ w in Metric.ball x (1 / (k + 1 : ℝ)), U.indicator f w ∂volume) -
          ⨍ w in Metric.ball y (1 / (k + 1 : ℝ)), U.indicator f w ∂volume| ≤
        (ballAverageHolderOn U D (U.indicator f)).toReal * ‖x - y‖ ^ (1 / 2 : ℝ) :=
    fun x y k hx hy => abs_setAverage_ball_sub_le_toReal hD hFint hSF hx hy
  -- the averages form a Cauchy sequence at every point of the open set
  have hcauchy : ∀ x ∈ U, CauchySeq
      fun k : ℕ => ⨍ w in Metric.ball x (1 / (k + 1 : ℝ)), U.indicator f w ∂volume := by
    intro x hxU
    rw [Metric.cauchySeq_iff]
    intro eps heps
    obtain ⟨delta, hdelta, hballx⟩ := Metric.isOpen_iff.1 hU x hxU
    have hSpos : (0 : ℝ) < (ballAverageHolderOn U D (U.indicator f)).toReal + 1 := by linarith
    have hrhopos : (0 : ℝ) < min delta
        ((eps / (4 * ((ballAverageHolderOn U D (U.indicator f)).toReal + 1))) ^ (2 : ℕ)) :=
      lt_min hdelta (by positivity)
    obtain ⟨y, hyball, hyleb⟩ : ∃ y ∈ Metric.ball x
        (min delta
          ((eps / (4 * ((ballAverageHolderOn U D (U.indicator f)).toReal + 1))) ^ (2 : ℕ))),
        Tendsto (fun k : ℕ => ⨍ w in Metric.ball y (1 / (k + 1 : ℝ)),
            U.indicator f w ∂volume) atTop (𝓝 (U.indicator f y)) := by
      by_contra hcon
      push Not at hcon
      have hnull : volume {z : Vec d | ¬ Tendsto
          (fun k : ℕ => ⨍ w in Metric.ball z (1 / (k + 1 : ℝ)), U.indicator f w ∂volume)
          atTop (𝓝 (U.indicator f z))} = 0 := by
        rw [← ae_iff]
        exact hleb
      exact (Metric.measure_ball_pos volume x hrhopos).ne'
        (measure_mono_null (fun z hz => hcon z hz) hnull)
    have hyU : y ∈ U := hballx (Metric.ball_subset_ball (min_le_left _ _) hyball)
    have hnormxy : ‖x - y‖ <
        (eps / (4 * ((ballAverageHolderOn U D (U.indicator f)).toReal + 1))) ^ (2 : ℕ) := by
      have hd : dist y x < min delta
          ((eps / (4 * ((ballAverageHolderOn U D (U.indicator f)).toReal + 1))) ^ (2 : ℕ)) :=
        Metric.mem_ball.1 hyball
      have hd' : ‖x - y‖ < min delta
          ((eps / (4 * ((ballAverageHolderOn U D (U.indicator f)).toReal + 1))) ^ (2 : ℕ)) := by
        rwa [dist_comm, dist_eq_norm] at hd
      exact lt_of_lt_of_le hd' (min_le_right _ _)
    have hsq : ‖x - y‖ ^ (1 / 2 : ℝ) ≤
        eps / (4 * ((ballAverageHolderOn U D (U.indicator f)).toReal + 1)) := by
      rw [← Real.sqrt_eq_rpow]
      calc Real.sqrt ‖x - y‖
          ≤ Real.sqrt ((eps /
              (4 * ((ballAverageHolderOn U D (U.indicator f)).toReal + 1))) ^ (2 : ℕ)) :=
            Real.sqrt_le_sqrt hnormxy.le
        _ = eps / (4 * ((ballAverageHolderOn U D (U.indicator f)).toReal + 1)) :=
            Real.sqrt_sq (by positivity)
    have hxy : (ballAverageHolderOn U D (U.indicator f)).toReal * ‖x - y‖ ^ (1 / 2 : ℝ) <
        eps / 4 := by
      have h1 := mul_le_mul_of_nonneg_left hsq hSnn
      have hfrac : (ballAverageHolderOn U D (U.indicator f)).toReal /
          ((ballAverageHolderOn U D (U.indicator f)).toReal + 1) < 1 :=
        (div_lt_one hSpos).2 (by linarith)
      have h2 : (ballAverageHolderOn U D (U.indicator f)).toReal *
          (eps / (4 * ((ballAverageHolderOn U D (U.indicator f)).toReal + 1))) < eps / 4 := by
        calc (ballAverageHolderOn U D (U.indicator f)).toReal *
              (eps / (4 * ((ballAverageHolderOn U D (U.indicator f)).toReal + 1)))
            = eps / 4 * ((ballAverageHolderOn U D (U.indicator f)).toReal /
                ((ballAverageHolderOn U D (U.indicator f)).toReal + 1)) := by
              field_simp
          _ < eps / 4 * 1 := mul_lt_mul_of_pos_left hfrac (by linarith)
          _ = eps / 4 := mul_one _
      linarith
    obtain ⟨K₁, hK₁⟩ := eventually_atTop.1 (eventually_double_ball_subset hU hxU)
    obtain ⟨K₂, hK₂⟩ := eventually_atTop.1 (eventually_double_ball_subset hU hyU)
    obtain ⟨K₃, hK₃⟩ := Metric.tendsto_atTop.1 hyleb (eps / 4) (by linarith)
    refine ⟨max K₁ (max K₂ K₃), fun m hm n hn => ?_⟩
    have hm1 := hK₁ m (le_trans (le_max_left _ _) hm)
    have hm2 := hK₂ m (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm)
    have hn1 := hK₁ n (le_trans (le_max_left _ _) hn)
    have hn2 := hK₂ n (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn)
    have hm3 := hK₃ m (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm)
    have hn3 := hK₃ n (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn)
    rw [Real.dist_eq] at hm3 hn3
    have hA := abs_le.1 (hbd x y m hm1 hm2)
    have hB := abs_le.1 (hbd x y n hn1 hn2)
    have hC := abs_lt.1 hm3
    have hE := abs_lt.1 hn3
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hA.1, hA.2, hB.1, hB.2, hC.1, hC.2, hE.1, hE.2, hxy]
  have htend : ∀ x ∈ U, Tendsto
      (fun k : ℕ => ⨍ w in Metric.ball x (1 / (k + 1 : ℝ)), U.indicator f w ∂volume)
      atTop (𝓝 (ballAverageLimit (U.indicator f) x)) := by
    intro x hx
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (hcauchy x hx)
    have heq : ballAverageLimit (U.indicator f) x = L := hL.limUnder_eq
    rw [heq]
    exact hL
  have hHol : HolderSeminormBoundOn U (1 / 2)
      (ballAverageHolderOn U D (U.indicator f)).toReal (ballAverageLimit (U.indicator f)) := by
    intro x hx y hy
    rw [Real.norm_eq_abs]
    have hlim : Tendsto (fun k : ℕ =>
        |(⨍ w in Metric.ball x (1 / (k + 1 : ℝ)), U.indicator f w ∂volume) -
          ⨍ w in Metric.ball y (1 / (k + 1 : ℝ)), U.indicator f w ∂volume|) atTop
        (𝓝 |ballAverageLimit (U.indicator f) x - ballAverageLimit (U.indicator f) y|) :=
      ((htend x hx).sub (htend y hy)).abs
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_double_ball_subset hU hx, eventually_double_ball_subset hU hy]
      with k h1 h2
    exact hbd x y k h1 h2
  refine ⟨ballAverageLimit (U.indicator f), ?_,
    continuousOn_of_holderSeminormBoundOn hSnn (by norm_num) hHol⟩
  refine (ae_restrict_iff' hUmeas).2 ?_
  filter_upwards [hleb] with x hx hxU
  have hval : U.indicator f x = f x := Set.indicator_of_mem hxU f
  rw [← hval]
  exact tendsto_nhds_unique (htend x hxU) hx

end

end Algsuperdiff.Section5.Support

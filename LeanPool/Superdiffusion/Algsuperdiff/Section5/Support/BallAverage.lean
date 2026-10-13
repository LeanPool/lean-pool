/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.EssentialSupremum
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Covering.Differentiation
public import Mathlib.MeasureTheory.Integral.Average

/-!
# BallAverage

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Averages over balls

The quantities of Section 5.1 are attached to almost-everywhere classes of
Sobolev functions, and the only thing known to be measurable in the sample is
the integral of the solution over a fixed set.  Both gauges are therefore read
off the averages

```text
  ⨍_{B(x, 1/(k+1))} u ,     x in a countable dense set,  k : ℕ ,
```

of which there are countably many.  This module collects what those averages
need: that open and closed balls agree away from a null set, that the average is
continuous in the centre at a fixed radius, that it converges to the value of
the function at almost every point (Lebesgue differentiation), and that
translating the centre translates the integrand.

## Main results

* `ball_ae_eq_closedBall`, `setAverage_ball_eq_closedBall`.
* `continuous_setIntegral_ball` — continuity in the centre.
* `ae_tendsto_setAverage_ball` — Lebesgue differentiation along `1/(k+1)`.
* `eLpNorm_top_restrict_eq_ballAverageSupNormOn` — the `L^∞` norm on an open set
  is the supremum of countably many ball averages.

## References

* ABK26, the localized error and regularity quantities of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open HCPolySupport MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

variable {d : ℕ}

/-! ## 1. Open and closed balls -/

theorem ball_ae_eq_closedBall [NeZero d] (x : Vec d) (r : ℝ) :
    Metric.ball x r =ᵐ[volume] Metric.closedBall x r := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [MeasureTheory.ae_eq_set]
  constructor
  · rw [Set.sdiff_eq_empty.2 Metric.ball_subset_closedBall]
    exact measure_empty
  · rw [Metric.closedBall_sdiff_ball]
    exact MeasureTheory.Measure.addHaar_sphere volume x r

theorem setIntegral_ball_eq_closedBall [NeZero d] (f : Vec d → ℝ) (x : Vec d) (r : ℝ) :
    (∫ z in Metric.ball x r, f z ∂volume) = ∫ z in Metric.closedBall x r, f z ∂volume :=
  setIntegral_congr_set (ball_ae_eq_closedBall x r)

theorem setAverage_ball_eq_closedBall [NeZero d] (f : Vec d → ℝ) (x : Vec d) (r : ℝ) :
    (⨍ z in Metric.ball x r, f z ∂volume) = ⨍ z in Metric.closedBall x r, f z ∂volume := by
  rw [setAverage_eq, setAverage_eq, setIntegral_ball_eq_closedBall f x r,
    measureReal_congr (ball_ae_eq_closedBall x r)]

/-! ## 2. Lebesgue differentiation along the radii `1/(k+1)` -/

theorem tendsto_oneDivSucc_nhdsWithin_pos :
    Tendsto (fun k : ℕ => 1 / (k + 1 : ℝ)) atTop (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    tendsto_one_div_add_atTop_nhds_zero_nat ?_
  exact Filter.Eventually.of_forall fun k => Set.mem_Ioi.2 (by positivity)

/-- **Lebesgue differentiation along the radii `1/(k+1)`.** -/
theorem ae_tendsto_setAverage_ball [NeZero d] {f : Vec d → ℝ}
    (hf : Integrable f volume) :
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      Tendsto (fun k : ℕ => ⨍ z in Metric.ball x (1 / (k + 1 : ℝ)), f z ∂volume)
        atTop (𝓝 (f x)) := by
  filter_upwards [(Besicovitch.vitaliFamily (volume : Measure (Vec d))).ae_tendsto_average
    hf.locallyIntegrable] with x hx
  have hclosed := hx.comp (Besicovitch.tendsto_filterAt (volume : Measure (Vec d)) x)
  have hseq := hclosed.comp tendsto_oneDivSucc_nhdsWithin_pos
  refine hseq.congr fun k => ?_
  exact (setAverage_ball_eq_closedBall f x (1 / (k + 1 : ℝ))).symm

/-! ## 3. Continuity of the average in the centre -/

/-- **At a fixed radius the integral over a ball is continuous in the centre.** -/
theorem continuous_setIntegral_ball [NeZero d] {f : Vec d → ℝ} (hf : Integrable f volume)
    (r : ℝ) : Continuous fun x : Vec d => ∫ z in Metric.ball x r, f z ∂volume := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hrw : (fun x : Vec d => ∫ z in Metric.ball x r, f z ∂volume) =
      fun x : Vec d => ∫ z, (Metric.ball x r).indicator f z ∂volume := by
    funext x
    rw [integral_indicator measurableSet_ball]
  rw [hrw]
  refine continuous_iff_continuousAt.2 fun x => ?_
  refine tendsto_integral_filter_of_dominated_convergence (fun z => ‖f z‖) ?_ ?_ hf.norm ?_
  · exact Filter.Eventually.of_forall fun x' =>
      (hf.aestronglyMeasurable.indicator measurableSet_ball)
  · refine Filter.Eventually.of_forall fun x' => Filter.Eventually.of_forall fun z => ?_
    by_cases hz : z ∈ Metric.ball x' r
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, norm_zero]
      exact norm_nonneg _
  · have hsphere : volume (Metric.sphere x r) = 0 :=
      MeasureTheory.Measure.addHaar_sphere volume x r
    have hae : ∀ᵐ z ∂(volume : Measure (Vec d)), z ∉ Metric.sphere x r := by
      rw [MeasureTheory.ae_iff]
      simpa using! hsphere
    filter_upwards [hae] with z hz
    rcases lt_or_gt_of_ne (fun hcon => hz (by simpa [Metric.mem_sphere] using! hcon) :
        dist z x ≠ r) with hlt | hgt
    · have hmem : z ∈ Metric.ball x r := Metric.mem_ball.2 hlt
      rw [Set.indicator_of_mem hmem]
      have hev : (fun x' : Vec d => (Metric.ball x' r).indicator f z) =ᶠ[𝓝 x]
          fun _ : Vec d => f z := by
        have hopen : ∀ᶠ x' in 𝓝 x, dist z x' < r := by
          have hcont : Continuous fun x' : Vec d => dist z x' := continuous_const.dist continuous_id
          exact (hcont.continuousAt (x := x)).eventually_lt_const hlt
        filter_upwards [hopen] with x' hx'
        exact Set.indicator_of_mem (Metric.mem_ball.2 hx') f
      exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds
    · have hnot : z ∉ Metric.ball x r := by
        simp only [Metric.mem_ball, not_lt]
        exact hgt.le
      rw [Set.indicator_of_notMem hnot]
      have hev : (fun x' : Vec d => (Metric.ball x' r).indicator f z) =ᶠ[𝓝 x]
          fun _ : Vec d => (0 : ℝ) := by
        have hopen : ∀ᶠ x' in 𝓝 x, r < dist z x' := by
          have hcont : Continuous fun x' : Vec d => dist z x' := continuous_const.dist continuous_id
          exact (hcont.continuousAt (x := x)).eventually_const_lt hgt
        filter_upwards [hopen] with x' hx'
        refine Set.indicator_of_notMem ?_ f
        simp only [Metric.mem_ball, not_lt]
        exact hx'.le
      exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds

/-- **At a fixed radius the average over a ball is continuous in the centre.** -/
theorem continuous_setAverage_ball [NeZero d] {f : Vec d → ℝ} (hf : Integrable f volume)
    (r : ℝ) :
    Continuous fun x : Vec d => ⨍ z in Metric.ball x r, f z ∂volume := by
  have hvol : ∀ x : Vec d,
      volume.real (Metric.ball x r) = volume.real (Metric.ball (0 : Vec d) r) := by
    intro x
    rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
      MeasureTheory.Measure.addHaar_ball_center volume x r]
  have hrw : (fun x : Vec d => ⨍ z in Metric.ball x r, f z ∂volume) =
      fun x : Vec d =>
        (volume.real (Metric.ball (0 : Vec d) r))⁻¹ * ∫ z in Metric.ball x r, f z ∂volume := by
    funext x
    rw [setAverage_eq, smul_eq_mul, hvol x]
  rw [hrw]
  exact continuous_const.mul (continuous_setIntegral_ball hf r)

/-! ## 4. The essential supremum as a countable supremum of ball averages -/

/-- **The countable family of ball averages of `f`**: the balls `B(x, 1/(k+1))`
with `x` in a set `D` that fit inside `U`.  With `D` countable this is a
countable supremum. -/
def ballAverageSupNormOn (U D : Set (Vec d)) (f : Vec d → ℝ) : ℝ≥0∞ :=
  ⨆ x ∈ D, ⨆ k : ℕ, ⨆ _ : Metric.ball x (1 / (k + 1 : ℝ)) ⊆ U,
    ENNReal.ofReal |⨍ z in Metric.ball x (1 / (k + 1 : ℝ)), f z ∂volume|

theorem le_ballAverageSupNormOn {U D : Set (Vec d)} {f : Vec d → ℝ} {x : Vec d}
    (hx : x ∈ D) (k : ℕ) (hball : Metric.ball x (1 / (k + 1 : ℝ)) ⊆ U) :
    ENNReal.ofReal |⨍ z in Metric.ball x (1 / (k + 1 : ℝ)), f z ∂volume| ≤
      ballAverageSupNormOn U D f :=
  le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le k (le_iSup_of_le hball le_rfl)))

private theorem abs_setAverage_ball_le_of_ae {U : Set (Vec d)} {f : Vec d → ℝ}
    {C : ℝ} (hae : ∀ᵐ z ∂(volume : Measure (Vec d)), z ∈ U → |f z| ≤ C)
    {x : Vec d} {r : ℝ} (hr : 0 < r) (hball : Metric.ball x r ⊆ U) :
    |⨍ z in Metric.ball x r, f z ∂volume| ≤ C := by
  have hpos : 0 < volume.real (Metric.ball x r) := by
    rw [MeasureTheory.measureReal_def]
    exact ENNReal.toReal_pos (Metric.measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne
  have hbd : ‖∫ z in Metric.ball x r, f z ∂volume‖ ≤ C * volume.real (Metric.ball x r) := by
    refine norm_setIntegral_le_of_norm_le_const_ae' measure_ball_lt_top ?_
    filter_upwards [hae] with z hz hzb
    simpa [Real.norm_eq_abs] using hz (hball hzb)
  rw [setAverage_eq, smul_eq_mul, abs_mul, abs_of_nonneg (inv_nonneg.2 hpos.le)]
  rw [Real.norm_eq_abs] at hbd
  calc (volume.real (Metric.ball x r))⁻¹ * |∫ z in Metric.ball x r, f z ∂volume|
      ≤ (volume.real (Metric.ball x r))⁻¹ * (C * volume.real (Metric.ball x r)) :=
        mul_le_mul_of_nonneg_left hbd (inv_nonneg.2 hpos.le)
    _ = C := by field_simp

/-- **The `L^∞` norm on an open set is the supremum of countably many ball
averages.**  The elementary inequality is that an average never exceeds the
essential supremum; the converse is Lebesgue differentiation together with the
continuity of the average in the centre, which moves the centre onto the
countable set `D`. -/
theorem eLpNorm_top_restrict_eq_ballAverageSupNormOn [NeZero d] {U D : Set (Vec d)}
    (hU : IsOpen U) (hD : Dense D) {f : Vec d → ℝ} (hf : IntegrableOn f U volume) :
    eLpNorm f ⊤ (volume.restrict U) = ballAverageSupNormOn U D f := by
  have hUmeas : MeasurableSet U := hU.measurableSet
  have hFint : Integrable (U.indicator f) volume := hf.integrable_indicator hUmeas
  have hFeq : ∀ {B : Set (Vec d)}, MeasurableSet B → B ⊆ U →
      (⨍ z in B, U.indicator f z ∂volume) = ⨍ z in B, f z ∂volume := by
    intro B hBmeas hBU
    rw [setAverage_eq, setAverage_eq,
      setIntegral_congr_fun hBmeas fun z hz => Set.indicator_of_mem (hBU hz) f]
  refine le_antisymm ?_ ?_
  · -- the essential supremum is at most the supremum of the averages
    rcases eq_top_or_lt_top (ballAverageSupNormOn U D f) with hS | hS
    · rw [hS]
      exact le_top
    rw [eLpNorm_exponent_top hf.aestronglyMeasurable]
    have hStoReal : (0 : ℝ) ≤ (ballAverageSupNormOn U D f).toReal := ENNReal.toReal_nonneg
    refine essSup_le_of_ae_le _ ((ae_restrict_iff' hUmeas).2 ?_)
    filter_upwards [ae_tendsto_setAverage_ball hFint] with z hz hzU
    change ‖f z‖ₑ ≤ ballAverageSupNormOn U D f
    rw [← ofReal_norm, ← ENNReal.ofReal_toReal hS.ne]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.norm_eq_abs]
    refine le_of_forall_pos_le_add fun eps heps => ?_
    obtain ⟨delta, hdelta, hdball⟩ := Metric.isOpen_iff.1 hU z hzU
    have hzF : U.indicator f z = f z := Set.indicator_of_mem hzU f
    rw [hzF] at hz
    have habs : Tendsto
        (fun k : ℕ => |⨍ w in Metric.ball z (1 / (k + 1 : ℝ)), U.indicator f w ∂volume|)
        atTop (𝓝 |f z|) := hz.abs
    obtain ⟨K₁, hK₁⟩ := Metric.tendsto_atTop.1 habs (eps / 2) (by linarith)
    obtain ⟨K₂, hK₂⟩ := exists_nat_gt (2 / delta)
    obtain ⟨k, hk₁, hk₂⟩ : ∃ k : ℕ, K₁ ≤ k ∧ K₂ ≤ k :=
      ⟨max K₁ K₂, le_max_left _ _, le_max_right _ _⟩
    set r : ℝ := 1 / (k + 1 : ℝ) with hrdef
    have hrpos : 0 < r := by rw [hrdef]; positivity
    have hr2 : 2 * r < delta := by
      have hK₂' : (2 : ℝ) / delta < (k : ℝ) + 1 := by
        have : ((K₂ : ℝ)) ≤ (k : ℝ) := by exact_mod_cast hk₂
        linarith [hK₂]
      rw [hrdef]
      rw [div_lt_iff₀ hdelta] at hK₂'
      have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      rw [mul_one_div, div_lt_iff₀ hkpos]
      linarith [hK₂']
    have hball2 : Metric.ball z (2 * r) ⊆ U :=
      subset_trans (Metric.ball_subset_ball hr2.le) hdball
    have hclose : |(|⨍ w in Metric.ball z r, U.indicator f w ∂volume| - |f z|)| < eps / 2 := by
      have := hK₁ k hk₁
      rwa [Real.dist_eq] at this
    -- move the centre onto `D`
    have hcont := continuous_setAverage_ball hFint r
    obtain ⟨eta, hetapos, heta⟩ :=
      Metric.continuous_iff.1 hcont z (eps / 2) (by linarith)
    obtain ⟨x, hxD, hxdist0⟩ := Metric.mem_closure_iff.1 (hD z) (min eta r) (lt_min hetapos hrpos)
    have hxdist : dist x z < min eta r := by rwa [dist_comm] at hxdist0
    have hxz : dist x z < r := lt_of_lt_of_le hxdist (min_le_right _ _)
    have hxball : Metric.ball x r ⊆ U := by
      refine subset_trans (fun w hw => ?_) hball2
      have h1 : dist w x < r := Metric.mem_ball.1 hw
      refine Metric.mem_ball.2 ?_
      calc dist w z ≤ dist w x + dist x z := dist_triangle _ _ _
        _ < r + r := by linarith
        _ = 2 * r := by ring
    have hcentre : |(⨍ w in Metric.ball x r, U.indicator f w ∂volume) -
        ⨍ w in Metric.ball z r, U.indicator f w ∂volume| < eps / 2 := by
      have := heta x (lt_of_lt_of_le hxdist (min_le_left _ _))
      rwa [Real.dist_eq] at this
    have hxS : ENNReal.ofReal |⨍ w in Metric.ball x r, f w ∂volume| ≤
        ballAverageSupNormOn U D f := by
      have := le_ballAverageSupNormOn (U := U) (D := D) (f := f) hxD k
        (by rw [← hrdef]; exact hxball)
      rw [← hrdef] at this
      exact this
    have hxReal : |⨍ w in Metric.ball x r, f w ∂volume| ≤
        (ballAverageSupNormOn U D f).toReal := by
      have h := ENNReal.toReal_mono hS.ne hxS
      rwa [ENNReal.toReal_ofReal (abs_nonneg _)] at h
    have hxF : (⨍ w in Metric.ball x r, U.indicator f w ∂volume) =
        ⨍ w in Metric.ball x r, f w ∂volume := hFeq measurableSet_ball hxball
    rw [hxF] at hcentre
    have habs1 := abs_lt.1 hclose
    have htri : |⨍ w in Metric.ball z r, U.indicator f w ∂volume| ≤
        |⨍ w in Metric.ball x r, f w ∂volume| +
          |(⨍ w in Metric.ball x r, f w ∂volume) -
            ⨍ w in Metric.ball z r, U.indicator f w ∂volume| := by
      have := abs_sub_abs_le_abs_sub (⨍ w in Metric.ball z r, U.indicator f w ∂volume)
        (⨍ w in Metric.ball x r, f w ∂volume)
      have habs' : |(⨍ w in Metric.ball z r, U.indicator f w ∂volume) -
          ⨍ w in Metric.ball x r, f w ∂volume| =
          |(⨍ w in Metric.ball x r, f w ∂volume) -
            ⨍ w in Metric.ball z r, U.indicator f w ∂volume| := abs_sub_comm _ _
      rw [habs'] at this
      linarith
    linarith [habs1.1, habs1.2, htri, hcentre, hxReal]
  · -- the supremum of the averages is at most the essential supremum
    refine iSup_le fun x => iSup_le fun _hx => iSup_le fun k => iSup_le fun hball => ?_
    set c : ℝ≥0∞ := eLpNorm f ⊤ (volume.restrict U) with hc
    rcases eq_top_or_lt_top c with hctop | hctop
    · rw [hctop]
      exact le_top
    have hae : ∀ᵐ z ∂(volume : Measure (Vec d)), z ∈ U → |f z| ≤ c.toReal := by
      have hle : ∀ᵐ z ∂(volume.restrict U), ‖f z‖ₑ ≤ c := by
        rw [hc, eLpNorm_exponent_top hf.aestronglyMeasurable]
        exact ae_le_essSup
      rw [← ae_restrict_iff' hUmeas]
      filter_upwards [hle] with z hz
      have h := ENNReal.toReal_mono hctop.ne hz
      rwa [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _),
        Real.norm_eq_abs] at h
    have hrpos : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
    have hbd := abs_setAverage_ball_le_of_ae (U := U) (f := f) hae hrpos hball
    rw [← ENNReal.ofReal_toReal hctop.ne]
    exact ENNReal.ofReal_le_ofReal hbd

end

end Algsuperdiff.Section5.Support

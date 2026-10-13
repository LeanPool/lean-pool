/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.BallAverage
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.DensePoints
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.SolutionSelector

/-!
# BallAverageHolder

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Hölder seminorm as a countable supremum of ball averages

The `1/2`-Hölder seminorm of Section 5.1 is a pointwise quantity, so it is
attached to a continuous representative and is `⊤` when there is none.  Both
readings are captured by one countable supremum of difference quotients of ball
averages,

```text
  S(f) = sup { |⨍_{B(x,1/(k+1))} f - ⨍_{B(z,1/(k+1))} f| / |x - z|^{1/2} } ,
```

the supremum running over distinct centres in a countable dense set and over the
radii `1/(k+1)` for which both balls fit inside the open set.

This module proves one half of the identification: where a continuous
representative exists, `S` is exactly its Hölder seminorm.  Averaging the
pointwise Hölder bound over a ball gives one inequality — the two balls are
translates of each other, so the two averages pair up — and letting the radius
shrink at a pair of points of the dense set gives the other.

## Main results

* `setAverage_ball_sub` — the difference of two ball averages as one integral.
* `abs_setAverage_ball_sub_le` — a Hölder bound survives averaging.
* `ballAverageHolderOn_eq_holderSeminormOn`.

## References

* ABK26, the localized regularity of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open HCPolySupport MeasureTheory Filter
open Algsuperdiff.Section4.Support
open scoped ENNReal Topology

noncomputable section

variable {d : ℕ}

/-! ## 1. Translating the centre of a ball -/

theorem setIntegral_ball_eq_setIntegral_ball_zero (f : Vec d → ℝ) (x : Vec d) (r : ℝ) :
    (∫ w in Metric.ball x r, f w ∂volume) =
      ∫ w in Metric.ball (0 : Vec d) r, f (x + w) ∂volume := by
  rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball,
    ← integral_add_left_eq_self (fun w => (Metric.ball x r).indicator f w) x]
  congr 1
  funext w
  by_cases hw : w ∈ Metric.ball (0 : Vec d) r
  · have hxw : x + w ∈ Metric.ball x r := by
      simp only [Metric.mem_ball, dist_eq_norm] at hw ⊢
      simpa using hw
    rw [Set.indicator_of_mem hxw, Set.indicator_of_mem hw]
  · have hxw : x + w ∉ Metric.ball x r := by
      simp only [Metric.mem_ball, dist_eq_norm] at hw ⊢
      simpa using hw
    rw [Set.indicator_of_notMem hxw, Set.indicator_of_notMem hw]

theorem mem_ball_zero_iff_add_mem_ball {x w : Vec d} {r : ℝ} :
    w ∈ Metric.ball (0 : Vec d) r ↔ x + w ∈ Metric.ball x r := by
  simp only [Metric.mem_ball, dist_eq_norm]
  simp

/-- **The difference of two ball averages of the same radius is one integral over
the ball at the origin.** -/
theorem setAverage_ball_sub {f : Vec d → ℝ} (hf : Integrable f volume)
    (x z : Vec d) (r : ℝ) :
    (⨍ w in Metric.ball x r, f w ∂volume) - ⨍ w in Metric.ball z r, f w ∂volume =
      (volume.real (Metric.ball (0 : Vec d) r))⁻¹ *
        ∫ w in Metric.ball (0 : Vec d) r, (f (x + w) - f (z + w)) ∂volume := by
  have hvx : volume.real (Metric.ball x r) = volume.real (Metric.ball (0 : Vec d) r) := by
    rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
      MeasureTheory.Measure.addHaar_ball_center volume x r]
  have hvz : volume.real (Metric.ball z r) = volume.real (Metric.ball (0 : Vec d) r) := by
    rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
      MeasureTheory.Measure.addHaar_ball_center volume z r]
  have hix : IntegrableOn (fun w => f (x + w)) (Metric.ball (0 : Vec d) r) volume :=
    (hf.comp_add_left x).integrableOn
  have hiz : IntegrableOn (fun w => f (z + w)) (Metric.ball (0 : Vec d) r) volume :=
    (hf.comp_add_left z).integrableOn
  rw [setAverage_eq, setAverage_eq, hvx, hvz, smul_eq_mul, smul_eq_mul,
    setIntegral_ball_eq_setIntegral_ball_zero f x r,
    setIntegral_ball_eq_setIntegral_ball_zero f z r, integral_sub hix hiz, mul_sub]

/-- **A Hölder bound survives averaging.**  Two balls of the same radius are
translates of each other, so the difference of the averages pairs the values of
`f` at points a fixed distance apart. -/
theorem abs_setAverage_ball_sub_le [NeZero d] {U : Set (Vec d)} {f : Vec d → ℝ}
    (hf : Integrable f volume) {H : ℝ} (hH : HolderSeminormBoundOn U (1 / 2) H f)
    {x z : Vec d} {r : ℝ} (hr : 0 < r)
    (hbx : Metric.ball x r ⊆ U) (hbz : Metric.ball z r ⊆ U) :
    |(⨍ w in Metric.ball x r, f w ∂volume) - ⨍ w in Metric.ball z r, f w ∂volume| ≤
      H * ‖x - z‖ ^ (1 / 2 : ℝ) := by
  have hvolpos : 0 < volume.real (Metric.ball (0 : Vec d) r) := by
    rw [MeasureTheory.measureReal_def]
    exact ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 hr).ne' measure_ball_lt_top.ne
  have hbd : ‖∫ w in Metric.ball (0 : Vec d) r, (f (x + w) - f (z + w)) ∂volume‖ ≤
      (H * ‖x - z‖ ^ (1 / 2 : ℝ)) * volume.real (Metric.ball (0 : Vec d) r) := by
    refine norm_setIntegral_le_of_norm_le_const_ae' measure_ball_lt_top ?_
    refine Filter.Eventually.of_forall fun w hw => ?_
    have hxw : x + w ∈ U := hbx (mem_ball_zero_iff_add_mem_ball.1 hw)
    have hzw : z + w ∈ U := hbz (mem_ball_zero_iff_add_mem_ball.1 hw)
    have hbound := hH (x + w) hxw (z + w) hzw
    have hsub : (x + w) - (z + w) = x - z := by abel
    rw [hsub] at hbound
    exact hbound
  rw [setAverage_ball_sub hf x z r, abs_mul, abs_of_nonneg (inv_nonneg.2 hvolpos.le)]
  rw [Real.norm_eq_abs] at hbd
  calc (volume.real (Metric.ball (0 : Vec d) r))⁻¹ *
        |∫ w in Metric.ball (0 : Vec d) r, (f (x + w) - f (z + w)) ∂volume|
      ≤ (volume.real (Metric.ball (0 : Vec d) r))⁻¹ *
          ((H * ‖x - z‖ ^ (1 / 2 : ℝ)) * volume.real (Metric.ball (0 : Vec d) r)) :=
        mul_le_mul_of_nonneg_left hbd (inv_nonneg.2 hvolpos.le)
    _ = H * ‖x - z‖ ^ (1 / 2 : ℝ) := by field_simp

/-! ## 2. The countable family of difference quotients -/

/-- **The `1/2`-Hölder seminorm read off countably many ball averages.** -/
def ballAverageHolderOn (U D : Set (Vec d)) (f : Vec d → ℝ) : ℝ≥0∞ :=
  ⨆ x ∈ D, ⨆ z ∈ D, ⨆ _ : x ≠ z, ⨆ k : ℕ,
    ⨆ _ : Metric.ball x (1 / (k + 1 : ℝ)) ⊆ U, ⨆ _ : Metric.ball z (1 / (k + 1 : ℝ)) ⊆ U,
      ENNReal.ofReal (|(⨍ w in Metric.ball x (1 / (k + 1 : ℝ)), f w ∂volume) -
          ⨍ w in Metric.ball z (1 / (k + 1 : ℝ)), f w ∂volume| / ‖x - z‖ ^ (1 / 2 : ℝ))

theorem le_ballAverageHolderOn {U D : Set (Vec d)} {f : Vec d → ℝ} {x z : Vec d}
    (hx : x ∈ D) (hz : z ∈ D) (hne : x ≠ z) (k : ℕ)
    (hbx : Metric.ball x (1 / (k + 1 : ℝ)) ⊆ U)
    (hbz : Metric.ball z (1 / (k + 1 : ℝ)) ⊆ U) :
    ENNReal.ofReal (|(⨍ w in Metric.ball x (1 / (k + 1 : ℝ)), f w ∂volume) -
        ⨍ w in Metric.ball z (1 / (k + 1 : ℝ)), f w ∂volume| / ‖x - z‖ ^ (1 / 2 : ℝ)) ≤
      ballAverageHolderOn U D f :=
  le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le z (le_iSup_of_le hz (le_iSup_of_le hne
    (le_iSup_of_le k (le_iSup_of_le hbx (le_iSup_of_le hbz le_rfl)))))))

/-! ## 3. Where a continuous representative exists -/

private theorem eventually_ball_subset {U : Set (Vec d)} (hU : IsOpen U) {x : Vec d}
    (hx : x ∈ U) : ∀ᶠ k : ℕ in atTop, Metric.ball x (1 / (k + 1 : ℝ)) ⊆ U := by
  obtain ⟨delta, hdelta, hball⟩ := Metric.isOpen_iff.1 hU x hx
  have hr0 : Tendsto (fun k : ℕ => 1 / (k + 1 : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [Filter.Tendsto.eventually_lt_const hdelta hr0] with k hk
  exact subset_trans (Metric.ball_subset_ball hk.le) hball

private theorem setAverage_congr_of_ae {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hae : g =ᵐ[volume.restrict U] f) {B : Set (Vec d)} (hBU : B ⊆ U) :
    (⨍ w in B, g w ∂volume) = ⨍ w in B, f w ∂volume := by
  rw [setAverage_eq, setAverage_eq]
  congr 1
  exact integral_congr_ae (hae.filter_mono (ae_mono (Measure.restrict_mono hBU le_rfl)))

/-- **Where a continuous representative exists, the countable supremum of
difference quotients of ball averages is exactly its Hölder seminorm.** -/
theorem ballAverageHolderOn_eq_holderSeminormOn [NeZero d] {U D : Set (Vec d)}
    (hU : IsOpen U) (hD : Dense D) {f g : Vec d → ℝ} (hf : IntegrableOn f U volume)
    (hae : g =ᵐ[volume.restrict U] f) (hg : ContinuousOn g U) :
    ballAverageHolderOn U D f = holderSeminormOn U (1 / 2) g := by
  have hUmeas : MeasurableSet U := hU.measurableSet
  have hgU : IntegrableOn g U volume := hf.congr hae.symm
  have hGint : Integrable (U.indicator g) volume := hgU.integrable_indicator hUmeas
  have hGeq : ∀ (p : Vec d) (r : ℝ), Metric.ball p r ⊆ U →
      (⨍ w in Metric.ball p r, U.indicator g w ∂volume) =
        ⨍ w in Metric.ball p r, f w ∂volume := by
    intro p r hBU
    rw [setAverage_eq, setAverage_eq]
    congr 1
    rw [setIntegral_congr_fun measurableSet_ball fun w hw => Set.indicator_of_mem (hBU hw) g]
    exact integral_congr_ae (hae.filter_mono (ae_mono (Measure.restrict_mono hBU le_rfl)))
  refine le_antisymm ?_ ?_
  · refine iSup_le fun x => iSup_le fun _hxD => iSup_le fun z => iSup_le fun _hzD =>
      iSup_le fun hne => iSup_le fun k => iSup_le fun hbx => iSup_le fun hbz => ?_
    rcases eq_top_or_lt_top (holderSeminormOn U (1 / 2) g) with htop | htop
    · rw [htop]
      exact le_top
    have hHnn : (0 : ℝ) ≤ (holderSeminormOn U (1 / 2) g).toReal := ENNReal.toReal_nonneg
    have hHeq : ENNReal.ofReal (holderSeminormOn U (1 / 2) g).toReal =
        holderSeminormOn U (1 / 2) g := ENNReal.ofReal_toReal htop.ne
    have hHol : HolderSeminormBoundOn U (1 / 2) (holderSeminormOn U (1 / 2) g).toReal g :=
      (holderSeminormOn_le_ofReal_iff hHnn).1 (le_of_eq hHeq.symm)
    have hHolG : HolderSeminormBoundOn U (1 / 2)
        (holderSeminormOn U (1 / 2) g).toReal (U.indicator g) := by
      intro p hp q hq
      rw [Set.indicator_of_mem hp, Set.indicator_of_mem hq]
      exact hHol p hp q hq
    have hrpos : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
    have hbound := abs_setAverage_ball_sub_le hGint hHolG hrpos hbx hbz
    rw [hGeq x _ hbx, hGeq z _ hbz] at hbound
    have hNpos : (0 : ℝ) < ‖x - z‖ ^ (1 / 2 : ℝ) :=
      Real.rpow_pos_of_pos (by rw [norm_pos_iff]; exact sub_ne_zero.2 hne) _
    rw [← hHeq]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ hNpos]
    exact hbound
  · rw [holderSeminormOn_eq_iSup_dense hU hD hg]
    refine iSup_le fun x => iSup_le fun hx => iSup_le fun z => iSup_le fun hz =>
      iSup_le fun hne => ?_
    have hrpos : ∀ k : ℕ, (0 : ℝ) < 1 / (k + 1 : ℝ) := fun k => by positivity
    have hr0 : Tendsto (fun k : ℕ => 1 / (k + 1 : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hxlim := tendsto_setAverage_ball_of_continuousOn hU hg hx.1 hrpos hr0
    have hzlim := tendsto_setAverage_ball_of_continuousOn hU hg hz.1 hrpos hr0
    have hlim : Tendsto (fun k : ℕ => ENNReal.ofReal
        (‖(⨍ w in Metric.ball x (1 / (k + 1 : ℝ)), g w ∂volume) -
           ⨍ w in Metric.ball z (1 / (k + 1 : ℝ)), g w ∂volume‖ / ‖x - z‖ ^ (1 / 2 : ℝ)))
        atTop (𝓝 (ENNReal.ofReal (‖g x - g z‖ / ‖x - z‖ ^ (1 / 2 : ℝ)))) := by
      refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
      exact ((hxlim.sub hzlim).norm).div_const _
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_ball_subset hU hx.1, eventually_ball_subset hU hz.1]
      with k hbx hbz
    rw [setAverage_congr_of_ae hae hbx, setAverage_congr_of_ae hae hbz, Real.norm_eq_abs]
    exact le_ballAverageHolderOn hx.2 hz.2 hne k hbx hbz

end

end Algsuperdiff.Section5.Support

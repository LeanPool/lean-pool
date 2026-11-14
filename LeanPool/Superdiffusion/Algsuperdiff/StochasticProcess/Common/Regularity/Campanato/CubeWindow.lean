/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Campanato.DiscreteScales
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Campanato.TriadicTelescope
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CoarseMeanComparison

/-!
# CubeWindow

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Windows clipped to a cube, and their volume

A regularity iteration run on a cube states its oscillation estimate on the
windows **clipped to that cube**: the window at a centre `x` and scale `r` is
`(x + □) ∩ □_m`, not `x + □`.  Away from the boundary the two agree, but the
whole interest of a boundary-to-boundary Hölder estimate is at centres for which
they do not.

In the ambient space `Vec d = Fin d → ℝ` the metric is the supremum norm, so a
clipped window is the intersection of two boxes and is again a box.  Its volume
is therefore easy to bracket, and the bracket is all the Campanato theory needs:

* every clipped window sits in the unclipped one, so its volume is at most
  `(2 r) ^ d`;
* a clipped window of a centre **inside** the cube contains a ball of radius
  `r / 2`, so its volume is at least `r ^ d`.

The lower bound is the only substantive point.  Pushing the centre toward the
face of the cube shrinks one side of the window, but never below `r`: the side
lost on one face is gained on the other.  The explicit inner ball is centred at
the projection of `x` onto the concentric cube of half-side `Rm - r / 2`.

The consequence is that all the volume ratios of the theory are bounded by
`(2 R / r) ^ d` instead of `(R / r) ^ d`: clipping costs a factor `2 ^ d` in the
volume, i.e. `2 ^ (d/2)` in the normalized `L²` price, once and for all.

## Main definitions

* `clipBall c Rm x r` — the window `B(x, r) ∩ B(c, Rm)`.

## Main results

* `exists_ball_subset_clipBall` — the inner ball of radius `r / 2`.
* `pow_le_volume_clipBall_toReal`, `volume_clipBall_toReal_le` — the volume
  bracket `r ^ d ≤ |W| ≤ (2 r) ^ d`.
* `sqrt_volume_clipBall_ratio_le` — the normalized-`L²` price of two clipped
  windows, `ballVolumePrice κ d` whenever `2 R ≤ κ r`.
* `oscillation_clipBall_le_of_subset` — the mean-oscillation comparison between
  nested clipped windows.
* `abs_volumeAverage_clipBall_sub_le` — the mean comparison between nested
  clipped windows.
* `eventually_clipBall_eq_ball` — at an interior centre the clipping is
  eventually inactive, which is what identifies the clipped telescope's limit
  with the unclipped one.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Campanato

open MeasureTheory HCPolySupport Filter Topology
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported

noncomputable section

variable {d : ℕ}

/-! ## 1. The clipped window -/

/-- **The window at `x` and scale `r`, clipped to the cube `B(c, Rm)`.**  In the
supremum metric of `Vec d` this is the intersection of the open cube of side
`2 r` centred at `x` with the open cube of side `2 Rm` centred at `c`. -/
def clipBall (c : Vec d) (Rm : ℝ) (x : Vec d) (r : ℝ) : Set (Vec d) :=
  Metric.ball x r ∩ Metric.ball c Rm

theorem clipBall_subset_ball (c : Vec d) (Rm : ℝ) (x : Vec d) (r : ℝ) :
    clipBall c Rm x r ⊆ Metric.ball x r := Set.inter_subset_left

theorem clipBall_subset_ambient (c : Vec d) (Rm : ℝ) (x : Vec d) (r : ℝ) :
    clipBall c Rm x r ⊆ Metric.ball c Rm := Set.inter_subset_right

theorem measurableSet_clipBall (c : Vec d) (Rm : ℝ) (x : Vec d) (r : ℝ) :
    MeasurableSet (clipBall c Rm x r) :=
  measurableSet_ball.inter measurableSet_ball

/-- A clipped window at a nearby centre and a larger scale contains the given
one. -/
theorem clipBall_subset_clipBall {c : Vec d} {Rm : ℝ} {x z : Vec d} {r R : ℝ}
    (h : r + ‖x - z‖ ≤ R) : clipBall c Rm x r ⊆ clipBall c Rm z R := by
  refine Set.inter_subset_inter_left _ (Metric.ball_subset_ball' ?_)
  rwa [dist_eq_norm]

/-- The clipping is inactive when the unclipped window already sits in the
cube. -/
theorem clipBall_eq_ball {c : Vec d} {Rm : ℝ} {x : Vec d} {r : ℝ}
    (h : Metric.ball x r ⊆ Metric.ball c Rm) : clipBall c Rm x r = Metric.ball x r :=
  Set.inter_eq_self_of_subset_left h

/-! ## 2. The inner ball -/

/-- **A clipped window of an interior centre contains a ball of half the
radius.**  The centre of that ball is the projection of `x` onto the cube
concentric with the ambient one of half-side `Rm - r / 2`: moving `x` toward the
centre by less than `r / 2` buys the room the clipping took away. -/
theorem exists_ball_subset_clipBall {c : Vec d} {Rm r : ℝ} {x : Vec d}
    (hr : 0 < r) (hrRm : r ≤ Rm) (hx : x ∈ Metric.ball c Rm) :
    ∃ p : Vec d, Metric.ball p (r / 2) ⊆ clipBall c Rm x r := by
  have hs0 : (0 : ℝ) ≤ Rm - r / 2 := by linarith only [hr, hrRm]
  have hcoord : ∀ i, |x i - c i| < Rm := by
    intro i
    have hnorm : ‖x - c‖ < Rm := by
      rwa [Metric.mem_ball, dist_eq_norm] at hx
    have hle := norm_le_pi_norm (x - c) i
    rw [Pi.sub_apply, Real.norm_eq_abs] at hle
    linarith only [hle, hnorm]
  obtain ⟨p, hp⟩ : ∃ p : Vec d, ∀ i,
      p i = max (c i - (Rm - r / 2)) (min (c i + (Rm - r / 2)) (x i)) :=
    ⟨fun i => max (c i - (Rm - r / 2)) (min (c i + (Rm - r / 2)) (x i)), fun _ => rfl⟩
  have hpc : ‖p - c‖ ≤ Rm - r / 2 := by
    refine (pi_norm_le_iff_of_nonneg hs0).2 fun i => ?_
    rw [Pi.sub_apply, Real.norm_eq_abs, abs_le, hp i]
    refine ⟨?_, ?_⟩
    · have h := le_max_left (c i - (Rm - r / 2)) (min (c i + (Rm - r / 2)) (x i))
      linarith only [h]
    · have h : max (c i - (Rm - r / 2)) (min (c i + (Rm - r / 2)) (x i)) ≤
          c i + (Rm - r / 2) := max_le (by linarith only [hs0]) (min_le_left _ _)
      linarith only [h]
  have hpx : ‖p - x‖ ≤ r / 2 := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    have hi := hcoord i
    rw [abs_lt] at hi
    rw [Pi.sub_apply, Real.norm_eq_abs, abs_le, hp i]
    refine ⟨?_, ?_⟩
    · have hmin : x i - r / 2 ≤ min (c i + (Rm - r / 2)) (x i) :=
        le_min (by linarith only [hi.2]) (by linarith only [hr])
      have h := hmin.trans
        (le_max_right (c i - (Rm - r / 2)) (min (c i + (Rm - r / 2)) (x i)))
      linarith only [h]
    · have h : max (c i - (Rm - r / 2)) (min (c i + (Rm - r / 2)) (x i)) ≤ x i + r / 2 :=
        max_le (by linarith only [hi.1])
          ((min_le_right _ _).trans (by linarith only [hr]))
      linarith only [h]
  refine ⟨p, Set.subset_inter (Metric.ball_subset_ball' ?_) (Metric.ball_subset_ball' ?_)⟩
  · rw [dist_eq_norm]
    linarith only [hpx]
  · rw [dist_eq_norm]
    linarith only [hpc]

/-! ## 3. The volume bracket -/

theorem volume_clipBall_ne_top (c : Vec d) (Rm : ℝ) (x : Vec d) {r : ℝ} (hr : 0 < r) :
    volume (clipBall c Rm x r) ≠ ⊤ := by
  have hball : volume (Metric.ball x r) ≠ ⊤ := by
    rw [Real.volume_pi_ball x hr]
    exact ENNReal.ofReal_ne_top
  exact ne_top_of_le_ne_top hball (measure_mono (clipBall_subset_ball c Rm x r))

theorem volume_clipBall_toReal_le (c : Vec d) (Rm : ℝ) (x : Vec d) {r : ℝ} (hr : 0 < r) :
    (volume (clipBall c Rm x r)).toReal ≤ (2 * r) ^ d := by
  have hball : volume (Metric.ball x r) ≠ ⊤ := by
    rw [Real.volume_pi_ball x hr]
    exact ENNReal.ofReal_ne_top
  have hle : (volume (clipBall c Rm x r)).toReal ≤ (volume (Metric.ball x r)).toReal :=
    ENNReal.toReal_mono hball (measure_mono (clipBall_subset_ball c Rm x r))
  rwa [volume_metricBall_toReal x hr] at hle

/-- **The volume lower bound.**  Clipping a window at an interior centre costs at
most the factor `2 ^ d`. -/
theorem pow_le_volume_clipBall_toReal {c : Vec d} {Rm r : ℝ} {x : Vec d}
    (hr : 0 < r) (hrRm : r ≤ Rm) (hx : x ∈ Metric.ball c Rm) :
    r ^ d ≤ (volume (clipBall c Rm x r)).toReal := by
  obtain ⟨p, hp⟩ := exists_ball_subset_clipBall hr hrRm hx
  have hhalf : (0 : ℝ) < r / 2 := by linarith only [hr]
  have hmono := ENNReal.toReal_mono (volume_clipBall_ne_top c Rm x hr) (measure_mono hp)
  rw [volume_metricBall_toReal p hhalf] at hmono
  have hid : (2 * (r / 2)) ^ d = r ^ d := by
    congr 1
    ring
  rwa [hid] at hmono

theorem volume_clipBall_toReal_pos {c : Vec d} {Rm r : ℝ} {x : Vec d}
    (hr : 0 < r) (hrRm : r ≤ Rm) (hx : x ∈ Metric.ball c Rm) :
    0 < (volume (clipBall c Rm x r)).toReal :=
  lt_of_lt_of_le (by positivity) (pow_le_volume_clipBall_toReal hr hrRm hx)

theorem volume_clipBall_pos {c : Vec d} {Rm r : ℝ} {x : Vec d}
    (hr : 0 < r) (hrRm : r ≤ Rm) (hx : x ∈ Metric.ball c Rm) :
    0 < volume (clipBall c Rm x r) := by
  by_contra hcon
  have hzero : volume (clipBall c Rm x r) = 0 := by
    simpa only [nonpos_iff_eq_zero] using not_lt.1 hcon
  have := volume_clipBall_toReal_pos hr hrRm hx
  rw [hzero, ENNReal.toReal_zero] at this
  exact lt_irrefl 0 this

/-- **The normalized-`L²` price of two clipped windows.**  The numerator is at
most `(2 R) ^ d` and the denominator at least `r ^ d`, so the price is
`ballVolumePrice κ d` for any `κ` with `2 R ≤ κ r`. -/
theorem sqrt_volume_clipBall_ratio_le {c : Vec d} {Rm r R kappa : ℝ} {x z : Vec d}
    (hr : 0 < r) (hrRm : r ≤ Rm) (hx : x ∈ Metric.ball c Rm) (hR : 0 < R)
    (hle : 2 * R ≤ kappa * r) :
    Real.sqrt ((volume (clipBall c Rm z R)).toReal /
        (volume (clipBall c Rm x r)).toReal) ≤ ballVolumePrice kappa d := by
  have hden : 0 < r ^ d := by positivity
  have hnum : (volume (clipBall c Rm z R)).toReal ≤ (kappa * r) ^ d := by
    refine (volume_clipBall_toReal_le c Rm z hR).trans ?_
    exact pow_le_pow_left₀ (by linarith only [hR]) hle d
  have hratio : (volume (clipBall c Rm z R)).toReal /
      (volume (clipBall c Rm x r)).toReal ≤ kappa ^ d := by
    rw [div_le_iff₀ (volume_clipBall_toReal_pos hr hrRm hx)]
    calc (volume (clipBall c Rm z R)).toReal ≤ (kappa * r) ^ d := hnum
      _ = kappa ^ d * r ^ d := by rw [mul_pow]
      _ ≤ kappa ^ d * (volume (clipBall c Rm x r)).toReal := by
          refine mul_le_mul_of_nonneg_left (pow_le_volume_clipBall_toReal hr hrRm hx) ?_
          have hk : 0 ≤ kappa := by
            by_contra hcon
            have : kappa * r < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hcon) hr
            linarith only [this, hR, hle]
          positivity
  rw [ballVolumePrice]
  exact Real.sqrt_le_sqrt hratio

/-! ## 4. The two comparisons on nested clipped windows -/

/-- **The mean-oscillation comparison between nested clipped windows.** -/
theorem oscillation_clipBall_le_of_subset {c : Vec d} {Rm r R kappa : ℝ}
    {x z : Vec d} {f : Vec d → ℝ}
    (hr : 0 < r) (hrRm : r ≤ Rm) (hx : x ∈ Metric.ball c Rm) (hR : 0 < R)
    (hRRm : R ≤ Rm) (hz : z ∈ Metric.ball c Rm)
    (hsub : clipBall c Rm x r ⊆ clipBall c Rm z R) (hle : 2 * R ≤ kappa * r)
    (hf : MemLp f 2 (volume.restrict (Metric.ball c Rm))) :
    normalizedL2On (clipBall c Rm x r)
        (fun y => f y - volumeAverage (clipBall c Rm x r) f) ≤
      ballVolumePrice kappa d *
        normalizedL2On (clipBall c Rm z R)
          (fun y => f y - volumeAverage (clipBall c Rm z R) f) := by
  have hmemOuter : MemLp f 2 (volume.restrict (clipBall c Rm z R)) :=
    hf.mono_measure (Measure.restrict_mono (clipBall_subset_ambient c Rm z R) le_rfl)
  have hmemInner : MemLp f 2 (volume.restrict (clipBall c Rm x r)) :=
    hf.mono_measure (Measure.restrict_mono (clipBall_subset_ambient c Rm x r) le_rfl)
  let finiteVolumeInner : IsFiniteMeasure (volume.restrict (clipBall c Rm x r)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 (volume_clipBall_ne_top c Rm x hr)⟩
  let finiteVolumeOuter : IsFiniteMeasure (volume.restrict (clipBall c Rm z R)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 (volume_clipBall_ne_top c Rm z hR)⟩
  have hmin := normalizedL2On_sub_average_le_sub_const
    (W := clipBall c Rm x r) (volume_clipBall_pos hr hrRm hx)
    (volume_clipBall_ne_top c Rm x hr)
    (hmemInner.integrable one_le_two) hmemInner.integrable_sq
    (volumeAverage (clipBall c Rm z R) f)
  have hdiffOuter : MemLp (fun y => f y - volumeAverage (clipBall c Rm z R) f) 2
      (volume.restrict (clipBall c Rm z R)) := hmemOuter.sub (memLp_const _)
  have hsubset := normalizedL2On_le_of_subset
    (f := fun y => f y - volumeAverage (clipBall c Rm z R) f)
    hsub (volume_clipBall_toReal_pos hR hRRm hz)
    (volume_clipBall_toReal_pos hr hrRm hx) hdiffOuter.integrable_sq
  have hprice := sqrt_volume_clipBall_ratio_le (z := z) hr hrRm hx hR hle
  exact hmin.trans (hsubset.trans
    (mul_le_mul_of_nonneg_right hprice (normalizedL2On_nonneg _ _)))

/-- **The mean comparison between nested clipped windows.** -/
theorem abs_volumeAverage_clipBall_sub_le {c : Vec d} {Rm r R kappa : ℝ}
    {x z : Vec d} {f : Vec d → ℝ}
    (hr : 0 < r) (hrRm : r ≤ Rm) (hx : x ∈ Metric.ball c Rm) (hR : 0 < R)
    (hRRm : R ≤ Rm) (hz : z ∈ Metric.ball c Rm)
    (hsub : clipBall c Rm x r ⊆ clipBall c Rm z R) (hle : 2 * R ≤ kappa * r)
    (hf : MemLp f 2 (volume.restrict (Metric.ball c Rm))) :
    |volumeAverage (clipBall c Rm x r) f - volumeAverage (clipBall c Rm z R) f| ≤
      ballVolumePrice kappa d *
        normalizedL2On (clipBall c Rm z R)
          (fun y => f y - volumeAverage (clipBall c Rm z R) f) := by
  have hmemOuter : MemLp f 2 (volume.restrict (clipBall c Rm z R)) :=
    hf.mono_measure (Measure.restrict_mono (clipBall_subset_ambient c Rm z R) le_rfl)
  have hmemInner : MemLp f 2 (volume.restrict (clipBall c Rm x r)) :=
    hf.mono_measure (Measure.restrict_mono (clipBall_subset_ambient c Rm x r) le_rfl)
  let finiteVolumeInner : IsFiniteMeasure (volume.restrict (clipBall c Rm x r)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 (volume_clipBall_ne_top c Rm x hr)⟩
  let finiteVolumeOuter : IsFiniteMeasure (volume.restrict (clipBall c Rm z R)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 (volume_clipBall_ne_top c Rm z hR)⟩
  have hdiffOuter : MemLp (fun y => f y - volumeAverage (clipBall c Rm z R) f) 2
      (volume.restrict (clipBall c Rm z R)) := hmemOuter.sub (memLp_const _)
  have hdiffInner : MemLp (fun y => f y - volumeAverage (clipBall c Rm z R) f) 2
      (volume.restrict (clipBall c Rm x r)) := hmemInner.sub (memLp_const _)
  have hmean := abs_volumeAverage_sub_windowAverage_le
    (measurableSet_clipBall c Rm x r) hsub
    (volume_clipBall_toReal_pos hR hRRm hz)
    (volume_clipBall_toReal_pos hr hrRm hx)
    (volume_clipBall_ne_top c Rm x hr)
    (hmemInner.integrable one_le_two) hdiffInner.integrable_sq hdiffOuter.integrable_sq
  have hprice := sqrt_volume_clipBall_ratio_le (z := z) hr hrRm hx hR hle
  exact hmean.trans (mul_le_mul_of_nonneg_right hprice (normalizedL2On_nonneg _ _))

/-! ## 5. The clipping is eventually inactive at an interior centre -/

/-- At a centre of the open cube the triadic windows are eventually untruncated:
the clipped and unclipped telescopes have the same tail, hence the same limit. -/
theorem eventually_clipBall_eq_ball {c : Vec d} {Rm : ℝ} (R : ℝ) {x : Vec d}
    (hx : x ∈ Metric.ball c Rm) :
    ∀ᶠ k in atTop, clipBall c Rm x (triadicRadius R k) =
      Metric.ball x (triadicRadius R k) := by
  have hnorm : ‖x - c‖ < Rm := by
    rwa [Metric.mem_ball, dist_eq_norm] at hx
  have htend : Tendsto (triadicRadius R) atTop (nhds (0 : ℝ)) := by
    have h : Tendsto (fun k : ℕ => R * (1 / 3 : ℝ) ^ k) atTop (nhds (R * 0)) :=
      tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one (𝕜 := ℝ) (r := (1 / 3 : ℝ))
          (by norm_num) (by norm_num))
    simpa only [triadicRadius, mul_zero] using! h
  have hev := htend.eventually_lt_const (by linarith only [hnorm] : (0 : ℝ) < Rm - ‖x - c‖)
  filter_upwards [hev] with k hk
  refine clipBall_eq_ball (Metric.ball_subset_ball' ?_)
  rw [dist_eq_norm]
  linarith only [hk]

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Campanato

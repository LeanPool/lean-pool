/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Campanato.CubeWindow

/-!
# CubeTelescope

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Campanato telescope on windows clipped to a cube

This file runs the triadic Campanato telescope with the windows clipped to a
cube, so that the resulting estimate reaches the boundary of the cube rather
than an interior sub-cube.

The construction is the unclipped one, with two changes.  Every volume ratio is
paid at `ballVolumePrice 6 d = 6 ^ (d/2)` rather than `3 ^ (d/2)`, because a
clipped window can be half as wide as the unclipped one in every direction; and
the enclosing window of the geometric step is taken at the same centre, so the
step needs no room above the top radius.

The limit of the clipped telescope is **the same function** as the limit of the
unclipped one: at a centre of the open cube the clipping is eventually inactive,
so the two sequences of means have the same tail.  Everything is therefore
stated for `campanatoRepresentative`, and the clipped theory only supplies
bounds for it that are valid up to the boundary.

## Main definitions

* `HasClipCampanatoDecayOn c Rm S Rtop α K f` — oscillation decay on the clipped
  windows, at every radius.
* `HasClipTriadicOscillationDecayOn c Rm S Rtop α K f` — the same at the discrete
  triadic radii only.
* `clipScaleStepConstant d α` — the price `6 ^ (d/2) 3 ^ α` of one triadic step
  on clipped windows.
* `clipCampanatoAverage c Rm f R x k` — the mean over the clipped window.

## Main results

* `hasClipCampanatoDecayOn_of_triadic` — the discrete family controls every
  radius.
* `dist_clipCampanatoAverage_succ_le` — the geometric bound on consecutive means.
* `tendsto_clipCampanatoAverage` — the clipped means converge to
  `campanatoRepresentative`.
* `dist_clipCampanatoAverage_representative_le` — the uniform tail.
* `campanatoRepresentative_ae_eq_of_clip` — the limit is a representative of `f`.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Campanato

open MeasureTheory HCPolySupport Filter Topology
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported

noncomputable section

variable {d : ℕ}

/-! ## 1. The hypotheses -/

/-- **Campanato oscillation decay on the clipped windows**: the
volume-normalized `L²` oscillation on `B(x, r) ∩ B(c, Rm)` is at most `K r ^ α`
for every centre `x ∈ S` and every radius `0 < r ≤ Rtop`. -/
def HasClipCampanatoDecayOn (c : Vec d) (Rm : ℝ) (S : Set (Vec d))
    (Rtop alpha K : ℝ) (f : Vec d → ℝ) : Prop :=
  ∀ x ∈ S, ∀ r : ℝ, 0 < r → r ≤ Rtop →
    normalizedL2On (clipBall c Rm x r)
      (fun y => f y - volumeAverage (clipBall c Rm x r) f) ≤ K * r ^ alpha

/-- **Oscillation decay on the clipped windows at the discrete triadic radii
only.**  This is the shape a scale-by-scale iteration produces. -/
def HasClipTriadicOscillationDecayOn (c : Vec d) (Rm : ℝ) (S : Set (Vec d))
    (Rtop alpha K : ℝ) (f : Vec d → ℝ) : Prop :=
  ∀ x ∈ S, ∀ j : ℕ,
    normalizedL2On (clipBall c Rm x (triadicRadius Rtop j))
      (fun y => f y - volumeAverage (clipBall c Rm x (triadicRadius Rtop j)) f) ≤
      K * triadicRadius Rtop j ^ alpha

/-- **The price of one triadic step between clipped windows**: the volume ratio
`6 ^ (d/2)` and the `α`-weight `3 ^ α`. -/
def clipScaleStepConstant (d : ℕ) (alpha : ℝ) : ℝ := ballVolumePrice 6 d * (3 : ℝ) ^ alpha

theorem clipScaleStepConstant_nonneg (d : ℕ) (alpha : ℝ) :
    0 ≤ clipScaleStepConstant d alpha :=
  mul_nonneg (ballVolumePrice_nonneg 6 d) (Real.rpow_nonneg (by norm_num) _)

/-! ## 2. From the discrete scales to all radii -/

/-- **The discrete clipped family controls every radius.** -/
theorem hasClipCampanatoDecayOn_of_triadic
    {c : Vec d} {Rm : ℝ} {S : Set (Vec d)} {Rtop alpha K : ℝ} {f : Vec d → ℝ}
    (hRtop : 0 < Rtop) (hRtopRm : Rtop ≤ Rm) (halpha : 0 ≤ alpha) (hK : 0 ≤ K)
    (hS : S ⊆ Metric.ball c Rm)
    (hf : MemLp f 2 (volume.restrict (Metric.ball c Rm)))
    (hdisc : HasClipTriadicOscillationDecayOn c Rm S Rtop alpha K f) :
    HasClipCampanatoDecayOn c Rm S Rtop alpha (clipScaleStepConstant d alpha * K) f := by
  intro x hx r hr hrTop
  obtain ⟨j, hjlo, hjhi⟩ := exists_triadicRadius_bracket hRtop hr hrTop
  have hrho : 0 < triadicRadius Rtop j := triadicRadius_pos hRtop j
  have hle : triadicRadius Rtop j ≤ 3 * r := by
    rw [triadicRadius_succ] at hjlo
    linarith only [hjlo]
  have hsub : clipBall c Rm x r ⊆ clipBall c Rm x (triadicRadius Rtop j) :=
    Set.inter_subset_inter_left _ (Metric.ball_subset_ball hjhi)
  have hcomp := oscillation_clipBall_le_of_subset (kappa := 6) hr
    (hrTop.trans hRtopRm) (hS hx) hrho
    ((triadicRadius_le hRtop.le j).trans hRtopRm) (hS hx) hsub
    (by linarith only [hle]) hf
  have hosc := hdisc x hx j
  have hpow : triadicRadius Rtop j ^ alpha ≤ (3 : ℝ) ^ alpha * r ^ alpha := by
    have hmono := Real.rpow_le_rpow hrho.le hle halpha
    rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hr.le] at hmono
  calc normalizedL2On (clipBall c Rm x r)
        (fun y => f y - volumeAverage (clipBall c Rm x r) f)
      ≤ ballVolumePrice 6 d *
        normalizedL2On (clipBall c Rm x (triadicRadius Rtop j))
          (fun y => f y - volumeAverage (clipBall c Rm x (triadicRadius Rtop j)) f) := hcomp
    _ ≤ ballVolumePrice 6 d * (K * triadicRadius Rtop j ^ alpha) :=
        mul_le_mul_of_nonneg_left hosc (ballVolumePrice_nonneg 6 d)
    _ ≤ ballVolumePrice 6 d * (K * ((3 : ℝ) ^ alpha * r ^ alpha)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hK)
          (ballVolumePrice_nonneg 6 d)
    _ = clipScaleStepConstant d alpha * K * r ^ alpha := by
        rw [clipScaleStepConstant]
        ring

/-! ## 3. The clipped telescope -/

/-- The mean of `f` over the clipped window of radius `R 3 ^ (-k)` at `x`. -/
def clipCampanatoAverage (c : Vec d) (Rm : ℝ) (f : Vec d → ℝ) (R : ℝ) (x : Vec d)
    (k : ℕ) : ℝ :=
  volumeAverage (clipBall c Rm x (triadicRadius R k)) f

/-- Consecutive means of the clipped telescope differ geometrically. -/
theorem dist_clipCampanatoAverage_succ_le
    {c : Vec d} {Rm : ℝ} {S : Set (Vec d)} {R Rtop alpha K : ℝ} {f : Vec d → ℝ}
    (hR : 0 < R) (hRRtop : R ≤ Rtop) (hRtopRm : Rtop ≤ Rm)
    (hS : S ⊆ Metric.ball c Rm)
    (hf : MemLp f 2 (volume.restrict (Metric.ball c Rm)))
    (hcamp : HasClipCampanatoDecayOn c Rm S Rtop alpha K f)
    {x : Vec d} (hx : x ∈ S) (k : ℕ) :
    dist (clipCampanatoAverage c Rm f R x k) (clipCampanatoAverage c Rm f R x (k + 1)) ≤
      (ballVolumePrice 6 d * K * R ^ alpha) * campanatoRatio alpha ^ k := by
  have hrk : 0 < triadicRadius R k := triadicRadius_pos hR k
  have hrkRm : triadicRadius R k ≤ Rm :=
    ((triadicRadius_le hR.le k).trans hRRtop).trans hRtopRm
  have hinner : 0 < triadicRadius R (k + 1) := triadicRadius_pos hR (k + 1)
  have hsucc : triadicRadius R (k + 1) = triadicRadius R k / 3 := triadicRadius_succ R k
  have hinnerRm : triadicRadius R (k + 1) ≤ Rm := by
    rw [hsucc]
    linarith only [hrk, hrkRm]
  have hsub : clipBall c Rm x (triadicRadius R (k + 1)) ⊆
      clipBall c Rm x (triadicRadius R k) :=
    Set.inter_subset_inter_left _ (Metric.ball_subset_ball (by rw [hsucc]; linarith only [hrk]))
  have hkappa : 2 * triadicRadius R k ≤ 6 * triadicRadius R (k + 1) := by
    rw [hsucc]
    linarith only [hrk]
  have hmean := abs_volumeAverage_clipBall_sub_le (kappa := 6) hinner hinnerRm (hS hx)
    hrk hrkRm (hS hx) hsub hkappa hf
  have hosc := hcamp x hx (triadicRadius R k) hrk ((triadicRadius_le hR.le k).trans hRRtop)
  have hstep := hmean.trans (mul_le_mul_of_nonneg_left hosc (ballVolumePrice_nonneg 6 d))
  rw [Real.dist_eq, clipCampanatoAverage, clipCampanatoAverage, abs_sub_comm]
  refine hstep.trans_eq ?_
  rw [triadicRadius_rpow hR.le k]
  ring

theorem cauchySeq_clipCampanatoAverage
    {c : Vec d} {Rm : ℝ} {S : Set (Vec d)} {R Rtop alpha K : ℝ} {f : Vec d → ℝ}
    (hR : 0 < R) (hRRtop : R ≤ Rtop) (hRtopRm : Rtop ≤ Rm) (halpha : 0 < alpha)
    (hS : S ⊆ Metric.ball c Rm)
    (hf : MemLp f 2 (volume.restrict (Metric.ball c Rm)))
    (hcamp : HasClipCampanatoDecayOn c Rm S Rtop alpha K f)
    {x : Vec d} (hx : x ∈ S) :
    CauchySeq (clipCampanatoAverage c Rm f R x) :=
  cauchySeq_of_le_geometric (campanatoRatio alpha)
    (ballVolumePrice 6 d * K * R ^ alpha) (campanatoRatio_lt_one halpha)
    (dist_clipCampanatoAverage_succ_le hR hRRtop hRtopRm hS hf hcamp hx)

/-- **The clipped telescope has the same limit as the unclipped one.**  At a
centre of the open cube the clipping is eventually inactive, so the two
sequences of means agree from some index on. -/
theorem tendsto_clipCampanatoAverage
    {c : Vec d} {Rm : ℝ} {S : Set (Vec d)} {R Rtop alpha K : ℝ} {f : Vec d → ℝ}
    (hR : 0 < R) (hRRtop : R ≤ Rtop) (hRtopRm : Rtop ≤ Rm) (halpha : 0 < alpha)
    (hS : S ⊆ Metric.ball c Rm)
    (hf : MemLp f 2 (volume.restrict (Metric.ball c Rm)))
    (hcamp : HasClipCampanatoDecayOn c Rm S Rtop alpha K f)
    {x : Vec d} (hx : x ∈ S) :
    Tendsto (clipCampanatoAverage c Rm f R x) atTop
      (nhds (campanatoRepresentative f R x)) := by
  have heq : campanatoAverage f R x =ᶠ[atTop] clipCampanatoAverage c Rm f R x := by
    filter_upwards [eventually_clipBall_eq_ball (c := c) (Rm := Rm) R (hS hx)] with k hk
    rw [campanatoAverage, clipCampanatoAverage, hk]
  have hclip := (cauchySeq_clipCampanatoAverage hR hRRtop hRtopRm halpha hS hf hcamp
    hx).tendsto_limUnder
  have hball : Tendsto (campanatoAverage f R x) atTop
      (nhds (limUnder atTop (clipCampanatoAverage c Rm f R x))) := hclip.congr' heq.symm
  have hlim : campanatoRepresentative f R x =
      limUnder atTop (clipCampanatoAverage c Rm f R x) := hball.limUnder_eq
  rw [hlim]
  exact hclip

/-- **The uniform tail of the clipped telescope.** -/
theorem dist_clipCampanatoAverage_representative_le
    {c : Vec d} {Rm : ℝ} {S : Set (Vec d)} {R Rtop alpha K : ℝ} {f : Vec d → ℝ}
    (hR : 0 < R) (hRRtop : R ≤ Rtop) (hRtopRm : Rtop ≤ Rm) (halpha : 0 < alpha)
    (hS : S ⊆ Metric.ball c Rm)
    (hf : MemLp f 2 (volume.restrict (Metric.ball c Rm)))
    (hcamp : HasClipCampanatoDecayOn c Rm S Rtop alpha K f)
    {x : Vec d} (hx : x ∈ S) (k : ℕ) :
    dist (clipCampanatoAverage c Rm f R x k) (campanatoRepresentative f R x) ≤
      campanatoTailConstant alpha * ballVolumePrice 6 d * K *
        triadicRadius R k ^ alpha := by
  have hraw := dist_le_of_le_geometric_of_tendsto (campanatoRatio alpha)
    (ballVolumePrice 6 d * K * R ^ alpha) (campanatoRatio_lt_one halpha)
    (dist_clipCampanatoAverage_succ_le hR hRRtop hRtopRm hS hf hcamp hx)
    (tendsto_clipCampanatoAverage hR hRRtop hRtopRm halpha hS hf hcamp hx) k
  refine hraw.trans_eq ?_
  rw [triadicRadius_rpow hR.le k, campanatoTailConstant, div_eq_mul_inv]
  ring

/-! ## 4. The limit is a representative -/

/-- **Lebesgue differentiation identifies the limit with `f`.** -/
theorem campanatoRepresentative_ae_eq_of_clip [NeZero d]
    {c : Vec d} {Rm : ℝ} {S : Set (Vec d)} {R Rtop alpha K : ℝ} {f : Vec d → ℝ}
    (hR : 0 < R) (hRRtop : R ≤ Rtop) (hRtopRm : Rtop ≤ Rm) (halpha : 0 < alpha)
    (hS : S ⊆ Metric.ball c Rm)
    (hf : MemLp f 2 (volume.restrict (Metric.ball c Rm)))
    (hcamp : HasClipCampanatoDecayOn c Rm S Rtop alpha K f)
    (hint : LocallyIntegrable f volume) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), x ∈ S → campanatoRepresentative f R x = f x := by
  filter_upwards [(Besicovitch.vitaliFamily (volume : Measure (Vec d))).ae_tendsto_average
    hint] with x hxDiff hxS
  have hclosed := hxDiff.comp (Besicovitch.tendsto_filterAt (volume : Measure (Vec d)) x)
  have havg : ∀ k : ℕ, campanatoAverage f R x k =
      ⨍ y in Metric.closedBall x (triadicRadius R k), f y ∂volume := by
    intro k
    rw [campanatoAverage,
      volumeAverage_metricBall_eq_setAverage_closedBall x (triadicRadius_pos hR k)]
  have hLeb : Tendsto (campanatoAverage f R x) atTop (nhds (f x)) :=
    (hclosed.comp (tendsto_triadicRadius_zero hR)).congr'
      (Eventually.of_forall fun k => (havg k).symm)
  have heq : campanatoAverage f R x =ᶠ[atTop] clipCampanatoAverage c Rm f R x := by
    filter_upwards [eventually_clipBall_eq_ball (c := c) (Rm := Rm) R (hS hxS)] with k hk
    rw [campanatoAverage, clipCampanatoAverage, hk]
  have hrep : Tendsto (campanatoAverage f R x) atTop
      (nhds (campanatoRepresentative f R x)) :=
    (tendsto_clipCampanatoAverage hR hRRtop hRtopRm halpha hS hf hcamp hxS).congr' heq.symm
  exact tendsto_nhds_unique hrep hLeb

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Campanato

/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.HeatCommutatorSliceIBP
public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.ForwardHeatRepresentation
public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.HeatOperatorLeibniz
public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.HeatCutoffExtension

/-!
# The cut-off heat-representation identity

`HB2_cutoff_decomposition` assembles the forward heat representation, the Leibniz rule for the
heat operator on a product, the compactly supported cutoff extension, and the three slice
integrations by parts of the cutoff-commutator kernel into a single identity: given `w = div U`
and `(∂ₜ − Δ) w = div Y` on an open set containing the backward parabolic window at `(x, s)`,
`w (x, s)` is recovered from the cut-off heat weight paired against `Y` and the cutoff-commutator
kernel paired against `U`. This is the pointwise heat bound of the interior estimates in the
proof of `lem:aniso:annulus`, one step short of the final norm bound.

The hypothesis `ρ ≤ 1` is required
because the two slice integrations by parts this file cites, `integral_serrinHeatWeight_mul_
spatialPartial` and `integral_divergence_mul_serrinCutoffKernel` (both in `HeatSliceIBP.lean`),
already carry it. The downstream heat bound that uses this lemma already assumes `ρ ≤ 1`, so
the extra hypothesis costs nothing.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN CKN.Foundation.Heat CKN.Core.Step3

noncomputable section
namespace CIV



private theorem fderiv_sq_serrinBallCutoff_eq_zero_of_lt (x : Vec3) {ρ : ℝ} (hρ : 0 < ρ)
    (i l : Fin 3) {y : Vec3} (hy : ρ < vec3EuclideanNorm (y - x)) :
    fderiv ℝ (fun y' => fderiv ℝ (serrinBallCutoff x ρ) y' (basisVec i)) y (basisVec l) = 0 := by
  have houter : IsOpen {y' : Vec3 | ρ < vec3EuclideanNorm (y' - x)} := by
    have hc : Continuous (fun y' : Vec3 => vec3EuclideanNorm (y' - x)) := by
      unfold vec3EuclideanNorm; fun_prop
    exact isOpen_lt continuous_const hc
  have hd1 : ∀ y' ∈ {y' : Vec3 | ρ < vec3EuclideanNorm (y' - x)},
      fderiv ℝ (serrinBallCutoff x ρ) y' (basisVec i) = 0 :=
    fun y' hy' => fderiv_serrinBallCutoff_eq_zero_of_lt x hρ i hy'
  exact fderiv_apply_eq_zero_of_eqOn_const houter hd1 (basisVec l) y hy

private theorem deriv_serrinTimeCut_eq_zero_of_lt {s ρ : ℝ} (hρ : 0 < ρ) {r : ℝ}
    (hr : r < s - ρ ^ 2) : deriv (serrinTimeCut s ρ) r = 0 := by
  have hev : serrinTimeCut s ρ =ᶠ[nhds r] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hr] with r' hr'
    unfold serrinTimeCut
    exact (serrinTimeBump_support (s := s) hρ r').2.1 hr'.le
  rw [hev.deriv_eq]; simp

private theorem serrinCutoff_timePartial_eq_zero_off_window (x : Vec3) {s ρ : ℝ} (hρ : 0 < ρ)
    {z : ParabolicPoint} (hz : z.2 < s)
    (hout : z ∉ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s) :
    timePartial (serrinCutoff x s ρ) z = 0 := by
  have e := congrFun (serrinCutoff_partials x (s := s) hρ (0 : Fin 3)).1 z
  rw [e]
  by_cases hball : vec3EuclideanNorm (z.1 - x) ≤ ρ
  · have htime : z.2 < s - ρ ^ 2 := by
      by_contra htime'; exact hout ⟨hball, le_of_not_gt htime', hz.le⟩
    rw [deriv_serrinTimeCut_eq_zero_of_lt hρ htime, mul_zero]
  · rw [(serrinBallCutoff_support x hρ z.1).2.1 (not_le.mp hball).le, zero_mul]

private theorem serrinCutoff_spatialPartial_eq_zero_off_window (x : Vec3) {s ρ : ℝ} (hρ : 0 < ρ)
    {z : ParabolicPoint} (hz : z.2 < s)
    (hout : z ∉ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s) (i : Fin 3) :
    spatialPartial (serrinCutoff x s ρ) i z = 0 := by
  have e := congrFun (serrinCutoff_partials x (s := s) hρ i).2.1 z
  rw [e]
  by_cases hball : vec3EuclideanNorm (z.1 - x) ≤ ρ
  · have htime : z.2 < s - ρ ^ 2 := by
      by_contra htime'; exact hout ⟨hball, le_of_not_gt htime', hz.le⟩
    have hT0 : serrinTimeCut s ρ z.2 = 0 := by
      unfold serrinTimeCut
      exact (serrinTimeBump_support (s := s) hρ z.2).2.1 htime.le
    rw [hT0, mul_zero]
  · rw [fderiv_serrinBallCutoff_eq_zero_of_lt x hρ i (not_le.mp hball), zero_mul]

private theorem serrinCutoff_spatialSecondPartial_eq_zero_off_window (x : Vec3) {s ρ : ℝ}
    (hρ : 0 < ρ) {z : ParabolicPoint} (hz : z.2 < s)
    (hout : z ∉ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s) (i : Fin 3) :
    spatialSecondPartial (serrinCutoff x s ρ) i i z = 0 := by
  have e := congrFun (serrinCutoff_partials x (s := s) hρ i).2.2 z
  rw [e]
  by_cases hball : vec3EuclideanNorm (z.1 - x) ≤ ρ
  · have htime : z.2 < s - ρ ^ 2 := by
      by_contra htime'; exact hout ⟨hball, le_of_not_gt htime', hz.le⟩
    have hT0 : serrinTimeCut s ρ z.2 = 0 := by
      unfold serrinTimeCut
      exact (serrinTimeBump_support (s := s) hρ z.2).2.1 htime.le
    rw [hT0, mul_zero]
  · rw [fderiv_sq_serrinBallCutoff_eq_zero_of_lt x hρ i i (not_le.mp hball), zero_mul]


private theorem serrinCutoff_eq_zero_off_window' (x : Vec3) {s ρ : ℝ} (hρ : 0 < ρ)
    {z : ParabolicPoint} (hz : z.2 < s)
    (hout : z ∉ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s) :
    serrinCutoff x s ρ z = 0 := by
  show serrinBallCutoff x ρ z.1 * serrinTimeCut s ρ z.2 = 0
  by_cases hball : vec3EuclideanNorm (z.1 - x) ≤ ρ
  · have htime : z.2 < s - ρ ^ 2 := by
      by_contra htime'; exact hout ⟨hball, le_of_not_gt htime', hz.le⟩
    have hT0 : serrinTimeCut s ρ z.2 = 0 := by
      unfold serrinTimeCut
      exact (serrinTimeBump_support (s := s) hρ z.2).2.1 htime.le
    rw [hT0, mul_zero]
  · rw [(serrinBallCutoff_support x hρ z.1).2.1 (not_le.mp hball).le, zero_mul]

private theorem timePartial_congr_of_eventuallyEq {F G : Vec3 × ℝ → ℝ} {z : Vec3 × ℝ}
    (hF : ∀ᶠ w : Vec3 × ℝ in nhds z, F w = G w) : timePartial F z = timePartial G z := by
  unfold timePartial
  have hcont : Continuous (fun t : ℝ => ((z.1, t) : Vec3 × ℝ)) := by fun_prop
  have h1 : (fun t : ℝ => F (z.1, t)) =ᶠ[nhds z.2] fun t : ℝ => G (z.1, t) := by
    have := hcont.continuousAt (x := z.2) |>.tendsto
    exact this.eventually (by simpa using hF)
  rw [h1.fderiv_eq]

private theorem spatialPartial_congr_of_eventuallyEq {F G : Vec3 × ℝ → ℝ} {z : Vec3 × ℝ}
    (hF : ∀ᶠ w in nhds z, F w = G w) (j : Fin 3) :
    spatialPartial F j z = spatialPartial G j z := by
  unfold spatialPartial
  have hcont : Continuous (fun x : Vec3 => ((x, z.2) : Vec3 × ℝ)) := by fun_prop
  have h1 : (fun x : Vec3 => F (x, z.2)) =ᶠ[nhds z.1] fun x : Vec3 => G (x, z.2) := by
    have := hcont.continuousAt (x := z.1) |>.tendsto
    exact this.eventually (by simpa using hF)
  rw [h1.fderiv_eq]


private theorem integrableOn_serrinHeatWeight_mul_spatialPartial {Y : ParabolicPoint → ℝ}
    {O : Set ParabolicPoint} {x : Vec3} {s ρ : ℝ} (hO : IsOpen (X := Vec3 × ℝ) O) (hρ : 0 < ρ)
    (hwin : {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s ⊆ O)
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => Y z) O) (j : Fin 3) :
    IntegrableOn (fun z => serrinHeatWeight x s ρ z * spatialPartial Y j z)
      {z : ParabolicPoint | z.2 < s} := by
  set W : Set (Vec3 × ℝ) := {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s
    with hWdef
  set U : Set (Vec3 × ℝ) := {z | z.2 < s} with hUdef
  have hUm : MeasurableSet U := measurableSet_lt measurable_snd measurable_const
  have hWc : IsCompact W := isCompact_serrinWindow x hρ
  have hWm : MeasurableSet W := hWc.isClosed.measurableSet
  have hYc : ContinuousOn (fun z : Vec3 × ℝ => Y z) O := hY.continuousOn
  have hdYc := continuousOn_spatialPartial_of_isOpen hO hY j
  obtain ⟨CdY, hCdY⟩ := hWc.exists_bound_of_continuousOn (hdYc.mono hwin)
  have hCdY0 : 0 ≤ CdY := (norm_nonneg _).trans (hCdY ((x, s) : Vec3 × ℝ) ⟨by
    show vec3EuclideanNorm (x - x) ≤ ρ; rw [sub_self, vec3EuclideanNorm_zero]; exact hρ.le,
    by have := sq_nonneg ρ; linarith only [this], le_rfl⟩)
  have hΨc : ContinuousOn (fun z : Vec3 × ℝ => serrinHeatWeight x s ρ z) U :=
    (contDiffOn_serrinHeatWeight x (s := s) hρ).continuousOn
  have hΨzero : ∀ z ∈ U, z ∉ W → serrinHeatWeight x s ρ z = 0 := by
    intro z hz hzW
    have hev := serrinCutoff_eventually_eq_zero x hρ hzW hz
    show heatKernel (x - z.1) (s - z.2) * serrinCutoff x s ρ z = 0
    rw [hev.self_of_nhds, mul_zero]
  refine integrableOn_of_window (g := fun z => CdY * (univ ×ˢ Ioc 0 (ρ ^ 2)).indicator
      (fun q : Vec3 × ℝ => heatKernelPlus q) ((x, s) - z)) hWm hUm
    ((hΨc.mono inter_subset_right).mul (hdYc.mono (inter_subset_left.trans hwin)))
    (fun z hz hzW => by rw [hΨzero z hz hzW, zero_mul])
    ((integrable_heatKernel_translate_strip x s ρ).const_mul CdY).integrableOn
    (fun z _ => mul_nonneg hCdY0 (indicator_nonneg (fun q _ => heatKernelPlus_nonneg q) _)) ?_
  intro z hz hzW
  have hmem : ((x, s) - z) ∈ (univ ×ˢ Ioc 0 (ρ ^ 2) : Set (Vec3 × ℝ)) :=
    ⟨mem_univ _, show 0 < s - z.2 by linarith only [show z.2 < s from hz],
      show s - z.2 ≤ ρ ^ 2 by linarith only [hzW.2.1]⟩
  rw [indicator_of_mem hmem, abs_mul]
  have hΨb : |serrinHeatWeight x s ρ z| ≤ heatKernelPlus ((x, s) - z) := by
    have hP : heatKernel (x - z.1) (s - z.2) = heatKernelPlus ((x, s) - z) :=
      (heatKernelPlus_eq_heatKernel (((x, s) - z : Vec3 × ℝ) : ParabolicPoint)).symm
    calc |serrinHeatWeight x s ρ z|
        = heatKernel (x - z.1) (s - z.2) * |serrinCutoff x s ρ z| := by
          show |heatKernel (x - z.1) (s - z.2) * serrinCutoff x s ρ z| = _
          rw [abs_mul, abs_of_nonneg (heatKernel_nonneg _ _)]
      _ ≤ heatKernel (x - z.1) (s - z.2) :=
          mul_le_of_le_one_right (heatKernel_nonneg _ _) (abs_serrinCutoff_le_one x s ρ z)
      _ = heatKernelPlus ((x, s) - z) := hP
  have hdY := hCdY z hzW
  rw [Real.norm_eq_abs] at hdY
  calc |serrinHeatWeight x s ρ z| * |spatialPartial Y j z|
      ≤ heatKernelPlus ((x, s) - z) * CdY :=
        mul_le_mul hΨb hdY (abs_nonneg _) (heatKernelPlus_nonneg _)
    _ = CdY * heatKernelPlus ((x, s) - z) := mul_comm _ _


theorem HB2_cutoff_decomposition {w : ParabolicPoint → ℝ} {U Y : Fin 3 → ParabolicPoint → ℝ}
    {O : Set ParabolicPoint} {x : Vec3} {s ρ : ℝ} (hO : IsOpen (X := Vec3 × ℝ) O)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hwin : {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s ⊆ O)
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => w z) O)
    (hU : ∀ l, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => U l z) O)
    (hY : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => Y j z) O)
    (hwU : ∀ z ∈ O, w z = ∑ l, spatialPartial (U l) l z)
    (heq : ∀ z ∈ O, timePartial w z - ∑ j, spatialSecondPartial w j j z =
      ∑ j, spatialPartial (Y j) j z) :
    w (x, s) =
      -(∑ j, ∫ z in {z : ParabolicPoint | z.2 < s},
          spatialPartial (serrinHeatWeight x s ρ) j z * Y j z) -
        ∑ l, ∫ z in {z : ParabolicPoint | z.2 < s},
          U l z * spatialPartial (serrinCutoffKernel x s ρ) l z := by
  obtain ⟨ζ, hζsmooth, hζcs, hζeq⟩ := HB2b_cutoff_extension hO hρ hwin hw
  have hopenLt : IsOpen (X := Vec3 × ℝ) {z' : Vec3 × ℝ | z'.2 < s} :=
    isOpen_lt continuous_snd continuous_const
  have hcenter1 : serrinCutoff x s ρ (x, s) = 1 := by
    show serrinBallCutoff x ρ x * serrinTimeCut s ρ s = 1
    have hb : serrinBallCutoff x ρ x = 1 := by
      apply (serrinBallCutoff_support x hρ x).1
      show vec3EuclideanNorm (x - x) ≤ ρ / 2
      rw [sub_self, vec3EuclideanNorm_zero]; linarith only [hρ]
    have ht : serrinTimeCut s ρ s = 1 := by
      unfold serrinTimeCut
      apply (serrinTimeBump_support (s := s) hρ s).1
      have := sq_nonneg ρ; linarith only [this]
    rw [hb, ht, one_mul]
  have hwxs : w (x, s) = ζ (x, s) := by
    have h1 := hζeq (x, s) le_rfl
    show w (x, s) = ζ (x, s)
    rw [h1, hcenter1, one_mul]
  have hb1 := HB1_forward_representation hζsmooth hζcs x s
  have hFeq : (fun z : ParabolicPoint => heatKernel (x - z.1) (s - z.2) *
      (timePartial ζ z - ∑ i, spatialSecondPartial ζ i i z)) =
      {z : ParabolicPoint | z.2 < s}.indicator
        (fun z => heatKernel (x - z.1) (s - z.2) *
          (timePartial ζ z - ∑ i, spatialSecondPartial ζ i i z)) := by
    funext z
    by_cases hz : z ∈ {z : ParabolicPoint | z.2 < s}
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz]
      have hz' : s - z.2 ≤ 0 := by
        simp only [Set.mem_ofPred_eq, not_lt] at hz
        linarith only [hz]
      rw [heatKernel_eq_zero_of_nonpos hz', zero_mul]
  have hb1' : ζ (x, s) = ∫ z in {z : ParabolicPoint | z.2 < s}, heatKernel (x - z.1) (s - z.2) *
      (timePartial ζ z - ∑ i, spatialSecondPartial ζ i i z) := by
    rw [hb1]
    rw [congrArg (MeasureTheory.integral (volume : Measure ParabolicPoint)) hFeq]
    exact integral_indicator (measurableSet_lt measurable_snd measurable_const)
  have hζ0 : ∀ z' : ParabolicPoint, z'.2 < s →
      z' ∉ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s → ζ z' = 0 := by
    intro z' hz' hout
    rw [hζeq z' hz'.le, serrinCutoff_eq_zero_off_window' x hρ hz' hout, zero_mul]
  have hVopen : IsOpen (X := Vec3 × ℝ)
      ({z' : Vec3 × ℝ | z'.2 < s} \
        {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s) :=
    hopenLt.sdiff (isCompact_serrinWindow x hρ).isClosed
  have hζderiv0 : ∀ z' : ParabolicPoint, z'.2 < s →
      z' ∉ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s →
      timePartial ζ z' = 0 ∧ ∀ i, spatialSecondPartial ζ i i z' = 0 := by
    intro z hz hzout
    have hmemV : z ∈ ({z' : Vec3 × ℝ | z'.2 < s} \
        {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s) := ⟨hz, hzout⟩
    have hζev : ∀ᶠ w' : Vec3 × ℝ in nhds z, ζ w' = 0 :=
      Filter.eventually_of_mem (hVopen.mem_nhds hmemV) (fun w' hw' => hζ0 w' hw'.1 hw'.2)
    refine ⟨timePartial_eq_zero_of_eventually_eq_zero hζev, fun i => ?_⟩
    have hdζ0 : ∀ w' ∈ ({z' : Vec3 × ℝ | z'.2 < s} \
        {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s),
        spatialPartial ζ i w' = 0 := fun w' hw' =>
      spatialPartial_eq_zero_of_eventually_eq_zero
        (Filter.eventually_of_mem (hVopen.mem_nhds hw') (fun w'' hw'' => hζ0 w'' hw''.1 hw''.2)) i
    have hdζev : ∀ᶠ w' : Vec3 × ℝ in nhds z, spatialPartial ζ i w' = 0 :=
      Filter.eventually_of_mem (hVopen.mem_nhds hmemV) hdζ0
    exact spatialPartial_eq_zero_of_eventually_eq_zero hdζev i
  have hpointwise : ∀ z : ParabolicPoint, z.2 < s →
      heatKernel (x - z.1) (s - z.2) * (timePartial ζ z - ∑ i, spatialSecondPartial ζ i i z) =
      serrinHeatWeight x s ρ z * (∑ j, spatialPartial (Y j) j z) +
      heatKernel (x - z.1) (s - z.2) * (w z * (timePartial (serrinCutoff x s ρ) z -
          ∑ i, spatialSecondPartial (serrinCutoff x s ρ) i i z) -
        2 * ∑ i, spatialPartial (serrinCutoff x s ρ) i z * spatialPartial w i z) := by
    intro z hz
    by_cases hzw : z ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s
    · have hzO : z ∈ O := hwin hzw
      have hζeqOpen : ∀ᶠ w' : Vec3 × ℝ in nhds z, ζ w' = serrinCutoff x s ρ w' * w w' := by
        filter_upwards [hopenLt.mem_nhds hz] with w' hw'
        exact hζeq w' hw'.le
      have hT : timePartial ζ z = timePartial (fun v => serrinCutoff x s ρ v * w v) z :=
        timePartial_congr_of_eventuallyEq hζeqOpen
      have hS : ∀ i, spatialSecondPartial ζ i i z =
          spatialSecondPartial (fun v => serrinCutoff x s ρ v * w v) i i z := by
        intro i
        have hSP : ∀ᶠ w' : Vec3 × ℝ in nhds z,
            spatialPartial ζ i w' = spatialPartial (fun v => serrinCutoff x s ρ v * w v) i w' := by
          filter_upwards [hopenLt.mem_nhds hz] with w' hw'
          have hζeqOpen' : ∀ᶠ w'' : Vec3 × ℝ in nhds w', ζ w'' = serrinCutoff x s ρ w'' * w w''
            := by
            filter_upwards [hopenLt.mem_nhds hw'] with w'' hw''
            exact hζeq w'' hw''.le
          exact spatialPartial_congr_of_eventuallyEq hζeqOpen' i
        exact spatialPartial_congr_of_eventuallyEq hSP i
      have hHB2a := HB2a_heat_operator_mul (χ := serrinCutoff x s ρ) hO
          (contDiff_serrinCutoff x (s := s) hρ).contDiffOn hw z hzO
      have hheq := heq z hzO
      have hSsum : (∑ i, spatialSecondPartial ζ i i z) =
          ∑ i, spatialSecondPartial (fun v => serrinCutoff x s ρ v * w v) i i z :=
        Finset.sum_congr rfl (fun i _ => hS i)
      rw [hT, hSsum, hHB2a, hheq]
      unfold serrinHeatWeight
      ring
    · have h1 := hζderiv0 z hz hzw
      have h2 : serrinCutoff x s ρ z = 0 := serrinCutoff_eq_zero_off_window' x hρ hz hzw
      have h3 : timePartial (serrinCutoff x s ρ) z = 0 :=
        serrinCutoff_timePartial_eq_zero_off_window x hρ hz hzw
      have h4 : ∀ i, spatialSecondPartial (serrinCutoff x s ρ) i i z = 0 :=
        fun i => serrinCutoff_spatialSecondPartial_eq_zero_off_window x hρ hz hzw i
      have h5 : ∀ i, spatialPartial (serrinCutoff x s ρ) i z = 0 :=
        fun i => serrinCutoff_spatialPartial_eq_zero_off_window x hρ hz hzw i
      have hΨ0 : serrinHeatWeight x s ρ z = 0 := by
        show heatKernel (x - z.1) (s - z.2) * serrinCutoff x s ρ z = 0
        rw [h2, mul_zero]
      have hSsum0 : (∑ i, spatialSecondPartial ζ i i z) = 0 :=
        Finset.sum_eq_zero (fun i _ => h1.2 i)
      have hSsum0' : (∑ i, spatialSecondPartial (serrinCutoff x s ρ) i i z) = 0 :=
        Finset.sum_eq_zero (fun i _ => h4 i)
      have hDsum0 : (∑ i, spatialPartial (serrinCutoff x s ρ) i z * spatialPartial w i z) = 0 :=
        Finset.sum_eq_zero (fun i _ => by rw [h5 i, zero_mul])
      rw [h1.1, hSsum0, hΨ0, h3, hSsum0', hDsum0]
      ring
  have hUmSet : MeasurableSet {z : ParabolicPoint | z.2 < s} :=
    measurableSet_lt measurable_snd measurable_const
  have hbig : ∫ z in {z : ParabolicPoint | z.2 < s}, heatKernel (x - z.1) (s - z.2) *
        (timePartial ζ z - ∑ i, spatialSecondPartial ζ i i z) =
      ∫ z in {z : ParabolicPoint | z.2 < s},
        (serrinHeatWeight x s ρ z * (∑ j, spatialPartial (Y j) j z) +
          heatKernel (x - z.1) (s - z.2) * (w z * (timePartial (serrinCutoff x s ρ) z -
              ∑ i, spatialSecondPartial (serrinCutoff x s ρ) i i z) -
            2 * ∑ i, spatialPartial (serrinCutoff x s ρ) i z * spatialPartial w i z)) :=
    setIntegral_congr_fun hUmSet (fun z hz => hpointwise z hz)
  have htimeCD : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => timePartial ζ z) :=
    timePartial_contDiff_full hζsmooth
  have hspCD : ∀ i : Fin 3,
      ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => spatialSecondPartial ζ i i z) :=
    fun i => spatialPartial_contDiff (spatialPartial_contDiff hζsmooth i) i
  have hsumCD : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => ∑ i, spatialSecondPartial ζ i i z) := by
    have heqsum : (fun z : Vec3 × ℝ => ∑ i, spatialSecondPartial ζ i i z) =
        (fun z => spatialSecondPartial ζ 0 0 z + spatialSecondPartial ζ 1 1 z +
          spatialSecondPartial ζ 2 2 z) := by
      funext z; rw [Fin.sum_univ_three]
    rw [heqsum]
    exact ((hspCD 0).add (hspCD 1)).add (hspCD 2)
  have hφCD : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ =>
      timePartial ζ z - ∑ i, spatialSecondPartial ζ i i z) := htimeCD.sub hsumCD
  have htimeCS : HasCompactSupport (fun z : Vec3 × ℝ => timePartial ζ z) := by
    rw [show (fun z : Vec3 × ℝ => timePartial ζ z) =
        (fun z : Vec3 × ℝ => (fderiv ℝ (fun w' : Vec3 × ℝ => ζ w') z) ((0, 1) : Vec3 × ℝ)) from
      funext (fun z => CKN.Foundation.Heat.timePartial_eq_fderiv_apply hζsmooth z.1 z.2)]
    exact hζcs.fderiv_apply (𝕜 := ℝ) ((0, 1) : Vec3 × ℝ)
  have hsecondCS : ∀ i : Fin 3,
      HasCompactSupport (fun z : Vec3 × ℝ => spatialSecondPartial ζ i i z) := by
    intro i
    have hηCS : HasCompactSupport (fun z : Vec3 × ℝ => spatialPartial ζ i z) := by
      rw [show (fun z : Vec3 × ℝ => spatialPartial ζ i z) =
          (fun z : Vec3 × ℝ =>
            (fderiv ℝ (fun w' : Vec3 × ℝ => ζ w') z) ((basisVec i, 0) : Vec3 × ℝ)) from
        funext (fun z => CKN.Foundation.Heat.spatialPartial_eq_fderiv_apply hζsmooth i z.1 z.2)]
      exact hζcs.fderiv_apply (𝕜 := ℝ) ((basisVec i, 0) : Vec3 × ℝ)
    rw [show (fun z : Vec3 × ℝ => spatialSecondPartial ζ i i z) =
        (fun z : Vec3 × ℝ =>
          (fderiv ℝ (fun w' : Vec3 × ℝ => spatialPartial ζ i w') z)
            ((basisVec i, 0) : Vec3 × ℝ)) from
      funext (fun z => CKN.Foundation.Heat.spatialPartial_eq_fderiv_apply
        (spatialPartial_contDiff hζsmooth i) i
        z.1 z.2)]
    exact hηCS.fderiv_apply (𝕜 := ℝ) ((basisVec i, 0) : Vec3 × ℝ)
  have hsumCS : HasCompactSupport (fun z : Vec3 × ℝ => ∑ i, spatialSecondPartial ζ i i z) := by
    have heqsum : (fun z : Vec3 × ℝ => ∑ i, spatialSecondPartial ζ i i z) =
        (fun z => spatialSecondPartial ζ 0 0 z + spatialSecondPartial ζ 1 1 z +
          spatialSecondPartial ζ 2 2 z) := by
      funext z; rw [Fin.sum_univ_three]
    rw [heqsum]
    exact ((hsecondCS 0).add (hsecondCS 1)).add (hsecondCS 2)
  have hφCS : HasCompactSupport (fun z : Vec3 × ℝ =>
      timePartial ζ z - ∑ i, spatialSecondPartial ζ i i z) := htimeCS.sub hsumCS
  have hΦintFull := integrable_reflectTime_potential hφCD hφCS x (-s)
  have hΦint : IntegrableOn (fun z : ParabolicPoint => heatKernel (x - z.1) (s - z.2) *
      (timePartial ζ z - ∑ i, spatialSecondPartial ζ i i z)) {z : ParabolicPoint | z.2 < s} := by
    have heq' : (fun z : Vec3 × ℝ => heatKernel (x - z.1) (-(-s) - z.2) *
        (timePartial ζ z - ∑ i, spatialSecondPartial ζ i i z)) =
        (fun z : ParabolicPoint => heatKernel (x - z.1) (s - z.2) *
          (timePartial ζ z - ∑ i, spatialSecondPartial ζ i i z)) := by
      funext z; rw [neg_neg]
    rw [heq'] at hΦintFull
    exact hΦintFull.integrableOn
  have hF1int : ∀ j : Fin 3,
      IntegrableOn (fun z => serrinHeatWeight x s ρ z * spatialPartial (Y j) j z)
        {z : ParabolicPoint | z.2 < s} :=
    fun j => integrableOn_serrinHeatWeight_mul_spatialPartial hO hρ hwin (hY j) j
  have hF1sumint : IntegrableOn (fun z => ∑ j, serrinHeatWeight x s ρ z * spatialPartial (Y j) j z)
      {z : ParabolicPoint | z.2 < s} :=
    integrable_finsetSum Finset.univ (fun j _ => hF1int j)
  have hF1eq : (fun z : ParabolicPoint => serrinHeatWeight x s ρ z *
      (∑ j, spatialPartial (Y j) j z)) =
      (fun z => ∑ j, serrinHeatWeight x s ρ z * spatialPartial (Y j) j z) := by
    funext z; rw [Finset.mul_sum]
  have hF1int' : IntegrableOn (fun z : ParabolicPoint => serrinHeatWeight x s ρ z *
      (∑ j, spatialPartial (Y j) j z)) {z : ParabolicPoint | z.2 < s} := by
    rw [hF1eq]; exact hF1sumint
  have hF12int : IntegrableOn (fun z : ParabolicPoint =>
      serrinHeatWeight x s ρ z * (∑ j, spatialPartial (Y j) j z) +
      heatKernel (x - z.1) (s - z.2) * (w z * (timePartial (serrinCutoff x s ρ) z -
          ∑ i, spatialSecondPartial (serrinCutoff x s ρ) i i z) -
        2 * ∑ i, spatialPartial (serrinCutoff x s ρ) i z * spatialPartial w i z))
      {z : ParabolicPoint | z.2 < s} :=
    hΦint.congr_fun hpointwise hUmSet
  have hF2int : IntegrableOn (fun z : ParabolicPoint => heatKernel (x - z.1) (s - z.2) *
      (w z * (timePartial (serrinCutoff x s ρ) z -
          ∑ i, spatialSecondPartial (serrinCutoff x s ρ) i i z) -
        2 * ∑ i, spatialPartial (serrinCutoff x s ρ) i z * spatialPartial w i z))
      {z : ParabolicPoint | z.2 < s} := by
    have hsub := hF12int.sub hF1int'
    have heqsub : ((fun z : ParabolicPoint =>
        serrinHeatWeight x s ρ z * (∑ j, spatialPartial (Y j) j z) +
          heatKernel (x - z.1) (s - z.2) * (w z * (timePartial (serrinCutoff x s ρ) z -
              ∑ i, spatialSecondPartial (serrinCutoff x s ρ) i i z) -
            2 * ∑ i, spatialPartial (serrinCutoff x s ρ) i z * spatialPartial w i z)) -
        (fun z : ParabolicPoint => serrinHeatWeight x s ρ z * (∑ j, spatialPartial (Y j) j z))) =
        (fun z => heatKernel (x - z.1) (s - z.2) * (w z * (timePartial (serrinCutoff x s ρ) z -
              ∑ i, spatialSecondPartial (serrinCutoff x s ρ) i i z) -
            2 * ∑ i, spatialPartial (serrinCutoff x s ρ) i z * spatialPartial w i z)) := by
      funext z
      show (serrinHeatWeight x s ρ z * (∑ j, spatialPartial (Y j) j z) +
          heatKernel (x - z.1) (s - z.2) * (w z * (timePartial (serrinCutoff x s ρ) z -
              ∑ i, spatialSecondPartial (serrinCutoff x s ρ) i i z) -
            2 * ∑ i, spatialPartial (serrinCutoff x s ρ) i z * spatialPartial w i z)) -
          serrinHeatWeight x s ρ z * (∑ j, spatialPartial (Y j) j z) =
          heatKernel (x - z.1) (s - z.2) * (w z * (timePartial (serrinCutoff x s ρ) z -
              ∑ i, spatialSecondPartial (serrinCutoff x s ρ) i i z) -
            2 * ∑ i, spatialPartial (serrinCutoff x s ρ) i z * spatialPartial w i z)
      ring
    rwa [heqsub] at hsub
  have hsplit : ∫ z in {z : ParabolicPoint | z.2 < s},
      (serrinHeatWeight x s ρ z * (∑ j, spatialPartial (Y j) j z) +
        heatKernel (x - z.1) (s - z.2) * (w z * (timePartial (serrinCutoff x s ρ) z -
            ∑ i, spatialSecondPartial (serrinCutoff x s ρ) i i z) -
          2 * ∑ i, spatialPartial (serrinCutoff x s ρ) i z * spatialPartial w i z)) =
      (∫ z in {z : ParabolicPoint | z.2 < s}, serrinHeatWeight x s ρ z *
          (∑ j, spatialPartial (Y j) j z)) +
      ∫ z in {z : ParabolicPoint | z.2 < s}, heatKernel (x - z.1) (s - z.2) *
          (w z * (timePartial (serrinCutoff x s ρ) z -
              ∑ i, spatialSecondPartial (serrinCutoff x s ρ) i i z) -
            2 * ∑ i, spatialPartial (serrinCutoff x s ρ) i z * spatialPartial w i z) :=
    integral_add hF1int' hF2int
  have hmainstep : w (x, s) =
      (∫ z in {z : ParabolicPoint | z.2 < s}, serrinHeatWeight x s ρ z *
          (∑ j, spatialPartial (Y j) j z)) +
      ∫ z in {z : ParabolicPoint | z.2 < s}, heatKernel (x - z.1) (s - z.2) *
          (w z * (timePartial (serrinCutoff x s ρ) z -
              ∑ i, spatialSecondPartial (serrinCutoff x s ρ) i i z) -
            2 * ∑ i, spatialPartial (serrinCutoff x s ρ) i z * spatialPartial w i z) := by
    rw [hwxs, hb1', hbig, hsplit]
  have hF1split : (∫ z in {z : ParabolicPoint | z.2 < s}, serrinHeatWeight x s ρ z *
        (∑ j, spatialPartial (Y j) j z)) =
      ∑ j, ∫ z in {z : ParabolicPoint | z.2 < s},
        serrinHeatWeight x s ρ z * spatialPartial (Y j) j z := by
    rw [hF1eq]
    exact integral_finsetSum Finset.univ (fun j _ => hF1int j)
  have hmainconv : ∀ j, ∫ z in {z : ParabolicPoint | z.2 < s},
      serrinHeatWeight x s ρ z * spatialPartial (Y j) j z =
      -∫ z in {z : ParabolicPoint | z.2 < s},
        spatialPartial (serrinHeatWeight x s ρ) j z * Y j z :=
    fun j => integral_serrinHeatWeight_mul_spatialPartial hO hρ hρ1 hwin (hY j) j
  have hF1final : (∫ z in {z : ParabolicPoint | z.2 < s}, serrinHeatWeight x s ρ z *
        (∑ j, spatialPartial (Y j) j z)) =
      -∑ j, ∫ z in {z : ParabolicPoint | z.2 < s},
        spatialPartial (serrinHeatWeight x s ρ) j z * Y j z := by
    rw [hF1split]
    rw [show (∑ j : Fin 3, ∫ z in {z : ParabolicPoint | z.2 < s},
        serrinHeatWeight x s ρ z * spatialPartial (Y j) j z) =
        (∫ z in {z : ParabolicPoint | z.2 < s}, serrinHeatWeight x s ρ z *
            spatialPartial (Y 0) 0 z) +
        (∫ z in {z : ParabolicPoint | z.2 < s}, serrinHeatWeight x s ρ z *
            spatialPartial (Y 1) 1 z) +
        (∫ z in {z : ParabolicPoint | z.2 < s}, serrinHeatWeight x s ρ z *
            spatialPartial (Y 2) 2 z) from Fin.sum_univ_three _]
    rw [hmainconv 0, hmainconv 1, hmainconv 2]
    rw [show (∑ j : Fin 3, ∫ z in {z : ParabolicPoint | z.2 < s},
        spatialPartial (serrinHeatWeight x s ρ) j z * Y j z) =
        (∫ z in {z : ParabolicPoint | z.2 < s},
            spatialPartial (serrinHeatWeight x s ρ) 0 z * Y 0 z) +
        (∫ z in {z : ParabolicPoint | z.2 < s},
            spatialPartial (serrinHeatWeight x s ρ) 1 z * Y 1 z) +
        (∫ z in {z : ParabolicPoint | z.2 < s},
            spatialPartial (serrinHeatWeight x s ρ) 2 z * Y 2 z) from Fin.sum_univ_three _]
    ring
  have hcomm := HB2c_commutator_slice_ibp hO hρ hwin hw
  have hwK0eq : ∀ z : ParabolicPoint, z.2 < s → w z * serrinCutoffKernel x s ρ z =
      (∑ l, spatialPartial (U l) l z) * serrinCutoffKernel x s ρ z := by
    intro z hz
    by_cases hzO : z ∈ O
    · rw [hwU z hzO]
    · have hzwin : z ∉ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s :=
        fun h => hzO (hwin h)
      rw [serrinCutoffKernel_eq_zero_off_window x hρ hz hzwin, mul_zero, mul_zero]
  have hcomm2 : ∫ z in {z : ParabolicPoint | z.2 < s}, w z * serrinCutoffKernel x s ρ z =
      ∫ z in {z : ParabolicPoint | z.2 < s},
        (∑ l, spatialPartial (U l) l z) * serrinCutoffKernel x s ρ z :=
    setIntegral_congr_fun hUmSet hwK0eq
  have hdiv := integral_divergence_mul_serrinCutoffKernel hO hρ hρ1 hwin hU
  have hF2final : ∫ z in {z : ParabolicPoint | z.2 < s}, heatKernel (x - z.1) (s - z.2) *
      (w z * (timePartial (serrinCutoff x s ρ) z -
          ∑ i, spatialSecondPartial (serrinCutoff x s ρ) i i z) -
        2 * ∑ i, spatialPartial (serrinCutoff x s ρ) i z * spatialPartial w i z) =
      -∑ l, ∫ z in {z : ParabolicPoint | z.2 < s},
        U l z * spatialPartial (serrinCutoffKernel x s ρ) l z := by
    rw [hcomm, hcomm2, hdiv]
  rw [hmainstep, hF1final, hF2final]
  ring

end CIV

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.LocalizedTailData
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.SubexponentialProfile
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.Vanishing

/-!
# LocalizedTailProfile

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The stream-field localized resolvent-tail profile

The logarithmic local constants in the two scale ranges give a pointwise
log-subexponential profile.  This module keeps the algebraic prefactor
explicit and proves its finite cubic layer-cake budget.
-/

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open DivergenceFormProcess.Decay
open DivergenceFormProcess.Form
open HCPolySupport
open HCPolySupport.Book.Ch02
open MarkovProcess.Semigroup
open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-- The point-dependent logarithmic weight. -/
def streamPointLogWeight (x : Vec d) : ℝ :=
  streamLogWeight (1 + euclideanNorm x)

/-- The radius-independent coefficient in the logarithmic upper bound for the
localized weighted estimate. -/
def streamLocalizedUpperBase (M : ABKModel d)
    (omega : FullSample d M.gamma) (x : Vec d) : ℝ :=
  localizedAgmonUpper M.nu 1
    (streamFieldSmallLocalConst M omega x 0)
    (streamFieldLargeDivLocalConst M omega x 0)

theorem streamLocalizedUpperBase_pos (M : ABKModel d)
    (omega : FullSample d M.gamma) (x : Vec d) :
    0 < streamLocalizedUpperBase M omega x := by
  exact localizedAgmonUpper_pos M.nu_pos
    (streamFieldSmallLocalConst_nonneg M omega (by norm_num))
    (streamFieldLargeDivLocalConst_nonneg M omega (by norm_num))

private theorem streamLogWeight_observation_le_mul {x : Vec d} {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s) :
    streamLogWeight (streamSplitObservationRadius x r) ≤
      streamPointLogWeight x * streamLogWeight (1 + s) := by
  have hs : 0 ≤ s := hr.trans hrs
  have hx : 0 ≤ euclideanNorm x := euclideanNorm_nonneg x
  have hobs : streamSplitObservationRadius x r ≤
      (1 + euclideanNorm x) * (1 + s) := by
    unfold streamSplitObservationRadius
    nlinarith only [hx, hs, hrs,
      mul_nonneg hx hs]
  have hobsPos : 0 < streamSplitObservationRadius x r := by
    unfold streamSplitObservationRadius
    linarith only [hx, hr]
  have hxPos : 0 < 1 + euclideanNorm x := by linarith only [hx]
  have hsPos : 0 < 1 + s := by linarith only [hs]
  have hlog := Real.strictMonoOn_log.monotoneOn hobsPos
    (mul_pos hxPos hsPos) hobs
  rw [Real.log_mul hxPos.ne' hsPos.ne'] at hlog
  have hlogx : 0 ≤ Real.log (1 + euclideanNorm x) :=
    Real.log_nonneg (by linarith only [hx])
  have hlogs : 0 ≤ Real.log (1 + s) :=
    Real.log_nonneg (by linarith only [hs])
  change 1 + Real.log (streamSplitObservationRadius x r) ≤
    (1 + Real.log (1 + euclideanNorm x)) * (1 + Real.log (1 + s))
  nlinarith only [hlog, hlogx, hlogs, mul_nonneg hlogx hlogs]

private theorem streamFieldSmallLocalConst_le_mul (M : ABKModel d)
    (omega : FullSample d M.gamma) {x : Vec d} {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s) :
    streamFieldSmallLocalConst M omega x r ≤
      streamFieldSmallLocalConst M omega x 0 * streamLogWeight (1 + s) := by
  have hw := streamLogWeight_observation_le_mul (x := x) hr hrs
  have hmul := mul_le_mul_of_nonneg_left hw
    (streamFieldSmallBallConst_nonneg M omega)
  simpa only [streamFieldSmallLocalConst, streamPointLogWeight,
    streamSplitObservationRadius, add_zero, mul_assoc] using hmul

private theorem streamFieldLargeDivLocalConst_le_mul (M : ABKModel d)
    (omega : FullSample d M.gamma) {x : Vec d} {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s) :
    streamFieldLargeDivLocalConst M omega x r ≤
      streamFieldLargeDivLocalConst M omega x 0 * streamLogWeight (1 + s) := by
  have hw := streamLogWeight_observation_le_mul (x := x) hr hrs
  have hbase : 0 ≤ Real.sqrt d * (d : ℝ) *
      streamFieldLargeGradientConst M omega := by
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg d) (Nat.cast_nonneg d))
      (streamFieldLargeGradientConst_nonneg M omega)
  have hmul := mul_le_mul_of_nonneg_left hw hbase
  simpa only [streamFieldLargeDivLocalConst, streamPointLogWeight,
    streamSplitObservationRadius, add_zero, mul_assoc] using hmul

/-- The effective upper constant at radius `r = s / sqrt mu` is at most its
point-dependent base times `1 + log (1+s)`, uniformly for `mu ≥ 1`. -/
theorem localizedAgmonUpper_stream_le (M : ABKModel d)
    (omega : FullSample d M.gamma) (x : Vec d)
    {mu r s : ℝ} (hmu : 1 ≤ mu) (hr : 0 ≤ r) (hrs : r ≤ s) :
    localizedAgmonUpper M.nu mu
        (streamFieldSmallLocalConst M omega x r)
        (streamFieldLargeDivLocalConst M omega x r) ≤
      streamLocalizedUpperBase M omega x * streamLogWeight (1 + s) := by
  have hs : 0 ≤ s := hr.trans hrs
  have hwpos : 0 < streamLogWeight (1 + s) :=
    streamLogWeight_pos (by linarith only [hs])
  have hwone : 1 ≤ streamLogWeight (1 + s) := by
    unfold streamLogWeight
    have hlog : 0 ≤ Real.log (1 + s) :=
      Real.log_nonneg (by linarith only [hs])
    linarith only [hlog]
  have hKs := streamFieldSmallLocalConst_le_mul M omega (x := x) hr hrs
  have hKl := streamFieldLargeDivLocalConst_le_mul M omega (x := x) hr hrs
  have hnu0 : 0 ≤ M.nu := M.nu_pos.le
  have hdiv : M.nu / mu ≤ M.nu := by
    exact div_le_self hnu0 hmu
  have hsqrt : Real.sqrt (M.nu / mu) ≤ Real.sqrt M.nu :=
    Real.sqrt_le_sqrt hdiv
  have hKl0 := streamFieldLargeDivLocalConst_nonneg M omega
    (x := x) (rho := 0) (by norm_num)
  unfold streamLocalizedUpperBase localizedAgmonUpper
  have hsmooth : 2 * streamFieldLargeDivLocalConst M omega x r *
      Real.sqrt (M.nu / mu) ≤
      2 * (streamFieldLargeDivLocalConst M omega x 0 *
        streamLogWeight (1 + s)) * Real.sqrt M.nu := by
    calc
      2 * streamFieldLargeDivLocalConst M omega x r * Real.sqrt (M.nu / mu) ≤
          2 * (streamFieldLargeDivLocalConst M omega x 0 *
            streamLogWeight (1 + s)) * Real.sqrt (M.nu / mu) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hKl (by norm_num))
          (Real.sqrt_nonneg _)
      _ ≤ 2 * (streamFieldLargeDivLocalConst M omega x 0 *
            streamLogWeight (1 + s)) * Real.sqrt M.nu :=
        mul_le_mul_of_nonneg_left hsqrt
          (mul_nonneg (by positivity) (mul_nonneg hKl0 hwpos.le))
  have hinside :
      M.nu + streamFieldSmallLocalConst M omega x r +
          2 * streamFieldLargeDivLocalConst M omega x r * Real.sqrt (M.nu / mu) ≤
        (M.nu + streamFieldSmallLocalConst M omega x 0 +
          2 * streamFieldLargeDivLocalConst M omega x 0 * Real.sqrt M.nu) *
            streamLogWeight (1 + s) := by
    calc
      M.nu + streamFieldSmallLocalConst M omega x r +
          2 * streamFieldLargeDivLocalConst M omega x r * Real.sqrt (M.nu / mu) ≤
        M.nu + streamFieldSmallLocalConst M omega x 0 * streamLogWeight (1 + s) +
          2 * (streamFieldLargeDivLocalConst M omega x 0 *
            streamLogWeight (1 + s)) * Real.sqrt M.nu :=
        add_le_add (add_le_add le_rfl hKs) hsmooth
      _ ≤ M.nu * streamLogWeight (1 + s) +
          streamFieldSmallLocalConst M omega x 0 * streamLogWeight (1 + s) +
          2 * (streamFieldLargeDivLocalConst M omega x 0 *
            streamLogWeight (1 + s)) * Real.sqrt M.nu := by
        have hnuScale : M.nu ≤ M.nu * streamLogWeight (1 + s) := by
          simpa only [mul_one] using
            (mul_le_mul_of_nonneg_left hwone M.nu_pos.le)
        exact add_le_add (add_le_add
          hnuScale le_rfl) le_rfl
      _ = (M.nu + streamFieldSmallLocalConst M omega x 0 +
          2 * streamFieldLargeDivLocalConst M omega x 0 * Real.sqrt M.nu) *
            streamLogWeight (1 + s) := by ring
  simpa only [div_one, mul_assoc] using
    (mul_le_mul_of_nonneg_left hinside (Real.sqrt_nonneg 2))

/-- A positive lower floor for the dimensionless frozen radius when the
outer dimensionless scale is beyond one and the mass is at least one. -/
def streamTailInnerFloor (M : ABKModel d)
    (omega : FullSample d M.gamma) (x : Vec d) : ℝ :=
  min (streamFreezingRadius M omega M.nu (streamLocalizedTailDelta d) x)
    (1 / 2 : ℝ)

theorem streamTailInnerFloor_pos (M : ABKModel d)
    (omega : FullSample d M.gamma) (x : Vec d) :
    0 < streamTailInnerFloor M omega x := by
  exact lt_min
    (streamFreezingRadius_pos M omega M.nu_pos (streamLocalizedTailDelta_pos d) x)
    (by norm_num)

/-- The pointwise log-subexponential decay rate. -/
def streamTailDecayRate (M : ABKModel d)
    (omega : FullSample d M.gamma) (x : Vec d) : ℝ :=
  agmonTailRate d M.nu (streamLocalizedUpperBase M omega x) (1 / 2 : ℝ)

variable [NeZero d]

omit [NeZero d] in
/-- The explicit algebraic amplitude.  Its two summands respectively control
the averaged/gradient terms and the bounded-forcing term of the frozen tail. -/
def streamTailAlgebraicAmplitude (M : ABKModel d) (omega : FullSample d M.gamma) (x : Vec d) : ℝ :=
  (agmonTailL2Coefficient d M.nu (streamLocalizedUpperBase M omega x) +
      agmonTailGradientCoefficient d M.nu
        (streamLocalizedUpperBase M omega x) (1 / 2 : ℝ)) /
      streamTailInnerFloor M omega x ^ d +
    4 * agmonTailForcingCoefficient d (1 / 2 : ℝ) / M.nu

omit [NeZero d] in
/-- The explicit profile for item 3 of `PACKET_M2_28b`. -/
def streamLocalizedTailProfile (M : ABKModel d) (omega : FullSample d M.gamma) (x : Vec d) : ℝ →
  ℝ :=
  logSubexponentialProfile (streamTailAlgebraicAmplitude M omega x)
    (streamTailDecayRate M omega x) (d + 1)

omit [NeZero d] in
theorem streamTailAlgebraicAmplitude_nonneg (M : ABKModel d)
    (omega : FullSample d M.gamma) (x : Vec d) :
    0 ≤ streamTailAlgebraicAmplitude M omega x := by
  have hB := (streamLocalizedUpperBase_pos M omega x).le
  have hb := (streamTailInnerFloor_pos M omega x).le
  have h1 := agmonTailL2Coefficient_nonneg d (lam := M.nu) hB
  have h2 := agmonTailGradientCoefficient_nonneg d
    (lam := M.nu) (alpha := (1 / 2 : ℝ)) M.nu_pos hB
  have h3 := agmonTailForcingCoefficient_nonneg d (1 / 2 : ℝ)
  unfold streamTailAlgebraicAmplitude
  exact add_nonneg
    (div_nonneg (add_nonneg h1 h2) (pow_nonneg hb d))
    (div_nonneg (mul_nonneg (by norm_num) h3) M.nu_pos.le)

private theorem streamTailInnerFloor_le_scaledClipped (M : ABKModel d)
    (omega : FullSample d M.gamma) (x : Vec d)
    {mu s : ℝ} (hmu : 1 ≤ mu) (hs : 1 ≤ s) :
    streamTailInnerFloor M omega x ≤
      Real.sqrt mu *
        (streamLocalizedSplitData M omega).clippedFreezingRadius x
          (s / Real.sqrt mu) := by
  have hmu0 : 0 ≤ mu := zero_le_one.trans hmu
  have hsqrt : 1 ≤ Real.sqrt mu := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hmu
  have hsqrtPos : 0 < Real.sqrt mu := zero_lt_one.trans_le hsqrt
  have hR0 : 0 < streamFreezingRadius M omega M.nu
      (streamLocalizedTailDelta d) x :=
    streamFreezingRadius_pos M omega M.nu_pos
      (streamLocalizedTailDelta_pos d) x
  rw [streamTailInnerFloor, WholeSpaceLocalizedSplitData.clippedFreezingRadius,
    show (streamLocalizedSplitData M omega).freezingRadius x =
      streamFreezingRadius M omega M.nu (streamLocalizedTailDelta d) x from rfl,
    mul_min_of_nonneg _ _ (Real.sqrt_nonneg mu)]
  have hleft : streamFreezingRadius M omega M.nu
      (streamLocalizedTailDelta d) x ≤
      Real.sqrt mu * streamFreezingRadius M omega M.nu
        (streamLocalizedTailDelta d) x := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hsqrt hR0.le
  have hright : (1 / 2 : ℝ) ≤
      Real.sqrt mu * (s / Real.sqrt mu / 2) := by
    rw [show Real.sqrt mu * (s / Real.sqrt mu / 2) = s / 2 by
      field_simp]
    linarith only [hs]
  exact min_le_min hleft hright

private theorem scaledClipped_le_half (M : ABKModel d)
    (omega : FullSample d M.gamma) (x : Vec d)
    {mu s : ℝ} (hmu : 0 < mu) :
    Real.sqrt mu *
        (streamLocalizedSplitData M omega).clippedFreezingRadius x
          (s / Real.sqrt mu) ≤ s / 2 := by
  have hsqrtPos : 0 < Real.sqrt mu := Real.sqrt_pos.2 hmu
  have hclip := (streamLocalizedSplitData M omega).clippedFreezingRadius_le_half
    x (s / Real.sqrt mu)
  have hmul := mul_le_mul_of_nonneg_left hclip hsqrtPos.le
  calc
    Real.sqrt mu *
        (streamLocalizedSplitData M omega).clippedFreezingRadius x
          (s / Real.sqrt mu) ≤ Real.sqrt mu * (s / Real.sqrt mu / 2) := hmul
    _ = s / 2 := by field_simp

private theorem streamLogWeight_one_add_le {s : ℝ} (hs : 0 ≤ s) :
    streamLogWeight (1 + s) ≤ 1 + s := by
  unfold streamLogWeight
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 + s by positivity)
  linarith only [hlog]

omit [NeZero d] in
private theorem agmonTailL2Coefficient_le_scale {lam L B w : ℝ}
    (hLB : L ≤ B * w) :
    agmonTailL2Coefficient d lam L ≤
      agmonTailL2Coefficient d lam B * w := by
  have hscale : ∀ T : ℝ, agmonTailL2Coefficient d lam T =
      agmonTailL2Coefficient d lam 1 * T := by
    intro T
    unfold agmonTailL2Coefficient
    ring
  rw [hscale L, hscale B, mul_assoc]
  exact mul_le_mul_of_nonneg_left hLB
    (agmonTailL2Coefficient_nonneg d (lam := lam) (by norm_num))

omit [NeZero d] in
private theorem agmonTailGradientCoefficient_le_scale
    {lam L B w alpha : ℝ} (hlam : 0 < lam) (hLB : L ≤ B * w) :
    agmonTailGradientCoefficient d lam L alpha ≤
      agmonTailGradientCoefficient d lam B alpha * w := by
  have hscale : ∀ T : ℝ, agmonTailGradientCoefficient d lam T alpha =
      agmonTailGradientCoefficient d lam 1 alpha * T := by
    intro T
    unfold agmonTailGradientCoefficient
    ring
  rw [hscale L, hscale B, mul_assoc]
  exact mul_le_mul_of_nonneg_left hLB
    (agmonTailGradientCoefficient_nonneg d hlam (by norm_num))

omit [NeZero d] in
private theorem agmonTailRate_div_logWeight_le
    {lam L B w alpha : ℝ} (hlam : 0 < lam) (hL : 0 < L)
    (hB : 0 < B) (hw : 0 < w) (halpha : 0 < alpha)
    (hLB : L ≤ B * w) :
    agmonTailRate d lam B alpha / w ≤ agmonTailRate d lam L alpha := by
  let K : ℝ := 3 * Real.sqrt lam / (16 * Real.sqrt 2)
  let Q : ℝ := alpha / (alpha + (d : ℝ) / 2)
  have hK : 0 < K := by
    unfold K
    positivity
  have hQ : 0 < Q := by
    unfold Q
    positivity
  have hdiv : K / (B * w) ≤ K / L :=
    div_le_div_of_nonneg_left hK.le hL hLB
  have hmul := mul_le_mul_of_nonneg_right hdiv hQ.le
  have hrateB : agmonTailRate d lam B alpha = K / B * Q := by
    unfold agmonTailRate K Q
    field_simp
  have hrateL : agmonTailRate d lam L alpha = K / L * Q := by
    unfold agmonTailRate K Q
    field_simp
  rw [hrateB, hrateL]
  have hw' : K / B * Q / w = K / (B * w) * Q := by
    field_simp [hw.ne', hB.ne']
    try ring
  rw [hw']
  exact hmul

omit [NeZero d] in
private theorem rpow_ratio_le_div_pow {b s s₀ q : ℝ}
    (hb : 0 < b) (hbhalf : b ≤ 1 / 2) (hs : 1 < s) (hbs₀ : b ≤ s₀)
    (hq0 : 0 ≤ q) (hqd : q ≤ d) :
    (s / (2 * s₀)) ^ q ≤ (s / b) ^ d := by
  have hs0 : 0 < s := one_pos.trans hs
  have hs₀ : 0 < s₀ := hb.trans_le hbs₀
  have hden : b ≤ 2 * s₀ := by
    nlinarith only [hbs₀, hb]
  have hratio : s / (2 * s₀) ≤ s / b :=
    div_le_div_of_nonneg_left hs0.le hb hden
  have hratio0 : 0 ≤ s / (2 * s₀) := by positivity
  have hbase : 1 ≤ s / b := by
    apply (le_div_iff₀ hb).2
    linarith only [hs, hbhalf]
  calc
    (s / (2 * s₀)) ^ q ≤ (s / b) ^ q :=
      Real.rpow_le_rpow hratio0 hratio hq0
    _ ≤ (s / b) ^ (d : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hbase hqd
    _ = (s / b) ^ d := Real.rpow_natCast _ _

private theorem streamFrozenTailBracket_le (M : ABKModel d)
    (omega : FullSample d M.gamma) (x : Vec d)
    {mu s : ℝ} (hmu : 1 ≤ mu) (hs : 1 < s) :
    let r := s / Real.sqrt mu
    let L := localizedAgmonUpper M.nu mu
      (streamFieldSmallLocalConst M omega x r)
      (streamFieldLargeDivLocalConst M omega x r)
    let s₀ := Real.sqrt mu *
      (streamLocalizedSplitData M omega).clippedFreezingRadius x r
    agmonTailL2Coefficient d M.nu L / |s| *
          (|s| / (2 * |s₀|)) ^ ((d : ℝ) / 2) +
        agmonTailGradientCoefficient d M.nu L (1 / 2 : ℝ) *
          (|s| / (2 * |s₀|)) ^ ((d : ℝ) / 2 - 1) +
        4 * agmonTailForcingCoefficient d (1 / 2 : ℝ) * s₀ ^ 2 / M.nu ≤
      streamTailAlgebraicAmplitude M omega x * (1 + s) ^ (d + 1) := by
  dsimp only
  let r := s / Real.sqrt mu
  let Ks := streamFieldSmallLocalConst M omega x r
  let Kl := streamFieldLargeDivLocalConst M omega x r
  let L := localizedAgmonUpper M.nu mu Ks Kl
  let B := streamLocalizedUpperBase M omega x
  let w := streamLogWeight (1 + s)
  let b := streamTailInnerFloor M omega x
  let s₀ := Real.sqrt mu *
    (streamLocalizedSplitData M omega).clippedFreezingRadius x r
  have hmu0 : 0 < mu := zero_lt_one.trans_le hmu
  have hs0 : 0 < s := one_pos.trans hs
  have hsqrt : 1 ≤ Real.sqrt mu := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hmu
  have hr : 0 < r := div_pos hs0 (zero_lt_one.trans_le hsqrt)
  have hrs : r ≤ s := by
    apply (div_le_iff₀ (zero_lt_one.trans_le hsqrt)).2
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsqrt hs0.le
  have hKs0 : 0 ≤ Ks := streamFieldSmallLocalConst_nonneg M omega hr.le
  have hKl0 : 0 ≤ Kl := streamFieldLargeDivLocalConst_nonneg M omega hr.le
  have hL : 0 < L := localizedAgmonUpper_pos M.nu_pos hKs0 hKl0
  have hB : 0 < B := streamLocalizedUpperBase_pos M omega x
  have hw : 0 < w := streamLogWeight_pos (by linarith only [hs0.le])
  have hwle : w ≤ 1 + s := streamLogWeight_one_add_le hs0.le
  have hLB : L ≤ B * w := by
    exact localizedAgmonUpper_stream_le M omega x hmu hr.le hrs
  have hb : 0 < b := streamTailInnerFloor_pos M omega x
  have hbhalf : b ≤ 1 / 2 := min_le_right _ _
  have hs₀ : 0 < s₀ := mul_pos (Real.sqrt_pos.2 hmu0)
    ((streamLocalizedSplitData M omega).clippedFreezingRadius_pos x hr)
  have hbs₀ : b ≤ s₀ := by
    exact streamTailInnerFloor_le_scaledClipped M omega x hmu hs.le
  have hs₀half : s₀ ≤ s / 2 := scaledClipped_le_half M omega x hmu0
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast M.shellPrefix.dimension
  have hq0 : 0 ≤ (d : ℝ) / 2 := by positivity
  have hqd : (d : ℝ) / 2 ≤ d := by linarith only [show 0 ≤ (d : ℝ) by positivity]
  have hp0 : 0 ≤ (d : ℝ) / 2 - 1 := by linarith only [hdR]
  have hpd : (d : ℝ) / 2 - 1 ≤ d := by
    linarith only [show 0 ≤ (d : ℝ) by positivity]
  have hratioQ : (s / (2 * s₀)) ^ ((d : ℝ) / 2) ≤ (s / b) ^ d :=
    rpow_ratio_le_div_pow hb hbhalf hs hbs₀ hq0 hqd
  have hratioP : (s / (2 * s₀)) ^ ((d : ℝ) / 2 - 1) ≤ (s / b) ^ d :=
    rpow_ratio_le_div_pow hb hbhalf hs hbs₀ hp0 hpd
  let A1 := agmonTailL2Coefficient d M.nu L
  let A2 := agmonTailGradientCoefficient d M.nu L (1 / 2 : ℝ)
  let A1B := agmonTailL2Coefficient d M.nu B
  let A2B := agmonTailGradientCoefficient d M.nu B (1 / 2 : ℝ)
  have hA1 : 0 ≤ A1 := agmonTailL2Coefficient_nonneg d hL.le
  have hA2 : 0 ≤ A2 :=
    agmonTailGradientCoefficient_nonneg d M.nu_pos hL.le
  have hA1B : 0 ≤ A1B := agmonTailL2Coefficient_nonneg d hB.le
  have hA2B : 0 ≤ A2B :=
    agmonTailGradientCoefficient_nonneg d M.nu_pos hB.le
  have hA1scale : A1 ≤ A1B * w :=
    agmonTailL2Coefficient_le_scale hLB
  have hA2scale : A2 ≤ A2B * w :=
    agmonTailGradientCoefficient_le_scale M.nu_pos hLB
  have hfirst : A1 / s * (s / (2 * s₀)) ^ ((d : ℝ) / 2) ≤
      A1 * (s / b) ^ d := by
    have hdiv : A1 / s ≤ A1 := div_le_self hA1 hs.le
    calc
      A1 / s * (s / (2 * s₀)) ^ ((d : ℝ) / 2) ≤
          A1 * (s / (2 * s₀)) ^ ((d : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right hdiv (Real.rpow_nonneg (by positivity) _)
      _ ≤ A1 * (s / b) ^ d :=
        mul_le_mul_of_nonneg_left hratioQ hA1
  have hsecond : A2 * (s / (2 * s₀)) ^ ((d : ℝ) / 2 - 1) ≤
      A2 * (s / b) ^ d :=
    mul_le_mul_of_nonneg_left hratioP hA2
  have hab : A1 + A2 ≤ (A1B + A2B) * w := by
    calc
      A1 + A2 ≤ A1B * w + A2B * w := add_le_add hA1scale hA2scale
      _ = (A1B + A2B) * w := by ring
  have hpowRatio : 0 ≤ (s / b) ^ d := pow_nonneg (by positivity) d
  have hradial : w * (s / b) ^ d ≤
      (1 + s) ^ (d + 1) / b ^ d := by
    have hspow : s ^ d ≤ (1 + s) ^ d :=
      pow_le_pow_left₀ hs0.le (by linarith only [hs0]) d
    have hprod : w * s ^ d ≤ (1 + s) ^ (d + 1) := by
      calc
        w * s ^ d ≤ (1 + s) * (1 + s) ^ d :=
          mul_le_mul hwle hspow (pow_nonneg hs0.le d) (by positivity)
        _ = (1 + s) ^ (d + 1) := by rw [pow_succ']
    rw [div_pow]
    rw [show w * (s ^ d / b ^ d) = (w * s ^ d) / b ^ d by ring]
    exact div_le_div_of_nonneg_right hprod (pow_nonneg hb.le d)
  have hmain :
      A1 / s * (s / (2 * s₀)) ^ ((d : ℝ) / 2) +
          A2 * (s / (2 * s₀)) ^ ((d : ℝ) / 2 - 1) ≤
        (A1B + A2B) / b ^ d * (1 + s) ^ (d + 1) := by
    calc
      A1 / s * (s / (2 * s₀)) ^ ((d : ℝ) / 2) +
          A2 * (s / (2 * s₀)) ^ ((d : ℝ) / 2 - 1) ≤
        (A1 + A2) * (s / b) ^ d := by
          nlinarith only [hfirst, hsecond]
      _ ≤ ((A1B + A2B) * w) * (s / b) ^ d :=
        mul_le_mul_of_nonneg_right hab hpowRatio
      _ ≤ (A1B + A2B) * ((1 + s) ^ (d + 1) / b ^ d) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hradial (add_nonneg hA1B hA2B)
      _ = (A1B + A2B) / b ^ d * (1 + s) ^ (d + 1) := by ring
  have hforce0 := agmonTailForcingCoefficient_nonneg d (1 / 2 : ℝ)
  have hsq : s₀ ^ 2 ≤ s ^ 2 := by
    calc
      s₀ ^ 2 ≤ (s / 2) ^ 2 := pow_le_pow_left₀ hs₀.le hs₀half 2
      _ ≤ s ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith only [hs0]) 2
  have hsPower : s ^ 2 ≤ (1 + s) ^ (d + 1) := by
    have hdNat : 2 ≤ d := M.shellPrefix.dimension
    calc
      s ^ 2 ≤ (1 + s) ^ 2 := pow_le_pow_left₀ hs0.le (by linarith only [hs0]) 2
      _ ≤ (1 + s) ^ (d + 1) :=
        pow_le_pow_right₀ (by linarith only [hs0]) (by omega)
  have hforce : 4 * agmonTailForcingCoefficient d (1 / 2 : ℝ) * s₀ ^ 2 / M.nu ≤
      (4 * agmonTailForcingCoefficient d (1 / 2 : ℝ) / M.nu) *
        (1 + s) ^ (d + 1) := by
    have hsq' := hsq.trans hsPower
    calc
      4 * agmonTailForcingCoefficient d (1 / 2 : ℝ) * s₀ ^ 2 / M.nu ≤
          4 * agmonTailForcingCoefficient d (1 / 2 : ℝ) *
            (1 + s) ^ (d + 1) / M.nu := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsq'
            (mul_nonneg (by norm_num) hforce0)) M.nu_pos.le
      _ = (4 * agmonTailForcingCoefficient d (1 / 2 : ℝ) / M.nu) *
          (1 + s) ^ (d + 1) := by ring
  rw [abs_of_pos hs0, abs_of_pos hs₀]
  change A1 / s * (s / (2 * s₀)) ^ ((d : ℝ) / 2) +
      A2 * (s / (2 * s₀)) ^ ((d : ℝ) / 2 - 1) +
      4 * agmonTailForcingCoefficient d (1 / 2 : ℝ) * s₀ ^ 2 / M.nu ≤ _
  unfold streamTailAlgebraicAmplitude
  change _ ≤ ((A1B + A2B) / b ^ d +
      4 * agmonTailForcingCoefficient d (1 / 2 : ℝ) / M.nu) *
        (1 + s) ^ (d + 1)
  calc
    _ ≤ (A1B + A2B) / b ^ d * (1 + s) ^ (d + 1) +
        (4 * agmonTailForcingCoefficient d (1 / 2 : ℝ) / M.nu) *
          (1 + s) ^ (d + 1) := add_le_add hmain hforce
    _ = _ := by ring

/-- The exact localized two-scale tail is bounded by the explicit
log-subexponential profile, uniformly in every mass `mu ≥ 1`. -/
theorem streamLocalizedSplitData_tail_le_profile (M : ABKModel d)
    (omega : FullSample d M.gamma) (mu : PositiveShift) (x : Vec d)
    (hmu : 1 ≤ (mu : ℝ)) {s : ℝ} (hs : 1 < s) :
    (streamLocalizedSplitData M omega).tail mu x
        (s / Real.sqrt (mu : ℝ)) ≤
      streamLocalizedTailProfile M omega x s := by
  let r := s / Real.sqrt (mu : ℝ)
  let Ks := streamFieldSmallLocalConst M omega x r
  let Kl := streamFieldLargeDivLocalConst M omega x r
  let L := localizedAgmonUpper M.nu (mu : ℝ) Ks Kl
  let B := streamLocalizedUpperBase M omega x
  let w := streamLogWeight (1 + s)
  let s₀ := Real.sqrt (mu : ℝ) *
    (streamLocalizedSplitData M omega).clippedFreezingRadius x r
  let P := agmonTailL2Coefficient d M.nu L / |s| *
          (|s| / (2 * |s₀|)) ^ ((d : ℝ) / 2) +
        agmonTailGradientCoefficient d M.nu L (1 / 2 : ℝ) *
          (|s| / (2 * |s₀|)) ^ ((d : ℝ) / 2 - 1) +
        4 * agmonTailForcingCoefficient d (1 / 2 : ℝ) * s₀ ^ 2 / M.nu
  have hmu0 : 0 < (mu : ℝ) := mu.property
  have hs0 : 0 < s := one_pos.trans hs
  have hsqrt : 0 < Real.sqrt (mu : ℝ) := Real.sqrt_pos.2 hmu0
  have hr : 0 < r := div_pos hs0 hsqrt
  have hKs : 0 ≤ Ks := streamFieldSmallLocalConst_nonneg M omega hr.le
  have hKl : 0 ≤ Kl := streamFieldLargeDivLocalConst_nonneg M omega hr.le
  have hL : 0 < L := localizedAgmonUpper_pos M.nu_pos hKs hKl
  have hB : 0 < B := streamLocalizedUpperBase_pos M omega x
  have hw : 0 < w := streamLogWeight_pos (by linarith only [hs0.le])
  have hrs : r ≤ s := by
    have hsqrtOne : 1 ≤ Real.sqrt (mu : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hmu
    apply (div_le_iff₀ hsqrt).2
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsqrtOne hs0.le
  have hLB : L ≤ B * w :=
    localizedAgmonUpper_stream_le M omega x hmu hr.le hrs
  have hrate : streamTailDecayRate M omega x / w ≤
      agmonTailRate d M.nu L (1 / 2 : ℝ) := by
    exact agmonTailRate_div_logWeight_le M.nu_pos hL hB hw (by norm_num) hLB
  have hexp : Real.exp (-(agmonTailRate d M.nu L (1 / 2 : ℝ) * s)) ≤
      Real.exp (-(streamTailDecayRate M omega x * s / w)) := by
    apply Real.exp_le_exp.2
    have hmul := mul_le_mul_of_nonneg_right hrate hs0.le
    calc
      -(agmonTailRate d M.nu L (1 / 2 : ℝ) * s) ≤
          -((streamTailDecayRate M omega x / w) * s) := neg_le_neg hmul
      _ = -(streamTailDecayRate M omega x * s / w) := by ring
  have hP : P ≤ streamTailAlgebraicAmplitude M omega x * (1 + s) ^ (d + 1) := by
    exact streamFrozenTailBracket_le M omega x hmu hs
  have hprofilePoly : 0 ≤
      streamTailAlgebraicAmplitude M omega x * (1 + s) ^ (d + 1) :=
    mul_nonneg (streamTailAlgebraicAmplitude_nonneg M omega x)
      (pow_nonneg (by linarith only [hs0]) _)
  have hscale : Real.sqrt (mu : ℝ) * r = s := by
    unfold r
    field_simp
  unfold WholeSpaceLocalizedSplitData.tail
  change agmonTailFunctionFrozen d M.nu L M.nu (1 / 2 : ℝ)
    (Real.sqrt (mu : ℝ) * r) s₀ ≤ _
  unfold agmonTailFunctionFrozen
  rw [hscale]
  change P * Real.exp (-(agmonTailRate d M.nu L (1 / 2 : ℝ) * s)) ≤ _
  calc
    P * Real.exp (-(agmonTailRate d M.nu L (1 / 2 : ℝ) * s)) ≤
        (streamTailAlgebraicAmplitude M omega x * (1 + s) ^ (d + 1)) *
          Real.exp (-(streamTailDecayRate M omega x * s / w)) :=
      mul_le_mul hP hexp (Real.exp_pos _).le hprofilePoly
    _ = streamLocalizedTailProfile M omega x s := by
      unfold streamLocalizedTailProfile logSubexponentialProfile
      rw [max_eq_left hs0.le]
      unfold w streamLogWeight
      congr 2
      ring

/-- The analytic minimal resolvent inherits the explicit pointwise
log-subexponential profile.  The estimate is uniform over the exhaustion
cubes used to define the minimal resolvent. -/
theorem mul_toReal_streamAnalyticMinimalResolvent_le_profile
    (M : ABKModel d) (omega : FullSample d M.gamma)
    (mu : PositiveShift) (hmu : 1 ≤ (mu : ℝ))
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, |f x| ≤ 1) {x : Vec d} {r : ℝ} (hr : 0 < r)
    (hs : 1 < Real.sqrt (mu : ℝ) * r)
    (hzero : ∀ y ∈ euclideanBall x r, f y = 0) :
    (mu : ℝ) *
        ((streamWholeSpaceAnalyticData M omega).analyticMinimalResolvent
          mu f hf hf1 x).toReal ≤
      streamLocalizedTailProfile M omega x
        (Real.sqrt (mu : ℝ) * r) := by
  have hsqrt : 0 < Real.sqrt (mu : ℝ) := Real.sqrt_pos.2 mu.property
  have hscale :
      (Real.sqrt (mu : ℝ) * r) / Real.sqrt (mu : ℝ) = r := by
    field_simp
  calc
    (mu : ℝ) *
        ((streamWholeSpaceAnalyticData M omega).analyticMinimalResolvent
          mu f hf hf1 x).toReal ≤
        (streamLocalizedSplitData M omega).tail mu x r :=
      (streamWholeSpaceAnalyticData M omega).mul_toReal_analyticMinimalResolvent_le_localizedTail
          (streamLocalizedSplitData M omega) mu hf hf0 hf1 hr hzero
    _ = (streamLocalizedSplitData M omega).tail mu x
          ((Real.sqrt (mu : ℝ) * r) / Real.sqrt (mu : ℝ)) := by rw [hscale]
    _ ≤ streamLocalizedTailProfile M omega x
          (Real.sqrt (mu : ℝ) * r) :=
      streamLocalizedSplitData_tail_le_profile M omega mu x hmu hs

end

end Algsuperdiff.Section5.Field

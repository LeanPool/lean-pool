/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.Exhaustion
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.LocalizedTailEnvelope

/-!
# UniformExhaustionProfile

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# A shift-uniform exhaustion-tail profile

Radius amplification controls the polynomially growing pointwise amplitude in
the far branch.  In the complementary branch the starting point is bounded in
terms of the shift and the dimensionless radius.  The latter branch is placed
beyond a cubic logarithmic cutoff.  Both branches are then dominated by
one cube-root stretched exponential with a shift-independent cubic budget.
-/

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open HCPolySupport
open HCPolySupport.Book.Ch02
open MeasureTheory Set

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The positive stretched-exponential rate used by the uniform profile. -/
def streamUniformExhaustionRate (M : ABKModel d)
    (omega : FullSample d M.gamma) : ℝ :=
  streamTailDecayConst M omega / 1000

/-- The scale constant of the cubic-log cutoff. -/
def streamUniformExhaustionScale (M : ABKModel d)
    (omega : FullSample d M.gamma) : ℝ :=
  1 + 100000 *
    (1 + streamTailAmplitudeExponent M + (d : ℝ) + 1) /
      streamTailDecayConst M omega

/-- A positive logarithmic weight for every real shift parameter. -/
def streamUniformShiftWeight (lam : ℝ) : ℝ :=
  1 + Real.log (max lam 1)

/-- The cubic-log cutting radius. -/
def streamUniformExhaustionCutoff (M : ABKModel d)
    (omega : FullSample d M.gamma) (lam : ℝ) : ℝ :=
  (streamUniformExhaustionScale M omega * streamUniformShiftWeight lam) ^ 3

/-- The common stretched-exponential majorant above the cutting radius. -/
def streamUniformExhaustionEnvelope (M : ABKModel d)
    (omega : FullSample d M.gamma) (s : ℝ) : ℝ :=
  streamTailAmplitudeConst M omega *
    Real.exp (-(streamUniformExhaustionRate M omega *
      (max s 0) ^ (1 / 3 : ℝ)))

/-- The shift-dependent profile is trivial below its cutoff and equals the
uniform envelope above it. -/
def streamUniformExhaustionProfile (M : ABKModel d)
    (omega : FullSample d M.gamma) (lam s : ℝ) : ℝ :=
  if streamUniformExhaustionCutoff M omega lam < s then
    streamUniformExhaustionEnvelope M omega s
  else 1

omit [NeZero d] in
private theorem streamTailAmplitudeExponent_pos (M : ABKModel d) :
    0 < streamTailAmplitudeExponent M := by
  unfold streamTailAmplitudeExponent
  have he := streamFreezingExponent_pos M
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hprod := mul_nonneg hd he.le
  linarith only [hprod]

omit [NeZero d] in
private theorem streamUniformExhaustionScale_pos (M : ABKModel d)
    (omega : FullSample d M.gamma) :
    0 < streamUniformExhaustionScale M omega := by
  unfold streamUniformExhaustionScale
  have hp := streamTailAmplitudeExponent_pos M
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hc := streamTailDecayConst_pos M omega
  have hnum : 0 < 1 + streamTailAmplitudeExponent M + (d : ℝ) + 1 := by
    linarith only [hp, hd]
  have hterm : 0 < 100000 *
      (1 + streamTailAmplitudeExponent M + (d : ℝ) + 1) /
        streamTailDecayConst M omega := by positivity
  linarith only [hterm]

omit [NeZero d] in
private theorem one_le_streamUniformExhaustionScale (M : ABKModel d)
    (omega : FullSample d M.gamma) :
    1 ≤ streamUniformExhaustionScale M omega := by
  unfold streamUniformExhaustionScale
  have hp := streamTailAmplitudeExponent_pos M
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hc := streamTailDecayConst_pos M omega
  have hterm : 0 ≤ 100000 *
      (1 + streamTailAmplitudeExponent M + (d : ℝ) + 1) /
        streamTailDecayConst M omega := by positivity
  linarith only [hterm]

private theorem one_le_streamUniformShiftWeight (lam : ℝ) :
    1 ≤ streamUniformShiftWeight lam := by
  unfold streamUniformShiftWeight
  have hmax : (1 : ℝ) ≤ max lam 1 := le_max_right _ _
  exact le_add_of_nonneg_right (Real.log_nonneg hmax)

omit [NeZero d] in
/-- The cubic-log cutoff is nonnegative. -/
theorem streamUniformExhaustionCutoff_nonneg (M : ABKModel d)
    (omega : FullSample d M.gamma) (lam : ℝ) :
    0 ≤ streamUniformExhaustionCutoff M omega lam := by
  unfold streamUniformExhaustionCutoff
  exact pow_nonneg (mul_nonneg (streamUniformExhaustionScale_pos M omega).le
    (zero_le_one.trans (one_le_streamUniformShiftWeight lam))) _

omit [NeZero d] in
/-- The cubic-log cutoff is at least one. -/
theorem one_le_streamUniformExhaustionCutoff (M : ABKModel d)
    (omega : FullSample d M.gamma) (lam : ℝ) :
    1 ≤ streamUniformExhaustionCutoff M omega lam := by
  unfold streamUniformExhaustionCutoff
  have hmul : 1 ≤ streamUniformExhaustionScale M omega *
      streamUniformShiftWeight lam := by
    nlinarith only [one_le_streamUniformExhaustionScale M omega,
      one_le_streamUniformShiftWeight lam]
  exact one_le_pow₀ hmul

theorem streamUniformExhaustionProfile_nonneg (M : ABKModel d)
    (omega : FullSample d M.gamma) (lam s : ℝ) :
    0 ≤ streamUniformExhaustionProfile M omega lam s := by
  unfold streamUniformExhaustionProfile streamUniformExhaustionEnvelope
  split_ifs
  · exact mul_nonneg (streamTailAmplitudeConst_nonneg M omega) (Real.exp_pos _).le
  · norm_num

/-- Below the cutting radius the uniform profile is the trivial unit bound. -/
theorem one_le_streamUniformExhaustionProfile_of_le_cutoff
    (M : ABKModel d) (omega : FullSample d M.gamma) {lam s : ℝ}
    (hs : s ≤ streamUniformExhaustionCutoff M omega lam) :
    1 ≤ streamUniformExhaustionProfile M omega lam s := by
  unfold streamUniformExhaustionProfile
  rw [ite_eq_right (not_lt_of_ge hs)]

private theorem rpow_one_third_cube {s : ℝ} (hs : 0 ≤ s) :
    (s ^ (1 / 3 : ℝ)) ^ 3 = s := by
  have hthree : (3 : ℕ) ≠ 0 := by norm_num
  simpa only [one_div, Nat.cast_ofNat] using Real.rpow_inv_natCast_pow hs hthree

private theorem rpow_one_sixth_pow_six {s : ℝ} (hs : 0 ≤ s) :
    (s ^ (1 / 6 : ℝ)) ^ 6 = s := by
  have hsix : (6 : ℕ) ≠ 0 := by norm_num
  simpa only [one_div, Nat.cast_ofNat] using Real.rpow_inv_natCast_pow hs hsix

private theorem one_le_rpow_one_third {s : ℝ} (hs : 1 ≤ s) :
    1 ≤ s ^ (1 / 3 : ℝ) :=
  Real.one_le_rpow hs (by norm_num)

private theorem one_le_rpow_one_sixth {s : ℝ} (hs : 1 ≤ s) :
    1 ≤ s ^ (1 / 6 : ℝ) :=
  Real.one_le_rpow hs (by norm_num)

private theorem logWeight_le_seven_mul_cuberoot {s : ℝ} (hs : 1 ≤ s) :
    1 + Real.log (1 + s) ≤ 7 * s ^ (1 / 3 : ℝ) := by
  have hs0 : 0 ≤ s := zero_le_one.trans hs
  have honeS : 0 ≤ 1 + s := by positivity
  have hlog := Real.log_le_rpow_div honeS (show (0 : ℝ) < 1 / 3 by norm_num)
  have hbase : 1 + s ≤ 2 * s := by linarith only [hs]
  have hrpow : (1 + s) ^ (1 / 3 : ℝ) ≤ (2 * s) ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow honeS hbase (by norm_num)
  have htwo : (2 : ℝ) ^ (1 / 3 : ℝ) ≤ 2 :=
    Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have hmul : (2 * s) ^ (1 / 3 : ℝ) ≤ 2 * s ^ (1 / 3 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hs0]
    exact mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hs0 _)
  have hrootOne := one_le_rpow_one_third hs
  calc
    1 + Real.log (1 + s) ≤ 1 + 3 * (1 + s) ^ (1 / 3 : ℝ) := by
      convert add_le_add_left hlog 1 using 1 <;> ring
    _ ≤ 1 + 6 * s ^ (1 / 3 : ℝ) := by
      have h := mul_le_mul_of_nonneg_left (hrpow.trans hmul) (by norm_num : (0 : ℝ) ≤ 3)
      linarith only [h]
    _ ≤ 7 * s ^ (1 / 3 : ℝ) := by linarith only [hrootOne]

private theorem logWeight_le_thirteen_mul_sixthRoot {s : ℝ} (hs : 1 ≤ s) :
    1 + Real.log (1 + s) ≤ 13 * s ^ (1 / 6 : ℝ) := by
  have hs0 : 0 ≤ s := zero_le_one.trans hs
  have honeS : 0 ≤ 1 + s := by positivity
  have hlog := Real.log_le_rpow_div honeS (show (0 : ℝ) < 1 / 6 by norm_num)
  have hbase : 1 + s ≤ 2 * s := by linarith only [hs]
  have hrpow : (1 + s) ^ (1 / 6 : ℝ) ≤ (2 * s) ^ (1 / 6 : ℝ) :=
    Real.rpow_le_rpow honeS hbase (by norm_num)
  have htwo : (2 : ℝ) ^ (1 / 6 : ℝ) ≤ 2 :=
    Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have hmul : (2 * s) ^ (1 / 6 : ℝ) ≤ 2 * s ^ (1 / 6 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hs0]
    exact mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hs0 _)
  have hrootOne := one_le_rpow_one_sixth hs
  calc
    1 + Real.log (1 + s) ≤ 1 + 6 * (1 + s) ^ (1 / 6 : ℝ) := by
      convert add_le_add_left hlog 1 using 1 <;> ring
    _ ≤ 1 + 12 * s ^ (1 / 6 : ℝ) := by
      have h := mul_le_mul_of_nonneg_left (hrpow.trans hmul) (by norm_num : (0 : ℝ) ≤ 6)
      linarith only [h]
    _ ≤ 13 * s ^ (1 / 6 : ℝ) := by linarith only [hrootOne]

private theorem shiftObservationWeight_le (lam : ℝ) (hlam : 1 ≤ lam) :
    1 + Real.log (1 + 4 * Real.sqrt lam) ≤
      5 * streamUniformShiftWeight lam := by
  have hlam0 : 0 ≤ lam := zero_le_one.trans hlam
  have hsqrt : Real.sqrt lam ≤ lam := by
    rw [Real.sqrt_le_iff]
    exact ⟨hlam0, by nlinarith only [hlam]⟩
  have harg : 1 + 4 * Real.sqrt lam ≤ 5 * lam := by
    linarith only [hsqrt, hlam]
  have hleft : 0 < 1 + 4 * Real.sqrt lam := by positivity
  have hright : 0 < 5 * lam := by positivity
  have hlog := Real.strictMonoOn_log.monotoneOn hleft hright harg
  have hlamne : lam ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hlam)
  rw [Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) hlamne] at hlog
  have hlogFive : Real.log (5 : ℝ) ≤ 4 := by
    simpa only [show (5 : ℝ) - 1 = 4 by norm_num] using
      (Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 by norm_num))
  have hlogLam : 0 ≤ Real.log lam := Real.log_nonneg hlam
  unfold streamUniformShiftWeight
  rw [max_eq_left hlam]
  linarith only [hlog, hlogFive, hlogLam]

omit [NeZero d] in
private theorem scale_mul_decayRate_large (M : ABKModel d)
    (omega : FullSample d M.gamma) :
    100000 * (1 + streamTailAmplitudeExponent M + (d : ℝ) + 1) ≤
      streamTailDecayConst M omega * streamUniformExhaustionScale M omega := by
  have hc := streamTailDecayConst_pos M omega
  unfold streamUniformExhaustionScale
  field_simp
  nlinarith only [hc]

private theorem cuberoot_gt_of_cube_lt {B L s : ℝ}
    (hs0 : 0 ≤ s)
    (hs : (B * L) ^ 3 < s) :
    B * L < s ^ (1 / 3 : ℝ) := by
  let z := s ^ (1 / 3 : ℝ)
  have hz0 : 0 ≤ z := Real.rpow_nonneg hs0 _
  have hzcube : z ^ 3 = s := rpow_one_third_cube hs0
  by_contra h
  have hzle : z ≤ B * L := le_of_not_gt h
  have hp := pow_le_pow_left₀ hz0 hzle 3
  rw [hzcube] at hp
  exact (not_lt_of_ge hp) hs

private theorem near_decay_lower {c L z Wq Ws S : ℝ}
    (hc : 0 ≤ c) (hL : 0 < L)
    (hWq : 0 < Wq) (hWs : 0 < Ws)
    (hWqBound : Wq ≤ 5 * L) (hWsBound : Ws ≤ 7 * z)
    (hcube : z ^ 3 = S) :
    c * z ^ 2 / (35 * L) ≤ (c / Wq) * S / Ws := by
  rw [div_le_div_iff₀ (by positivity : 0 < 35 * L) hWs]
  rw [show c / Wq * S * (35 * L) = c * S * (35 * L) / Wq by ring,
    le_div_iff₀ hWq]
  have hden : Wq * Ws ≤ 35 * L * z := by
    calc
      Wq * Ws ≤ (5 * L) * (7 * z) :=
        mul_le_mul hWqBound hWsBound hWs.le (by positivity)
      _ = 35 * L * z := by ring
  have hmul := mul_le_mul_of_nonneg_left hden (mul_nonneg hc (sq_nonneg z))
  calc
    c * z ^ 2 * Ws * Wq = c * z ^ 2 * (Wq * Ws) := by ring
    _ ≤ c * z ^ 2 * (35 * L * z) := hmul
    _ = c * S * (35 * L) := by rw [← hcube]; ring

private theorem active_decay_lower {c z Wq Ws S : ℝ}
    (hc : 0 ≤ c) (hz : 0 < z) (hWq : 0 < Wq) (hWs : 0 < Ws)
    (hWqBound : Wq ≤ 26 * z) (hWsBound : Ws ≤ 13 * z)
    (hsix : z ^ 6 = S) :
    c * z ^ 4 / 338 ≤ (c / Wq) * S / Ws := by
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 338) hWs]
  rw [show c / Wq * S * 338 = c * S * 338 / Wq by ring,
    le_div_iff₀ hWq]
  have hden : Wq * Ws ≤ 338 * z ^ 2 := by
    calc
      Wq * Ws ≤ (26 * z) * (13 * z) :=
        mul_le_mul hWqBound hWsBound hWs.le (by positivity)
      _ = 338 * z ^ 2 := by ring
  have hmul := mul_le_mul_of_nonneg_left hden
    (mul_nonneg hc (pow_nonneg hz.le 4))
  calc
    c * z ^ 4 * Ws * Wq = c * z ^ 4 * (Wq * Ws) := by ring
    _ ≤ c * z ^ 4 * (338 * z ^ 2) := hmul
    _ = c * S * 338 := by rw [← hsix]; ring

private theorem near_exponent_algebra {p n c B L z lq ls decay : ℝ}
    (hp : 0 ≤ p) (hn : 1 ≤ n) (hc : 0 < c) (hB : 1 ≤ B)
    (hL : 1 ≤ L) (hz : B * L < z)
    (hlarge : 100000 * (1 + p + n) ≤ c * B)
    (hlq : lq ≤ 5 * L) (hls : ls ≤ 7 * z)
    (hdecay : c * z ^ 2 / (35 * L) ≤ decay) :
    p * lq + n * ls - decay ≤ -(c / 1000 * z) := by
  have hBLone : 1 ≤ B * L := by
    nlinarith only [hB, hL, mul_nonneg (zero_le_one.trans hB) (zero_le_one.trans hL)]
  have hz0 : 0 ≤ z := by linarith only [hBLone, hz]
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hBLz : B * L * z ≤ z ^ 2 := by
    nlinarith only [hz, hz0]
  have hdecay' : c * B * z / 35 ≤ decay := by
    calc
      c * B * z / 35 ≤ c * z ^ 2 / (35 * L) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 35) (by positivity : 0 < 35 * L)]
        nlinarith only [hBLz, hc]
      _ ≤ decay := hdecay
  have hLz : L ≤ z := by nlinarith only [hB, hL, hz]
  have hlq' : lq ≤ 5 * z := hlq.trans (by linarith only [hLz])
  have hcB : c ≤ c * B := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hB hc.le
  have hcoeff : 5 * p + 7 * n + c / 1000 ≤ c * B / 35 := by
    nlinarith only [hlarge, hcB, hp, hn]
  have hpoly : p * lq + n * ls + c / 1000 * z ≤
      (5 * p + 7 * n + c / 1000) * z := by
    nlinarith only [hlq', hls, hp, hn, hz0]
  have hcoeffz := mul_le_mul_of_nonneg_right hcoeff hz0
  nlinarith only [hpoly, hcoeffz, hdecay']

private theorem active_exponent_algebra {p n c B z t lq ls decay : ℝ}
    (hp : 0 ≤ p) (hn : 1 ≤ n) (hc : 0 < c) (hB : 1 ≤ B)
    (hz : 1 ≤ z) (htz : t ≤ z ^ 2)
    (hlarge : 100000 * (1 + p + n) ≤ c * B)
    (hBz : B ≤ z ^ 2) (hlq : lq ≤ 26 * z) (hls : ls ≤ 13 * z)
    (hdecay : c * z ^ 4 / 338 ≤ decay) :
    p * lq + n * ls - decay ≤ -(c / 1000 * t) := by
  have hz0 : 0 ≤ z := zero_le_one.trans hz
  have hzz : z ≤ z ^ 2 := by nlinarith only [hz]
  have hdecay' : c * B * z ^ 2 / 338 ≤ decay := by
    have hpow : B * z ^ 2 ≤ z ^ 4 := by
      calc
        B * z ^ 2 ≤ z ^ 2 * z ^ 2 :=
          mul_le_mul_of_nonneg_right hBz (sq_nonneg z)
        _ = z ^ 4 := by ring
    have hcpow := mul_le_mul_of_nonneg_left hpow hc.le
    calc
      c * B * z ^ 2 / 338 ≤ c * z ^ 4 / 338 := by
        exact div_le_div_of_nonneg_right (by nlinarith only [hcpow]) (by norm_num)
      _ ≤ decay := hdecay
  have hcB : c ≤ c * B := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hB hc.le
  have hcoeff : 26 * p + 13 * n + c / 1000 ≤ c * B / 338 := by
    nlinarith only [hlarge, hcB, hp, hn]
  have hpoly : p * lq + n * ls + c / 1000 * t ≤
      (26 * p + 13 * n + c / 1000) * z ^ 2 := by
    nlinarith only [hlq, hls, hzz, htz, hp, hn, hc]
  have hcoeffz := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg z)
  nlinarith only [hpoly, hcoeffz, hdecay']

private theorem localizedProfile_le_envelope_of_exponent
    (M : ABKModel d) (omega : FullSample d M.gamma) (x : Vec d)
    {S s : ℝ} (hS : 0 < S) (hs : 0 < s)
    (hexp : streamTailAmplitudeExponent M * Real.log (1 + ‖x‖) +
        ((d : ℝ) + 1) * Real.log (1 + S) -
          (streamTailDecayConst M omega / (1 + Real.log (1 + ‖x‖))) * S /
            (1 + Real.log (1 + S)) ≤
        -(streamUniformExhaustionRate M omega * s ^ (1 / 3 : ℝ))) :
    streamLocalizedTailProfile M omega x S ≤
      streamUniformExhaustionEnvelope M omega s := by
  let p := streamTailAmplitudeExponent M
  let n := d + 1
  let qx : ℝ := 1 + ‖x‖
  let A := streamTailAmplitudeConst M omega
  let c := streamTailDecayConst M omega
  let cx := streamTailDecayRate M omega x
  have hqx : 0 < qx := by unfold qx; positivity
  have h1S : 0 < 1 + S := by linarith only [hS]
  have hWqx : 0 < 1 + Real.log qx := by
    have := Real.log_nonneg (show 1 ≤ qx by
      unfold qx
      exact le_add_of_nonneg_right (norm_nonneg x))
    linarith only [this]
  have hWS : 0 < 1 + Real.log (1 + S) := by
    have := Real.log_nonneg (show 1 ≤ 1 + S by linarith only [hS])
    linarith only [this]
  have hAmp := streamTailAlgebraicAmplitude_le M omega x
  have hRate := streamTailDecayRate_ge M omega x
  have hpoly : 0 ≤ (1 + S) ^ n := pow_nonneg h1S.le _
  have hExpRate :
      -cx * S / (1 + Real.log (1 + S)) ≤
        -(c / (1 + Real.log qx)) * S / (1 + Real.log (1 + S)) := by
    have hmul := mul_le_mul_of_nonneg_right hRate hS.le
    have hdiv := div_le_div_of_nonneg_right hmul hWS.le
    calc
      -cx * S / (1 + Real.log (1 + S)) =
          -(cx * S / (1 + Real.log (1 + S))) := by ring
      _ ≤ -((c / (1 + Real.log qx)) * S /
          (1 + Real.log (1 + S))) := neg_le_neg hdiv
      _ = _ := by ring
  have hdecay := Real.exp_le_exp.mpr hExpRate
  have hpre :
      streamTailAlgebraicAmplitude M omega x * (1 + S) ^ n *
          Real.exp (-cx * S / (1 + Real.log (1 + S))) ≤
        A * qx ^ p * (1 + S) ^ n *
          Real.exp (-(c / (1 + Real.log qx)) * S /
            (1 + Real.log (1 + S))) := by
    calc
      _ ≤ (A * qx ^ p) * (1 + S) ^ n *
          Real.exp (-cx * S / (1 + Real.log (1 + S))) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hAmp hpoly) (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left hdecay
        (mul_nonneg (mul_nonneg (streamTailAmplitudeConst_nonneg M omega)
          (Real.rpow_nonneg hqx.le _)) hpoly)
  have hrewrite :
      A * qx ^ p * (1 + S) ^ n *
          Real.exp (-(c / (1 + Real.log qx)) * S /
            (1 + Real.log (1 + S))) =
        A * Real.exp (p * Real.log qx + (n : ℝ) * Real.log (1 + S) -
          (c / (1 + Real.log qx)) * S / (1 + Real.log (1 + S))) := by
    rw [Real.rpow_def_of_pos hqx]
    rw [show (1 + S) ^ n = Real.exp ((n : ℝ) * Real.log (1 + S)) by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos h1S]
      congr 1
      ring]
    calc
      A * Real.exp (Real.log qx * p) * Real.exp ((n : ℝ) * Real.log (1 + S)) *
          Real.exp (-(c / (1 + Real.log qx)) * S /
            (1 + Real.log (1 + S))) =
        A * (Real.exp (p * Real.log qx) *
          Real.exp ((n : ℝ) * Real.log (1 + S)) *
          Real.exp (-(c / (1 + Real.log qx)) * S /
            (1 + Real.log (1 + S)))) := by
              rw [mul_comm (Real.log qx) p]
              ring
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2
        ring
  unfold streamLocalizedTailProfile logSubexponentialProfile
    streamUniformExhaustionEnvelope
  rw [max_eq_left hS.le, max_eq_left hs.le]
  change _ ≤ A * Real.exp (-(streamUniformExhaustionRate M omega *
    s ^ (1 / 3 : ℝ)))
  refine hpre.trans ?_
  rw [hrewrite]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
    simpa only [p, n, qx, c, Nat.cast_add, Nat.cast_one] using hexp))
    (streamTailAmplitudeConst_nonneg M omega)

/-- The per-point localized profile at the amplified radius is dominated by
the shift-uniform profile above the cubic-log cutoff. -/
theorem streamLocalizedTailProfile_amp_le_uniform
    (M : ABKModel d) (omega : FullSample d M.gamma)
    {lam : ℝ} (hlam : 1 ≤ lam) (x : Vec d) {r : ℝ} (hr : 0 < r)
    (hs : streamUniformExhaustionCutoff M omega lam < Real.sqrt lam * r) :
    streamLocalizedTailProfile M omega x
        (Real.sqrt lam * streamExhaustionAmp x r) ≤
      streamUniformExhaustionProfile M omega lam (Real.sqrt lam * r) := by
  let s := Real.sqrt lam * r
  let qx : ℝ := 1 + ‖x‖
  let B := streamUniformExhaustionScale M omega
  let L := streamUniformShiftWeight lam
  let c := streamTailDecayConst M omega
  let p := streamTailAmplitudeExponent M
  let n : ℝ := d + 1
  have hlam0 : 0 ≤ lam := zero_le_one.trans hlam
  have hsqrt : 1 ≤ Real.sqrt lam := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hlam
  have hsqrtPos : 0 < Real.sqrt lam := zero_lt_one.trans_le hsqrt
  have hspos : 0 < s := mul_pos hsqrtPos hr
  have hB : 1 ≤ B := one_le_streamUniformExhaustionScale M omega
  have hL : 1 ≤ L := one_le_streamUniformShiftWeight lam
  have hc : 0 < c := streamTailDecayConst_pos M omega
  have hp : 0 ≤ p := (streamTailAmplitudeExponent_pos M).le
  have hn : 1 ≤ n := by unfold n; exact le_add_of_nonneg_left (Nat.cast_nonneg d)
  have hlarge : 100000 * (1 + p + n) ≤ c * B := by
    simpa only [p, n, c, B, add_assoc] using scale_mul_decayRate_large M omega
  have hcut : (B * L) ^ 3 < s := by
    simpa only [streamUniformExhaustionCutoff, B, L, s] using hs
  have hsone : 1 ≤ s :=
    (one_le_streamUniformExhaustionCutoff M omega lam).trans hs.le
  have hprofile : streamUniformExhaustionProfile M omega lam s =
      streamUniformExhaustionEnvelope M omega s := by
    unfold streamUniformExhaustionProfile
    rw [ite_eq_left (by simpa only [s] using hs)]
  rw [show Real.sqrt lam * r = s by rfl, hprofile]
  unfold streamExhaustionAmp
  split_ifs with hamp
  · let S := Real.sqrt lam * max r (2 / 3 * qx)
    let z := S ^ (1 / 6 : ℝ)
    let t := s ^ (1 / 3 : ℝ)
    let Wq := 1 + Real.log qx
    let Ws := 1 + Real.log (1 + S)
    have hqx : 1 ≤ qx := by unfold qx; exact le_add_of_nonneg_right (norm_nonneg x)
    have hampPos : 0 < max r (2 / 3 * qx) := hr.trans_le (le_max_left _ _)
    have hS : 0 < S := mul_pos hsqrtPos hampPos
    have hSge : s ≤ S :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.sqrt_nonneg lam)
    have hSone : 1 ≤ S := hsone.trans hSge
    have hqxS : qx ≤ 2 * S := by
      have hmax := le_max_right r (2 / 3 * qx)
      have hampLe : max r (2 / 3 * qx) ≤ S := by
        simpa only [S, one_mul] using
          mul_le_mul_of_nonneg_right hsqrt hampPos.le
      nlinarith only [hmax, hampLe, hqx]
    have hWq : 0 < Wq := by
      unfold Wq
      have := Real.log_nonneg hqx
      linarith only [this]
    have hWs : 0 < Ws := by
      unfold Ws
      have := Real.log_nonneg (show 1 ≤ 1 + S by linarith only [hS])
      linarith only [this]
    have hWqWs : Wq ≤ 2 * Ws := by
      have harg : qx ≤ 2 * (1 + S) := hqxS.trans (by linarith only [hS])
      have hTwoPos : (0 : ℝ) < 2 := by norm_num
      have hOneSPos : 0 < 1 + S := by linarith only [hS]
      have hlog := Real.strictMonoOn_log.monotoneOn
        (lt_of_lt_of_le zero_lt_one hqx)
        (mul_pos hTwoPos hOneSPos) harg
      have hOneSne : (1 + S : ℝ) ≠ 0 := ne_of_gt hOneSPos
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hOneSne] at hlog
      have hlogTwo : Real.log (2 : ℝ) ≤ 1 := by
        simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
          (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2))
      have hlogS : 0 ≤ Real.log (1 + S) :=
        Real.log_nonneg (by linarith only [hS])
      unfold Wq Ws
      nlinarith only [hlog, hlogTwo, hlogS]
    have hzone : 1 ≤ z := one_le_rpow_one_sixth hSone
    have hWsBound : Ws ≤ 13 * z := logWeight_le_thirteen_mul_sixthRoot hSone
    have hWqBound : Wq ≤ 26 * z := hWqWs.trans (by linarith only [hWsBound])
    have hsix : z ^ 6 = S := rpow_one_sixth_pow_six hS.le
    have htcube : t ^ 3 = s := rpow_one_third_cube hspos.le
    have htz : t ≤ z ^ 2 := by
      by_contra h
      have hylt : z ^ 2 < t := lt_of_not_ge h
      have hpw := pow_lt_pow_left₀ hylt (sq_nonneg z)
        (by norm_num : (3 : ℕ) ≠ 0)
      rw [htcube, show (z ^ 2) ^ 3 = z ^ 6 by ring, hsix] at hpw
      exact (not_lt_of_ge hSge) hpw
    have hBgap := cuberoot_gt_of_cube_lt hspos.le hcut
    have hBz : B ≤ z ^ 2 := by nlinarith only [hBgap, hL, htz]
    have hdecay := active_decay_lower hc.le (zero_lt_one.trans_le hzone)
      hWq hWs hWqBound hWsBound hsix
    apply localizedProfile_le_envelope_of_exponent M omega x hS hspos
    apply active_exponent_algebra hp hn hc hB hzone htz hlarge hBz
    · linarith only [hWqBound]
    · linarith only [hWsBound]
    · simpa only [c, Wq, Ws, S, t, streamUniformExhaustionRate, div_mul_eq_mul_div]
        using hdecay
  · let z := s ^ (1 / 3 : ℝ)
    let Wq := 1 + Real.log qx
    let Ws := 1 + Real.log (1 + s)
    have hqx : 1 ≤ qx := by unfold qx; exact le_add_of_nonneg_right (norm_nonneg x)
    have hrlt : r < 4 / qx := by
      have := lt_of_not_ge hamp
      simpa only [streamExhaustionRho, qx, div_eq_mul_inv] using this
    have hqr : r * qx < 4 := (lt_div_iff₀ (lt_of_lt_of_le zero_lt_one hqx)).mp hrlt
    have hqxBound : qx ≤ 1 + 4 * Real.sqrt lam := by
      have hmul : qx ≤ qx * s := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hsone (zero_le_one.trans hqx)
      have hstrict : qx * s < 4 * Real.sqrt lam := by
        unfold s
        nlinarith only [hqr, hsqrtPos]
      linarith only [hmul, hstrict]
    have hlog := Real.strictMonoOn_log.monotoneOn
      (lt_of_lt_of_le zero_lt_one hqx) (by positivity : 0 < 1 + 4 * Real.sqrt lam) hqxBound
    have hWq : 0 < Wq := by unfold Wq; have := Real.log_nonneg hqx; linarith only [this]
    have hWs : 0 < Ws := by
      unfold Ws
      have := Real.log_nonneg (by linarith only [hspos] : 1 ≤ 1 + s)
      linarith only [this]
    have hWqBound : Wq ≤ 5 * L := by
      have hfirst : Wq ≤ 1 + Real.log (1 + 4 * Real.sqrt lam) := by
        unfold Wq
        linarith only [hlog]
      exact hfirst.trans (by simpa only [L] using shiftObservationWeight_le lam hlam)
    have hWsBound : Ws ≤ 7 * z := logWeight_le_seven_mul_cuberoot hsone
    have hcube : z ^ 3 = s := rpow_one_third_cube hspos.le
    have hzgap := cuberoot_gt_of_cube_lt hspos.le hcut
    have hdecay := near_decay_lower hc.le (zero_lt_one.trans_le hL)
      hWq hWs hWqBound hWsBound hcube
    apply localizedProfile_le_envelope_of_exponent M omega x hspos hspos
    apply near_exponent_algebra hp hn hc hB hL hzgap hlarge
    · linarith only [hWqBound]
    · linarith only [hWsBound]
    · simpa only [c, Wq, Ws, z, streamUniformExhaustionRate, div_mul_eq_mul_div]
        using hdecay

end

end Algsuperdiff.Section5.Field

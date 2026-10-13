/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.WholeSpaceC0

/-!
# ShiftAsymptotics

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Large-shift asymptotics of the stream tail profile

The cubic logarithmic cutting radius is negligible compared with the natural
square-root resolvent scale.  Consequently every fixed positive spatial
radius eventually lies in the stretched-exponential branch of the uniform
profile, where that profile tends to zero.
-/

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 Filter Topology
open MarkovProcess.Semigroup

noncomputable section

variable {d : ℕ}

/-- The cubic logarithmic cutoff divided by the square-root mass tends to
zero. -/
theorem tendsto_streamUniformExhaustionCutoff_div_sqrt
    (M : ABKModel d) (omega : FullSample d M.gamma) :
    Tendsto (fun mu : PositiveShift ↦
      streamUniformExhaustionCutoff M omega (mu : ℝ) /
        Real.sqrt (mu : ℝ)) atTop (nhds 0) := by
  let p : ℝ := 1 / 6
  have hp : 0 < p := by unfold p; norm_num
  have hpowTop : Tendsto (fun x : ℝ ↦ x ^ p) atTop atTop :=
    tendsto_rpow_atTop hp
  have hone : Tendsto (fun x : ℝ ↦ 1 / x ^ p) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hpowTop
  have hlog : Tendsto (fun x : ℝ ↦ Real.log x / x ^ p) atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop hp).tendsto_div_nhds_zero
  have hratio : Tendsto (fun x : ℝ ↦ (1 + Real.log x) / x ^ p)
      atTop (nhds 0) := by
    convert hone.add hlog using 1
    · funext x
      ring_nf
    · norm_num
  have hcomp := hratio.comp tendsto_positiveShift_coe_atTop
  have hcubed := hcomp.pow 3
  have hscaled := hcubed.const_mul
    (streamUniformExhaustionScale M omega ^ 3)
  have hscaled' : Tendsto (fun mu : PositiveShift ↦
      streamUniformExhaustionScale M omega ^ 3 *
        (((1 + Real.log (mu : ℝ)) / (mu : ℝ) ^ p) ^ 3))
      atTop (nhds 0) := by
    have hzero : streamUniformExhaustionScale M omega ^ 3 * (0 : ℝ) ^ 3 = 0 := by
      norm_num
    rw [hzero] at hscaled
    simpa only [Function.comp_apply] using hscaled
  apply hscaled'.congr'
  let oneShift : PositiveShift := ⟨1, Set.mem_Ioi.mpr one_pos⟩
  filter_upwards [eventually_ge_atTop oneShift] with mu hmu
  have hmu1 : 1 ≤ (mu : ℝ) := by exact_mod_cast hmu
  have hmu0 : 0 < (mu : ℝ) := mu.property
  have hpow : ((mu : ℝ) ^ p) ^ 3 = (mu : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hmu0.le]
    unfold p
    congr 1
    norm_num
  unfold streamUniformExhaustionCutoff streamUniformShiftWeight
  rw [max_eq_left hmu1, Real.sqrt_eq_rpow, ← hpow, mul_pow]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hmu0 p)]

/-- At every fixed positive spatial radius, the uniform envelope on the
natural square-root scale tends to zero as the mass tends to infinity. -/
theorem tendsto_streamUniformExhaustionEnvelope_sqrt_mul
    [NeZero d] (M : ABKModel d) (omega : FullSample d M.gamma) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun mu : PositiveShift ↦
      streamUniformExhaustionEnvelope M omega
        (Real.sqrt (mu : ℝ) * r)) atTop (nhds 0) := by
  have hsqrt : Tendsto (fun mu : PositiveShift ↦ Real.sqrt (mu : ℝ))
      atTop atTop := by
    simpa only [Real.sqrt_eq_rpow, Function.comp_def] using
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        tendsto_positiveShift_coe_atTop
  exact (tendsto_streamUniformExhaustionEnvelope_atTop M omega).comp
    (hsqrt.atTop_mul_const hr)

/-- A fixed positive radius eventually lies beyond the cubic logarithmic
cutoff on the square-root mass scale. -/
theorem eventually_streamUniformExhaustionCutoff_lt_sqrt_mul
    (M : ABKModel d) (omega : FullSample d M.gamma) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ mu : PositiveShift in atTop,
      streamUniformExhaustionCutoff M omega (mu : ℝ) <
        Real.sqrt (mu : ℝ) * r := by
  have hzero := tendsto_streamUniformExhaustionCutoff_div_sqrt M omega
  have hevent := (Metric.tendsto_nhds.mp hzero) r hr
  filter_upwards [hevent] with mu hmu
  rw [Real.dist_eq, sub_zero] at hmu
  have hcut0 : 0 ≤ streamUniformExhaustionCutoff M omega (mu : ℝ) :=
    streamUniformExhaustionCutoff_nonneg M omega (mu : ℝ)
  have hsqrt : 0 < Real.sqrt (mu : ℝ) := Real.sqrt_pos.2 mu.property
  rw [abs_of_nonneg (div_nonneg hcut0 hsqrt.le)] at hmu
  simpa only [mul_comm] using (div_lt_iff₀ hsqrt).mp hmu

end

end Algsuperdiff.Section5.Field

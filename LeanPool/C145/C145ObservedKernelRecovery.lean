/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import LeanPool.C145.C145ActualTimeConvolution
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
Observed first and quadratic time-kernel recovery from ordinary response jets.
Tests are globally smooth and compactly supported inside the physical interval.
Only the terminal-time response derivatives are used. No continuation beyond
that interval, spectral calibration, graph premise or noisy inverse is asserted.
-/

@[expose] public section

noncomputable section
namespace C145.ObservedKernelRecovery
open MeasureTheory Set Filter
open C145.ActualResponse
open scoped Topology ContDiff
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup
  AddCommGroup.toAddCommMonoid
  NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace
  UniformSpace.toTopologicalSpace

/-- The source's smooth temporal directions, with compact support in (0,T). -/
def SmoothTemporalTest (T : ℝ) (g : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ Ioo (0 : ℝ) T

/-- The real-time reflection that sends a time to its difference from the horizon. -/
def reflection (T : ℝ) : ℝ ≃ₜ ℝ where
  toFun s := T - s
  invFun s := T - s
  left_inv s := by dsimp; ring
  right_inv s := by dsimp; ring
  continuous_toFun := continuous_const.sub continuous_id
  continuous_invFun := continuous_const.sub continuous_id

/-- Reflection of a smooth test remains a physically allowed smooth test. -/
theorem smoothTemporalTest_reflect {T : ℝ} {g : ℝ → ℝ}
    (hg : SmoothTemporalTest T g) :
    SmoothTemporalTest T (fun s => g (T - s)) := by
  refine ⟨hg.1.comp (contDiff_const.sub contDiff_id), ?_, ?_⟩
  · exact hg.2.1.comp_homeomorph (reflection T)
  · change tsupport (g ∘ reflection T) ⊆ Ioo (0 : ℝ) T
    rw [tsupport_comp_eq_preimage]
    intro s hs
    have h := hg.2.2 hs
    change 0 < T - s ∧ T - s < T at h
    constructor <;> linarith

/-- The imported distribution lemma separates smooth compact test functions;
continuity makes the resulting almost-everywhere equality pointwise. -/
theorem continuous_zero_of_smooth_tests {T : ℝ} (hT : 0 < T)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hTest : ∀ g : ℝ → ℝ, SmoothTemporalTest T g →
      (∫ r in (0 : ℝ)..T, f r * g r) = 0) :
    ∀ r ∈ Icc (0 : ℝ) T, f r = 0 := by
  have hae : ∀ᵐ r : ℝ, r ∈ Ioo (0 : ℝ) T → f r = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hf.continuousOn.locallyIntegrableOn measurableSet_Ioo)
    intro g hgd hgc hgs
    have hsupport : Function.support (fun r => g r * f r) ⊆ Ioc (0 : ℝ) T := by
      intro r hr
      have hgzero : g r ≠ 0 := by
        intro he
        exact hr (by simp [he])
      have hin := hgs (subset_tsupport g (show r ∈ Function.support g from hgzero))
      exact ⟨hin.1, hin.2.le⟩
    change (∫ x : ℝ, g x * f x) = 0
    rw [← intervalIntegral.integral_eq_integral_of_support_subset hsupport]
    simpa only [smul_eq_mul, mul_comm] using hTest g ⟨hgd, hgc, hgs⟩
  have haeU : f =ᵐ[volume.restrict (Ioo (0 : ℝ) T)] (fun _ => 0) := by
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Ioo] with r hr hmem
    exact hr hmem
  have hinside : EqOn f (fun _ => 0) (Ioo (0 : ℝ) T) :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq haeU isOpen_Ioo hf.continuousOn
      continuous_const.continuousOn
  have hclosure : Icc (0 : ℝ) T ⊆ closure (Ioo (0 : ℝ) T) := by
    rw [closure_Ioo hT.ne]
  exact hinside.of_subset_closure hf.continuousOn continuous_const.continuousOn
    Ioo_subset_Icc_self hclosure

/-- Product smooth temporal tests separate a continuous kernel on the square.
One-dimensional smooth-test separation is applied twice, without additional data. -/
theorem continuous_square_zero_of_smooth_product_tests {T : ℝ} (hT : 0 < T)
    (K : ℝ → ℝ → ℝ) (hK : Continuous (fun p : ℝ × ℝ => K p.1 p.2))
    (hTest : ∀ g h : ℝ → ℝ, SmoothTemporalTest T g → SmoothTemporalTest T h →
      (∫ r in (0 : ℝ)..T, ∫ s in (0 : ℝ)..T, K r s * g r * h s) = 0) :
    ∀ r ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (0 : ℝ) T, K r s = 0 := by
  have hmarg (h : ℝ → ℝ) (hh : SmoothTemporalTest T h) :
      ∀ r ∈ Icc (0 : ℝ) T, (∫ s in (0 : ℝ)..T, K r s * h s) = 0 := by
    have hcontinuous : Continuous (fun r : ℝ => ∫ s in (0 : ℝ)..T, K r s * h s) := by
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (a₀ := (0 : ℝ)) (b₀ := T)
      exact hK.mul (hh.1.continuous.comp continuous_snd)
    apply continuous_zero_of_smooth_tests hT _ hcontinuous
    intro g hg
    calc
      (∫ r in (0 : ℝ)..T, (∫ s in (0 : ℝ)..T, K r s * h s) * g r) =
          ∫ r in (0 : ℝ)..T, ∫ s in (0 : ℝ)..T, K r s * g r * h s := by
        apply intervalIntegral.integral_congr
        intro r hr
        change (∫ s in (0 : ℝ)..T, K r s * h s) * g r =
          ∫ s in (0 : ℝ)..T, K r s * g r * h s
        rw [← intervalIntegral.integral_mul_const]
        apply intervalIntegral.integral_congr
        intro s hs
        change (K r s * h s) * g r = K r s * g r * h s
        ring
      _ = 0 := hTest g h hg hh
  intro r hr
  apply continuous_zero_of_smooth_tests hT (K r)
    (hK.comp (continuous_const.prodMk continuous_id))
  intro h hh
  exact hmarg h hh r hr

theorem firstKernel_continuous {n : ℕ} (Q : Frame n) (rates b : State n) :
    Continuous (C145.DelayKernel.firstKernel Q rates b) := by
  change Continuous (fun r : ℝ => C145.DelayKernel.firstKernel Q rates b r)
  simp_rw [C145.DelayKernel.firstKernel_expansion]
  fun_prop

theorem delayKernel_continuous {n : ℕ} (Q : Frame n) (rates b : State n) :
    Continuous (fun p : ℝ × ℝ => C145.DelayKernel.delayKernel Q rates b p.1 p.2) := by
  unfold C145.DelayKernel.delayKernel
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
  · unfold C145.DelayKernel.delayIntegrand C145.Pulse.heatAction
    fun_prop
  · exact continuous_fst.min continuous_snd

theorem extendInput_reflected {T : ℝ} (hT : 0 < T) (g : ℝ → ℝ)
    (hg : Continuous g) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) T) :
    extendInput hT (restrictInput T (fun s => g (T - s))
      (hg.comp (continuous_const.sub continuous_id))) (T - r) = g r := by
  have hlow : 0 ≤ T - r := by linarith [hr.2]
  have hupp : T - r ≤ T := by linarith [hr.1]
  change g (T - max 0 (min T (T - r))) = g r
  rw [min_eq_right hupp, max_eq_right hlow]
  congr 1
  ring

/-- Canonical first derivative, tested with a reflected smooth direction. -/
theorem rawFirst_reflected {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates b : State n)
    (hQ : C145PhysicalFrame.ColumnOrthonormal Q)
    (R : Input T → Path n T) (hR : IsActualResponse hT Q rates b R)
    (hcR : ContDiffAt ℝ 2 R 0) (g : ℝ → ℝ) (hg : Continuous g) :
    rawFirst b R (restrictInput T (fun s => g (T - s))
      (hg.comp (continuous_const.sub continuous_id))) (endTime T hT) =
      ∫ r in (0 : ℝ)..T, C145.DelayKernel.firstKernel Q rates b r * g r := by
  rw [(C145.ActualTimeConvolution.actual_response_time_kernel hT Q rates b hQ R hR hcR
    (restrictInput T (fun s => g (T - s)) (hg.comp (continuous_const.sub continuous_id)))
    (restrictInput T (fun s => g (T - s)) (hg.comp (continuous_const.sub continuous_id)))
    (endTime T hT)).1]
  apply intervalIntegral.integral_congr
  intro r hr
  change C145.DelayKernel.firstKernel Q rates b r *
    extendInput hT (restrictInput T (fun s => g (T - s))
      (hg.comp (continuous_const.sub continuous_id))) (T - r) =
      C145.DelayKernel.firstKernel Q rates b r * g r
  rw [extendInput_reflected hT g hg r (by simpa [endTime, uIcc_of_le hT.le] using hr)]

/-- The factor one half is already in canonical rawMixed; no rescaling occurs. -/
theorem rawMixed_reflected {n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q : Frame n) (rates b : State n)
    (hQ : C145PhysicalFrame.ColumnOrthonormal Q)
    (R : Input T → Path n T) (hR : IsActualResponse hT Q rates b R)
    (hcR : ContDiffAt ℝ 2 R 0) (g h : ℝ → ℝ) (hg : Continuous g) (hh : Continuous h) :
    rawMixed b R
      (restrictInput T (fun s => g (T - s)) (hg.comp (continuous_const.sub continuous_id)))
      (restrictInput T (fun s => h (T - s)) (hh.comp (continuous_const.sub continuous_id)))
      (endTime T hT) =
      ∫ r in (0 : ℝ)..T, ∫ s in (0 : ℝ)..T,
        C145.DelayKernel.delayKernel Q rates b r s * g r * h s := by
  rw [(C145.ActualTimeConvolution.actual_response_time_kernel hT Q rates b hQ R hR hcR
    (restrictInput T (fun s => g (T - s)) (hg.comp (continuous_const.sub continuous_id)))
    (restrictInput T (fun s => h (T - s)) (hh.comp (continuous_const.sub continuous_id)))
    (endTime T hT)).2.1]
  apply intervalIntegral.integral_congr
  intro r hr
  apply intervalIntegral.integral_congr
  intro s hs
  change C145.DelayKernel.delayKernel Q rates b r s *
    extendInput hT (restrictInput T (fun s => g (T - s))
      (hg.comp (continuous_const.sub continuous_id))) (T - r) *
    extendInput hT (restrictInput T (fun s => h (T - s))
      (hh.comp (continuous_const.sub continuous_id))) (T - s) =
    C145.DelayKernel.delayKernel Q rates b r s * g r * h s
  rw [extendInput_reflected hT g hg r (by simpa [endTime, uIcc_of_le hT.le] using hr),
    extendInput_reflected hT h hh s (by simpa [endTime, uIcc_of_le hT.le] using hs)]

/-- Actual ordinary C2 response data on smooth compact temporal directions
recover the two observed kernels, without any supplied kernel equality. -/
theorem ordinary_C2_jets_recover_observed_time_kernels {m n : ℕ} {T : ℝ}
    (hT : 0 < T)
    (Q0 : Frame m) (rates0 b0 : State m) (Q1 : Frame n) (rates1 b1 : State n)
    (hQ0 : C145PhysicalFrame.ColumnOrthonormal Q0)
    (hQ1 : C145PhysicalFrame.ColumnOrthonormal Q1)
    (R0 : Input T → Path m T) (R1 : Input T → Path n T)
    (hR0 : IsActualResponse hT Q0 rates0 b0 R0)
    (hR1 : IsActualResponse hT Q1 rates1 b1 R1)
    (hcR0 : ContDiffAt ℝ 2 R0 0) (hcR1 : ContDiffAt ℝ 2 R1 0)
    (hFirst : ∀ (g : ℝ → ℝ) (hg : SmoothTemporalTest T g),
      rawFirst b0 R0 (restrictInput T g hg.1.continuous) (endTime T hT) =
      rawFirst b1 R1 (restrictInput T g hg.1.continuous) (endTime T hT))
    (hMixed : ∀ (g h : ℝ → ℝ) (hg : SmoothTemporalTest T g) (hh : SmoothTemporalTest T h),
      rawMixed b0 R0 (restrictInput T g hg.1.continuous) (restrictInput T h hh.1.continuous)
          (endTime T hT) =
      rawMixed b1 R1 (restrictInput T g hg.1.continuous) (restrictInput T h hh.1.continuous)
          (endTime T hT)) :
    (∀ r ∈ Icc (0 : ℝ) T,
      C145.DelayKernel.firstKernel Q0 rates0 b0 r =
        C145.DelayKernel.firstKernel Q1 rates1 b1 r) ∧
    (∀ r ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (0 : ℝ) T,
      C145.DelayKernel.delayKernel Q0 rates0 b0 r s =
        C145.DelayKernel.delayKernel Q1 rates1 b1 r s) := by
  have hk0 := firstKernel_continuous Q0 rates0 b0
  have hk1 := firstKernel_continuous Q1 rates1 b1
  have hK0 := delayKernel_continuous Q0 rates0 b0
  have hK1 := delayKernel_continuous Q1 rates1 b1
  constructor
  · have hz := continuous_zero_of_smooth_tests hT
      (fun r => C145.DelayKernel.firstKernel Q0 rates0 b0 r -
        C145.DelayKernel.firstKernel Q1 rates1 b1 r) (hk0.sub hk1) ?_
    · intro r hr
      exact sub_eq_zero.mp (hz r hr)
    · intro g hg
      have heq := hFirst (fun s => g (T - s)) (smoothTemporalTest_reflect hg)
      rw [rawFirst_reflected hT Q0 rates0 b0 hQ0 R0 hR0 hcR0 g hg.1.continuous,
        rawFirst_reflected hT Q1 rates1 b1 hQ1 R1 hR1 hcR1 g hg.1.continuous] at heq
      simp_rw [sub_mul]
      rw [intervalIntegral.integral_sub
        (f := fun r => C145.DelayKernel.firstKernel Q0 rates0 b0 r * g r)
        (g := fun r => C145.DelayKernel.firstKernel Q1 rates1 b1 r * g r)
        ((hk0.mul hg.1.continuous).intervalIntegrable _ _)
        ((hk1.mul hg.1.continuous).intervalIntegrable _ _), heq, sub_self]
  · have hz := continuous_square_zero_of_smooth_product_tests hT
      (fun r s => C145.DelayKernel.delayKernel Q0 rates0 b0 r s -
        C145.DelayKernel.delayKernel Q1 rates1 b1 r s) (hK0.sub hK1) ?_
    · intro r hr s hs
      exact sub_eq_zero.mp (hz r hr s hs)
    · intro g h hg hh
      have heq := hMixed (fun s => g (T - s)) (fun s => h (T - s))
        (smoothTemporalTest_reflect hg) (smoothTemporalTest_reflect hh)
      rw [rawMixed_reflected hT Q0 rates0 b0 hQ0 R0 hR0 hcR0 g h
          hg.1.continuous hh.1.continuous,
        rawMixed_reflected hT Q1 rates1 b1 hQ1 R1 hR1 hcR1 g h
          hg.1.continuous hh.1.continuous] at heq
      have hcont0 : Continuous (fun p : ℝ × ℝ =>
          C145.DelayKernel.delayKernel Q0 rates0 b0 p.1 p.2 * g p.1 * h p.2) :=
        (hK0.mul (hg.1.continuous.comp continuous_fst)).mul
          (hh.1.continuous.comp continuous_snd)
      have hcont1 : Continuous (fun p : ℝ × ℝ =>
          C145.DelayKernel.delayKernel Q1 rates1 b1 p.1 p.2 * g p.1 * h p.2) :=
        (hK1.mul (hg.1.continuous.comp continuous_fst)).mul
          (hh.1.continuous.comp continuous_snd)
      have hc0 : Continuous (fun r : ℝ => ∫ s in (0 : ℝ)..T,
          C145.DelayKernel.delayKernel Q0 rates0 b0 r s * g r * h s) :=
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcont0 0 T
      have hc1 : Continuous (fun r : ℝ => ∫ s in (0 : ℝ)..T,
          C145.DelayKernel.delayKernel Q1 rates1 b1 r s * g r * h s) :=
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcont1 0 T
      simp_rw [sub_mul]
      have hsubinner (r : ℝ) :
          (∫ s in (0 : ℝ)..T,
            C145.DelayKernel.delayKernel Q0 rates0 b0 r s * g r * h s -
            C145.DelayKernel.delayKernel Q1 rates1 b1 r s * g r * h s) =
          (∫ s in (0 : ℝ)..T, C145.DelayKernel.delayKernel Q0 rates0 b0 r s * g r * h s) -
          (∫ s in (0 : ℝ)..T, C145.DelayKernel.delayKernel Q1 rates1 b1 r s * g r * h s) := by
        exact intervalIntegral.integral_sub
          (f := fun s => C145.DelayKernel.delayKernel Q0 rates0 b0 r s * g r * h s)
          (g := fun s => C145.DelayKernel.delayKernel Q1 rates1 b1 r s * g r * h s)
          ((hcont0.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
          ((hcont1.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
      simp_rw [hsubinner]
      rw [intervalIntegral.integral_sub
        (f := fun r => ∫ s in (0 : ℝ)..T, C145.DelayKernel.delayKernel Q0 rates0 b0 r s * g r * h s)
        (g := fun r => ∫ s in (0 : ℝ)..T, C145.DelayKernel.delayKernel Q1 rates1 b1 r s * g r * h s)
        (hc0.intervalIntegrable _ _) (hc1.intervalIntegrable _ _), heq, sub_self]


end C145.ObservedKernelRecovery
end

end

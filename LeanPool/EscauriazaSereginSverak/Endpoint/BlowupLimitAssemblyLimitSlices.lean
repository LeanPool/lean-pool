/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblySourceAE
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupSliceBound
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# The critical slice bound of the blow-up limit

Every slice of the rescaled trace has global L³ norm at most the trace
bound, and strong local L³ convergence passes this bound to almost every
negative-time slice of the limit (`prop:blowup-limit`, the bound
u ∈ L^∞((-∞,0); L³)).
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Every slice of the rescaled trace has global L³ norm bounded by the
trace bound. -/
theorem blowupLimitAssembly_trace_slice_Lthree
    (W : Vec3 × Icc (-(3 / 4 : ℝ) ^ 2) 0 → Vec3) (M : ℝ)
    (hsource : ∀ t,
      MemLp ((vec3Ball (0 : Vec3) (3 / 4 : ℝ)).indicator
        (fun x => W (x, t))) 3 volume ∧
      eLpNorm (fun x => vec3EuclideanNorm
        ((vec3Ball (0 : Vec3) (3 / 4 : ℝ)).indicator
          (fun y => W (y, t)) x)) 3 volume ≤ ENNReal.ofReal M)
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r) (t : ℝ) :
    eLpNorm (fun x => vec3EuclideanNorm
      (blowupLimitTraceRescaling W x₀ t₀ r (x,t))) 3 volume ≤ ENNReal.ofReal M := by
  by_cases hτ : t₀ + r ^ 2 * t ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0
  · set τI : Icc (-(3 / 4 : ℝ) ^ 2) 0 := ⟨t₀ + r ^ 2 * t, hτ⟩
    set g : Vec3 → Vec3 := (vec3Ball (0 : Vec3) (3 / 4 : ℝ)).indicator
      (fun y => W (y,τI))
    have hfun : (fun x => blowupLimitTraceRescaling W x₀ t₀ r (x,t)) =
        fun x => r • g (x₀ + r • x) := by
      funext x
      by_cases hx : x₀ + r • x ∈ vec3Ball (0 : Vec3) (3 / 4 : ℝ)
      · have hx' : vec3EuclideanNorm (x₀ + r • x) < 3 / 4 := by
          have h := hx
          rw [mem_vec3Ball, sub_zero] at h
          exact h
        simp [blowupLimitTraceRescaling, blowupLimitTraceZeroExtension,
          parabolicTranslate, parabolicScale, g, τI, hx', hτ]
      · have hx' : ¬ vec3EuclideanNorm (x₀ + r • x) < 3 / 4 := by
          intro h
          apply hx
          rw [mem_vec3Ball, sub_zero]
          exact h
        simp [blowupLimitTraceRescaling, blowupLimitTraceZeroExtension,
          parabolicTranslate, parabolicScale, g, hx']
    have hnorm : (fun x => vec3EuclideanNorm
        (blowupLimitTraceRescaling W x₀ t₀ r (x,t))) =
        fun x => vec3EuclideanNorm (r • g (x₀ + r • x)) := by
      funext x
      rw [congrFun hfun x]
    rw [hnorm, blowup_rescaled_velocitySlice_eLpNorm_three_eq g
      (hsource τI).1.aestronglyMeasurable x₀ r hr]
    exact (hsource τI).2
  · have hzero : (fun x => vec3EuclideanNorm
        (blowupLimitTraceRescaling W x₀ t₀ r (x,t))) = fun _ => (0 : ℝ) := by
      funext x
      simp [blowupLimitTraceRescaling, blowupLimitTraceZeroExtension,
        parabolicTranslate, parabolicScale, hτ, vec3EuclideanNorm_zero]
    rw [hzero]
    simp

/-- Strong local L³ convergence of fields with uniformly bounded global
L³ slices bounds almost every negative-time slice of the limit. -/
theorem blowupLimitAssembly_slice_Lthree_of_local_convergence
    (U : ParabolicPoint → Vec3) (hU : Measurable U)
    (v : ℕ → ParabolicPoint → Vec3) (hv : ∀ k, Measurable (v k))
    (M : ℝ≥0∞)
    (hvslice : ∀ k t, eLpNorm (fun x => vec3EuclideanNorm (v k (x, t))) 3 volume ≤ M)
    (hconv : ∀ N : ℕ, Tendsto (fun k => eLpNorm (fun z => v k z - U z) 3
      (volume.restrict (vec3Ball (0 : Vec3) ((N : ℝ) + 1) ×ˢ
        Ioo (-((N : ℝ) + 1)) 0))) atTop (nhds 0)) :
    ∀ᵐ t ∂(volume.restrict (Iio (0 : ℝ))),
      eLpNorm (fun x => vec3EuclideanNorm (U (x,t))) 3 volume ≤ M := by
  have hlocal : ∀ N : ℕ, ∀ᵐ t ∂(volume : Measure ℝ),
      t ∈ Ioo (-((N : ℝ) + 1)) 0 →
        eLpNorm (fun x => vec3EuclideanNorm (U (x,t))) 3
          (volume.restrict (vec3Ball (0 : Vec3) ((N : ℝ) + 1))) ≤ M := by
    intro N
    set B : Set Vec3 := vec3Ball (0 : Vec3) ((N : ℝ) + 1)
    set J : Set ℝ := Ioo (-((N : ℝ) + 1)) 0
    have hmeas := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) (hconv N)
    obtain ⟨σ, _, hae⟩ := hmeas.exists_seq_tendsto_ae
    have hslices := blowupLimitAssembly_ae_slices_of_ae_spaceTime
      (Ω := B) (I := J) (p := fun z => Tendsto (fun n => v (σ n) z) atTop (nhds (U z)))
      hae
    rw [← ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hslices] with t ht
    have hfatou := MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 3) (μ := volume.restrict B)
      (f := fun n x => vec3EuclideanNorm (v (σ n) (x,t)))
      (fun n => (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.measurable.comp
        ((hv (σ n)).comp measurable_prodMk_right)).aestronglyMeasurable)
      (fun x => vec3EuclideanNorm (U (x,t)))
      (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.measurable.comp
        (hU.comp measurable_prodMk_right)).aestronglyMeasurable
      (by
        filter_upwards [ht] with x hx
        exact (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.tendsto _).comp hx)
    refine hfatou.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_))
    exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hvslice (σ n) t)
  have hall : ∀ᵐ t ∂(volume : Measure ℝ), ∀ N : ℕ,
      t ∈ Ioo (-((N : ℝ) + 1)) 0 →
        eLpNorm (fun x => vec3EuclideanNorm (U (x,t))) 3
          (volume.restrict (vec3Ball (0 : Vec3) ((N : ℝ) + 1))) ≤ M :=
    ae_all_iff.2 hlocal
  rw [ae_restrict_iff' measurableSet_Iio]
  filter_upwards [hall] with t ht htneg
  set f : Vec3 → ℝ := fun x => vec3EuclideanNorm (U (x,t))
  let g : ℕ → Vec3 → ℝ := fun N => (vec3Ball (0 : Vec3) ((N : ℝ) + 1)).indicator f
  have hfm : Measurable f :=
    CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.measurable.comp
      (hU.comp measurable_prodMk_right)
  have hgm : ∀ N, AEStronglyMeasurable (g N) volume := fun N =>
    (hfm.indicator (isOpen_vec3Ball _ _).measurableSet).aestronglyMeasurable
  have hglim : ∀ x, Tendsto (fun N => g N x) atTop (nhds (f x)) := by
    intro x
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (vec3EuclideanNorm x)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N₀] with N hN
    have hx : x ∈ vec3Ball (0 : Vec3) ((N : ℝ) + 1) := by
      rw [mem_vec3Ball, sub_zero]
      have : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
      linarith only [hN₀, this]
    simp only [g, indicator_of_mem hx]
  have hfatou := MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 3) (μ := volume) hgm f
    hfm.aestronglyMeasurable (Eventually.of_forall hglim)
  refine hfatou.trans (liminf_le_of_frequently_le' ?_)
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (-t)
  refine (eventually_ge_atTop N₀).frequently.mono fun N hN => ?_
  have htN : t ∈ Ioo (-((N : ℝ) + 1)) 0 := by
    have : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
    exact ⟨by linarith only [hN₀, this], htneg⟩
  simp only [g]
  rw [eLpNorm_indicator_eq_eLpNorm_restrict (isOpen_vec3Ball _ _).measurableSet]
  exact ht N htN

end ESS

end

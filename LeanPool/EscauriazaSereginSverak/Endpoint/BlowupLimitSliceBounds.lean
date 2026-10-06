/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitTraceField
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupSliceBound
public import LeanPool.CaffarelliKohnNirenberg.Foundation.RellichBallsCore

/-!
# Compact spatial slice bounds for the blow-up trace

The all-time measurable trace has uniformly bounded rescaled `L²` slices on
each compact spatial set. This is the slice input to
`CKN.Leray.lem_compactness`.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A uniformly bounded source `L³` trace gives a uniform rescaled local
`L²` bound on every time slice. -/
theorem blowup_limit_trace_rescaled_compact_slice_bound
    (W : Vec3 × Icc (-(3 / 4 : ℝ) ^ 2) 0 → Vec3)
    (M : ℝ)
    (hsource : ∀ t,
      MemLp ((vec3Ball (0 : Vec3) (3 / 4 : ℝ)).indicator
        (fun x => W (x,t))) 3 volume ∧
      eLpNorm (fun x => vec3EuclideanNorm
        ((vec3Ball (0 : Vec3) (3 / 4 : ℝ)).indicator
          (fun y => W (y,t)) x)) 3 volume ≤ ENNReal.ofReal M)
    (x₀ : Vec3) (r : ℝ) (hr : 0 < r)
    (C : Set Vec3) (hC : IsCompact C) :
    ∀ t : Icc (-(3 / 4 : ℝ) ^ 2) 0,
      (∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm
        (r • (vec3Ball (0 : Vec3) (3 / 4 : ℝ)).indicator
          (fun y => W (y,t)) (x₀ + r • x))) ^ (2 : ℝ) ∂volume) ≤
        (ENNReal.ofReal M * (volume C) ^ (1 / 6 : ℝ)) ^ (2 : ℝ) := by
  intro t
  let B : Set Vec3 := vec3Ball (0 : Vec3) (3 / 4 : ℝ)
  let g : Vec3 → Vec3 := B.indicator (fun y => W (y,t))
  let f : Vec3 → ℝ := fun x => vec3EuclideanNorm (r • g (x₀ + r • x))
  let μ : Measure Vec3 := volume.restrict C
  have hμfinite : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact IsCompact.measure_lt_top (μ := volume) hC
  let := hμfinite
  have hgm : AEStronglyMeasurable g volume := by
    simpa [g, B] using (hsource t).1.aestronglyMeasurable
  have hfm : AEStronglyMeasurable f μ := by
    change AEStronglyMeasurable (fun x => vec3EuclideanNorm
      (r • g (x₀ + r • x))) μ
    exact (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      (blowup_rescaled_velocitySlice_aestronglyMeasurable g hgm x₀ r hr)).restrict
  have hglobal : eLpNorm f 3 volume ≤ ENNReal.ofReal M := by
    change eLpNorm (fun x => vec3EuclideanNorm
      (r • g (x₀ + r • x))) 3 volume ≤ ENNReal.ofReal M
    rw [blowup_rescaled_velocitySlice_eLpNorm_three_eq g hgm x₀ r hr]
    simpa [g, B] using (hsource t).2
  have hlocal : eLpNorm f 3 μ ≤ ENNReal.ofReal M := by
    exact (eLpNorm_mono_measure f Measure.restrict_le_self).trans hglobal
  have hcompare := eLpNorm_le_eLpNorm_mul_rpow_measure_univ_of_pos
    (μ := μ) (f := f) (p := (2 : ℝ≥0∞)) (q := (3 : ℝ≥0∞))
    (by norm_num) (by norm_num)
  have htwo : eLpNorm f 2 μ ≤
      ENNReal.ofReal M * (volume C) ^ (1 / 6 : ℝ) := by
    calc
      eLpNorm f 2 μ ≤ eLpNorm f 3 μ * (μ Set.univ) ^ (1 / 6 : ℝ) := by
        convert hcompare using 1
        norm_num
      _ ≤ ENNReal.ofReal M * (volume C) ^ (1 / 6 : ℝ) := by
        rw [show μ Set.univ = volume C by simp [μ]]
        gcongr
  have hsq : eLpNorm f (2 : NNReal) μ ^ (2 : ℝ) =
      ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ :=
    eLpNorm_nnreal_pow_eq_lintegral (by norm_num : (2 : NNReal) ≠ 0) hfm
  have hsq' : (eLpNorm f 2 μ) ^ (2 : ℝ) =
      ∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm
        (r • g (x₀ + r • x))) ^ (2 : ℝ) ∂volume := by
    simpa [f, μ, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (vec3EuclideanNorm_nonneg _)] using hsq
  rw [← hsq']
  gcongr

/-- Every fixed terminal trace slice has strongly vanishing local `L²`
rescalings, by absolute continuity of its source `L³` integral. -/
theorem blowup_limit_trace_terminal_rescaling_tendsto_zero
    (W : Vec3 × Icc (-(3 / 4 : ℝ) ^ 2) 0 → Vec3)
    (hsource : ∀ t,
      MemLp ((vec3Ball (0 : Vec3) (3 / 4 : ℝ)).indicator
        (fun x => W (x,t))) 3 volume)
    (t₀ : Icc (-(3 / 4 : ℝ) ^ 2) 0)
    (x₀ c : Vec3) (r : ℕ → ℝ)
    (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (nhds 0)) :
    Tendsto (fun k => eLpNorm
      (fun x => r k • (vec3Ball (0 : Vec3) (3 / 4 : ℝ)).indicator
        (fun y => W (y,t₀)) (x₀ + r k • x)) 2
      (volume.restrict (vec3Ball c 1))) atTop (nhds 0) := by
  let B : Set Vec3 := vec3Ball (0 : Vec3) (3 / 4 : ℝ)
  let g : Vec3 → Vec3 := B.indicator (fun y => W (y,t₀))
  have hg : MemLp g 3 volume := by simpa [g, B] using hsource t₀
  have hu : MemLp g 3 (volume.restrict (Set.univ : Set Vec3)) := by
    simpa using hg
  have h := blowup_terminal_local_trace_rescaled_tendsto_zero
    (Set.univ : Set Vec3) MeasurableSet.univ g hu x₀ c r hr hr0
  simpa [g, B] using h

end ESS

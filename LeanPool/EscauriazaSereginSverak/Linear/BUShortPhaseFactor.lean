/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortNormalDerivatives

/-!
# Derivatives of the phase transition factor

The smooth transition in the shifted normal phase is differentiated as
a one-dimensional composition with the extended phase.
-/

public section


open Filter CKN CKN.Foundation.Parabolic
open scoped Topology

noncomputable section

namespace ESS

/-- The argument of the canonical transition profile in the normal
phase factor. -/
@[expose] def buShortPhaseArgument (scale y s : ℝ) : ℝ :=
  12 * ((buShortFExt y s - buShortB scale) / buShortB scale) + 9

/-- The smooth phase transition as a function of height and time. -/
@[expose] def buShortPhaseFactor (scale y s : ℝ) : ℝ :=
  smoothTransitionProfile (buShortPhaseArgument scale y s)

/-- The first height derivative of the smooth phase is differentiable
above the active height threshold. -/
theorem buShortFExt_height_deriv_differentiable
    {y s : ℝ} (hy : 2 < y) (hs : 1 / 2 ≤ s) :
    DifferentiableAt ℝ
      (fun r : ℝ => deriv (fun q : ℝ => buShortFExt q s) r) y := by
  have hpow : DifferentiableAt ℝ (fun r : ℝ => r ^ (1 / 2 : ℝ)) y :=
    (Real.hasDerivAt_rpow_const (p := (1 / 2 : ℝ))
      (Or.inl (show y ≠ 0 by linarith only [hy]))).differentiableAt
  have hdiff : DifferentiableAt ℝ
      (fun r : ℝ => (3 / 2 : ℝ) * (1 - s) *
        r ^ (1 / 2 : ℝ) * s ^ (-(3 / 4 : ℝ))) y := by
    fun_prop
  have heq :
      (fun r : ℝ => deriv (fun q : ℝ => buShortFExt q s) r) =ᶠ[𝓝 y]
      (fun r : ℝ => (3 / 2 : ℝ) * (1 - s) *
        r ^ (1 / 2 : ℝ) * s ^ (-(3 / 4 : ℝ))) := by
    filter_upwards [Ioi_mem_nhds hy] with r hr
    rw [buShortFExt_deriv_height_eq hr hs]
    exact buShortF_deriv_height
      (lt_trans (by norm_num : (0 : ℝ) < 2) hr)
  exact hdiff.congr_of_eventuallyEq heq

/-- The height derivative of the phase argument. -/
theorem buShortPhaseArgument_deriv_height (scale y s : ℝ) :
    deriv (fun r : ℝ => buShortPhaseArgument scale r s) y =
      12 / buShortB scale *
        deriv (fun r : ℝ => buShortFExt r s) y := by
  have hF : DifferentiableAt ℝ (fun r : ℝ => buShortFExt r s) y := by
    have hpair : Differentiable ℝ (fun r : ℝ => ((r, s) : ℝ × ℝ)) :=
      differentiable_id.prodMk (differentiable_const s)
    exact ((buShortFExt_smooth.differentiable (by simp)).comp hpair) y
  have h := (((hF.hasDerivAt.sub_const (buShortB scale)).div_const
    (buShortB scale)).const_mul 12).add_const 9
  change deriv (fun r : ℝ =>
      12 * ((buShortFExt r s - buShortB scale) / buShortB scale) + 9) y = _
  convert h.deriv using 1
  ring

/-- The time derivative of the phase argument. -/
theorem buShortPhaseArgument_deriv_time (scale y s : ℝ) :
    deriv (fun t : ℝ => buShortPhaseArgument scale y t) s =
      12 / buShortB scale *
        deriv (fun t : ℝ => buShortFExt y t) s := by
  have hF : DifferentiableAt ℝ (fun t : ℝ => buShortFExt y t) s := by
    have hpair : Differentiable ℝ (fun t : ℝ => ((y, t) : ℝ × ℝ)) :=
      (differentiable_const y).prodMk differentiable_id
    exact ((buShortFExt_smooth.differentiable (by simp)).comp hpair) s
  have h := (((hF.hasDerivAt.sub_const (buShortB scale)).div_const
    (buShortB scale)).const_mul 12).add_const 9
  change deriv (fun t : ℝ =>
      12 * ((buShortFExt y t - buShortB scale) / buShortB scale) + 9) s = _
  convert h.deriv using 1
  ring

/-- The height derivative of the phase transition factor. -/
theorem buShortPhaseFactor_deriv_height (scale y s : ℝ) :
    deriv (fun r : ℝ => buShortPhaseFactor scale r s) y =
      deriv smoothTransitionProfile (buShortPhaseArgument scale y s) *
        (12 / buShortB scale *
          deriv (fun r : ℝ => buShortFExt r s) y) := by
  have harg : DifferentiableAt ℝ
      (fun r : ℝ => buShortPhaseArgument scale r s) y := by
    have hF : Differentiable ℝ (fun r : ℝ => buShortFExt r s) := by
      have hpair : ContDiff ℝ (⊤ : ℕ∞)
          (fun r : ℝ => ((r, s) : ℝ × ℝ)) :=
        contDiff_id.prodMk contDiff_const
      exact (buShortFExt_smooth.comp hpair).differentiable (by simp)
    unfold buShortPhaseArgument
    fun_prop
  have h := (smoothTransitionProfile.smooth.differentiable (by simp)
    (buShortPhaseArgument scale y s)).hasDerivAt.comp y harg.hasDerivAt
  have h' : deriv (fun r => smoothTransitionProfile
      (buShortPhaseArgument scale r s)) y =
      deriv smoothTransitionProfile (buShortPhaseArgument scale y s) *
        deriv (fun r => buShortPhaseArgument scale r s) y := by
    simpa only [Function.comp_def] using h.deriv
  change deriv (fun r => smoothTransitionProfile
      (buShortPhaseArgument scale r s)) y = _
  rw [h', buShortPhaseArgument_deriv_height]

/-- The time derivative of the phase transition factor. -/
theorem buShortPhaseFactor_deriv_time (scale y s : ℝ) :
    deriv (fun t : ℝ => buShortPhaseFactor scale y t) s =
      deriv smoothTransitionProfile (buShortPhaseArgument scale y s) *
        (12 / buShortB scale *
          deriv (fun t : ℝ => buShortFExt y t) s) := by
  have harg : DifferentiableAt ℝ
      (fun t : ℝ => buShortPhaseArgument scale y t) s := by
    have hF : Differentiable ℝ (fun t : ℝ => buShortFExt y t) := by
      have hpair : ContDiff ℝ (⊤ : ℕ∞)
          (fun t : ℝ => ((y, t) : ℝ × ℝ)) :=
        contDiff_const.prodMk contDiff_id
      exact (buShortFExt_smooth.comp hpair).differentiable (by simp)
    unfold buShortPhaseArgument
    fun_prop
  have h := (smoothTransitionProfile.smooth.differentiable (by simp)
    (buShortPhaseArgument scale y s)).hasDerivAt.comp s harg.hasDerivAt
  have h' : deriv (fun t => smoothTransitionProfile
      (buShortPhaseArgument scale y t)) s =
      deriv smoothTransitionProfile (buShortPhaseArgument scale y s) *
        deriv (fun t => buShortPhaseArgument scale y t) s := by
    simpa only [Function.comp_def] using h.deriv
  change deriv (fun t => smoothTransitionProfile
      (buShortPhaseArgument scale y t)) s = _
  rw [h', buShortPhaseArgument_deriv_time]

/-- The second height derivative of the phase transition factor on the
active half-space strip. -/
theorem buShortPhaseFactor_deriv_height_twice
    {scale y s : ℝ} (hy : 2 < y) (hs : 1 / 2 ≤ s) :
    deriv (fun r : ℝ =>
      deriv (fun q : ℝ => buShortPhaseFactor scale q s) r) y =
      deriv (deriv smoothTransitionProfile)
          (buShortPhaseArgument scale y s) *
        (12 / buShortB scale *
          deriv (fun r : ℝ => buShortFExt r s) y) ^ 2 +
      deriv smoothTransitionProfile
          (buShortPhaseArgument scale y s) *
        (12 / buShortB scale *
          deriv (fun r : ℝ =>
            deriv (fun q : ℝ => buShortFExt q s) r) y) := by
  have hfun :
      (fun r : ℝ =>
        deriv (fun q : ℝ => buShortPhaseFactor scale q s) r) =
      (fun r => deriv smoothTransitionProfile
          (buShortPhaseArgument scale r s) *
        (12 / buShortB scale *
          deriv (fun q : ℝ => buShortFExt q s) r)) := by
    funext r
    exact buShortPhaseFactor_deriv_height scale r s
  rw [hfun]
  have hprofile : Differentiable ℝ (deriv smoothTransitionProfile) := by
    have h := smoothTransitionProfile.smooth.differentiable_iteratedDeriv 1
      (by simp)
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h
  have harg : DifferentiableAt ℝ
      (fun r : ℝ => buShortPhaseArgument scale r s) y := by
    have hF : Differentiable ℝ (fun r : ℝ => buShortFExt r s) := by
      have hpair : ContDiff ℝ (⊤ : ℕ∞)
          (fun r : ℝ => ((r, s) : ℝ × ℝ)) :=
        contDiff_id.prodMk contDiff_const
      exact (buShortFExt_smooth.comp hpair).differentiable (by simp)
    unfold buShortPhaseArgument
    fun_prop
  have hfirst := (hprofile _).hasDerivAt.comp y harg.hasDerivAt
  have hsecond :=
    ((buShortFExt_height_deriv_differentiable hy hs).hasDerivAt.const_mul
      (12 / buShortB scale))
  have hprod := hfirst.mul hsecond
  have hprod' :
      deriv (fun r => deriv smoothTransitionProfile
          (buShortPhaseArgument scale r s) *
        (12 / buShortB scale *
          deriv (fun q : ℝ => buShortFExt q s) r)) y =
        deriv (deriv smoothTransitionProfile)
            (buShortPhaseArgument scale y s) *
          deriv (fun r => buShortPhaseArgument scale r s) y *
            (12 / buShortB scale *
              deriv (fun q : ℝ => buShortFExt q s) y) +
          deriv smoothTransitionProfile
            (buShortPhaseArgument scale y s) *
            (12 / buShortB scale *
              deriv (fun r : ℝ =>
                deriv (fun q : ℝ => buShortFExt q s) r) y) := by
    change HasDerivAt
      (fun r => deriv smoothTransitionProfile
        (buShortPhaseArgument scale r s) *
          (12 / buShortB scale *
            deriv (fun q : ℝ => buShortFExt q s) r)) _ y at hprod
    exact hprod.deriv
  rw [hprod', buShortPhaseArgument_deriv_height]
  ring

end ESS

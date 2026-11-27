/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.ComplexEuclideanVolume
public import LeanPool.VacuumBellSeparation.Shell.HolomorphicVolumeSubmean
public import Mathlib.MeasureTheory.Group.Measure

/-!
# Submean in the actual six-real-dimensional shell coordinate space

The centered complex polydisc is transported by a genuine volume
preserving affine coordinate map. A three-coordinate polydisc of radius
R lies in the Euclidean ball of radius 2R; the resulting local estimate
therefore applies directly to the actual shell chart domain.
-/

@[expose] public section

namespace VacuumBellSeparation

open Complex MeasureTheory Metric Set
open scoped ENNReal BigOperators

/-- Shell coordinate polydisc with membership specified by `{w | ∀ i, ‖w i - c i‖ < R}`. -/
def shellCoordinatePolydisc (c : ShellEuclideanDomain) (R : ℝ) : Set ShellEuclideanDomain :=
  {w | ∀ i, ‖w i - c i‖ < R}

/-- Shell coordinate closed polydisc with membership specified by `{w | ∀ i, ‖w i - c i‖ ≤ R}`. -/
def shellCoordinateClosedPolydisc (c : ShellEuclideanDomain) (R : ℝ) :
    Set ShellEuclideanDomain := {w | ∀ i, ‖w i - c i‖ ≤ R}

theorem isOpen_shellCoordinatePolydisc (c : ShellEuclideanDomain) (R : ℝ) :
    IsOpen (shellCoordinatePolydisc c R) := by
  rw [show shellCoordinatePolydisc c R =
      ⋂ i : Fin 3, {w : ShellEuclideanDomain | ‖w i - c i‖ < R} by
    ext w
    simp only [shellCoordinatePolydisc, Set.mem_ofPred_eq, Set.mem_iInter]]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) i).sub
    continuous_const).norm continuous_const

theorem shellCoordinateClosedPolydisc_subset_ball {c : ShellEuclideanDomain} {R : ℝ}
    (hR : 0 < R) : shellCoordinateClosedPolydisc c R ⊆ ball c (2 * R) := by
  intro w hw
  have hs : ‖w - c‖ ^ 2 ≤ 3 * R ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _ : Fin 3, R ^ 2 := Finset.sum_le_sum fun i _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hw i) 2
      _ = _ := by simp
  rw [mem_ball, dist_eq_norm]
  nlinarith [sq_nonneg (‖w - c‖), norm_nonneg (w - c)]

theorem shellCoordinatePolydisc_subset_ball {c : ShellEuclideanDomain} {R : ℝ}
    (hR : 0 < R) : shellCoordinatePolydisc c R ⊆ ball c (2 * R) :=
  fun _ hw => shellCoordinateClosedPolydisc_subset_ball hR (fun i => (hw i).le)

theorem shellCoordinate_submean_sq {R : ℝ} (hR : 0 < R)
    (F : ShellEuclideanDomain → ℂ) (hm : Measurable F) (c : ShellEuclideanDomain)
    (hF : ∀ w ∈ shellCoordinateClosedPolydisc c R, DifferentiableAt ℂ F w) :
    ENNReal.ofReal (‖F c‖ ^ 2) * volume (ball (0 : ℂ) R) ^ 3 ≤
      ∫⁻ w in shellCoordinatePolydisc c R, ENNReal.ofReal (‖F w‖ ^ 2) := by
  let e : (Fin 3 → ℂ) → ShellEuclideanDomain := fun z => c + shellEuclideanCoordinates.symm z
  have he : MeasurePreserving e :=
    (measurePreserving_add_left (volume : Measure ShellEuclideanDomain) c).comp
      shellEuclideanCoordinates_symm_measurePreserving
  have hpre : e ⁻¹' shellCoordinatePolydisc c R = coordinateOpenPolydisc 3 R := by
    ext z
    simp only [Set.mem_preimage, shellCoordinatePolydisc, Set.mem_ofPred_eq,
      e, shellEuclideanCoordinates, PiLp.add_apply, PiLp.continuousLinearEquiv_symm_apply,
      add_sub_cancel_left, coordinateOpenPolydisc, Set.mem_pi, Set.mem_univ,
      forall_true_left, mem_ball_zero_iff]
  have hd : ∀ z ∈ Gaussian.coordinateClosedPolydisc 3 R,
      DifferentiableAt ℂ (fun z => F (e z)) z := by
    intro z hz
    have hez : e z ∈ shellCoordinateClosedPolydisc c R := by
      intro i
      simpa only [e, shellEuclideanCoordinates, PiLp.add_apply,
        PiLp.continuousLinearEquiv_symm_apply, PiLp.toLp_apply, add_sub_cancel_left] using hz i
    exact (hF (e z) hez).comp z
      ((differentiableAt_const c).add shellEuclideanCoordinates.symm.differentiableAt)
  have hs := holomorphic_volume_submean_sq 3 hR (fun z => F (e z))
    (hm.comp he.measurable) hd
  have hzero : e 0 = c := by simp only [e, map_zero, add_zero]
  rw [hzero] at hs
  have hchange := he.setLIntegral_comp_preimage
    (isOpen_shellCoordinatePolydisc c R).measurableSet
    (ENNReal.measurable_ofReal.comp (hm.norm.pow_const 2))
  rw [hpre] at hchange
  exact hs.trans_eq hchange

theorem shellEuclidean_ball_submean_sq {R : ℝ} (hR : 0 < R)
    (F : ShellEuclideanDomain → ℂ) (hm : Measurable F) (c : ShellEuclideanDomain)
    (hF : ∀ w ∈ ball c (2 * R), DifferentiableAt ℂ F w) :
    ENNReal.ofReal (‖F c‖ ^ 2) * volume (ball (0 : ℂ) R) ^ 3 ≤
      ∫⁻ w in ball c (2 * R), ENNReal.ofReal (‖F w‖ ^ 2) := by
  apply (shellCoordinate_submean_sq hR F hm c
    (fun w hw => hF w (shellCoordinateClosedPolydisc_subset_ball hR hw))).trans
  exact lintegral_mono_set (shellCoordinatePolydisc_subset_ball hR)

end VacuumBellSeparation

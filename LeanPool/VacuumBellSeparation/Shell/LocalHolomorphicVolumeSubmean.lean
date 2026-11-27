/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.EuclideanShellSubmean

/-!
# Local holomorphic submean without global chart regularity

A chart expression need only be holomorphic on its actual open domain.
Its zero extension is measurable and agrees locally, so the genuine
Euclidean volume estimate requires no global principal-root continuity.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

theorem local_shellEuclidean_submean_sq {D : Set ShellEuclideanDomain} (hD : IsOpen D)
    (F : ShellEuclideanDomain → ℂ)
    (hF : ∀ w ∈ D, DifferentiableAt ℂ F w)
    {c : ShellEuclideanDomain} {R : ℝ} (hR : 0 < R)
    (hsub : ball c (2 * R) ⊆ D) :
    ENNReal.ofReal (‖F c‖ ^ 2) * volume (ball (0 : ℂ) R) ^ 3 ≤
      ∫⁻ w in ball c (2 * R), ENNReal.ofReal (‖F w‖ ^ 2) := by
  classical
  let G : ShellEuclideanDomain → ℂ := D.piecewise F (fun _ => 0)
  have hcont : ContinuousOn F D := fun w hw => (hF w hw).continuousAt.continuousWithinAt
  have hm : Measurable G := hcont.measurable_piecewise continuousOn_const hD.measurableSet
  have hlocal (w : ShellEuclideanDomain) (hw : w ∈ D) : G =ᶠ[𝓝 w] F := by
    filter_upwards [hD.mem_nhds hw] with x hx
    exact Set.piecewise_eq_of_mem D F (fun _ => 0) hx
  have hc : c ∈ D := hsub (mem_ball_self (by positivity))
  have hs := shellEuclidean_ball_submean_sq hR G hm c
    (fun w hw => (hF w (hsub hw)).congr_of_eventuallyEq (hlocal w (hsub hw)))
  have hGc : G c = F c := Set.piecewise_eq_of_mem D F (fun _ => 0) hc
  rw [hGc] at hs
  convert hs using 1
  apply setLIntegral_congr_fun measurableSet_ball
  intro w hw
  dsimp only
  rw [show G w = F w from Set.piecewise_eq_of_mem D F (fun _ => 0) (hsub hw)]

end VacuumBellSeparation

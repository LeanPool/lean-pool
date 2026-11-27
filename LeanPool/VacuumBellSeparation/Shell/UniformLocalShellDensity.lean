/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.InducedShellMassContinuity

/-!
# Genuine chart-density bounds on a mass-coordinate neighbourhood

The compact neighbourhood lives in the actual joint domain. Its mass
coordinate may be zero. The constants are chosen before the varying
mass, and are bounds for the derivative of the original shell chart.
-/

@[expose] public section

namespace VacuumBellSeparation

open Metric Filter Topology

theorem inducedShellChartDensity_joint_local_bounds {m : ℝ}
    (Λ : Spacetime ≃L[ℝ] Spacetime) {w : ShellEuclideanDomain}
    (hw : w ∈ euclideanShellChartDomain m) :
    ∃ ε c C : ℝ, 0 < ε ∧ 0 < c ∧ 0 < C ∧
      ∀ t : ℝ, |t - m| ≤ ε → ∀ x : ShellEuclideanDomain, dist x w ≤ ε →
        x ∈ euclideanShellChartDomain t ∧
        c ≤ inducedShellChartDensity t Λ x ∧ inducedShellChartDensity t Λ x ≤ C := by
  let d := inducedShellChartDensity m Λ w
  have hd : 0 < d := inducedShellChartDensity_pos Λ hw
  have hdom : ∀ᶠ q in nhds (m, w), q ∈ euclideanShellJointDomain :=
    isOpen_euclideanShellJointDomain.mem_nhds hw
  have hc : ContinuousAt (fun q : ℝ × ShellEuclideanDomain =>
      inducedShellChartDensity q.1 Λ q.2) (m, w) :=
    (continuousOn_inducedShellChartDensity_joint Λ).continuousAt hdom
  have hlo : ∀ᶠ q in nhds (m, w), d / 2 < inducedShellChartDensity q.1 Λ q.2 :=
    continuousAt_const.eventually_lt hc (half_lt_self hd)
  have hhi : ∀ᶠ q in nhds (m, w), inducedShellChartDensity q.1 Λ q.2 < d + 1 :=
    hc.eventually_lt continuousAt_const (by dsimp only [d]; linarith)
  obtain ⟨r, hr, hh⟩ := Metric.eventually_nhds_iff.mp (hdom.and (hlo.and hhi))
  refine ⟨r / 2, d / 2, d + 1, half_pos hr, half_pos hd, by positivity, ?_⟩
  intro t ht x hx
  have hdist : dist (t, x) (m, w) < r := by
    rw [Prod.dist_eq, Real.dist_eq]
    exact (max_le ht hx).trans_lt (half_lt_self hr)
  exact ⟨(hh hdist).1, (hh hdist).2.1.le, (hh hdist).2.2.le⟩

end VacuumBellSeparation

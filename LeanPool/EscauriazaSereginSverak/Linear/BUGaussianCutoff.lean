/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianShiftData
public import LeanPool.EscauriazaSereginSverak.Linear.UCCutoffOperatorSq
public import LeanPool.EscauriazaSereginSverak.Linear.BUZeroExtendWeak

/-!
# A cutoff on the positive-time Gaussian cylinder

The initial transition is translated to the positive starting face in
`lem:bu-gaussian`, so the Gaussian weight remains bounded on its support.
-/

public section


open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The Gaussian cutoff shifted to start at time `1/6` and stopped before time `2`.
(`lem:bu-gaussian#cutoff-construction`). -/
@[expose] def buGaussianShiftedCutoff (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ)
    (z : ParabolicPoint) : ℝ :=
  ucGaussianCutoff ρ hρ ε ((buGaussianTimeShiftPoint (1 / 6)).symm z)

/-- The scalar shifted cutoff is smooth. -/
theorem buGaussian_shiftedCutoff_smooth (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => buGaussianShiftedCutoff ρ hρ ε z) := by
  have hmap : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => (z.1, z.2 - 1 / 6)) := by fun_prop
  have hbase := (ucGaussianCutoff_smooth ρ hρ ε).comp hmap
  have hpoint (z : Vec3 × ℝ) :
      (buGaussianTimeShiftPoint (1 / 6)).symm
          (show ParabolicPoint from z) =
        (z.1, z.2 - 1 / 6) :=
    buGaussian_timeShift_point_symm_apply (1 / 6) (show ParabolicPoint from z)
  have heq : (fun z : Vec3 × ℝ => buGaussianShiftedCutoff ρ hρ ε z) =
      (fun z => ucGaussianCutoff ρ hρ ε (z.1, z.2 - 1 / 6)) := by
    funext z
    change ucGaussianCutoff ρ hρ ε
        ((buGaussianTimeShiftPoint (1 / 6)).symm (show ParabolicPoint from z)) = _
    rw [hpoint z]
  rw [heq]
  exact hbase

/-- The shifted cutoff has compact support. -/
theorem buGaussian_shiftedCutoff_hasCompactSupport
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) :
    HasCompactSupport (buGaussianShiftedCutoff ρ hρ ε) := by
  let T := buGaussianTimeShiftPoint (1 / 6)
  let base : ParabolicPoint → ℝ := fun z => ucGaussianCutoff ρ hρ ε (T.symm z)
  have hbase : HasCompactSupport base := by
    dsimp [base]
    exact (ucGaussianCutoff_hasCompactSupport hρ hε).comp_homeomorph T.symm
  change HasCompactSupport base
  exact hbase

/-- The topological support of the shifted cutoff lies in the positive-time
Gaussian cylinder. -/
theorem buGaussian_shiftedCutoff_tsupport_subset
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) :
    tsupport (buGaussianShiftedCutoff ρ hρ ε) ⊆
      spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2) := by
  let T := buGaussianTimeShiftPoint (1 / 6)
  have hbase : tsupport (fun z : ParabolicPoint =>
      ucGaussianCutoff ρ hρ ε (T.symm z)) ⊆
      spaceTimeSet (vec3Ball 0 ρ) (Ioi (1 / 6)) := by
    change tsupport (ucGaussianCutoff ρ hρ ε ∘ T.symm) ⊆ _
    rw [tsupport_comp_eq_preimage (ucGaussianCutoff ρ hρ ε) T.symm]
    intro z hz
    have hz' : T.symm z ∈ tsupport (ucGaussianCutoff ρ hρ ε) := hz
    have hball := ucGaussianCutoff_tsupport_subset_cylinder hρ hε hz'
    have htime : (T.symm z).2 = z.2 - 1 / 6 := by
      rw [buGaussian_timeShift_point_symm_apply]
    have hspace : z.1 ∈ vec3Ball 0 ρ := by
      have hp : (T.symm z).1 = z.1 := by
        rw [buGaussian_timeShift_point_symm_apply]
      simpa only [hp] using hball.1
    refine ⟨hspace, ?_⟩
    change 1 / 6 < z.2
    linarith only [htime, hball.2.1]
  have hbaseLate : tsupport (ucGaussianCutoff ρ hρ ε) ⊆
      {z : ParabolicPoint | z.2 ≤ 7 / 4} := by
    apply closure_minimal
    · intro z hz
      by_contra hnot
      have hzero := ucFinalTimeCutoff_eq_zero (le_of_lt (lt_of_not_ge hnot))
      exact (Function.mem_support.mp hz) (by
        simp [ucGaussianCutoff, ucCutoffScalar, hzero])
    · exact isClosed_le (continuous_snd.comp parabolicHomeomorph.continuous)
        continuous_const
  intro z hz
  have hzbase : T.symm z ∈ tsupport (ucGaussianCutoff ρ hρ ε) := by
    change z ∈ tsupport (ucGaussianCutoff ρ hρ ε ∘ T.symm) at hz
    rw [tsupport_comp_eq_preimage (ucGaussianCutoff ρ hρ ε) T.symm] at hz
    exact hz
  have hparts := hbase hz
  have hlate : (T.symm z).2 ≤ 7 / 4 := hbaseLate hzbase
  have htime : (T.symm z).2 = z.2 - 1 / 6 := by
    rw [buGaussian_timeShift_point_symm_apply]
  refine ⟨hparts.1, hparts.2, ?_⟩
  rw [htime] at hlate
  linarith only [hlate]

end ESS

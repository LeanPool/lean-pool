/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Collar
import LeanPool.GraphMinor.Surface.PushOff

/-!
# Radius coordinates for joining two collars

For the disc homeomorphism used in XII (4.3), claim (7), page 251,
join an inner collar of radius two to an outer collar. On the outer
annulus the change of radius is `r ↦ r - 1`. Using a denominator
bounded below by two gives a continuous plane map, including at zero.
-/

@[expose] public section

namespace GraphMinor.GM12

open Set Metric

/-- The outer-annulus change of radius used to join two collars. -/
noncomputable def collarOuterStep (z : ℂ) : ℂ :=
  ((max 2 ‖z‖ - 1) / max 2 ‖z‖ : ℝ) • z

theorem continuous_collarOuterStep : Continuous collarOuterStep := by
  have hf : Continuous (fun z : ℂ => (max 2 ‖z‖ - 1) / max 2 ‖z‖) := by
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro z
      have h : (0 : ℝ) < max 2 ‖z‖ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
      exact h.ne'
  exact hf.smul continuous_id

theorem collarOuterStep_norm {z : ℂ} (hz : 2 ≤ ‖z‖) :
    ‖collarOuterStep z‖ = ‖z‖ - 1 := by
  have hn : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) hz
  rw [collarOuterStep, max_eq_right hz, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos (by linarith) hn), div_mul_cancel₀ _ hn.ne']

theorem collarOuterStep_injOn : InjOn collarOuterStep {z : ℂ | 2 ≤ ‖z‖} := by
  intro z hz w hw heq
  change 2 ≤ ‖z‖ at hz
  change 2 ≤ ‖w‖ at hw
  have hnorm : ‖z‖ = ‖w‖ := by
    have h := congrArg norm heq
    rw [collarOuterStep_norm hz, collarOuterStep_norm hw] at h
    linarith
  have hscale : (‖z‖ - 1) / ‖z‖ ≠ 0 := by
    apply ne_of_gt
    exact div_pos (by linarith [hz]) (by linarith [hz])
  simp only [collarOuterStep, max_eq_right hz, ← hnorm] at heq
  exact (smul_right_injective _ hscale) heq

theorem collarOuterStep_two {z : ℂ} (hz : ‖z‖ = 2) :
    collarOuterStep z = (1 / 2 : ℝ) • z := by
  simp only [collarOuterStep, hz, max_self]
  norm_num

/-- The inverse radius change on the outer annulus. -/
theorem exists_collarOuterStep_preimage {w : ℂ} (hw : 1 ≤ ‖w‖) :
    ∃ z : ℂ, ‖z‖ = ‖w‖ + 1 ∧ collarOuterStep z = w := by
  have hn : 0 < ‖w‖ := lt_of_lt_of_le zero_lt_one hw
  let z : ℂ := ((‖w‖ + 1) / ‖w‖ : ℝ) • w
  have hz : ‖z‖ = ‖w‖ + 1 := by
    rw [show z = ((‖w‖ + 1) / ‖w‖ : ℝ) • w from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos (by linarith) hn), div_mul_cancel₀ _ hn.ne']
  refine ⟨z, hz, ?_⟩
  have hz2 : 2 ≤ ‖z‖ := by rw [hz]; linarith
  rw [collarOuterStep, max_eq_right hz2, hz]
  dsimp only [z]
  rw [smul_smul]
  have heq : (‖w‖ + 1 - 1) / (‖w‖ + 1) * ((‖w‖ + 1) / ‖w‖) = 1 := by
    field_simp
    ring
  rw [heq, one_smul]

end GraphMinor.GM12

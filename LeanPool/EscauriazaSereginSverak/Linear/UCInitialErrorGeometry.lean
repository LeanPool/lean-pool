/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCWeightBound

/-!
# Spatial scale of the initial time transition

A quarter-power spatial radius contains the transition time interval
while shrinking toward the flatness center.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The fourth-root spatial scale is larger than the parabolic time
scale of the initial transition. -/
theorem uc_initial_error_fourth_root_geometry
    {ρ ε : ℝ} (hρ : 4 ≤ ρ) (hε : 0 < ε)
    (hεsmall : ε < 1 / 4) :
    let r := Real.sqrt (Real.sqrt ε)
    0 < r ∧ r < ρ ∧ r ^ 4 = ε ∧ 2 * ε < r ^ 2 := by
  dsimp
  let r := Real.sqrt (Real.sqrt ε)
  have hroot : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hr : 0 < r := Real.sqrt_pos.2 hroot
  have hrSq : r ^ 2 = Real.sqrt ε := by
    dsimp [r]
    exact Real.sq_sqrt hroot.le
  have hr4 : r ^ 4 = ε := by
    calc
      r ^ 4 = (r ^ 2) ^ 2 := by ring
      _ = (Real.sqrt ε) ^ 2 := by rw [hrSq]
      _ = ε := Real.sq_sqrt hε.le
  have hrootSq : (Real.sqrt ε) ^ 2 = ε := Real.sq_sqrt hε.le
  have hroot1 : Real.sqrt ε < 1 := by
    nlinarith only [hroot, hrootSq, hεsmall]
  have hr1 : r < 1 := by
    nlinarith only [hr, hrSq, hroot1]
  have htime : 2 * ε < r ^ 2 := by
    rw [hrSq]
    nlinarith only [hroot, hrootSq, hεsmall]
  refine ⟨hr, ?_, hr4, htime⟩
  linarith only [hr1, hρ]

end ESS

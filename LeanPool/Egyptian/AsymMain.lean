/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.Main
public import LeanPool.Egyptian.FiniteRays
public import LeanPool.Egyptian.AsymRigidity
public import LeanPool.Egyptian.AsymWinningBridge

/-! Theorem 4 for every positive rational, proved from finite maximizing rays. -/

public section

namespace Egyptian

theorem fullAsymptoticRigidity : AsymptoticRigidity := by
  apply asymptoticRigidity_of_finite_rays (exists_benchmark_of_compatible compatibleUnitTails)
  intro q b hq hb
  obtain ⟨s,hv,hzero,hs⟩ := Control.exists_initial_state hq
  have hi : Control.Interior s := by simpa [Control.Interior, hzero] using hv.2
  rw [← hs] at hb ⊢
  exact (Control.finite_winningRays s hv hi).subset
    (Control.equal_tail_subset_winningRays s hv hzero hb)

end Egyptian

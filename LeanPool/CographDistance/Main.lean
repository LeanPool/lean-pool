/-
Copyright (c) 2026 Horace Dong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horace Dong
-/
module

public import LeanPool.CographDistance.Eigen

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Answer to part (i): no -/

@[expose] public section

namespace CographDist

/-- Every connected cograph `G_m = K₁ ∨ (K₁ ∪ m K₂)` (`m ≥ 1`) has a distance eigenvalue in
`(-2 - 1/(2m), -2)`. -/
theorem family_theorem (m : ℕ) (hm : 1 ≤ m) :
    (fam m).Connected ∧ ¬(SimpleGraph.pathGraph 4).IsIndContained (fam m) ∧
      ∃ l : ℝ, -2 - 1 / (2 * (m : ℝ)) < l ∧ l < -2 ∧ IsDistEigenvalue (fam m) l :=
  ⟨fam_connected m, fam_isCograph m, fam_eigenvalue m hm⟩

/-- The answer to Open Problem (i) of arXiv:2611.06981 is no. -/
theorem openProblemI_negative (ε : ℝ) (hε : 0 < ε) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      G.Connected ∧ ¬(SimpleGraph.pathGraph 4).IsIndContained G ∧
        ∃ μ : ℝ, -2 - ε < μ ∧ μ < -2 ∧ IsDistEigenvalue G μ := by
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / ε)
  have hm0 : (0 : ℝ) < m := lt_trans (by positivity) hm
  have hm1 : 1 ≤ m := by exact_mod_cast (Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hm0))
  obtain ⟨_, hc, l, h1, h2, h3⟩ := family_theorem m hm1
  refine ⟨W m, inferInstance, fam m, fam_connected m, hc, l, ?_, h2, h3⟩
  have : 1 / (2 * (m : ℝ)) < ε := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hm
    nlinarith
  linarith

end CographDist

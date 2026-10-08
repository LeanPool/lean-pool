/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCarlemanAdmissible
public import LeanPool.EscauriazaSereginSverak.Linear.CarlemanSobolevConsumers
public import LeanPool.EscauriazaSereginSverak.Linear.CarlemanHalfSpaceProof
public import LeanPool.EscauriazaSereginSverak.Linear.CarlemanHalfWeightsBounds
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortHeatSq

/-!
# Energy comparison in the short-time cylinder

The half-space Carleman mass and gradient terms dominate the quadratic
cutoff energy needed to absorb the scaled differential inequality.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- At times below one, the Carleman left integrand dominates the
weighted quadratic cutoff energy for parameters at least one. -/
theorem bu_short_carleman_mass_gradient_lower
    (a s X G : ℝ) (ha : 1 ≤ a) (hs : 0 < s) (hs1 : s ≤ 1)
    (hG : 0 ≤ G) :
    s ^ 2 * (X ^ 2 + G) ≤
      s ^ 2 * (a * X ^ 2 / s ^ 2 + G / s) := by
  have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
  have hs2le : s ^ 2 ≤ 1 := pow_le_one₀ hs.le hs1
  have hmass : s ^ 2 * X ^ 2 ≤ a * X ^ 2 := by
    exact mul_le_mul_of_nonneg_right (hs2le.trans ha) (sq_nonneg X)
  have hgrad : s ^ 2 * G ≤ s * G := by
    have hs2s : s ^ 2 ≤ s := by nlinarith only [hs, hs1]
    exact mul_le_mul_of_nonneg_right hs2s hG
  have hm : s ^ 2 * (a * X ^ 2 / s ^ 2) = a * X ^ 2 := by
    field_simp
  have hg : s ^ 2 * (G / s) = s * G := by
    field_simp
  rw [mul_add, mul_add, hm, hg]
  exact add_le_add hmass hgrad

end ESS

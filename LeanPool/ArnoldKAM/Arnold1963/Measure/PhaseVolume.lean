/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Iteration.LimitDomain

/-!
Physical phase volume of retained action domains. Angle cells have side length 2 * pi.
This source-volume estimate is separate from volume preservation by transformations.
-/

@[expose] public section
noncomputable section
open Set
open scoped NNReal ENNReal
namespace KamProject.Arnold1963.Iteration.InitialData
variable {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
  (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D)

theorem limit_physicalCell_volume_gt :
    ENNReal.ofReal (1 - κ) *
        realPhaseLebesgue n (realSlice h.domain ×ˢ realAngleCell n (2 * Real.pi)) <
      realPhaseLebesgue n (realSlice (h.limitDomain b) ×ˢ
        realAngleCell n (2 * Real.pi)) := by
  rw [realPhaseLebesgue_physicalCell, realPhaseLebesgue_physicalCell, ← mul_assoc]
  exact ENNReal.mul_lt_mul_left (by positivity) (by finiteness) (h.limit_volume_gt b)

end KamProject.Arnold1963.Iteration.InitialData

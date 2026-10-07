/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCTargetEstimate

/-!
# Restriction of integral flatness

Integral vanishing of every order persists when the allowed spatial radius
or time length is shortened in `lem:uc-gaussian`.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Integral flatness at a center remains valid on a smaller admissible
cylinder (`thm:uc`). -/
theorem uc_integral_flatness_mono
    (x₀ : Vec3) (R R' T T' : ℝ)
    (hR : R' ≤ R) (hT : T' ≤ T)
    (w : ParabolicPoint → Vec3)
    (hflat : UCIntegralFlatness x₀ R T w) :
    UCIntegralFlatness x₀ R' T' w := by
  intro m
  obtain ⟨C, r₀, hC, hr₀, hbound⟩ := hflat m
  refine ⟨C, r₀, hC, hr₀, ?_⟩
  intro r hr hrsmall
  have hroot : Real.sqrt T' ≤ Real.sqrt T := Real.sqrt_le_sqrt hT
  have hmin : min R' (min (Real.sqrt T') r₀) ≤
      min R (min (Real.sqrt T) r₀) := by
    exact min_le_min hR (min_le_min hroot le_rfl)
  exact hbound r hr (lt_of_lt_of_le hrsmall hmin)

end ESS

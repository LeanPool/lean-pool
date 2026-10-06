/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EscauriazaSereginSverak.Main.BackwardUniqueness

/-!
# BUAny Growth

Backward uniqueness for solutions with general growth control.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Backward uniqueness on a half-space for an arbitrary growth exponent
`M ∈ ℝ`, as stated in `thm:bu`: the bound `e^{M|x|²}` is at most
`e^{max(M,1)|x|²}`, so the positive-exponent case applies. -/
theorem backwardUniqueness_real_growth (c₁ M : ℝ) (hc₁ : 0 < c₁)
    (w : ParabolicPoint → Vec3) (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3) (Dtw : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w ({x : Vec3 | 0 < x 2} ×ˢ Ico 0 1))
    (hinit : ∀ x : Vec3, 0 < x 2 → w (x, 0) = 0)
    (hderiv : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1) w Dw D2w Dtw)
    (hL2 : ∀ S : Set ParabolicPoint, S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) + ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1))),
      vec3EuclideanNorm (fun i => Dtw z i + ∑ j, D2w z i j j) ≤
        c₁ * (Real.sqrt (spatialGradientSq w Dw z) + vec3EuclideanNorm (w z)))
    (hgrowth : ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
      vec3EuclideanNorm (w z) ≤ Real.exp (M * vec3EuclideanNorm z.1 ^ 2)) :
    ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1), w z = 0 := by
  refine ESS.Main.backwardUniqueness c₁ (max M 1) hc₁
    (lt_of_lt_of_le one_pos (le_max_right M 1)) w Dw D2w Dtw hcont hinit hderiv hL2
    hineq (fun z hz => (hgrowth z hz).trans ?_)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left M 1) (sq_nonneg _))

end ESS

/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.LorentzFrameOrientation

/-!
# Proper future Lorentz frames for any orthogonal negative pair

The normalization and gamma identity use the original Minkowski form.
No frame-existence or determinant hypothesis remains in this endpoint.
-/

@[expose] public section

namespace VacuumBellSeparation

/-- Negative Minkowski length obtained from `Real.sqrt`. -/
noncomputable def negativeMinkowskiLength (u : Spacetime) : ℝ :=
  Real.sqrt (-minkowskiForm u u)

/-- Normalize a spacelike vector to have Minkowski square minus one. -/
noncomputable def negativeMinkowskiUnit (u : Spacetime) : Spacetime :=
  (negativeMinkowskiLength u)⁻¹ • u

theorem negativeMinkowskiLength_pos {u : Spacetime} (hu : minkowskiForm u u < 0) :
    0 < negativeMinkowskiLength u := Real.sqrt_pos.2 (neg_pos.2 hu)

theorem negativeMinkowskiLength_sq {u : Spacetime} (hu : minkowskiForm u u < 0) :
    negativeMinkowskiLength u ^ 2 = -minkowskiForm u u := Real.sq_sqrt (neg_nonneg.2 hu.le)

theorem negativeMinkowskiUnit_square {u : Spacetime} (hu : minkowskiForm u u < 0) :
    minkowskiForm (negativeMinkowskiUnit u) (negativeMinkowskiUnit u) = -1 := by
  have hq : minkowskiForm u u = -(negativeMinkowskiLength u ^ 2) := by
    rw [negativeMinkowskiLength_sq hu, neg_neg]
  simp only [negativeMinkowskiUnit, minkowskiForm_smul_left, minkowskiForm_smul_right, hq]
  field_simp [ne_of_gt (negativeMinkowskiLength_pos hu)]

theorem negativeMinkowskiUnit_orthogonal {u v : Spacetime} (huv : minkowskiForm u v = 0) :
    minkowskiForm (negativeMinkowskiUnit u) (negativeMinkowskiUnit v) = 0 := by
  simp only [negativeMinkowskiUnit, minkowskiForm_smul_left, minkowskiForm_smul_right,
    huv, mul_zero]

theorem negativeMinkowskiLength_smul_unit {u : Spacetime} (hu : minkowskiForm u u < 0) :
    negativeMinkowskiLength u • negativeMinkowskiUnit u = u := by
  rw [negativeMinkowskiUnit, smul_smul, mul_inv_cancel₀ (ne_of_gt (negativeMinkowskiLength_pos hu)),
    one_smul]

/-- Continuous linear equivalence for the lorentz negative pair frame, of type `Spacetime ≃L[ℝ]
Spacetime`. -/
noncomputable def lorentzNegativePairFrame {u v : Spacetime}
    (hu : minkowskiForm u u < 0) (hv : minkowskiForm v v < 0)
    (huv : minkowskiForm u v = 0) : Spacetime ≃L[ℝ] Spacetime :=
  lorentzPairFrame (negativeMinkowskiUnit_square hu) (negativeMinkowskiUnit_square hv)
    (negativeMinkowskiUnit_orthogonal huv)

theorem lorentzNegativePairFrame_isProper {u v : Spacetime}
    (hu : minkowskiForm u u < 0) (hv : minkowskiForm v v < 0)
    (huv : minkowskiForm u v = 0) : IsProperLorentzMap (lorentzNegativePairFrame hu hv huv) :=
  lorentzPairFrame_isProper _ _ _

theorem lorentzNegativePairFrame_isOrthochronous {u v : Spacetime}
    (hu : minkowskiForm u u < 0) (hv : minkowskiForm v v < 0)
    (huv : minkowskiForm u v = 0) : IsOrthochronousMap (lorentzNegativePairFrame hu hv huv) :=
  lorentzPairFrame_isOrthochronous _ _ _

theorem lorentzNegativePairFrame_first {u v : Spacetime}
    (hu : minkowskiForm u u < 0) (hv : minkowskiForm v v < 0)
    (huv : minkowskiForm u v = 0) :
    lorentzNegativePairFrame hu hv huv (spacetimeAxis 0) = negativeMinkowskiUnit u :=
  lorentzFrameLinear_first _ _

theorem lorentzNegativePairFrame_second {u v : Spacetime}
    (hu : minkowskiForm u u < 0) (hv : minkowskiForm v v < 0)
    (huv : minkowskiForm u v = 0) :
    lorentzNegativePairFrame hu hv huv (spacetimeAxis 1) = negativeMinkowskiUnit v :=
  lorentzFrameLinear_second _ _

theorem lorentzNegativePairFrame_third_time {u v : Spacetime}
    (hu : minkowskiForm u u < 0) (hv : minkowskiForm v v < 0)
    (huv : minkowskiForm u v = 0) :
    (lorentzNegativePairFrame hu hv huv (spacetimeAxis 2)).1 = 0 := by
  change (lorentzFrameLinear (negativeMinkowskiUnit u) (negativeMinkowskiUnit v)
    (spacetimeAxis 2)).1 = 0
  rw [lorentzFrameLinear_third, lorentzFrameNormal_time]

theorem lorentzNegativePairFrame_gamma_sq {u v : Spacetime}
    (hu : minkowskiForm u u < 0) (hv : minkowskiForm v v < 0)
    (huv : minkowskiForm u v = 0) :
    (lorentzNegativePairFrame hu hv huv (1, 0)).1 ^ 2 =
      1 + u.1 ^ 2 / (-minkowskiForm u u) + v.1 ^ 2 / (-minkowskiForm v v) := by
  change (lorentzPairFrame _ _ _ (1, 0)).1 ^ 2 = _
  rw [lorentzPairFrame_gamma_sq]
  change 1 + ((negativeMinkowskiLength u)⁻¹ * u.1) ^ 2 +
    ((negativeMinkowskiLength v)⁻¹ * v.1) ^ 2 = _
  rw [mul_pow, mul_pow, inv_pow, inv_pow, negativeMinkowskiLength_sq hu,
    negativeMinkowskiLength_sq hv]
  simp only [div_eq_mul_inv]
  ring

/-- Exact manuscript frame completion, including proper orientation,
zero-time complementary column and its quantitative Lorentz factor. -/
theorem exists_proper_future_negative_pair_frame {u v : Spacetime}
    (hu : minkowskiForm u u < 0) (hv : minkowskiForm v v < 0)
    (huv : minkowskiForm u v = 0) :
    ∃ Λ : Spacetime ≃L[ℝ] Spacetime,
      IsProperLorentzMap Λ ∧ IsOrthochronousMap Λ ∧
      Λ (negativeMinkowskiLength u • spacetimeAxis 0) = u ∧
      Λ (negativeMinkowskiLength v • spacetimeAxis 1) = v ∧
      (Λ (spacetimeAxis 2)).1 = 0 ∧
      (Λ (1, 0)).1 ^ 2 =
        1 + u.1 ^ 2 / (-minkowskiForm u u) + v.1 ^ 2 / (-minkowskiForm v v) := by
  refine ⟨lorentzNegativePairFrame hu hv huv, lorentzNegativePairFrame_isProper hu hv huv,
    lorentzNegativePairFrame_isOrthochronous hu hv huv, ?_, ?_,
    lorentzNegativePairFrame_third_time hu hv huv, lorentzNegativePairFrame_gamma_sq hu hv huv⟩
  · rw [map_smul, lorentzNegativePairFrame_first, negativeMinkowskiLength_smul_unit hu]
  · rw [map_smul, lorentzNegativePairFrame_second, negativeMinkowskiLength_smul_unit hv]

end VacuumBellSeparation

/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Noether.ClosedFormBaseChange
import LeanPool.CCDN.ForMathlib.Matrix

/-! A nonzero integer minor of the closed-form coefficient matrix.
Rank drop after reduction forces divisibility of this same integer. The
geometric rank-drop criterion and the height bound are separate obligations. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Matrix

/-- Determinants of selected coefficient minors commute with any coefficient
ring map. -/
theorem closedForm_minor_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (d r : ℕ) (f : R[X][X])
    (a : Fin r → ℕ × ℕ) (c : Fin r → ClosedFormColumns d) :
    φ (((closedFormCoefficientMatrix d f).submatrix a c).det) =
      ((closedFormCoefficientMatrix d (bivariateMap φ f)).submatrix a c).det := by
  rw [φ.map_det]
  change (((closedFormCoefficientMatrix d f).map φ).submatrix a c).det = _
  rw [closedFormCoefficientMatrix_map]

/-- Any characteristic-p rank drop below the chosen minor order makes p
 divide its integer determinant. The field may be an algebraic closure. -/
theorem characteristic_dvd_closedForm_minor_of_rank_lt
    {K : Type*} [Field K] (p : ℕ) [CharP K p]
    (d r : ℕ) (f : ℤ[X][X]) (a : Fin r → ℕ × ℕ)
    (c : Fin r → ClosedFormColumns d)
    (hr : (closedFormCoefficientMatrix d (bivariateMap (Int.castRingHom K) f)).rank < r) :
    (p : ℤ) ∣ ((closedFormCoefficientMatrix d f).submatrix a c).det := by
  apply (CharP.intCast_eq_zero_iff K p _).mp
  change (Int.castRingHom K) _ = 0
  rw [closedForm_minor_map]
  by_contra hn
  exact hr.not_ge (Matrix.le_rank_of_det_submatrix_ne_zero _ a c hn)

end
end CCDN

/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.SVI.RankOneSignature

/-! # Signature of an orthogonal product

Part of the SVI polynomial-sign certificate (#174).

The signature of a weighted sum of squares is the sum of the signs of its weights, equivalent
forms have equal signatures, and the signature is additive over orthogonal products, degenerate
forms included (`formSignature_prod`).

## Main definitions

* `formProd`: the orthogonal product of two quadratic forms, `(x, y) ↦ Q x + R y` on `V × W`.

## Main results

* `formSignature_weightedSumSquares`: the signature of `weightedSumSquares ℝ w` is
  `∑ i, sign (w i)`.
* `formSignature_eq_of_equivalent`: equivalent real quadratic forms have equal signature.
* `formSignature_prod`: for finite-dimensional `V`, `W`, the signature of `formProd Q R` is the
  sum of the signatures of `Q` and `R`, degenerate forms included.

## Tags

quadratic form signature, orthogonal product, sum of squares signature, SVI, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI
open scoped BigOperators

private theorem sign_indicators (a : ℝ) :
    sign a = (if 0 < a then (1 : ℤ) else 0) - (if a < 0 then 1 else 0) := by
  rcases lt_trichotomy a 0 with h | rfl | h <;> simp [sign, *, not_lt_of_ge, le_of_lt]

theorem formSignature_weightedSumSquares {ι : Type*} [Fintype ι] (w : ι → ℝ) :
    formSignature (QuadraticMap.weightedSumSquares ℝ w) = ∑ i, sign (w i) := by
  classical
  unfold formSignature
  rw [QuadraticForm.sigPos_weightedSumSquares, QuadraticForm.sigNeg_weightedSumSquares]
  simp_rw [sign_indicators]
  rw [Finset.sum_sub_distrib]
  simp [Set.ncard_eq_toFinset_card']

theorem formSignature_eq_of_equivalent {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] {Q : QuadraticForm ℝ V} {R : QuadraticForm ℝ W}
    (he : QuadraticMap.Equivalent Q R) : formSignature Q = formSignature R := by
  unfold formSignature
  rw [he.sigPos_eq, he.sigNeg_eq]

/-- The orthogonal product of two quadratic forms on `V × W`. -/
noncomputable def formProd {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (Q : QuadraticForm ℝ V) (R : QuadraticForm ℝ W) :
    QuadraticForm ℝ (V × W) :=
  Q.comp (LinearMap.fst ℝ V W) + R.comp (LinearMap.snd ℝ V W)

@[simp] theorem formProd_apply {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (Q : QuadraticForm ℝ V) (R : QuadraticForm ℝ W)
    (x : V × W) : formProd Q R x = Q x.1 + R x.2 := rfl

/-- Signature is additive under orthogonal products, including degenerate forms. -/
theorem formSignature_prod {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (Q : QuadraticForm ℝ V) (R : QuadraticForm ℝ W) :
    formSignature (formProd Q R) = formSignature Q + formSignature R := by
  classical
  obtain ⟨w, ⟨e⟩⟩ := QuadraticForm.equivalent_weightedSumSquares Q
  obtain ⟨v, ⟨f⟩⟩ := QuadraticForm.equivalent_weightedSumSquares R
  let E := (e.toLinearEquiv.prodCongr f.toLinearEquiv).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin (Module.finrank ℝ V))
      (Fin (Module.finrank ℝ W)) ℝ ℝ).symm
  have he : QuadraticMap.Equivalent (formProd Q R)
      (QuadraticMap.weightedSumSquares ℝ (Sum.elim w v)) := by
    refine ⟨{ E with map_app' := ?_ }⟩
    intro x
    simp only [QuadraticMap.weightedSumSquares_apply, Fintype.sum_sum_type]
    change (∑ i, w i * (e x.1 i * e x.1 i)) +
      (∑ j, v j * (f x.2 j * f x.2 j)) = Q x.1 + R x.2
    have he := e.map_app x.1
    have hf := f.map_app x.2
    simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul] at he hf
    rw [he, hf]
  rw [formSignature_eq_of_equivalent he,
    formSignature_eq_of_equivalent (show QuadraticMap.Equivalent Q _ from ⟨e⟩),
    formSignature_eq_of_equivalent (show QuadraticMap.Equivalent R _ from ⟨f⟩)]
  simp [formSignature_weightedSumSquares, Fintype.sum_sum_type]

end SVI
end MathFin

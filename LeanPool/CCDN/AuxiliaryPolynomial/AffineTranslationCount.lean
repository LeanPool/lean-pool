/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.AffineTranslation
public import LeanPool.CCDN.Determinant.SingularReduction
import LeanPool.CCDN.Plane.GridHeight

/-! Bounded translations remove a zero constant coefficient and preserve the
finite-field residue count, primitivity and integer point families. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Evaluating the affine translate of `f` by `a` at `x` gives the value of `f` at `x + a`. -/
lemma affineTranslation_eval {R : Type*} [CommRing R] {n : ℕ}
    (a x : Fin n → R) (f : MvPolynomial (Fin n) R) :
    eval x (affineTranslation R a f) = eval (x + a) f := by
  change eval x (eval₂ C (fun j => X j + C (a j)) f) = _
  rw [← eval_assoc]
  congr 2
  funext j
  simp

/-- The constant coefficient of the affine translate of `f` by `a` is the value of `f` at
`a`. -/
lemma affineTranslation_constantCoeff {R : Type*} [CommRing R] {n : ℕ}
    (a : Fin n → R) (f : MvPolynomial (Fin n) R) :
    (affineTranslation R a f).coeff 0 = eval a f := by
  have he := affineTranslation_eval a 0 f
  simpa only [zero_add, eval_zero, constantCoeff_eq] using he

/-- An integral affine translate of a primitive integral polynomial is primitive. -/
lemma PrimitiveIntegerPolynomial.translate_affine {n : ℕ} (a : Fin n → ℤ)
    {f : MvPolynomial (Fin n) ℤ} (hf : PrimitiveIntegerPolynomial f) :
    PrimitiveIntegerPolynomial (affineTranslation ℤ a f) := by
  intro c hc
  have hd := (C_dvd_iff_dvd_coeff c _).mpr hc
  have he := map_dvd (affineTranslation ℤ a).symm.toRingHom hd
  have hC : (affineTranslation ℤ a).symm (C c) = C c := (affineTranslation ℤ a).symm.commutes c
  change (affineTranslation ℤ a).symm (C c) ∣
    (affineTranslation ℤ a).symm (affineTranslation ℤ a f) at he
  rw [hC, AlgEquiv.symm_apply_apply] at he
  exact hf c ((C_dvd_iff_dvd_coeff c f).mp he)

/-- Translation of the residue zero set, over ZMod p for every p. -/
private def affineTranslationResidueEquiv (a : Fin 2 → ℤ) (f : MvPolynomial (Fin 2) ℤ) (p : ℕ) :
    PlaneResidue (affineTranslation ℤ a f) p ≃ PlaneResidue f p where
  toFun x := ⟨x.val + fun j => (a j : ZMod p), by
    have h := x.property
    rw [← eval_map] at h
    rw [affineTranslation_map, affineTranslation_eval] at h
    simpa only [eval_map, Function.comp_def, Int.coe_castRingHom] using h⟩
  invFun x := ⟨x.val - fun j => (a j : ZMod p), by
    rw [← eval_map]
    rw [affineTranslation_map, affineTranslation_eval]
    simpa only [Function.comp_def, Int.coe_castRingHom, sub_add_cancel, eval_map] using x.property⟩
  left_inv x := by apply Subtype.ext; exact add_sub_cancel_right _ _
  right_inv x := by apply Subtype.ext; exact sub_add_cancel _ _

/-- An integral affine translation of a plane polynomial preserves the number of its zeros
modulo `p` in the affine plane over `ZMod p`. -/
lemma affineTranslation_residue_card (a : Fin 2 → ℤ) (f : MvPolynomial (Fin 2) ℤ) (p : ℕ) :
    Nat.card (PlaneResidue (affineTranslation ℤ a f) p) = Nat.card (PlaneResidue f p) :=
  Nat.card_congr (affineTranslationResidueEquiv a f p)

/-- A nonzero integral plane polynomial `f` has an integral translate with nonzero constant
coefficient by a vector whose entries lie in `[0, deg f]`. -/
theorem exists_bounded_translation_nonzero_constant (f : MvPolynomial (Fin 2) ℤ) (hf : f ≠ 0) :
    ∃ a : Fin 2 → ℤ, (∀ j, 0 ≤ a j ∧ a j ≤ f.totalDegree) ∧
      (affineTranslation ℤ a f).coeff 0 ≠ 0 := by
  obtain ⟨x, y, hx, hy, hn, _⟩ := exists_integer_plane_grid_height_witness f hf le_rfl
  refine ⟨![(x : ℤ), (y : ℤ)], ?_, ?_⟩
  · intro j
    fin_cases j
    · change 0 ≤ (x : ℤ) ∧ (x : ℤ) ≤ f.totalDegree
      exact ⟨by positivity, by exact_mod_cast hx⟩
    · change 0 ≤ (y : ℤ) ∧ (y : ℤ) ≤ f.totalDegree
      exact ⟨by positivity, by exact_mod_cast hy⟩
  · rwa [affineTranslation_constantCoeff]

end
end CCDN

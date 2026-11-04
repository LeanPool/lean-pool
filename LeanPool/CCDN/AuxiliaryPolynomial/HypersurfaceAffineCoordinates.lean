/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.OriginShift
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Tactic.LinearCombination
import LeanPool.CCDN.Determinant.PlaneMultiplicity
import LeanPool.CCDN.ForMathlib.MvPolynomialDerivative

/-! Explicit invertible affine coordinates along a direction with nonzero
first component. The same map carries its base point to the origin and
identifies the first partial derivative with the directional derivative. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The linear coordinates x_i = b_i*x_0 + z_i, with no z_0. -/
def directionCoordinatesHom {K σ : Type*} [Field K] (b : Option σ → K) :
    MvPolynomial (Option σ) K →ₐ[K] MvPolynomial (Option σ) K :=
  aeval (fun i => C (b i) * X none + Option.elim i 0 (fun j => X (some j)))

/-- The inverse of the linear coordinates `directionCoordinatesHom b` when `b none ≠ 0`: the
substitution sending $x_0$ to $b_0^{-1} x_0$ and every other $x_i$ to $x_i - b_i b_0^{-1} x_0$. -/
def directionCoordinatesInv {K σ : Type*} [Field K] (b : Option σ → K) :
    MvPolynomial (Option σ) K →ₐ[K] MvPolynomial (Option σ) K :=
  aeval (fun i => Option.elim i (C (b none)⁻¹ * X none)
    (fun j => X (some j) - C (b (some j)) * C (b none)⁻¹ * X none))

/-- The linear coordinates $x_i = b_i x_0 + z_i$ (with no $z_0$) as an algebra automorphism,
for a direction `b` with nonzero first component. -/
def directionCoordinates {K σ : Type*} [Field K] (b : Option σ → K) (hb : b none ≠ 0) :
    MvPolynomial (Option σ) K ≃ₐ[K] MvPolynomial (Option σ) K := by
  have hu : (C (b none)⁻¹ : MvPolynomial (Option σ) K) * C (b none) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hb, map_one]
  refine AlgEquiv.ofAlgHom (directionCoordinatesHom b) (directionCoordinatesInv b) ?_ ?_
  · apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | none =>
      simp only [directionCoordinatesHom, directionCoordinatesInv, AlgHom.comp_apply,
        aeval_X, Option.elim_none, map_mul, aeval_C, algebraMap_eq, add_zero, AlgHom.id_apply]
      linear_combination X (none : Option σ) * hu
    | some i =>
      simp only [directionCoordinatesHom, directionCoordinatesInv, AlgHom.comp_apply,
        aeval_X, Option.elim_some, Option.elim_none, map_sub, map_mul, aeval_C,
        algebraMap_eq, add_zero, AlgHom.id_apply]
      linear_combination -C (b (some i)) * X (none : Option σ) * hu
  · apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | none =>
      simp only [directionCoordinatesHom, directionCoordinatesInv, AlgHom.comp_apply,
        aeval_X, Option.elim_none, map_mul, aeval_C, algebraMap_eq,
        add_zero, AlgHom.id_apply]
      linear_combination X (none : Option σ) * hu
    | some i =>
      simp only [directionCoordinatesHom, directionCoordinatesInv, AlgHom.comp_apply,
        aeval_X, Option.elim_some, Option.elim_none, map_add, map_mul, aeval_C,
        algebraMap_eq, AlgHom.id_apply]
      ring

/-- Substitute a_i+b_i*x_0+z_i, so the new origin is the old point a. -/
def hypersurfaceAffineCoordinates {K σ : Type*} [Field K]
    (a b : Option σ → K) (hb : b none ≠ 0) :
    MvPolynomial (Option σ) K ≃ₐ[K] MvPolynomial (Option σ) K :=
  (originShiftEquiv a).trans (directionCoordinates b hb)

/-- The affine coordinates substitute $a_i + b_i x_0 + z_i$ for the variable $x_i$, with no
$z_0$ term for the distinguished variable. -/
lemma hypersurfaceAffineCoordinates_X {K σ : Type*} [Field K]
    (a b : Option σ → K) (hb : b none ≠ 0) (i : Option σ) :
    hypersurfaceAffineCoordinates a b hb (X i) =
      C (a i) + C (b i) * X none + Option.elim i 0 (fun j => X (some j)) := by
  simp [hypersurfaceAffineCoordinates, directionCoordinates, directionCoordinatesHom]
  ring

/-- The affine change of coordinates `hypersurfaceAffineCoordinates a b hb` does not increase
the total degree. -/
lemma hypersurfaceAffineCoordinates_totalDegree_le {K σ : Type*} [Field K]
    (a b : Option σ → K) (hb : b none ≠ 0) (f : MvPolynomial (Option σ) K) :
    (hypersurfaceAffineCoordinates a b hb f).totalDegree ≤ f.totalDegree := by
  have he : (hypersurfaceAffineCoordinates a b hb).toAlgHom =
      aeval (fun i => C (a i) + C (b i) * X none + Option.elim i 0 (fun j => X (some j))) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgEquiv.coe_toAlgHom, aeval_X]
    exact hypersurfaceAffineCoordinates_X a b hb i
  change ((hypersurfaceAffineCoordinates a b hb).toAlgHom f).totalDegree ≤ _
  rw [he]
  apply linear_eval₂_totalDegree_le _ _ _ f
  intro i
  cases i <;>
    apply (totalDegree_add _ _).trans <;>
    apply max_le
  all_goals first | simp | exact (totalDegree_add _ _).trans (max_le (by simp)
    ((totalDegree_mul _ _).trans (by simp)))

/-- The affine coordinates carry the base point `a` to the origin: the transformed polynomial
takes at `0` the value of `f` at `a`. -/
lemma hypersurfaceAffineCoordinates_eval_zero {K σ : Type*} [Field K]
    (a b : Option σ → K) (hb : b none ≠ 0) (f : MvPolynomial (Option σ) K) :
    eval (0 : Option σ → K) (hypersurfaceAffineCoordinates a b hb f) = eval a f := by
  have he :
      (eval (0 : Option σ → K)).comp (hypersurfaceAffineCoordinates a b hb).toRingHom =
        eval a := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change eval (0 : Option σ → K) (hypersurfaceAffineCoordinates a b hb (C r)) = eval a (C r)
      rw [show hypersurfaceAffineCoordinates a b hb (C r) = C r from
        (hypersurfaceAffineCoordinates a b hb).commutes r]
      simp
    · intro i
      change eval (0 : Option σ → K) (hypersurfaceAffineCoordinates a b hb (X i)) = eval a (X i)
      rw [hypersurfaceAffineCoordinates_X]
      cases i <;> simp
  exact RingHom.congr_fun he f

/-- In the affine coordinates, the first partial derivative at the origin is the derivative of
`f` at `a` in the direction `b`. -/
lemma hypersurfaceAffineCoordinates_partial_zero {K σ : Type*} [Field K] [Fintype σ]
    (a b : Option σ → K) (hb : b none ≠ 0) (f : MvPolynomial (Option σ) K) :
    eval (0 : Option σ → K) (pderiv none (hypersurfaceAffineCoordinates a b hb f)) =
      ∑ i, eval a (pderiv i f) * b i := by
  change eval (0 : Option σ → K) (pderiv none
    ((hypersurfaceAffineCoordinates a b hb).toAlgHom f)) = _
  rw [MvPolynomial.pderiv_algHom, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul]
  simp only [AlgEquiv.coe_toAlgHom]
  rw [hypersurfaceAffineCoordinates_eval_zero]
  congr 1
  rw [hypersurfaceAffineCoordinates_X]
  cases i <;> simp

end
end CCDN

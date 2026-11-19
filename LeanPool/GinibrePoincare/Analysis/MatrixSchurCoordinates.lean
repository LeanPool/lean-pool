/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurCoordinates.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurJacobian

/-!
# Matrix Schur coordinates

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `schurCoordinateTangent_bijective`.
-/

@[expose] public section

open Matrix OrderDual
open scoped Matrix BigOperators
namespace GinibrePoincare
noncomputable section

/-- Positions `(i, j)` with `i ≤ j`, i.e. the upper-triangular entries including the
diagonal. -/
abbrev SchurUpperIndex (n : ℕ) := {p : Fin n × Fin n // p.1 ≤ p.2}
/-- Schur coordinates: complex values on the strictly lower positions together with complex
values on the upper-triangular positions. -/
abbrev SchurCoordinates (n : ℕ) := (SchurLowerIndex n → ℂ) × (SchurUpperIndex n → ℂ)

/-- The upper-triangular matrix whose `(i, j)` entry is `y (i, j)` for `i ≤ j`. -/
def schurUpperCombination {n : ℕ} (y : SchurUpperIndex n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ p, y p • Matrix.single p.val.1 p.val.2 1

theorem schurUpperCombination_entry {n : ℕ} (y : SchurUpperIndex n → ℂ) (p : SchurUpperIndex n) :
    schurUpperCombination y p.val.1 p.val.2 = y p := by
  classical
  have he (q : SchurUpperIndex n) : (q.val.1 = p.val.1 ∧ q.val.2 = p.val.2) ↔ q = p :=
    ⟨fun h => Subtype.ext (Prod.ext h.1 h.2), fun h => by simp [h]⟩
  simp [schurUpperCombination, Matrix.sum_apply, Matrix.single_apply, he]

theorem schurUpperCombination_lower_zero {n : ℕ} (y : SchurUpperIndex n → ℂ)
    (i j : Fin n) (hij : j < i) : schurUpperCombination y i j = 0 := by
  classical
  simp only [schurUpperCombination, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have hnot : ¬(p.val.1 = i ∧ p.val.2 = j) := by
    rintro ⟨hi, hj⟩
    have hh := p.property
    rw [hi, hj] at hh
    exact not_le_of_gt hij hh
  simp [hnot]

theorem schurUpperCombination_reconstruct {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, j < i → A i j = 0) :
    schurUpperCombination (fun p : SchurUpperIndex n => A p.val.1 p.val.2) = A := by
  ext i j
  by_cases hij : i ≤ j
  · exact schurUpperCombination_entry _ ⟨(i, j), hij⟩
  · rw [schurUpperCombination_lower_zero _ i j (lt_of_not_ge hij), hA i j (lt_of_not_ge hij)]

/-- The tangent map of the Schur parametrization at `T`: `(x, y) ↦ S T - T S + Y`, where `S` is
the skew-Hermitian matrix built from `x` and `Y` the upper-triangular matrix built from `y`. -/
def schurCoordinateTangent {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (p : SchurCoordinates n) : Matrix (Fin n) (Fin n) ℂ :=
  schurSkewCombination p.1 * T - T * schurSkewCombination p.1 + schurUpperCombination p.2

theorem schurCoordinateTangent_lower {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) (z : SchurCoordinates n) (p : SchurLowerIndex n) :
    schurCoordinateTangent T z (schurLowerRow p) (schurLowerCol p) =
      (schurLowerJacobian T *ᵥ z.1) p := by
  unfold schurCoordinateTangent
  have hz : schurUpperCombination z.2 (schurLowerRow p) (schurLowerCol p) = 0 :=
    schurUpperCombination_lower_zero z.2 _ _ p.property
  rw [Matrix.add_apply, hz, add_zero]
  exact (schurLowerJacobian_skew_commutator T hT z.1 p).symm

/-- The real square Schur differential is bijective whenever its diagonal is distinct. -/
theorem schurCoordinateTangent_bijective {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) (hd : Function.Injective (fun i => T i i)) :
    Function.Bijective (schurCoordinateTangent T) := by
  classical
  have hunit : IsUnit (schurLowerJacobian T) := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (schurLowerJacobian_det_ne_zero T hT hd))
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hunit
  have hsur := Matrix.mulVec_surjective_iff_isUnit.mpr hunit
  constructor
  · intro z w heq
    have hx : z.1 = w.1 := hinj (funext fun p => by
      have hh := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A (schurLowerRow p) (schurLowerCol
          p)) heq
      simpa only [schurCoordinateTangent_lower T hT] using hh)
    have hy : z.2 = w.2 := by
      have hu : schurUpperCombination z.2 = schurUpperCombination w.2 := by
        unfold schurCoordinateTangent at heq
        rw [hx] at heq
        exact add_left_cancel heq
      funext p
      have hh := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A p.val.1 p.val.2) hu
      simpa only [schurUpperCombination_entry] using hh
    exact Prod.ext hx hy
  · intro A
    obtain ⟨x, hx⟩ := hsur (fun p => A (schurLowerRow p) (schurLowerCol p))
    let C := schurSkewCombination x * T - T * schurSkewCombination x
    let R := A - C
    have hR : ∀ i j, j < i → R i j = 0 := by
      intro i j hij
      let p : SchurLowerIndex n := ⟨toLex (j, toDual i), hij⟩
      have hp := congrFun hx p
      have hc := schurLowerJacobian_skew_commutator T hT x p
      change R (schurLowerRow p) (schurLowerCol p) = 0
      change A (schurLowerRow p) (schurLowerCol p) - C (schurLowerRow p) (schurLowerCol p) = 0
      exact sub_eq_zero.mpr (hp.symm.trans hc)
    refine ⟨(x, fun p : SchurUpperIndex n => R p.val.1 p.val.2), ?_⟩
    change C + schurUpperCombination (fun p : SchurUpperIndex n => R p.val.1 p.val.2) = A
    rw [schurUpperCombination_reconstruct R hR]
    dsimp [R]
    abel

end
end GinibrePoincare

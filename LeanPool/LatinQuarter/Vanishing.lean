/-
Copyright (c) 2026 Richard Bean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Bean
-/
module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Algebra.CharP.Frobenius
public import LeanPool.LatinQuarter.Minors
public import LeanPool.LatinQuarter.SquareZero

/-!
# Vanishing of products of matrix minors
-/

@[expose] public section

namespace LatinQuarter
open scoped BigOperators Matrix

variable {R : Type*} [CommRing R] [CharP R 2]

/-- The square map is a ring homomorphism in characteristic two. -/
noncomputable abbrev squareHom : R →+* R := frobenius R 2

/-- Marked top-left block entries square to the identity, so that block
is invertible even though the coefficient ring is not a field. -/
theorem isUnit_det_of_square_map_eq_one {k : ℕ}
    (A : Matrix (Fin k) (Fin k) R)
    (hA : squareHom.mapMatrix A = 1) : IsUnit A.det := by
  have hs : A.det * A.det = 1 := by
    have hm := squareHom.map_det A
    rw [hA, Matrix.det_one] at hm
    simpa only [squareHom, frobenius_def, pow_two] using hm
  exact ⟨⟨A.det, A.det, hs, hs⟩, rfl⟩

/-- One block elimination gives a common ideal for all the minors. -/
theorem marked_blocks_minor_ideal {k h : ℕ}
    (A : Matrix (Fin k) (Fin k) R)
    (B : Matrix (Fin k) (Fin h) R)
    (C : Matrix (Fin h) (Fin k) R)
    (D : Matrix (Fin h) (Fin h) R)
    (hA : squareHom.mapMatrix A = 1)
    (hC : C.map squareHom = 0)
    (hD : D.map squareHom = 0) :
    ∃ z : Fin h × Fin h → R,
      (∀ j, z j * z j = 0) ∧
      ∀ t, AllMinorsIn (Matrix.fromBlocks A B C D) t
        (Ideal.span (Set.range z) ^ (t - k)) := by
  classical
  let := Matrix.invertibleOfIsUnitDet A (isUnit_det_of_square_map_eq_one A hA)
  let Z := D - C * ⅟A * B
  let z : Fin h × Fin h → R := fun p => Z p.1 p.2
  refine ⟨z, ?_, ?_⟩
  · have hm : squareHom.mapMatrix Z = 0 := by
      simp only [Z, RingHom.mapMatrix_apply, Matrix.map_sub _ (map_sub squareHom),
        Matrix.map_mul]
      change D.map squareHom -
        C.map squareHom * squareHom.mapMatrix (⅟A) * B.map squareHom = 0
      rw [hC, hD, Matrix.zero_mul, Matrix.zero_mul, sub_zero]
    intro j
    have hj := congrArg (fun M => M j.1 j.2) hm
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, squareHom,
      frobenius_def, pow_two, Matrix.zero_apply] using hj
  · intro t
    rw [Matrix.fromBlocks_eq_of_invertible₁₁ A B C D]
    apply allMinorsIn_mul_right
    apply allMinorsIn_mul_left
    apply allMinorsIn_fromBlocks_diagonal
    intro i j
    exact Ideal.subset_span ⟨(i, j), rfl⟩

/-- The abstract vanishing lemma: more residual factors than residual
positions force a repeated square-zero entry. -/
theorem marked_blocks_product_vanishes {k h : ℕ} {ι : Type*} [Fintype ι]
    (A : Matrix (Fin k) (Fin k) R)
    (B : Matrix (Fin k) (Fin h) R)
    (C : Matrix (Fin h) (Fin k) R)
    (D : Matrix (Fin h) (Fin h) R)
    (hA : squareHom.mapMatrix A = 1)
    (hC : C.map squareHom = 0)
    (hD : D.map squareHom = 0)
    (t : ι → ℕ)
    (r c : (i : ι) → Fin (t i) → Fin k ⊕ Fin h)
    (hbudget : h * h < ∑ i, (t i - k)) :
    (∏ i, ((Matrix.fromBlocks A B C D).submatrix (r i) (c i)).det) = 0 := by
  classical
  obtain ⟨z, hz, hm⟩ := marked_blocks_minor_ideal A B C D hA hC hD
  have hp := Ideal.prod_mem_prod (s := Finset.univ)
    (I := fun i => Ideal.span (Set.range z) ^ (t i - k))
    (x := fun i => ((Matrix.fromBlocks A B C D).submatrix (r i) (c i)).det)
    (fun i _ => hm (t i) (r i) (c i))
  rw [Finset.prod_pow_eq_pow_sum] at hp
  rw [span_square_zero_pow_eq_bot z hz (by simpa using hbudget)] at hp
  exact hp

end LatinQuarter

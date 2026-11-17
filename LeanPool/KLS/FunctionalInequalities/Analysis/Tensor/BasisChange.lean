/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Tensor.Coefficients

/-!
# Basis independence of the Hilbert–Schmidt norm of coefficient arrays

For a real `k`-linear form `Φ` on a finite-dimensional real inner product space `E` and an
orthonormal basis `b`, `coordTensor b Φ = (Φ (b i₁, …, b i_k))_i` is the coefficient array of
`Analysis/Tensor/Coefficients.lean` (Bizeul–Klartag–Lehec, arXiv:2610.05474v1, Section 2). Its
Euclidean norm is the Hilbert–Schmidt norm of `Φ`, which is an intrinsic quantity.

## What is proved

* `sum_coordTensor_sq_eq`: `∑ᵢ Φ(b i)² = ∑ₗ Φ(b' l)²` for any two orthonormal bases `b`, `b'`
  (of possibly differently indexed but equal cardinality `Fin n`, `Fin n'`);
* `norm_coordTensor_eq`: `‖coordTensor b Φ‖ = ‖coordTensor b' Φ‖`.

## The argument

Expanding each `b (i j)` in `b'` (`apply_eq_sum_coordTensor`) gives
`Φ (b ∘ i) = ∑ₗ Φ(b' ∘ l) Mᵢₗ` with `Mᵢₗ = ∏ⱼ ⟪b' (l j), b (i j)⟫`. The columns of `M` are
orthonormal: `∑ᵢ Mᵢₗ Mᵢₗ' = ∏ⱼ ∑ₘ ⟪b' (l j), b m⟫ ⟪b' (l' j), b m⟫ = ∏ⱼ ⟪b' (l j), b' (l' j)⟫`
by Parseval in `b`, and the last product is `1` if `l = l'` and `0` otherwise by orthonormality
of `b'`. Expanding the square therefore yields the sum of squares in `b'`. No induction on `k`
is needed.

## What this is not

This is a statement about real-valued multilinear forms only; it does not identify the norm with
an intrinsic Hilbert–Schmidt norm defined without bases, and it says nothing about the operator
norm beyond `norm_le_norm_coordTensor`.
-/

@[expose] public section

noncomputable section

open Finset
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The change-of-basis matrix between product bases is column-orthonormal:
`∑ᵢ (∏ⱼ ⟪b' (l j), b (i j)⟫) (∏ⱼ ⟪b' (l' j), b (i j)⟫) = δ_{l l'}`. -/
private lemma sum_prod_inner_mul_prod_inner {n n' k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (b' : OrthonormalBasis (Fin n') ℝ E) (l l' : Fin k → Fin n') :
    ∑ i : Fin k → Fin n, (∏ j, ⟪b' (l j), b (i j)⟫) * ∏ j, ⟪b' (l' j), b (i j)⟫ =
      if l = l' then 1 else 0 := by
  classical
  calc
    ∑ i : Fin k → Fin n, (∏ j, ⟪b' (l j), b (i j)⟫) * ∏ j, ⟪b' (l' j), b (i j)⟫
        = ∑ i : Fin k → Fin n, ∏ j, ⟪b' (l j), b (i j)⟫ * ⟪b' (l' j), b (i j)⟫ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.prod_mul_distrib]
    _ = ∏ j : Fin k, ∑ m : Fin n, ⟪b' (l j), b m⟫ * ⟪b' (l' j), b m⟫ := by
          rw [Fintype.prod_sum]
    _ = ∏ j : Fin k, ⟪b' (l j), b' (l' j)⟫ := by
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [← b.sum_inner_mul_inner (b' (l j)) (b' (l' j))]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [real_inner_comm (b' (l' j)) (b m)]
    _ = ∏ j : Fin k, (if l j = l' j then (1 : ℝ) else 0) := by
          refine Finset.prod_congr rfl fun j _ => ?_
          exact orthonormal_iff_ite.mp b'.orthonormal (l j) (l' j)
    _ = if l = l' then 1 else 0 := by
          rw [Finset.prod_boole]
          simp [funext_iff]

/-- The sum of squares of the coefficients of a multilinear form does not depend on the
orthonormal basis. -/
theorem sum_coordTensor_sq_eq {n n' k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (b' : OrthonormalBasis (Fin n') ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :
    ∑ i : Fin k → Fin n, coordTensor b Φ i ^ 2 = ∑ l : Fin k → Fin n', coordTensor b' Φ l ^ 2 := by
  classical
  set c := coordTensor b' Φ
  set M : (Fin k → Fin n) → (Fin k → Fin n') → ℝ := fun i l => ∏ j, ⟪b' (l j), b (i j)⟫
  have hexp (i : Fin k → Fin n) : coordTensor b Φ i = ∑ l, c l * M i l := by
    rw [coordTensor_apply]
    exact apply_eq_sum_coordTensor b' Φ (fun j => b (i j))
  calc
    ∑ i : Fin k → Fin n, coordTensor b Φ i ^ 2
        = ∑ i : Fin k → Fin n, ∑ l, ∑ l', c l * c l' * (M i l * M i l') := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hexp, sq, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
          ring
    _ = ∑ l, ∑ l', c l * c l' * ∑ i : Fin k → Fin n, M i l * M i l' := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l' _ => ?_
          rw [Finset.mul_sum]
    _ = ∑ l, ∑ l', c l * c l' * (if l = l' then 1 else 0) := by
          refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
          rw [sum_prod_inner_mul_prod_inner b b' l l']
    _ = ∑ l : Fin k → Fin n', c l ^ 2 := by
          refine Finset.sum_congr rfl fun l _ => ?_
          simp [sq]

/-- **Basis independence of the Hilbert–Schmidt norm.** The Euclidean norm of the coefficient
array of a real multilinear form is the same in any two orthonormal bases. -/
theorem norm_coordTensor_eq {n n' k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (b' : OrthonormalBasis (Fin n') ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :
    ‖coordTensor b Φ‖ = ‖coordTensor b' Φ‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  rw [sum_coordTensor_sq_eq b b' Φ]

end FunctionalInequalities.Analysis.Tensor

/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.SVI.Companion

/-! # The weighted trace form

Part of the SVI polynomial-sign certificate (#174).

`weightedTraceForm f q` is `(x, y) ↦ tr(q·x·y)` on `ℝ[X]/(f)`, nilpotents included, and the
Hermite matrix is its matrix in the power basis.

## Main definitions

* `weightedTraceForm`: the bilinear form `(x, y) ↦ tr(q·x·y)` on `AdjoinRoot f`, nilpotents
  included.

## Main results

* `weightedTraceForm_apply`: `weightedTraceForm f q x y` is the algebra trace of
  `aeval (root f) q * x * y`.
* `hermite_entry_eq_trace`: for `f ≠ 0`, the `(i, j)` entry of `hermite f q f.natDegree` is the
  algebra trace of `q(root f) * (root f)^(i + j)`.
* `hermite_eq_traceForm_matrix`: for `f ≠ 0`, `hermite f q f.natDegree` is the matrix of
  `weightedTraceForm f q` in the power basis.

## Tags

weighted trace form, Hermite matrix, quotient algebra, SVI, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI
open Polynomial

/-- The matrix entries are those of the weighted quotient-algebra trace
pairing in its power basis. -/
theorem hermite_entry_eq_trace (f q : ℝ[X]) (hf : f ≠ 0)
    (i j : Fin f.natDegree) :
    hermite f q f.natDegree i j =
      Algebra.trace ℝ (AdjoinRoot f)
        ((aeval (AdjoinRoot.root f) q) * (AdjoinRoot.root f)^(i.val+j.val)) := by
  unfold hermite
  simp_rw [trace_companion_pow_eq_algebraTrace f hf]
  rw [aeval_def, eval₂_eq_sum, sum_def, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [mul_assoc, ← pow_add, ← Algebra.smul_def, map_smul, smul_eq_mul]
  congr 2
  rw [Nat.add_comm]

/-- Weighted trace bilinear form on the full quotient, including nilpotents. -/
noncomputable def weightedTraceForm (f q : ℝ[X]) :
    LinearMap.BilinForm ℝ (AdjoinRoot f) :=
  (Algebra.traceForm ℝ (AdjoinRoot f)).compl₁₂
    (Algebra.lmul ℝ (AdjoinRoot f) (aeval (AdjoinRoot.root f) q)) LinearMap.id

theorem weightedTraceForm_apply (f q : ℝ[X]) (x y : AdjoinRoot f) :
    weightedTraceForm f q x y =
      Algebra.trace ℝ (AdjoinRoot f) (aeval (AdjoinRoot.root f) q * x * y) := by
  simp [weightedTraceForm, Algebra.traceForm_apply]

theorem hermite_eq_traceForm_matrix (f q : ℝ[X]) (hf : f ≠ 0) :
    hermite f q f.natDegree =
      (weightedTraceForm f q).toMatrix (AdjoinRoot.powerBasis hf).basis := by
  ext i j
  rw [hermite_entry_eq_trace f q hf]
  have hb (k : Fin f.natDegree) :
      (AdjoinRoot.powerBasis hf).basis k = AdjoinRoot.root f ^ (k : ℕ) :=
    (AdjoinRoot.powerBasis hf).basis_eq_pow k
  refine Eq.trans ?_ (LinearMap.BilinForm.toMatrix_apply _ _ i j).symm
  rw [weightedTraceForm_apply, pow_add, ← mul_assoc]
  exact congrArg _ (congrArg₂ (fun x y ↦ aeval (AdjoinRoot.root f) q * x * y)
    (hb i).symm (hb j).symm)

end SVI
end MathFin

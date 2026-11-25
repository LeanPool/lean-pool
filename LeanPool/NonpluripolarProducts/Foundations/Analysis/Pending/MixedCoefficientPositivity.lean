/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MixedCoefficientCongruence
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Positivity of the mixed coefficient on positive semidefinite inputs

Gram decomposition, slot multilinearity, and the rank-one formula
`C(Q₁,…,Qₙ) = |det V|²` show that the real part of the mixed coefficient of
positive semidefinite matrices is nonnegative.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.MixedMongeAmpere

open FirstPass FirstPass.MixedMongeAmpere

variable {n : ℕ}

/-- For rank-one positive inputs, the mixed coefficient is the squared norm
of the determinant of the matrix whose rows are the defining vectors. -/
private theorem mixedCoefficient_vecMulVec (v : Fin n → Fin n → ℂ) :
    mixedCoefficient (fun i => Matrix.vecMulVec (v i) (star (v i))) =
      Matrix.det (fun i j => v i j) * star (Matrix.det (fun i j => v i j)) := by
  rw [mixedCoefficient_vecMulVec']
  congr 1
  exact ((starRingEnd ℂ).map_det _).symm

/-- The real part of the actual permutation-sum coefficient is nonnegative
for PSD inputs. A proof is Gram decomposition, slot multilinearity, and the
rank-one formula `C(Q₁,...,Qₙ) = |det V|²`. Individual summands need not be PSD. -/
theorem mixedCoefficient_re_nonneg (H : Fin n → Matrix (Fin n) (Fin n) ℂ)
    (hH : ∀ i, (H i).PosSemidef) : 0 ≤ (mixedCoefficient H).re := by
  classical
  choose m v hv using fun i => Matrix.posSemidef_iff_eq_sum_vecMulVec.mp (hH i)
  have hExpand :
      mixedCoefficient H =
        ∑ r : ∀ i, Fin (m i),
          mixedCoefficient (fun i => Matrix.vecMulVec (v i (r i)) (star (v i (r i)))) := by
    rw [← mixedCoefficientML_apply]
    have hHsum : H = fun i => ∑ a, Matrix.vecMulVec (v i a) (star (v i a)) := by
      funext i
      exact hv i
    rw [hHsum]
    rw [MultilinearMap.map_sum]
    simp only [mixedCoefficientML_apply]
  rw [hExpand, Complex.re_sum]
  exact Finset.sum_nonneg fun r _ => by
    rw [mixedCoefficient_vecMulVec]
    let z : ℂ := Matrix.det (fun i j => v i (r i) j)
    change 0 ≤ (z * star z).re
    rw [Complex.star_def, Complex.mul_conj]
    simpa using Complex.normSq_nonneg z

end SGPT.Foundations.Analysis.Pending.MixedMongeAmpere

/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SkewNormalForm
public import LeanPool.VacuumBellSeparation.Gaussian.SymplecticBlocks

/-!
# The actual skew normal form in the source symplectic orientation

Applying the constructed rotation theorem to the negative map gives the
source block `ν Ω₂`. The normal form is then identified with the literal
matrix of the map in its constructed orthonormal basis.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped Kronecker

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_real_skew_symplectic_basis (A : E →ₗ[ℝ] E)
    (hA : A.adjoint = -A) (hinj : Function.Injective A) :
    ∃ (m : ℕ) (ν : Fin m → ℝ) (b : OrthonormalBasis (Fin m × Fin 2) ℝ E),
      (∀ i, 0 < ν i) ∧
      ∀ i, A (b (i, 0)) = (-ν i) • b (i, 1) ∧
        A (b (i, 1)) = ν i • b (i, 0) := by
  have hneg : (-A).adjoint = -(-A) := by simp [hA]
  have hinjneg : Function.Injective (-A) := by
    intro x y hxy
    apply hinj
    simpa only [LinearMap.neg_apply, neg_inj] using hxy
  obtain ⟨m, ν, b, hν, hb⟩ := exists_real_skew_normal_form (-A) hneg hinjneg
  refine ⟨m, ν, b, hν, fun i => ⟨?_, ?_⟩⟩
  · simpa only [LinearMap.neg_apply, neg_neg, neg_smul] using congrArg Neg.neg (hb i).1
  · simpa only [LinearMap.neg_apply, neg_neg, neg_smul] using congrArg Neg.neg (hb i).2

/-- Identification of the actual matrix from its action on the constructed
basis, with the positive source symplectic orientation. -/
theorem toMatrixOrthonormal_eq_modeDiagonal_symplectic {m : ℕ}
    (A : E →ₗ[ℝ] E) (ν : Fin m → ℝ)
    (b : OrthonormalBasis (Fin m × Fin 2) ℝ E)
    (hb : ∀ i, A (b (i, 0)) = (-ν i) • b (i, 1) ∧
      A (b (i, 1)) = ν i • b (i, 0)) :
    LinearMap.toMatrixOrthonormal b A = modeDiagonal ν * modeSymplecticForm := by
  ext ⟨i, a⟩ ⟨j, c⟩
  rw [LinearMap.toMatrixOrthonormal_apply_apply]
  by_cases hij : i = j
  · subst j
    fin_cases a <;> fin_cases c <;>
      simp [(hb i).1, (hb i).2, real_inner_smul_right,
        orthonormal_iff_ite.mp b.orthonormal, modeDiagonal, Matrix.diagonal_mul,
        modeSymplecticForm, oneModeSymplecticForm]
  · fin_cases a <;> fin_cases c <;>
      simp [(hb j).1, (hb j).2, real_inner_smul_right,
        orthonormal_iff_ite.mp b.orthonormal, modeDiagonal, Matrix.diagonal_mul,
        modeSymplecticForm, oneModeSymplecticForm, hij, Prod.mk.injEq]

/-- Every injective real skew-adjoint map has a genuine orthonormal matrix
normal form `diag(ν) Ω`, with all frequencies positive. -/
theorem exists_real_skew_matrix_normal_form (A : E →ₗ[ℝ] E)
    (hA : A.adjoint = -A) (hinj : Function.Injective A) :
    ∃ (m : ℕ) (ν : Fin m → ℝ) (b : OrthonormalBasis (Fin m × Fin 2) ℝ E),
      (∀ i, 0 < ν i) ∧
      LinearMap.toMatrixOrthonormal b A = modeDiagonal ν * modeSymplecticForm := by
  obtain ⟨m, ν, b, hν, hb⟩ := exists_real_skew_symplectic_basis A hA hinj
  exact ⟨m, ν, b, hν, toMatrixOrthonormal_eq_modeDiagonal_symplectic A ν b hb⟩

end VacuumBellSeparation.Gaussian

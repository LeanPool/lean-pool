/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.HermitianTraceDerivative
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Algebra.Algebra.Spectrum.Pi

/-!
# Genuine finite complex-matrix functional calculus identities

Real diagonal matrices and actual unitary conjugations commute with the
continuous functional calculus. Finite spectra justify arbitrary scalar
functions here. In particular, the even scalar trace can be evaluated
on the actual operator absolute value without choosing signed eigenvectors.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Complex diagonal star alg hom. -/
def complexDiagonalStarAlgHom : (ι → ℂ) →⋆ₐ[ℂ] Matrix ι ι ℂ :=
  { Matrix.diagonalAlgHom ℂ with
    map_star' := by
      intro d
      ext i j
      by_cases h : i = j
      · subst j
        simp []
      · simp [h, Ne.symm h] }

theorem cfc_complex_real_diagonal (f : ℝ → ℝ) (d : ι → ℝ) :
    cfc f (Matrix.diagonal (fun i => (d i : ℂ))) =
      Matrix.diagonal (fun i => (f (d i) : ℂ)) := by
  let : CStarAlgebra (ι → ℂ) := {}
  let : IsometricContinuousFunctionalCalculus ℝ (ι → ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
  let a : ι → ℂ := fun i => (d i : ℂ)
  have ha : IsSelfAdjoint a := by
    change star a = a
    funext i
    simp [a]
  have hdiag : IsSelfAdjoint (complexDiagonalStarAlgHom (ι := ι) a) :=
    (Matrix.isHermitian_diagonal_of_self_adjoint a ha).isSelfAdjoint
  have hs : (⋃ i, spectrum ℝ (a i)).Finite :=
    Set.finite_iUnion fun i => (Set.finite_singleton (d i)).subset
      (CFC.spectrum_algebraMap_subset (A := ℂ) (d i))
  have hm := StarAlgHomClass.map_cfc (complexDiagonalStarAlgHom (ι := ι)) f a
    (by rw [Pi.spectrum_eq]; exact hs.continuousOn f)
    (complexDiagonalStarAlgHom.toAlgHom.toLinearMap.continuous_of_finiteDimensional)
    ha hdiag
  rw [cfc_map_pi (S := ℂ) f a (hs.continuousOn f) ha
    (fun i => by change star (d i : ℂ) = (d i : ℂ); simp)] at hm
  have he : (fun i => cfc f (a i)) = fun i => (f (d i) : ℂ) := by
    funext i
    exact cfc_algebraMap (A := ℂ) (d i) f
  rw [he] at hm
  exact hm.symm

theorem cfc_complex_unitary_conjugate (U : unitary (Matrix ι ι ℂ))
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ) =
      (U : Matrix ι ι ℂ) * cfc f A * (U : Matrix ι ι ℂ)ᴴ := by
  let φ := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  have hφ : IsSelfAdjoint (φ A) := by
    simpa only [φ, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
      (Matrix.isHermitian_mul_mul_conjTranspose (U : Matrix ι ι ℂ) hA).isSelfAdjoint
  have hcφ : Continuous φ := by
    change Continuous (fun B : Matrix ι ι ℂ =>
      (U : Matrix ι ι ℂ) * B * star (U : Matrix ι ι ℂ))
    exact (continuous_const.mul continuous_id).mul continuous_const
  have hm := StarAlgHomClass.map_cfc φ f A (A.finite_real_spectrum.continuousOn f)
    hcφ hA.isSelfAdjoint hφ
  simpa only [φ, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using hm.symm

theorem real_trace_cfc_unitary_conjugate (U : unitary (Matrix ι ι ℂ))
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ)).trace.re =
      (cfc f A).trace.re := by
  rw [cfc_complex_unitary_conjugate U hA f, Matrix.trace_mul_cycle]
  change (star (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ) * cfc f A).trace.re = _
  rw [Unitary.coe_star_mul_self, Matrix.one_mul]

theorem cfc_complex_abs_composition {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc (fun x : ℝ => f |x|) A = cfc f (CFC.abs A) := by
  have hf : ContinuousOn f ((fun x : ℝ => ‖x‖) '' spectrum ℝ A) :=
    (A.finite_real_spectrum.image _).continuousOn f
  have h := cfc_comp' f (fun x : ℝ => ‖x‖) A hf continuous_norm.continuousOn hA.isSelfAdjoint
  simpa only [Real.norm_eq_abs, CFC.abs_eq_cfc_norm A hA.isSelfAdjoint] using h

theorem cfc_trace_even_of_abs_unitary_diagonal {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (U : unitary (Matrix ι ι ℂ)) (d : ι → ℝ)
    (habs : CFC.abs A = (U : Matrix ι ι ℂ) * Matrix.diagonal (fun i => (d i : ℂ)) *
      (U : Matrix ι ι ℂ)ᴴ) (f : ℝ → ℝ) :
    (cfc (fun x : ℝ => f |x|) A).trace.re = ∑ i, f (d i) := by
  have hd : (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian :=
    Matrix.isHermitian_diagonal_of_self_adjoint _ (by
      change star (fun i => (d i : ℂ)) = _
      funext i
      simp)
  rw [cfc_complex_abs_composition hA f, habs, real_trace_cfc_unitary_conjugate U hd f,
    cfc_complex_real_diagonal, Matrix.trace_diagonal, Complex.re_sum]
  simp only [Complex.ofReal_re]

end VacuumBellSeparation.Gaussian

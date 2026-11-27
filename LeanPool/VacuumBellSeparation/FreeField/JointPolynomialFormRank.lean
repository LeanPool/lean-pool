/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointPolynomialMomentRange
public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Actual polynomial moment operators have cubic rank

Only the left spatial exponent determines a range vector. The number of
six-variable coefficients therefore does not inflate the rank to sixth
order. The result applies equally to real and complex Hilbert spaces.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open MvPolynomial InnerProductSpace
open scoped InnerProductSpace

/-- Spatial six left exponent defined as `d (Fin.castAdd 3 i)`. -/
def spatialSixLeftExponent (d : Fin 6 →₀ ℕ) (i : Fin 3) : ℕ := d (Fin.castAdd 3 i)
/-- Spatial six right exponent defined as `d (Fin.natAdd 3 i)`. -/
def spatialSixRightExponent (d : Fin 6 →₀ ℕ) (i : Fin 3) : ℕ := d (Fin.natAdd 3 i)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The actual finite sum of rank-one moment operators. Real coefficient
parts implement the real restriction of the complex polynomial kernel. -/
def jointPolynomialMomentOperator (v : (Fin 3 → ℕ) → E) (P : MvPolynomial (Fin 6) ℂ) :
    E →L[𝕜] E :=
  ∑ d ∈ P.support, (algebraMap ℝ 𝕜 (P.coeff d).re) •
    rankOne 𝕜 (v (spatialSixLeftExponent d)) (v (spatialSixRightExponent d))

theorem range_jointPolynomialMomentOperator_le (v : (Fin 3 → ℕ) → E)
    (P : MvPolynomial (Fin 6) ℂ) {D : ℕ} (hP : P.totalDegree ≤ D) :
    (jointPolynomialMomentOperator (𝕜 := 𝕜) v P).toLinearMap.range ≤
      spatialMomentDegreeRange (𝕜 := 𝕜) v D := by
  rintro _ ⟨x, rfl⟩
  change jointPolynomialMomentOperator (𝕜 := 𝕜) v P x ∈
    spatialMomentDegreeRange (𝕜 := 𝕜) v D
  simp only [jointPolynomialMomentOperator, _root_.sum_apply,
    smul_apply, rankOne_apply]
  apply Submodule.sum_mem
  intro d hd
  apply Submodule.smul_mem
  apply Submodule.smul_mem
  exact mem_spatialMomentDegreeRange v D (spatialSixLeftExponent d) (fun i =>
    (MvPolynomial.le_degreeOf_of_mem_support (Fin.castAdd 3 i) hd).trans
      ((MvPolynomial.degreeOf_le_totalDegree P _).trans hP))

instance finiteDimensional_range_jointPolynomialMomentOperator
    (v : (Fin 3 → ℕ) → E) (P : MvPolynomial (Fin 6) ℂ) :
    FiniteDimensional 𝕜 (jointPolynomialMomentOperator (𝕜 := 𝕜) v P).toLinearMap.range :=
  Submodule.finiteDimensional_of_le (range_jointPolynomialMomentOperator_le v P le_rfl)

theorem finrank_jointPolynomialMomentOperator_le (v : (Fin 3 → ℕ) → E)
    (P : MvPolynomial (Fin 6) ℂ) {D : ℕ} (hP : P.totalDegree ≤ D) :
    Module.finrank 𝕜 (jointPolynomialMomentOperator (𝕜 := 𝕜) v P).toLinearMap.range ≤
      (D + 1) ^ 3 :=
  (Submodule.finrank_mono (range_jointPolynomialMomentOperator_le v P hP)).trans
    (finrank_spatialMomentDegreeRange_le v D)

theorem inner_jointPolynomialMomentOperator_real {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (v : (Fin 3 → ℕ) → F) (P : MvPolynomial (Fin 6) ℂ) (x y : F) :
    inner ℝ x (jointPolynomialMomentOperator (𝕜 := ℝ) v P y) =
      ∑ d ∈ P.support, (P.coeff d).re * inner ℝ x (v (spatialSixLeftExponent d)) *
        inner ℝ y (v (spatialSixRightExponent d)) := by
  simp only [jointPolynomialMomentOperator, _root_.sum_apply, inner_sum,
    smul_apply, rankOne_apply, real_inner_smul_right,
    Algebra.algebraMap_self_apply]
  apply Finset.sum_congr rfl
  intro d hd
  rw [real_inner_comm (v (spatialSixRightExponent d)) y]
  ring

end VacuumBellSeparation

/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointPolynomialComplexification
public import LeanPool.VacuumBellSeparation.Gaussian.FiniteRankNuclearBound

/-!
# One cubic moment range controls both sectors and their increments

Successive polynomials use the same actual moment families. Their
difference therefore remains in the same two-sector degree space; no
extra factor for the number of polynomial terms or increments is needed.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open Gaussian
open scoped ENNReal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Joint moment degree range. -/
def jointMomentDegreeRange (u v : (Fin 3 → ℕ) → E) (D : ℕ) : Submodule 𝕜 E :=
  Submodule.span 𝕜 (Set.range fun p : Bool × (Fin 3 → Fin (D + 1)) =>
    (if p.1 then v else u) (fun i => (p.2 i).val))

instance finiteDimensional_jointMomentDegreeRange (u v : (Fin 3 → ℕ) → E) (D : ℕ) :
    FiniteDimensional 𝕜 (jointMomentDegreeRange (𝕜 := 𝕜) u v D) :=
  FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)

theorem spatialMomentDegreeRange_le_joint_left (u v : (Fin 3 → ℕ) → E) (D : ℕ) :
    spatialMomentDegreeRange (𝕜 := 𝕜) u D ≤ jointMomentDegreeRange (𝕜 := 𝕜) u v D := by
  apply Submodule.span_le.mpr
  rintro _ ⟨α, rfl⟩
  exact Submodule.subset_span ⟨(false, α), rfl⟩

theorem spatialMomentDegreeRange_le_joint_right (u v : (Fin 3 → ℕ) → E) (D : ℕ) :
    spatialMomentDegreeRange (𝕜 := 𝕜) v D ≤ jointMomentDegreeRange (𝕜 := 𝕜) u v D := by
  apply Submodule.span_le.mpr
  rintro _ ⟨α, rfl⟩
  exact Submodule.subset_span ⟨(true, α), rfl⟩

theorem finrank_jointMomentDegreeRange_le (u v : (Fin 3 → ℕ) → E) (D : ℕ) :
    Module.finrank 𝕜 (jointMomentDegreeRange (𝕜 := 𝕜) u v D) ≤ 2 * (D + 1) ^ 3 := by
  calc
    _ ≤ Fintype.card (Bool × (Fin 3 → Fin (D + 1))) :=
      finrank_range_le_card (R := 𝕜)
        (fun p : Bool × (Fin 3 → Fin (D + 1)) =>
          (if p.1 then v else u) (fun i => (p.2 i).val))
    _ = 2 * (D + 1) ^ 3 := by
      simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fun, Fintype.card_fin]

theorem range_jointPolynomial_difference_le
    (u v : (Fin 3 → ℕ) → E) (P Q P' Q' : MvPolynomial (Fin 6) ℂ)
    {D : ℕ} (hP : P.totalDegree ≤ D) (hQ : Q.totalDegree ≤ D)
    (hP' : P'.totalDegree ≤ D) (hQ' : Q'.totalDegree ≤ D) :
    ((jointPolynomialMomentOperator (𝕜 := 𝕜) u P + jointPolynomialMomentOperator (𝕜 := 𝕜) v Q) -
      (jointPolynomialMomentOperator (𝕜 := 𝕜) u P' + jointPolynomialMomentOperator
        (𝕜 := 𝕜) v Q')).toLinearMap.range ≤
        jointMomentDegreeRange (𝕜 := 𝕜) u v D := by
  have hp := (range_jointPolynomialMomentOperator_le (𝕜 := 𝕜) u P hP).trans
    (spatialMomentDegreeRange_le_joint_left (𝕜 := 𝕜) u v D)
  have hq := (range_jointPolynomialMomentOperator_le (𝕜 := 𝕜) v Q hQ).trans
    (spatialMomentDegreeRange_le_joint_right (𝕜 := 𝕜) u v D)
  have hp' := (range_jointPolynomialMomentOperator_le (𝕜 := 𝕜) u P' hP').trans
    (spatialMomentDegreeRange_le_joint_left (𝕜 := 𝕜) u v D)
  have hq' := (range_jointPolynomialMomentOperator_le (𝕜 := 𝕜) v Q' hQ').trans
    (spatialMomentDegreeRange_le_joint_right (𝕜 := 𝕜) u v D)
  rintro _ ⟨x, rfl⟩
  exact Submodule.sub_mem _
    (Submodule.add_mem _ (hp ⟨x, rfl⟩) (hq ⟨x, rfl⟩))
    (Submodule.add_mem _ (hp' ⟨x, rfl⟩) (hq' ⟨x, rfl⟩))

theorem finrank_jointPolynomial_difference_le
    (u v : (Fin 3 → ℕ) → E) (P Q P' Q' : MvPolynomial (Fin 6) ℂ)
    {D : ℕ} (hP : P.totalDegree ≤ D) (hQ : Q.totalDegree ≤ D)
    (hP' : P'.totalDegree ≤ D) (hQ' : Q'.totalDegree ≤ D) :
    Module.finrank 𝕜
      ((jointPolynomialMomentOperator (𝕜 := 𝕜) u P + jointPolynomialMomentOperator (𝕜 := 𝕜) v Q) -
        (jointPolynomialMomentOperator (𝕜 := 𝕜) u P' + jointPolynomialMomentOperator
          (𝕜 := 𝕜) v Q')).toLinearMap.range ≤
      2 * (D + 1) ^ 3 :=
  (Submodule.finrank_mono (range_jointPolynomial_difference_le u v P Q P' Q'
    hP hQ hP' hQ')).trans (finrank_jointMomentDegreeRange_le u v D)

theorem nuclear_jointPolynomial_difference_le
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (u v : (Fin 3 → ℕ) → F) (P Q P' Q' : MvPolynomial (Fin 6) ℂ)
    {D : ℕ} (hP : P.totalDegree ≤ D) (hQ : Q.totalDegree ≤ D)
    (hP' : P'.totalDegree ≤ D) (hQ' : Q'.totalDegree ≤ D)
    (hA : IsSelfAdjoint
      ((jointPolynomialMomentOperator (𝕜 := ℂ) u P + jointPolynomialMomentOperator (𝕜 := ℂ) v Q) -
        (jointPolynomialMomentOperator (𝕜 := ℂ) u P' + jointPolynomialMomentOperator
          (𝕜 := ℂ) v Q'))) :
    operatorTraceNorm
      ((jointPolynomialMomentOperator (𝕜 := ℂ) u P + jointPolynomialMomentOperator (𝕜 := ℂ) v Q) -
        (jointPolynomialMomentOperator (𝕜 := ℂ) u P' + jointPolynomialMomentOperator
          (𝕜 := ℂ) v Q')) ≤
      ENNReal.ofReal ((2 * (D + 1) ^ 3 : ℕ) *
        ‖(jointPolynomialMomentOperator (𝕜 := ℂ) u P + jointPolynomialMomentOperator (𝕜 := ℂ) v Q) -
          (jointPolynomialMomentOperator (𝕜 := ℂ) u P' + jointPolynomialMomentOperator
            (𝕜 := ℂ) v Q')‖) := by
  apply (operatorTraceNorm_le_finrank_mul_norm_of_range_le hA
    (jointMomentDegreeRange (𝕜 := ℂ) u v D)
    (range_jointPolynomial_difference_le u v P Q P' Q' hP hQ hP' hQ')).trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast finrank_jointMomentDegreeRange_le (𝕜 := ℂ) u v D) (norm_nonneg _)

end VacuumBellSeparation

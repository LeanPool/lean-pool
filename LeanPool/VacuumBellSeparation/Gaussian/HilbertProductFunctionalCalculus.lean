/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ComplexifiedHilbertProduct
public import LeanPool.VacuumBellSeparation.Gaussian.NormalizedCommutation
public import LeanPool.VacuumBellSeparation.Gaussian.UnitaryTrace
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi

/-!
# Actual functional calculus on the Hilbert product

The block map is a continuous unital star-algebra homomorphism, so actual
positive powers and reserve square roots act separately in the two
regional Hilbert spaces. All exponents here are nonnegative; zero in a
reserve spectrum is allowed throughout.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap

-- Resolve the native real scalar algebra before specializing its carrier to
-- the completed Hilbert product. This is the existing CLM algebra instance.
/-- Hilbert product native real algebra with underlying type `ContinuousLinearMap.algebra`. -/
noncomputable abbrev hilbertProductNativeRealAlgebra {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] :
    Algebra ℝ (G →L[ℂ] G) := ContinuousLinearMap.algebra

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Real algebra obtained by restricting scalars on the operators on a Hilbert product. -/
local instance hilbertProductOperatorRealAlgebra :
    Algebra ℝ (WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F)) :=
  hilbertProductNativeRealAlgebra

theorem complexHilbertProductOperator_adjoint (A : E →L[ℂ] E) (B : F →L[ℂ] F) :
    (complexHilbertProductOperator A B).adjoint = complexHilbertProductOperator A.adjoint
      B.adjoint := by
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [adjoint_inner_right]
  simp only [complexHilbertProductOperator_apply, WithLp.prod_inner_apply,
    adjoint_inner_right,
    WithLp.ofLp_fst, WithLp.ofLp_snd]

/-- Continuous linear map for the hilbert product star alg hom, of type `((E →L[ℂ] E) × (F →L[ℂ]
F)) →⋆ₐ[ℂ] (WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F)) where toFun p`. -/
def hilbertProductStarAlgHom : ((E →L[ℂ] E) × (F →L[ℂ] F)) →⋆ₐ[ℂ]
    (WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F)) where
  toFun p := complexHilbertProductOperator p.1 p.2
  map_zero' := by ext x; rfl
  map_one' := by ext x; rfl
  map_add' p q := by ext x; rfl
  map_mul' p q := by ext x; rfl
  commutes' c := by ext x; rfl
  map_star' p := (complexHilbertProductOperator_adjoint p.1 p.2).symm

private theorem hilbertProductStarAlgHom_apply (p : (E →L[ℂ] E) × (F →L[ℂ] F)) :
    hilbertProductStarAlgHom p = complexHilbertProductOperator p.1 p.2 := rfl

theorem hilbertProductStarAlgHom_continuous :
    Continuous (hilbertProductStarAlgHom (E := E) (F := F)) := by
  apply AddMonoidHomClass.continuous_of_bound _ 1
  intro p
  simpa only [one_mul, Prod.norm_def, hilbertProductStarAlgHom_apply] using
    norm_complexHilbertProductOperator_le p.1 p.2
      ((norm_nonneg p.1).trans (le_max_left _ _)) (le_max_left _ _) (le_max_right _ _)

theorem complexHilbertProductOperator_nonneg {A : E →L[ℂ] E} {B : F →L[ℂ] F}
    (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ complexHilbertProductOperator A B :=
  map_nonneg hilbertProductStarAlgHom (show (0 : (E →L[ℂ] E) × (F →L[ℂ] F)) ≤ (A, B) from ⟨hA, hB⟩)

theorem complexHilbertProductOperator_isSelfAdjoint {A : E →L[ℂ] E} {B : F →L[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (complexHilbertProductOperator A B) := by
  change (complexHilbertProductOperator A B).adjoint = _
  rw [complexHilbertProductOperator_adjoint, hA.adjoint_eq, hB.adjoint_eq]

theorem cfc_complexHilbertProductOperator (f : ℝ → ℝ) (hf : Continuous f)
    {A : E →L[ℂ] E} {B : F →L[ℂ] F} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    cfc f (complexHilbertProductOperator A B) = complexHilbertProductOperator (cfc f A)
      (cfc f B) := by
  let : CStarAlgebra ((E →L[ℂ] E) × (F →L[ℂ] F)) := {}
  let : IsometricContinuousFunctionalCalculus ℝ
      ((E →L[ℂ] E) × (F →L[ℂ] F)) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
  have hp : IsSelfAdjoint (A, B) := by
    change (star A, star B) = (A, B)
    rw [hA.star_eq, hB.star_eq]
  have hm := StarAlgHomClass.map_cfc (hilbertProductStarAlgHom (E := E) (F := F)) f (A, B)
    hf.continuousOn hilbertProductStarAlgHom_continuous hp
      (complexHilbertProductOperator_isSelfAdjoint hA hB)
  rw [cfc_map_prod (S := ℂ) f A B hf.continuousOn hp hA hB] at hm
  simpa only [hilbertProductStarAlgHom_apply] using hm.symm

theorem complexHilbertProductOperator_rpow {A : E →L[ℂ] E} {B : F →L[ℂ] F}
    (hA : 0 ≤ A) (hB : 0 ≤ B) {p : ℝ} (hp : 0 ≤ p) :
    (complexHilbertProductOperator A B) ^ p = complexHilbertProductOperator (A ^ p) (B ^ p) := by
  rw [CFC.rpow_eq_cfc_real (complexHilbertProductOperator_nonneg hA hB),
    CFC.rpow_eq_cfc_real hA, CFC.rpow_eq_cfc_real hB]
  exact cfc_complexHilbertProductOperator _ (Real.continuous_rpow_const hp)
    hA.isSelfAdjoint hB.isSelfAdjoint

theorem complexHilbertProductOperator_sqrt {A : E →L[ℂ] E} {B : F →L[ℂ] F}
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    CFC.sqrt (complexHilbertProductOperator A B) =
      complexHilbertProductOperator (CFC.sqrt A) (CFC.sqrt B) := by
  simp only [CFC.sqrt_eq_rpow]
  exact complexHilbertProductOperator_rpow (p := (1 / 2 : ℝ)) hA hB (by norm_num)

theorem complexHilbertProductOperator_reserveSquare (A : E →L[ℂ] E) (B : F →L[ℂ] F) :
    reserveSquare (complexHilbertProductOperator A B) =
      complexHilbertProductOperator (reserveSquare A) (reserveSquare B) := by
  have hm := map_sub (hilbertProductStarAlgHom (E := E) (F := F)) 1 ((A, B) ^ 2)
  have hp : (1 : (E →L[ℂ] E) × (F →L[ℂ] F)) - (A, B) ^ 2 =
      (1 - A ^ 2, 1 - B ^ 2) := rfl
  rw [map_one, map_pow, hp] at hm
  simpa only [hilbertProductStarAlgHom_apply, reserveSquare] using hm.symm

theorem complexHilbertProductOperator_reserve {A : E →L[ℂ] E} {B : F →L[ℂ] F}
    (hA : IsSelfAdjoint A) (hAn : ‖A‖ ≤ 1) (hB : IsSelfAdjoint B) (hBn : ‖B‖ ≤ 1) :
    reserve (complexHilbertProductOperator A B) = complexHilbertProductOperator (reserve A)
      (reserve B) := by
  rw [reserve, complexHilbertProductOperator_reserveSquare,
    complexHilbertProductOperator_sqrt (reserveSquare_nonneg hA hAn) (reserveSquare_nonneg hB hBn)]
  simp only [reserve]

theorem complexHilbertProductOperator_reserve_rpow {A : E →L[ℂ] E} {B : F →L[ℂ] F}
    (hA : IsSelfAdjoint A) (hAn : ‖A‖ ≤ 1) (hB : IsSelfAdjoint B) (hBn : ‖B‖ ≤ 1)
    {p : ℝ} (hp : 0 ≤ p) :
    reserve (complexHilbertProductOperator A B) ^ p =
      complexHilbertProductOperator (reserve A ^ p) (reserve B ^ p) := by
  rw [complexHilbertProductOperator_reserve hA hAn hB hBn]
  have hRA : 0 ≤ reserve A := CFC.sqrt_nonneg (reserveSquare A)
  have hRB : 0 ≤ reserve B := CFC.sqrt_nonneg (reserveSquare B)
  exact complexHilbertProductOperator_rpow (A := reserve A) (B := reserve B)
    (p := p) hRA hRB hp

end VacuumBellSeparation.Gaussian

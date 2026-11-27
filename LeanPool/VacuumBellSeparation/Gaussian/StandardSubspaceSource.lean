/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ComplexConjugation
public import LeanPool.VacuumBellSeparation.Gaussian.NormalizedCommutation
public import LeanPool.VacuumBellSeparation.FreeField.PolarUnitary

/-!
# The actual source complexification of an arbitrary standard real subspace

Only the defining closedness, separation and cyclicity of Mathlib's
StandardSubspace are used. The map is the literal inclusion x+iy in the
ambient Hilbert space. No physical-region or bounded-inverse assumption is
introduced when passing to the general standard-subspace setting.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian
open ClosedSubmodule ContinuousLinearMap HilbertComplexification
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Standard source with underlying type `HilbertComplexification S.toClosedSubmodule`. -/
abbrev StandardSource (S : StandardSubspace H) := HilbertComplexification S.toClosedSubmodule

/-- Linear isometry for the standard real inclusion, of type `S.toClosedSubmodule →ₗᵢ[ℝ] H where
toFun x`. -/
noncomputable def standardRealInclusion (S : StandardSubspace H) :
    S.toClosedSubmodule →ₗᵢ[ℝ] H where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

/-- Standard source map obtained from `sourceMap`. -/
noncomputable def standardSourceMap (S : StandardSubspace H) : StandardSource S →L[ℂ] H :=
  sourceMap (standardRealInclusion S)

omit [CompleteSpace H] in
@[simp] theorem standardSourceMap_apply (S : StandardSubspace H) (z : StandardSource S) :
    standardSourceMap S z = (z.re : H) + Complex.I • (z.im : H) := rfl

omit [CompleteSpace H] in
theorem standardSourceMap_eq_zero (S : StandardSubspace H) (z : StandardSource S)
    (hz : standardSourceMap S z = 0) : z = 0 := by
  have hsum : (z.re : H) + Complex.I • (z.im : H) = 0 := hz
  have hre : (z.re : H) = Complex.I • (-(z.im : H)) := by
    rw [smul_neg]
    exact eq_neg_of_add_eq_zero_left hsum
  have himem : (z.re : H) ∈ S.toClosedSubmodule.mulI := by
    rw [hre]
    change scalarSMulCLE H Complex.UnitI (-(z.im : H)) ∈
      S.toClosedSubmodule.mapEquiv (scalarSMulCLE H Complex.UnitI)
    rw [ClosedSubmodule.mem_mapEquiv_iff']
    exact S.toClosedSubmodule.neg_mem z.im.property
  have hmem : (z.re : H) ∈ S.toClosedSubmodule ⊓ S.toClosedSubmodule.mulI :=
    ⟨z.re.property, himem⟩
  rw [S.IsSeparating] at hmem
  have hr0 : (z.re : H) = 0 := hmem
  have hi0 : (z.im : H) = 0 := by
    rw [hr0, zero_add] at hsum
    exact (smul_eq_zero.mp hsum).resolve_left Complex.I_ne_zero
  apply HilbertComplexification.ext
  · exact Subtype.ext hr0
  · exact Subtype.ext hi0

omit [CompleteSpace H] in
theorem standardSourceMap_injective (S : StandardSubspace H) :
    Function.Injective (standardSourceMap S) := by
  intro x y h
  apply sub_eq_zero.mp
  apply standardSourceMap_eq_zero S
  rw [map_sub, h, sub_self]

omit [CompleteSpace H] in
theorem standardSourceMap_denseRange (S : StandardSubspace H) :
    DenseRange (standardSourceMap S) := by
  let C : ClosedSubmodule ℝ H := ((standardSourceMap S).restrictScalars ℝ).range.closure
  have hS : S.toClosedSubmodule ≤ C := by
    intro x hx
    apply subset_closure
    refine ⟨ofReal ⟨x, hx⟩, ?_⟩
    change standardSourceMap S (ofReal ⟨x, hx⟩) = x
    rw [standardSourceMap, sourceMap_ofReal]
    rfl
  have hiS : S.toClosedSubmodule.mulI ≤ C := by
    intro x hx
    have hpre := (ClosedSubmodule.mem_mapEquiv_iff
      (scalarSMulCLE H Complex.UnitI) S.toClosedSubmodule x).mp hx
    let y : S.toClosedSubmodule := ⟨(scalarSMulCLE H Complex.UnitI).symm x, hpre⟩
    apply subset_closure
    refine ⟨Complex.I • ofReal y, ?_⟩
    change standardSourceMap S (Complex.I • ofReal y) = x
    rw [map_smul]
    have hreal : standardSourceMap S (ofReal y) = (y : H) := by
      simp only [standardSourceMap, sourceMap_ofReal]
      rfl
    rw [hreal]
    exact (scalarSMulCLE H Complex.UnitI).apply_symm_apply x
  have hC : C = ⊤ := by
    apply top_unique
    rw [← S.IsCyclic]
    exact sup_le hS hiS
  rw [denseRange_iff_closure_range]
  change (C : Set H) = Set.univ
  rw [hC]
  rfl

/-- Continuous linear map for the standard gram, of type `StandardSource S →L[ℂ] StandardSource
S`. -/
noncomputable def standardGram (S : StandardSubspace H) : StandardSource S →L[ℂ] StandardSource S :=
  (standardSourceMap S).adjoint.comp (standardSourceMap S)

/-- Standard conjugate gram obtained from `conjugateOperator`. -/
noncomputable def standardConjugateGram (S : StandardSubspace H) :
    StandardSource S →L[ℂ] StandardSource S := conjugateOperator (standardGram S)

theorem standardGram_nonneg (S : StandardSubspace H) : 0 ≤ standardGram S :=
  nonneg_iff_isPositive.mpr (isPositive_adjoint_comp_self (standardSourceMap S))

theorem standardGram_injective (S : StandardSubspace H) : Function.Injective (standardGram S) := by
  intro x y h
  apply standardSourceMap_injective S
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hG : standardGram S (x - y) = 0 := by rw [map_sub, h, sub_self]
  have hn := (standardSourceMap S).apply_norm_sq_eq_inner_adjoint_right (x - y)
  change ‖standardSourceMap S (x - y)‖ ^ 2 = (inner ℂ (x - y) (standardGram S (x - y))).re at hn
  rw [hG, inner_zero_right, Complex.zero_re] at hn
  simpa only [map_sub] using (sq_eq_zero_iff.mp hn)

theorem standardConjugateGram_eq_two_sub (S : StandardSubspace H) :
    standardConjugateGram S = 2 - standardGram S := by
  rw [standardConjugateGram, standardGram, standardSourceMap,
    conjugate_sourceMap_gram, sourceMap_adjoint_mul_self]
  rw [show (2 : StandardSource S →L[ℂ] StandardSource S) = 1 + 1 by norm_num]
  abel

theorem standardConjugateGram_nonneg (S : StandardSubspace H) : 0 ≤ standardConjugateGram S := by
  rw [standardConjugateGram, standardGram, standardSourceMap, conjugate_sourceMap_gram]
  exact gramMinus_nonneg
    (normalizedCommutation_isSelfAdjoint (complexCommutation_mem_skewAdjoint
      (standardRealInclusion S)))
    (norm_normalizedCommutation_le_one (norm_complexCommutation_le_two (standardRealInclusion S)))

theorem standardHilbertOperator_real_isScalarTower {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    IsScalarTower ℝ (E →L[ℂ] E) (E →L[ℂ] E) := IsScalarTower.right

local instance standardSourceOperator_real_isScalarTower (S : StandardSubspace H) :
    IsScalarTower ℝ (StandardSource S →L[ℂ] StandardSource S)
      (StandardSource S →L[ℂ] StandardSource S) :=
  standardHilbertOperator_real_isScalarTower (E := StandardSource S)

theorem standardHilbertOperator_realCFC {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] :
    IsometricContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint := inferInstance

local instance standardSourceOperator_realCFC (S : StandardSubspace H) :
    IsometricContinuousFunctionalCalculus ℝ
      (StandardSource S →L[ℂ] StandardSource S) IsSelfAdjoint :=
  standardHilbertOperator_realCFC (E := StandardSource S)

theorem standardHilbertOperator_realNonUnitalCFC {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] :
    NonUnitalContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint := inferInstance

local instance standardSourceOperator_realNonUnitalCFC (S : StandardSubspace H) :
    NonUnitalContinuousFunctionalCalculus ℝ
      (StandardSource S →L[ℂ] StandardSource S) IsSelfAdjoint :=
  standardHilbertOperator_realNonUnitalCFC (E := StandardSource S)

/-- Linear isometry equivalence for the standard polar unitary, of type `StandardSource S ≃ₗᵢ[ℂ]
H`. -/
noncomputable def standardPolarUnitary (S : StandardSubspace H) : StandardSource S ≃ₗᵢ[ℂ] H :=
  polarUnitary (standardSourceMap S) (standardSourceMap_injective S)
    (standardSourceMap_denseRange S)

theorem standardPolarUnitary_sqrt (S : StandardSubspace H) (z : StandardSource S) :
    standardPolarUnitary S (CFC.sqrt (standardGram S) z) = standardSourceMap S z :=
  polarUnitary_polarGramRoot _ _ _ z

end VacuumBellSeparation.Gaussian

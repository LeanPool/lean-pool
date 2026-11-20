/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Operator.CompactAtkinson
public import Mathlib.Algebra.Module.LinearMap.Index

/-!
# Index zero for a compact perturbation of the identity

This module complements Atkinson's theorem with the index computation.  The
algebraic core is a finite-range version of the Sylvester reduction.  If
`A : M →ₗ M` has finite range `V`, then `1 - A` on `M` and
`1 - A.rangeRestrict ∘ V.subtype` on the finite-dimensional space `V`
have linearly equivalent kernels and cokernels.  Rank-nullity on `V` therefore
shows that `1 - A` has index zero.

For a compact operator `K` on a complex Hilbert space, the finite-range
approximation from `CompactAtkinson` gives

`1 - K = (1 - (K - F)) ∘ (1 - (1 - (K - F))⁻¹ F)`.

The first factor is invertible and the second is identity minus a finite-range
map, so additivity of the algebraic Fredholm index gives the result.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open scoped LinearMap.FiniteRangeSetoid

namespace CompactAtkinsonIndexZero

universe u v

section Algebraic

variable {k : Type u} {M : Type v}
  [DivisionRing k] [AddCommGroup M] [Module k M]

/-- The finite-dimensional reduction of `1 - A` to the range of `A`. -/
def rangeReduction (A : M →ₗ[k] M) : A.range →ₗ[k] A.range :=
  LinearMap.id - A.rangeRestrict.comp A.range.subtype

/-- The kernels of `1 - A` on the ambient module and of its reduction to
`A.range` are naturally equivalent. -/
def kerEquivRangeReduction (A : M →ₗ[k] M) :
    (LinearMap.id - A).ker ≃ₗ[k] (rangeReduction A).ker where
  toFun x := ⟨A.rangeRestrict x, by
    change (rangeReduction A) (A.rangeRestrict x) = 0
    apply Subtype.ext
    change A x - A (A x) = 0
    have hx : x - A x = 0 := x.property
    have hAx := congrArg A hx
    simpa using hAx⟩
  invFun y := ⟨A.range.subtype y, by
    change (y : M) - A y = 0
    have hy := congrArg Subtype.val y.property
    simpa [rangeReduction] using hy⟩
  left_inv x := by
    apply Subtype.ext
    change A x = x
    have hx : x - A x = 0 := x.property
    exact (sub_eq_zero.mp hx).symm
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    change A (y : M) = (y : M)
    have hy := congrArg Subtype.val y.property
    have hzero : (y : M) - A y = 0 := by
      simpa [rangeReduction] using hy
    exact (sub_eq_zero.mp hzero).symm
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' c x := by
    apply Subtype.ext
    simp

/-- The cokernels of `1 - A` on the ambient module and of its reduction to
`A.range` are naturally equivalent. -/
def cokerEquivRangeReduction (A : M →ₗ[k] M) :
    (M ⧸ (LinearMap.id - A).range) ≃ₗ[k]
      (A.range ⧸ (rangeReduction A).range) := by
  let T : M →ₗ[k] M := LinearMap.id - A
  let S : A.range →ₗ[k] A.range := rangeReduction A
  let a : M →ₗ[k] A.range := A.rangeRestrict
  let i : A.range →ₗ[k] M := A.range.subtype
  have ha : T.range ≤ S.range.comap a := by
    rintro _ ⟨x, rfl⟩
    refine ⟨a x, ?_⟩
    apply Subtype.ext
    simp [T, S, a, rangeReduction]
  have hi : S.range ≤ T.range.comap i := by
    rintro _ ⟨y, rfl⟩
    refine ⟨i y, ?_⟩
    change i (S y) = T (i y)
    simp [T, S, i, rangeReduction]
  let qa : (M ⧸ T.range) →ₗ[k] (A.range ⧸ S.range) :=
    T.range.mapQ S.range a ha
  let qi : (A.range ⧸ S.range) →ₗ[k] (M ⧸ T.range) :=
    S.range.mapQ T.range i hi
  have hqiqa : qi.comp qa = LinearMap.id := by
    apply Submodule.linearMap_qext
    ext x
    apply (Submodule.Quotient.eq T.range).2
    change i (a x) - x ∈ T.range
    refine ⟨-x, ?_⟩
    simp [T, a, i]
    abel
  have hqaqi : qa.comp qi = LinearMap.id := by
    apply Submodule.linearMap_qext
    ext y
    apply (Submodule.Quotient.eq S.range).2
    change a (i y) - y ∈ S.range
    refine ⟨-y, ?_⟩
    simp [S, a, i, rangeReduction]
    abel
  exact LinearEquiv.ofLinearMap qa qi hqaqi hqiqa

/-- Identity minus a finite-range endomorphism has algebraic Fredholm index
zero.  This statement is purely algebraic and is reusable independently of
compactness or topology. -/
theorem index_id_sub_of_hasFiniteRange (A : M →ₗ[k] M)
    (hA : A.HasFiniteRange) :
    (LinearMap.id - A).index = 0 := by
  let : FiniteDimensional k A.range :=
    (Submodule.fg_iff_finiteDimensional A.range).1 hA.fg_range
  calc
    (LinearMap.id - A).index =
        (Module.finrank k (LinearMap.id - A).ker : ℤ) -
          Module.finrank k (M ⧸ (LinearMap.id - A).range) := LinearMap.index_eq_finrank_sub
    _ = (Module.finrank k (rangeReduction A).ker : ℤ) -
          Module.finrank k (A.range ⧸ (rangeReduction A).range) := by
      rw [(kerEquivRangeReduction A).finrank_eq,
        (cokerEquivRangeReduction A).finrank_eq]
    _ = (rangeReduction A).index := LinearMap.index_eq_finrank_sub.symm
    _ = 0 := by
      rw [LinearMap.index_eq_of_finiteDimensional]
      simp

end Algebraic

section Compact

variable {H : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The algebraic Fredholm index of identity minus a compact operator on a
complex Hilbert space is zero. -/
theorem index_id_sub_of_isCompact {K : H →L[ℂ] H}
    (hK : IsCompactOperator K) :
    (ContinuousLinearMap.id ℂ H - K).toLinearMap.index = 0 := by
  obtain ⟨F, hFfinite, herror⟩ :=
    CompactAtkinson.exists_hasFiniteRange_norm_sub_lt hK
      (epsilon := (1 : ℝ)) zero_lt_one
  let U : H →L[ℂ] H := ContinuousLinearMap.id ℂ H - (K - F)
  have hU : U.IsInvertible := by
    have hsmall : ‖-(K - F)‖ < 1 := by
      rw [norm_neg]
      exact herror
    simpa [U, sub_eq_add_neg] using
      ContinuousLinearMap.isInvertible_id_add_of_norm_lt_one hsmall
  let A : H →L[ℂ] H := U.inverse.comp F
  have hAfin : A.toLinearMap.HasFiniteRange :=
    hFfinite.comp_left U.inverse.toLinearMap
  have hfactor :
      (ContinuousLinearMap.id ℂ H - K).toLinearMap =
        U.toLinearMap.comp
          (ContinuousLinearMap.id ℂ H - A).toLinearMap := by
    ext x
    change x - K x = U (x - U.inverse (F x))
    rw [map_sub, hU.self_apply_inverse]
    simp [U]
    abel
  have hUFred : ContinuousLinearMap.IsFredholm U :=
    FredholmIsolation.IsInvertible.isFredholm hU
  have hAFred :
      ContinuousLinearMap.IsFredholm (ContinuousLinearMap.id ℂ H - A) := by
    have hId : (ContinuousLinearMap.id ℂ H).IsInvertible :=
      ⟨ContinuousLinearEquiv.refl ℂ H, rfl⟩
    apply FredholmIsolation.IsInvertible.isFredholm_of_hasFiniteRange_sub
      (u := ContinuousLinearMap.id ℂ H)
      (v := ContinuousLinearMap.id ℂ H - A)
    · exact hId
    · have heq :
          ((ContinuousLinearMap.id ℂ H - A) -
            ContinuousLinearMap.id ℂ H).toLinearMap = -A.toLinearMap := by
          ext x
          simp
      rw [heq]
      exact hAfin.neg
  let : FiniteDimensional ℂ
      (ContinuousLinearMap.id ℂ H - A).ker := hAFred.finite_ker
  let : FiniteDimensional ℂ
      (H ⧸ (ContinuousLinearMap.id ℂ H - A).range) := hAFred.finite_coker
  let : FiniteDimensional ℂ U.ker := hUFred.finite_ker
  let : FiniteDimensional ℂ (H ⧸ U.range) := hUFred.finite_coker
  rw [hfactor, LinearMap.index_comp]
  have hUindex : U.toLinearMap.index = 0 := by
    rcases hU with ⟨e, he⟩
    rw [← he]
    exact e.toLinearEquiv.index_eq_zero
  have hAindex :
      (ContinuousLinearMap.id ℂ H - A).toLinearMap.index = 0 := by
    change (LinearMap.id - A.toLinearMap).index = 0
    exact index_id_sub_of_hasFiniteRange A.toLinearMap hAfin
  rw [hUindex, hAindex]
  simp

end Compact

end CompactAtkinsonIndexZero

end

end FastDynamo

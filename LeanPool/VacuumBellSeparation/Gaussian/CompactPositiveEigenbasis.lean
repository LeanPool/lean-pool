/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.HilbertSchmidtCompact
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

/-!
# A genuine Hilbert eigenbasis for a compact positive operator

Choose Hilbert bases of the actual closed eigenspaces and take their
orthogonal union. The pinned compact self-adjoint spectral theorem proves
totality. Zero eigenspaces are included, so no injectivity or inverse is
assumed. Positivity supplies real nonnegative eigenvalues.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap Module.End
open scoped ComplexConjugate ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Index type for orthonormal basis vectors in the eigenspaces of a compact operator. -/
def operatorEigenspaceIndex (A : E →L[ℂ] E) (μ : ℂ) :
    Set (eigenspace A.toLinearMap μ) :=
  Classical.choose (exists_hilbertBasis (𝕜 := ℂ) (E := eigenspace A.toLinearMap μ))

/-- Operator eigenspace basis. -/
def operatorEigenspaceBasis (A : E →L[ℂ] E) (μ : ℂ) :
    HilbertBasis (operatorEigenspaceIndex A μ) ℂ (eigenspace A.toLinearMap μ) :=
  Classical.choose (Classical.choose_spec
    (exists_hilbertBasis (𝕜 := ℂ) (E := eigenspace A.toLinearMap μ)))

/-- Continuous linear map for the operator eigen index, of type `E →L[ℂ] E)`. -/
def operatorEigenIndex (A : E →L[ℂ] E) := Σ μ : ℂ, operatorEigenspaceIndex A μ

/-- Operator eigen family obtained from `operatorEigenspaceBasis`. -/
def operatorEigenFamily (A : E →L[ℂ] E) (i : operatorEigenIndex A) : E :=
  operatorEigenspaceBasis A i.1 i.2

theorem operatorEigenFamily_mem (A : E →L[ℂ] E) (i : operatorEigenIndex A) :
    operatorEigenFamily A i ∈ eigenspace A.toLinearMap i.1 :=
  (operatorEigenspaceBasis A i.1 i.2).property

theorem operatorEigenFamily_orthonormal {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) :
    Orthonormal ℂ (operatorEigenFamily A) :=
  hA.isSymmetric.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal
    (fun μ => (operatorEigenspaceBasis A μ).orthonormal)

theorem operatorEigenFamily_orthogonal_eq_bot {A : E →L[ℂ] E}
    (hc : IsCompactOperator A) (hA : IsSelfAdjoint A) :
    (Submodule.span ℂ (Set.range (operatorEigenFamily A)))ᗮ = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hx' : x ∈ (⨆ μ : ℂ, eigenspace A.toLinearMap μ)ᗮ := by
    rw [← Submodule.iInf_orthogonal]
    apply (Submodule.mem_iInf _).mpr
    intro μ
    apply (Submodule.mem_orthogonal' _ x).mpr
    intro y hy
    let y' : eigenspace A.toLinearMap μ := ⟨y, hy⟩
    have hz (j : operatorEigenspaceIndex A μ) :
        inner ℂ x (operatorEigenspaceBasis A μ j : E) = 0 :=
      (Submodule.span ℂ (Set.range (operatorEigenFamily A))).inner_left_of_mem_orthogonal
        (Submodule.subset_span ⟨⟨μ, j⟩, rfl⟩) hx
    have hs := ((innerSL ℂ x).comp (eigenspace A.toLinearMap μ).subtypeL).hasSum
      ((operatorEigenspaceBasis A μ).hasSum_repr y')
    have hs' : HasSum (fun _ : operatorEigenspaceIndex A μ => (0 : ℂ)) (inner ℂ x y) := by
      simpa [ContinuousLinearMap.comp_apply, map_smul, hz, y'] using hs
    exact hs'.unique hasSum_zero
  rw [ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hc hA.isSymmetric] at hx'
  exact hx'

/-- Compact self adjoint basis. -/
def compactSelfAdjointBasis {A : E →L[ℂ] E} (hc : IsCompactOperator A)
    (hA : IsSelfAdjoint A) : HilbertBasis (operatorEigenIndex A) ℂ E :=
  HilbertBasis.mkOfOrthogonalEqBot (operatorEigenFamily_orthonormal hA)
    (operatorEigenFamily_orthogonal_eq_bot hc hA)

@[simp] theorem compactSelfAdjointBasis_apply {A : E →L[ℂ] E} (hc : IsCompactOperator A)
    (hA : IsSelfAdjoint A) (i : operatorEigenIndex A) :
    compactSelfAdjointBasis hc hA i = operatorEigenFamily A i := by
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) i

theorem operatorEigenFamily_eigenvalue_real {A : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    (i : operatorEigenIndex A) : (i.1.re : ℂ) = i.1 := by
  have hn : operatorEigenFamily A i ≠ 0 := by
    intro hz
    have h := (operatorEigenFamily_orthonormal hA).norm_eq_one i
    simp [hz] at h
  have hc := hA.isSymmetric.conj_eigenvalue_eq_self
    (hasEigenvalue_of_hasEigenvector ⟨operatorEigenFamily_mem A i, hn⟩)
  simpa only [RCLike.re_eq_complex_re, RCLike.ofReal_eq_complex_ofReal] using
    (RCLike.conj_eq_iff_re.mp hc)

theorem compactSelfAdjointBasis_apply_operator {A : E →L[ℂ] E}
    (hc : IsCompactOperator A) (hA : IsSelfAdjoint A) (i : operatorEigenIndex A) :
    A (compactSelfAdjointBasis hc hA i) =
      (i.1.re : ℂ) • compactSelfAdjointBasis hc hA i := by
  rw [compactSelfAdjointBasis_apply, operatorEigenFamily_eigenvalue_real hA]
  exact mem_eigenspace_iff.mp (operatorEigenFamily_mem A i)

theorem operatorEigenFamily_eigenvalue_nonneg {A : E →L[ℂ] E} (hA : 0 ≤ A)
    (i : operatorEigenIndex A) : 0 ≤ i.1.re := by
  have hi := (ContinuousLinearMap.nonneg_iff_isPositive.mp hA).re_inner_nonneg_right
    (operatorEigenFamily A i)
  have heig : A (operatorEigenFamily A i) = i.1 • operatorEigenFamily A i :=
    mem_eigenspace_iff.mp (operatorEigenFamily_mem A i)
  rw [heig,
    ← operatorEigenFamily_eigenvalue_real hA.isSelfAdjoint i, inner_smul_right,
    inner_self_eq_norm_sq_to_K,
    (operatorEigenFamily_orthonormal hA.isSelfAdjoint).norm_eq_one i] at hi
  simpa only [one_pow, RCLike.ofReal_one, mul_one, RCLike.re_eq_complex_re,
    Complex.ofReal_re] using hi

/-- An orthonormal eigenbasis of a positive trace-class operator, indexed by its compact spectral
decomposition. -/
def positiveTraceClassEigenbasis {A : E →L[ℂ] E} (hA : IsPositiveTraceClass A) :
    HilbertBasis (operatorEigenIndex A) ℂ E :=
  compactSelfAdjointBasis (positiveTraceClass_isCompactOperator hA) hA.1.isSelfAdjoint

theorem positiveTrace_eq_eigenvalue_sum {A : E →L[ℂ] E} (hc : IsCompactOperator A)
    (hA : 0 ≤ A) : positiveTrace A = ∑' i : operatorEigenIndex A, ENNReal.ofReal i.1.re := by
  rw [positiveTrace_eq_tsum_diagonal (compactSelfAdjointBasis hc hA.isSelfAdjoint) hA]
  apply tsum_congr
  intro i
  rw [compactSelfAdjointBasis_apply_operator, inner_smul_right, inner_self_eq_norm_sq_to_K,
    (compactSelfAdjointBasis hc hA.isSelfAdjoint).orthonormal.norm_eq_one]
  simp only [one_pow, RCLike.ofReal_one, mul_one, Complex.ofReal_re]

end VacuumBellSeparation.Gaussian

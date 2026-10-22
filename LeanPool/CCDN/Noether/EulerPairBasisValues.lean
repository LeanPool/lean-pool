/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ForMathlib.Matrix
public import LeanPool.CCDN.Noether.EulerPairBasis

/-! Explicit monomial values of the Euler basis and nonzero minors of the
correct Noether order d^2-1. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Module

private lemma euler_restrict_basis_val {R : Type*} [CommRing R]
    (S : Set (Fin 2 →₀ ℕ)) (i : S) :
    (basisRestrictSupport R S i).val = monomial i.val 1 := by
  classical
  change AddMonoidAlgebra.ofCoeff
    (((Finsupp.supportedEquivFinsupp (M := R) (R := R) S).symm
      (Finsupp.single i 1)).val) = _
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

/-- The basis vector of `eulerLowBasis R k` indexed by `i` is the monomial with exponent vector
corresponding to `i` and coefficient one. -/
lemma eulerLowBasis_apply {R : Type*} [CommRing R] (k : ℕ) (i : EulerLowIndex k) :
    (eulerLowBasis R k i).val =
      monomial ((Finsupp.degreeLeEquivSym (Fin 2) k).symm i).val 1 := by
  classical
  have h := Basis.reindex_apply (basisRestrictSupport R {p : Fin 2 →₀ ℕ | p.degree ≤ k})
    (Finsupp.degreeLeEquivSym (Fin 2) k) i
  exact (congrArg Subtype.val h).trans (euler_restrict_basis_val _ _)

/-- The basis vector of `eulerTopBasis R k` indexed by `i` is the monomial of degree `k` with
exponent vector corresponding to `i` and coefficient one. -/
lemma eulerTopBasis_apply {R : Type*} [CommRing R] (k : ℕ) (i : EulerTopIndex k) :
    (eulerTopBasis R k i).val =
      monomial ((degreeEqEquivSym (Fin 2) k).symm i).val 1 := by
  classical
  simp only [eulerTopBasis, Basis.map_apply, Basis.reindex_apply]
  exact euler_restrict_basis_val _ _

private theorem eulerClosedFormCoefficientMatrix_rank
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (k : ℕ) (f : Polynomial (Polynomial F)) (hf : Irreducible f)
    (a : F) (ha : a ≠ 0) (hl : f.leadingCoeff = Polynomial.C a)
    (hdeg : f.natDegree = k + 2) :
    (eulerClosedFormCoefficientMatrix k f).rank = (k + 2) ^ 2 - 1 := by
  have hi := eulerClosedFormCoefficientMatrix_columns_independent k f hf a ha hl hdeg
  have hr : (eulerClosedFormCoefficientMatrix k f).rank = Fintype.card (EulerColumns k) := by
    rw [Matrix.rank_eq_finrank_span_cols, linearIndependent_iff_card_eq_finrank_span.mp hi,
      Set.finrank]
  rw [hr, card_eulerColumns]

/-- A nonzero maximal minor has precisely the universal Noether
order d^2-1. -/
theorem exists_eulerClosedForm_nonzero_minor
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (k : ℕ) (f : Polynomial (Polynomial F)) (hf : Irreducible f)
    (a : F) (ha : a ≠ 0) (hl : f.leadingCoeff = Polynomial.C a)
    (hdeg : f.natDegree = k + 2) :
    (eulerClosedFormCoefficientMatrix k f).HasNonzeroMinor ((k + 2) ^ 2 - 1) :=
  Matrix.hasNonzeroMinor_of_le_rank _ (eulerClosedFormCoefficientMatrix_rank k f hf a ha hl hdeg).ge

end
end CCDN

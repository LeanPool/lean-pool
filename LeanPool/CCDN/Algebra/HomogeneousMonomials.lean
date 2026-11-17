/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.MonomialEvaluationMatrix
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Sym.Card

/-! Complete homogeneous monomial lists, their exact cardinalities, and the
corresponding polynomial-space dimensions. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Exponents of total degree exactly `M` are multisets of cardinality `M`. -/
def degreeEqEquivSym (σ : Type*) [Fintype σ] [DecidableEq σ] (M : ℕ) :
    {p : σ →₀ ℕ // p.degree = M} ≃ Sym σ M :=
  (Finsupp.equivFunOnFinite.subtypeEquiv (fun p => by simp [Finsupp.degree_eq_sum])).trans
    (Sym.equivNatSumOfFintype σ M).symm

/-- There are exactly `(n + M).choose M` exponent vectors of total degree `M` in `n + 1`
variables. -/
theorem card_degree_eq (n M : ℕ) :
    Nat.card {p : Fin (n + 1) →₀ ℕ // p.degree = M} = (n + M).choose M := by
  rw [Nat.card_congr (degreeEqEquivSym (Fin (n + 1)) M), Nat.card_eq_fintype_card,
    Sym.card_sym_eq_choose]
  simp only [Fintype.card_fin]
  congr 1
  omega

/-- A canonical finite indexing of all degree-`M` monomials in `n+1` variables. -/
def homogeneousExponentEquiv (n M : ℕ) :
    Fin ((n + M).choose M) ≃ {p : Fin (n + 1) →₀ ℕ // p.degree = M} := by
  let e := degreeEqEquivSym (Fin (n + 1)) M
  let _ := Fintype.ofEquiv (Sym (Fin (n + 1)) M) e.symm
  have hc : Fintype.card {p : Fin (n + 1) →₀ ℕ // p.degree = M} =
      (n + M).choose M := by rw [← Nat.card_eq_fintype_card, card_degree_eq]
  exact (finCongr hc.symm).trans (Fintype.equivFin _).symm

/-- The list of all exponent vectors of total degree `M` in `n + 1` variables, indexed by
`Fin ((n + M).choose M)` via `homogeneousExponentEquiv`. -/
def homogeneousMonomials (n M : ℕ) : Fin ((n + M).choose M) → (Fin (n + 1) →₀ ℕ) :=
  fun j => (homogeneousExponentEquiv n M j).val

/-- Distinct indices give distinct monomials in `homogeneousMonomials n M`. -/
lemma homogeneousMonomials_injective (n M : ℕ) : Function.Injective (homogeneousMonomials n M) :=
  Subtype.val_injective.comp (homogeneousExponentEquiv n M).injective

/-- Every monomial in `homogeneousMonomials n M` has total degree `M`. -/
lemma homogeneousMonomials_degree (n M : ℕ) (j : Fin ((n + M).choose M)) :
    (homogeneousMonomials n M j).degree = M :=
  (homogeneousExponentEquiv n M j).property

/-- Every exponent vector of total degree `M` in `n + 1` variables occurs in
`homogeneousMonomials n M`. -/
lemma homogeneousMonomials_surjective (n M : ℕ) (p : Fin (n + 1) →₀ ℕ)
    (hp : p.degree = M) : ∃ j, homogeneousMonomials n M j = p := by
  obtain ⟨j, hj⟩ := (homogeneousExponentEquiv n M).surjective ⟨p, hp⟩
  exact ⟨j, congrArg Subtype.val hj⟩

/-- An integer combination of the degree-`M` monomials `homogeneousMonomials n M` is a
homogeneous polynomial of degree `M`. -/
theorem polynomialOfCoefficients_homogeneous (n M : ℕ)
    (v : Fin ((n + M).choose M) → ℤ) :
    (polynomialOfCoefficients (homogeneousMonomials n M) v).IsHomogeneous M := by
  apply IsHomogeneous.sum
  intro j _
  apply isHomogeneous_monomial
  exact homogeneousMonomials_degree n M j

end
end CCDN

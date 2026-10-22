/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Noether.EulerUniversalForms
import LeanPool.CCDN.Noether.EulerMonomialColumns
import LeanPool.CCDN.Noether.EulerPairSpecialization
import LeanPool.CCDN.Noether.ShearNormalization

/-! Each row and Euler column uses at most one coefficient of the defining
equation, with integer multiplier bounded by its degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

private def eulerLowExponent (k : ℕ) (i : EulerLowIndex k) : Fin 2 →₀ ℕ :=
  ((Finsupp.degreeLeEquivSym (Fin 2) k).symm i).val

private def eulerTopExponent (k : ℕ) (i : EulerTopIndex k) : Fin 2 →₀ ℕ :=
  ((degreeEqEquivSym (Fin 2) k).symm i).val

private lemma eulerLowExponent_degree (k : ℕ) (i : EulerLowIndex k) :
    eulerLowExponent k i 0 + eulerLowExponent k i 1 ≤ k := by
  have hh := ((Finsupp.degreeLeEquivSym (Fin 2) k).symm i).property
  change (eulerLowExponent k i).sum (fun _ e => e) ≤ k at hh
  rw [bivariate_exponent_eq (eulerLowExponent k i), bivariate_exponent_sum] at hh
  exact hh

private lemma eulerTopExponent_degree (k : ℕ) (i : EulerTopIndex k) :
    eulerTopExponent k i 0 + eulerTopExponent k i 1 = k := by
  have hh := ((degreeEqEquivSym (Fin 2) k).symm i).property
  change (eulerTopExponent k i).sum (fun _ e => e) = k at hh
  rw [bivariate_exponent_eq (eulerTopExponent k i), bivariate_exponent_sum] at hh
  exact hh

private lemma eulerLowExponent_injective (k : ℕ) : Function.Injective (eulerLowExponent k) :=
  Subtype.val_injective.comp (Finsupp.degreeLeEquivSym (Fin 2) k).symm.injective

private def eulerMonomialOutput (k : ℕ) (col : EulerColumns k)
    (i : EulerLowIndex (k + 2)) : ℕ × ℕ :=
  let s := eulerLowExponent (k + 2) i 0
  let t := eulerLowExponent (k + 2) i 1
  match col with
  | .inl j => (eulerLowExponent k j 0 + s, eulerLowExponent k j 1 + t - 1)
  | .inr (.inl j) => (eulerLowExponent k j 0 + s - 1, eulerLowExponent k j 1 + t)
  | .inr (.inr j) => (eulerTopExponent k j 0 + s, eulerTopExponent k j 1 + t)

private def eulerMonomialWeight (k : ℕ) (col : EulerColumns k) (i : EulerLowIndex (k + 2)) : ℤ :=
  let s := eulerLowExponent (k + 2) i 0
  let t := eulerLowExponent (k + 2) i 1
  match col with
  | .inl j => (eulerLowExponent k j 1 : ℤ) - t
  | .inr (.inl j) => (s : ℤ) - eulerLowExponent k j 0
  | .inr (.inr _) => (k + 2 : ℕ) - (s : ℤ) - t

private lemma eulerBivariatePair_basis_left {R : Type*} [CommRing R] (k : ℕ) (i : EulerLowIndex k) :
    eulerBivariatePair R k (eulerPairBasis R k (.inl i)) =
      (monomial (eulerLowExponent k i 0) (monomial (eulerLowExponent k i 1) (1 : R)), 0) := by
  simp only [eulerBivariatePair, LinearMap.comp_apply, LinearMap.prodMap_apply,
    AlgEquiv.toLinearMap_apply, eulerPairCoordinates_basis_left, bivariatePolynomialEquiv_monomial,
    map_zero, eulerLowExponent]

private lemma eulerBivariatePair_basis_right {R : Type*} [CommRing R] (k : ℕ)
    (i : EulerLowIndex k) :
    eulerBivariatePair R k (eulerPairBasis R k (.inr (.inl i))) =
      (0, monomial (eulerLowExponent k i 0) (monomial (eulerLowExponent k i 1) (1 : R))) := by
  simp only [eulerBivariatePair, LinearMap.comp_apply, LinearMap.prodMap_apply,
    AlgEquiv.toLinearMap_apply, eulerPairCoordinates_basis_right, bivariatePolynomialEquiv_monomial,
    map_zero, eulerLowExponent]

private lemma eulerBivariatePair_basis_radial {R : Type*} [CommRing R] (k : ℕ)
    (i : EulerTopIndex k) :
    eulerBivariatePair R k (eulerPairBasis R k (.inr (.inr i))) =
      (monomial (eulerTopExponent k i 0) (monomial (eulerTopExponent k i 1 + 1) (1 : R)),
       -(monomial (eulerTopExponent k i 0 + 1) (monomial (eulerTopExponent k i 1) (1 : R)))) := by
  simp only [eulerBivariatePair, LinearMap.comp_apply, LinearMap.prodMap_apply,
    AlgEquiv.toLinearMap_apply, eulerPairCoordinates_basis_radial, map_mul, map_neg,
    bivariatePolynomialEquiv_monomial, bivariatePolynomialEquiv_X_zero,
    bivariatePolynomialEquiv_X_one, C_mul_monomial, X_mul_monomial, eulerTopExponent]

private lemma eulerCoefficientMonomial_eq {R : Type*} [CommRing R] (k : ℕ) (i : EulerLowIndex k) :
    eulerCoefficientMonomial R k i =
      monomial (eulerLowExponent k i 0) (monomial (eulerLowExponent k i 1) (1 : R)) :=
  bivariatePolynomialEquiv_monomial _ _

private lemma eulerMonomialWeight_abs_le (k : ℕ) (col : EulerColumns k)
    (i : EulerLowIndex (k + 2)) :
    |eulerMonomialWeight k col i| ≤ (k + 2 : ℕ) := by
  have hi := eulerLowExponent_degree (k + 2) i
  rcases col with j | j | j
  · have hj := eulerLowExponent_degree k j
    change |(eulerLowExponent k j 1 : ℤ) - eulerLowExponent (k + 2) i 1| ≤ _
    rw [abs_le]
    constructor <;> omega
  · have hj := eulerLowExponent_degree k j
    change |(eulerLowExponent (k + 2) i 0 : ℤ) - eulerLowExponent k j 0| ≤ _
    rw [abs_le]
    constructor <;> omega
  · change |((k + 2 : ℕ) : ℤ) - eulerLowExponent (k + 2) i 0 - eulerLowExponent (k + 2) i 1| ≤ _
    rw [abs_le]
    constructor <;> omega

private theorem eulerClosedForm_monomial_output (k : ℕ) (col : EulerColumns k)
    (i : EulerLowIndex (k + 2)) :
    eulerClosedFormOperator k (eulerCoefficientMonomial ℤ (k + 2) i)
      (eulerPairBasis ℤ k col) =
      monomial (eulerMonomialOutput k col i).1
        (monomial (eulerMonomialOutput k col i).2 (eulerMonomialWeight k col i)) := by
  change closedFormOperator _ (eulerBivariatePair ℤ k (eulerPairBasis ℤ k col)) = _
  rw [eulerCoefficientMonomial_eq]
  rcases col with j | j | j
  · rw [eulerBivariatePair_basis_left, closedFormOperator_monomial_left]
    rfl
  · rw [eulerBivariatePair_basis_right, closedFormOperator_monomial_right]
    rfl
  · rw [eulerBivariatePair_basis_radial, closedFormOperator_monomial_radial,
      eulerTopExponent_degree]
    rfl

private theorem eulerClosedForm_monomial_entry (k : ℕ) (row : ℕ × ℕ)
    (col : EulerColumns k) (i : EulerLowIndex (k + 2)) :
    eulerClosedFormCoefficientMatrix k (eulerCoefficientMonomial ℤ (k + 2) i) row col =
      if eulerMonomialOutput k col i = row then eulerMonomialWeight k col i else 0 := by
  change ((eulerClosedFormOperator k (eulerCoefficientMonomial ℤ (k + 2) i)
    (eulerPairBasis ℤ k col)).coeff row.1).coeff row.2 = _
  rw [eulerClosedForm_monomial_output]
  by_cases h₀ : (eulerMonomialOutput k col i).1 = row.1 <;>
    by_cases h₁ : (eulerMonomialOutput k col i).2 = row.2 <;>
    simp [coeff_monomial, Prod.ext_iff, h₀, h₁]

/-- Distinct input monomials cannot contribute to the same entry, unless
their contribution is zero. -/
private theorem eulerMonomialOutput_injective_on_nonzero (k : ℕ) (col : EulerColumns k)
    (i j : EulerLowIndex (k + 2))
    (hi : eulerMonomialWeight k col i ≠ 0) (hj : eulerMonomialWeight k col j ≠ 0)
    (he : eulerMonomialOutput k col i = eulerMonomialOutput k col j) : i = j := by
  apply eulerLowExponent_injective (k + 2)
  have h₀ := congrArg Prod.fst he
  have h₁ := congrArg Prod.snd he
  ext t
  rcases col with c | c | c
  · change (eulerLowExponent k c 1 : ℤ) - eulerLowExponent (k + 2) i 1 ≠ 0 at hi
    change (eulerLowExponent k c 1 : ℤ) - eulerLowExponent (k + 2) j 1 ≠ 0 at hj
    change eulerLowExponent k c 0 + eulerLowExponent (k + 2) i 0 =
      eulerLowExponent k c 0 + eulerLowExponent (k + 2) j 0 at h₀
    change eulerLowExponent k c 1 + eulerLowExponent (k + 2) i 1 - 1 =
      eulerLowExponent k c 1 + eulerLowExponent (k + 2) j 1 - 1 at h₁
    fin_cases t
    · change eulerLowExponent (k + 2) i 0 = eulerLowExponent (k + 2) j 0
      omega
    · change eulerLowExponent (k + 2) i 1 = eulerLowExponent (k + 2) j 1
      omega
  · change (eulerLowExponent (k + 2) i 0 : ℤ) - eulerLowExponent k c 0 ≠ 0 at hi
    change (eulerLowExponent (k + 2) j 0 : ℤ) - eulerLowExponent k c 0 ≠ 0 at hj
    change eulerLowExponent k c 0 + eulerLowExponent (k + 2) i 0 - 1 =
      eulerLowExponent k c 0 + eulerLowExponent (k + 2) j 0 - 1 at h₀
    change eulerLowExponent k c 1 + eulerLowExponent (k + 2) i 1 =
      eulerLowExponent k c 1 + eulerLowExponent (k + 2) j 1 at h₁
    fin_cases t
    · change eulerLowExponent (k + 2) i 0 = eulerLowExponent (k + 2) j 0
      omega
    · change eulerLowExponent (k + 2) i 1 = eulerLowExponent (k + 2) j 1
      omega
  · change eulerTopExponent k c 0 + eulerLowExponent (k + 2) i 0 =
      eulerTopExponent k c 0 + eulerLowExponent (k + 2) j 0 at h₀
    change eulerTopExponent k c 1 + eulerLowExponent (k + 2) i 1 =
      eulerTopExponent k c 1 + eulerLowExponent (k + 2) j 1 at h₁
    fin_cases t
    · change eulerLowExponent (k + 2) i 0 = eulerLowExponent (k + 2) j 0
      omega
    · change eulerLowExponent (k + 2) i 1 = eulerLowExponent (k + 2) j 1
      omega

/-- An entry is zero or a single coefficient variable with multiplier
of absolute value at most the defining equation's degree. -/
theorem universalEulerMatrix_sparse (k : ℕ) (row : ℕ × ℕ) (col : EulerColumns k) :
    universalEulerMatrix k row col = 0 ∨
      ∃ (i : EulerLowIndex (k + 2)) (c : ℤ), |c| ≤ (k + 2 : ℕ) ∧
        universalEulerMatrix k row col = MvPolynomial.C c * MvPolynomial.X i := by
  classical
  by_cases hex : ∃ i, eulerMonomialWeight k col i ≠ 0 ∧ eulerMonomialOutput k col i = row
  · obtain ⟨i, hi, hrow⟩ := hex
    right
    refine ⟨i, eulerMonomialWeight k col i, eulerMonomialWeight_abs_le k col i, ?_⟩
    unfold universalEulerMatrix
    rw [Finset.sum_eq_single i]
    · rw [eulerClosedForm_monomial_entry, ite_eq_left hrow]
    · intro j _ hji
      rw [eulerClosedForm_monomial_entry]
      by_cases hout : eulerMonomialOutput k col j = row
      · rw [ite_eq_left hout]
        have hz : eulerMonomialWeight k col j = 0 := by
          by_contra hj
          exact hji (eulerMonomialOutput_injective_on_nonzero k col j i hj hi
            (hout.trans hrow.symm))
        rw [hz, map_zero, zero_mul]
      · rw [ite_eq_right hout, map_zero, zero_mul]
    · simp
  · left
    unfold universalEulerMatrix
    apply Finset.sum_eq_zero
    intro i _
    rw [eulerClosedForm_monomial_entry]
    by_cases hout : eulerMonomialOutput k col i = row
    · rw [ite_eq_left hout]
      have hz : eulerMonomialWeight k col i = 0 := by
        by_contra hi
        exact hex ⟨i, hi, hout⟩
      rw [hz, map_zero, zero_mul]
    · rw [ite_eq_right hout, map_zero, zero_mul]

end
end CCDN

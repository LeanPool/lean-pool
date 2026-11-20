/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.FallingFactorial

/-!
# Square-free Boolean polynomials and the interpolated slice functional

A monomial is a finite set of indices. Multiplication takes unions, so `zᵢ² = zᵢ`
holds in the algebra itself. This retains repeated-index contributions correctly.
The interpolated slice functional is linear, not multiplicative or positive in general.
-/

@[expose] public section

namespace NoncommutativeAMGM

open scoped BigOperators

/-- A square-free Boolean monomial, represented by its variable set. -/
def BooleanMonomial (n : ℕ) := Finset (Fin n)

namespace BooleanMonomial

/-- The variables occurring in a Boolean monomial. -/
def toFinset {n : ℕ} (S : BooleanMonomial n) : Finset (Fin n) := S

/-- Regard a variable set as a Boolean monomial. -/
def ofFinset {n : ℕ} (S : Finset (Fin n)) : BooleanMonomial n := S

instance (n : ℕ) : DecidableEq (BooleanMonomial n) :=
  inferInstanceAs (DecidableEq (Finset (Fin n)))

instance (n : ℕ) : Fintype (BooleanMonomial n) :=
  inferInstanceAs (Fintype (Finset (Fin n)))

instance (n : ℕ) : CommMonoid (BooleanMonomial n) where
  mul S T := ((S : Finset (Fin n)) ∪ (T : Finset (Fin n)) : Finset (Fin n))
  one := (∅ : Finset (Fin n))
  mul_assoc := Finset.union_assoc
  one_mul := Finset.empty_union
  mul_one := Finset.union_empty
  mul_comm := Finset.union_comm

end BooleanMonomial

/-- The real algebra of multilinear polynomials modulo the Boolean relations. -/
abbrev BooleanPolynomial (n : ℕ) := MonoidAlgebra ℝ (BooleanMonomial n)

/-- A scalar multiple of a square-free monomial. -/
noncomputable def booleanMonomial {n : ℕ} (S : Finset (Fin n)) (c : ℝ) :
    BooleanPolynomial n := MonoidAlgebra.single (BooleanMonomial.ofFinset S) c

/-- A coordinate variable in the Boolean algebra. -/
noncomputable def booleanVar {n : ℕ} (i : Fin n) : BooleanPolynomial n :=
  booleanMonomial {i} 1

/-- The sum of all coordinate variables, denoted `Z` in Appendix C. -/
noncomputable def totalVariable (n : ℕ) : BooleanPolynomial n := ∑ i, booleanVar i

/-- A degree bound in the square-free monomial basis. -/
def BooleanDegreeLE {n : ℕ} (f : BooleanPolynomial n) (d : ℕ) : Prop :=
  ∀ S : BooleanMonomial n, f.coeff S ≠ 0 → (S : Finset (Fin n)).card ≤ d

/-- The prescribed slice moment `(s)ᵣ/(n)ᵣ`. -/
noncomputable def sliceMoment (n : ℕ) (s : ℝ) (r : ℕ) : ℝ := falling s r / falling n r

/-- The interpolated slice functional `νₛ`, acting on Boolean polynomials. -/
noncomputable def sliceFunctional (n : ℕ) (s : ℝ) : BooleanPolynomial n →ₗ[ℝ] ℝ :=
  (Finsupp.linearCombination ℝ
    (fun S : BooleanMonomial n ↦ sliceMoment n s (S : Finset (Fin n)).card)).comp
      (MonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap

theorem sliceFunctional_monomial {n : ℕ} (s : ℝ) (S : Finset (Fin n)) (c : ℝ) :
    sliceFunctional n s (booleanMonomial S c) = c * sliceMoment n s S.card := by
  change Finsupp.linearCombination ℝ _ (Finsupp.single (show BooleanMonomial n from S) c) = _
  rw [Finsupp.linearCombination_single]
  rfl

theorem booleanMonomial_mul {n : ℕ} (S T : Finset (Fin n)) (a b : ℝ) :
    booleanMonomial S a * booleanMonomial T b = booleanMonomial (S ∪ T) (a * b) := by
  exact MonoidAlgebra.single_mul_single _ _ _ _

/-- Boolean reduction is exact, including in products with repeated indices. -/
@[simp] theorem booleanVar_sq {n : ℕ} (i : Fin n) : booleanVar i ^ 2 = booleanVar i := by
  simp [pow_two, booleanVar, booleanMonomial_mul]

theorem booleanMonomial_empty {n : ℕ} :
    booleanMonomial (∅ : Finset (Fin n)) 1 = 1 := rfl

theorem booleanMonomial_prod {n : ℕ} (S : Finset (Fin n)) :
    ∏ i ∈ S, booleanVar i = booleanMonomial S 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact booleanMonomial_empty.symm
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, ih, booleanVar, booleanMonomial_mul]
    simp

/-- The moment rule in Sections 2.1 and 3.1. -/
theorem sliceFunctional_prod {n : ℕ} (s : ℝ) (S : Finset (Fin n)) :
    sliceFunctional n s (∏ i ∈ S, booleanVar i) = falling s S.card / falling n S.card := by
  rw [booleanMonomial_prod, sliceFunctional_monomial, one_mul]
  rfl

@[simp] theorem sliceMoment_zero (n : ℕ) (s : ℝ) : sliceMoment n s 0 = 1 := by
  simp [sliceMoment]

/-- The moment recurrence underlying the first part of Lemma C.1. -/
theorem sliceMoment_succ (n r : ℕ) (s : ℝ) (hr : r < n) :
    ((n : ℝ) - r) * sliceMoment n s (r + 1) =
      (s - r) * sliceMoment n s r := by
  have hnr : (n : ℝ) - r ≠ 0 := by
    have : (r : ℝ) < n := by exact_mod_cast hr
    linarith
  have hf : falling (n : ℝ) r ≠ 0 := by
    rw [falling_natCast]
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hr.le))
  simp only [sliceMoment, falling_succ]
  field_simp [hnr, hf]

/-- Summing the moments obtained by multiplying a monomial by every variable. -/
theorem sum_sliceMoment_insert {n : ℕ} (s : ℝ) (S : Finset (Fin n)) (hS : S.card < n) :
    ∑ i : Fin n, sliceMoment n s (insert i S).card = s * sliceMoment n s S.card := by
  classical
  have hcard (i : Fin n) : (insert i S).card =
      if i ∈ S then S.card else S.card + 1 := by
    by_cases hi : i ∈ S <;> simp [hi]
  simp_rw [hcard, apply_ite]
  rw [Finset.sum_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.filter_notMem_eq_sdiff, Finset.sum_const, Finset.card_sdiff,
    Finset.inter_univ, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Nat.cast_sub hS.le]
  have hrec := sliceMoment_succ n S.card s hS
  nlinarith

/-- The monomial case of Lemma C.1's first identity. -/
theorem slice_total_mul_monomial {n : ℕ} (s : ℝ) (S : Finset (Fin n))
    (c : ℝ) (hS : S.card < n) :
    sliceFunctional n s (totalVariable n * booleanMonomial S c) =
      s * sliceFunctional n s (booleanMonomial S c) := by
  classical
  rw [totalVariable, Finset.sum_mul, map_sum]
  simp only [booleanVar, booleanMonomial_mul, one_mul, Finset.singleton_union,
    sliceFunctional_monomial]
  rw [← Finset.mul_sum, sum_sliceMoment_insert s S hS]
  ring

/-- Lemma C.1, first identity: `(Z-s)` annihilates every polynomial of degree at most
`n-1`. The construction uses the actual Boolean product, including repeated indices. -/
theorem slice_total_sub_mul {n : ℕ} (hn : 0 < n) (s : ℝ) (f : BooleanPolynomial n)
    (hf : BooleanDegreeLE f (n - 1)) :
    sliceFunctional n s ((totalVariable n - s • 1) * f) = 0 := by
  classical
  have hexpand : f = ∑ S ∈ f.coeff.support,
      booleanMonomial (S : Finset (Fin n)) (f.coeff S) := by
    exact (MonoidAlgebra.sum_coeff_single f).symm
  have htotal : sliceFunctional n s (totalVariable n * f) = s * sliceFunctional n s f := by
    conv_lhs => rw [hexpand]
    rw [Finset.mul_sum, map_sum]
    conv_rhs => rw [hexpand]
    rw [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    have hcard := hf S (Finsupp.mem_support_iff.mp hS)
    exact slice_total_mul_monomial s _ _ (by omega)
  rw [sub_mul, smul_mul_assoc, one_mul, map_sub, map_smul]
  simp [htotal, smul_eq_mul]

end NoncommutativeAMGM

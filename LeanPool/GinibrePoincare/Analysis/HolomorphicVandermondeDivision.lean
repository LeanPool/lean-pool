/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/HolomorphicVandermondeDivision.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.MultivariateComplexHermite
public import LeanPool.GinibrePoincare.Analysis.GinibreMassFiniteness
public import LeanPool.GinibrePoincare.Concrete.NormalizedGroundState
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Algebra.MvPolynomial.Funext

/-! # Algebraic alternating polynomials and the Vandermonde -/


@[expose] public section


open scoped BigOperators

namespace GinibrePoincare

noncomputable section

attribute [local simp] MvPolynomial.optionEquivLeft_X_none
  MvPolynomial.optionEquivLeft_X_some MvPolynomial.optionEquivLeft_C

/-- Holomorphic polynomials in the particle coordinates. -/
abbrev ConfigurationPolynomial (n : ℕ) := MvPolynomial (Fin n) ℂ

/-- Relabel the variables of a configuration polynomial. -/
def permuteConfigurationPolynomial {n : ℕ} (σ : ParticlePermutation n) :
    ConfigurationPolynomial n →ₐ[ℂ] ConfigurationPolynomial n :=
  MvPolynomial.renameEquiv ℂ σ

/-- Algebraic symmetry under all particle relabellings. -/
def IsSymmetricConfigurationPolynomial {n : ℕ}
    (P : ConfigurationPolynomial n) : Prop :=
  ∀ σ : ParticlePermutation n, permuteConfigurationPolynomial σ P = P

/-- Algebraic alternation under all particle relabellings. -/
def IsAlternatingConfigurationPolynomial {n : ℕ}
    (P : ConfigurationPolynomial n) : Prop :=
  ∀ σ : ParticlePermutation n,
    permuteConfigurationPolynomial σ P =
      MvPolynomial.C (permutationSign σ) * P

/-- The polynomial Vandermonde determinant. -/
def polynomialVandermonde (n : ℕ) : ConfigurationPolynomial n :=
  (Matrix.vandermonde (fun i : Fin n ↦
    MvPolynomial.X i : Fin n → ConfigurationPolynomial n)).det

/-- Its usual product formula. -/
theorem polynomialVandermonde_eq_product (n : ℕ) :
    polynomialVandermonde n =
      ∏ i : Fin n, ∏ j > i, (MvPolynomial.X j - MvPolynomial.X i) := by
  exact Matrix.det_vandermonde _

/-- Evaluation of the polynomial Vandermonde is the concrete Vandermonde. -/
@[simp] theorem eval_polynomialVandermonde (n : ℕ) (z : Configuration n) :
    MvPolynomial.eval z (polynomialVandermonde n) = vandermonde z := by
  rw [polynomialVandermonde_eq_product, vandermonde_eq_product]
  simp

/-- Evaluation after relabelling variables is evaluation on the relabelled
configuration. -/
theorem eval_permuteConfigurationPolynomial {n : ℕ}
    (σ : ParticlePermutation n) (P : ConfigurationPolynomial n)
    (z : Configuration n) :
    MvPolynomial.eval z (permuteConfigurationPolynomial σ P) =
      MvPolynomial.eval (permute σ z) P := by
  change MvPolynomial.eval z (MvPolynomial.rename σ P) = _
  rw [MvPolynomial.eval_rename]
  rfl

/-- Algebraic symmetry implies symmetry of the evaluated polynomial
function. -/
theorem isSymmetric_eval_of_polynomial {n : ℕ}
    {P : ConfigurationPolynomial n} (hP : IsSymmetricConfigurationPolynomial P) :
    IsSymmetric (fun z : Configuration n ↦ MvPolynomial.eval z P) := by
  intro σ z
  change MvPolynomial.eval (permute σ z) P = MvPolynomial.eval z P
  rw [← eval_permuteConfigurationPolynomial σ P z, hP σ]

/-- Algebraic alternation implies alternation of the evaluated polynomial
function. -/
theorem isAlternating_eval_of_polynomial {n : ℕ}
    {P : ConfigurationPolynomial n}
    (hP : IsAlternatingConfigurationPolynomial P) :
    IsAlternating (fun z : Configuration n ↦ MvPolynomial.eval z P) := by
  intro σ z
  change MvPolynomial.eval (permute σ z) P =
    permutationSign σ * MvPolynomial.eval z P
  rw [← eval_permuteConfigurationPolynomial σ P z, hP σ]
  simp

/-- The polynomial Vandermonde is algebraically alternating. -/
theorem isAlternating_polynomialVandermonde (n : ℕ) :
    IsAlternatingConfigurationPolynomial (polynomialVandermonde n) := by
  intro σ
  have hmatrix :
      Matrix.vandermonde (fun i : Fin n ↦ MvPolynomial.X (σ i) :
        Fin n → ConfigurationPolynomial n) =
        (Matrix.vandermonde (fun i : Fin n ↦ MvPolynomial.X i :
          Fin n → ConfigurationPolynomial n)).submatrix σ id := by
    ext i j
    simp
  unfold permuteConfigurationPolynomial polynomialVandermonde
  change MvPolynomial.rename σ
      (Matrix.vandermonde (fun i : Fin n ↦ MvPolynomial.X i :
        Fin n → ConfigurationPolynomial n)).det = _
  calc
    _ = ((MvPolynomial.rename σ).mapMatrix
        (Matrix.vandermonde (fun i : Fin n ↦ MvPolynomial.X i :
          Fin n → ConfigurationPolynomial n))).det :=
      RingHom.map_det _ _
    _ = (Matrix.vandermonde (fun i : Fin n ↦ MvPolynomial.X (σ i) :
          Fin n → ConfigurationPolynomial n)).det := by
      congr 1
      ext i j
      simp
    _ = _ := by
      rw [hmatrix, Matrix.det_permute]
      simp [permutationSign]

/-- The polynomial Vandermonde is nonzero. -/
theorem polynomialVandermonde_ne_zero (n : ℕ) :
    polynomialVandermonde n ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval (fun i : Fin n ↦ ((i : ℕ) : ℂ))) hzero
  simp only [eval_polynomialVandermonde, map_zero] at heval
  exact (vandermonde_ne_zero_iff _).2 (fun i j hij ↦ by
    exact Fin.ext (by exact_mod_cast Complex.ofReal_injective hij)) heval

/-- A symmetric polynomial multiplied by the Vandermonde is alternating. -/
theorem isAlternating_polynomialVandermonde_mul {n : ℕ}
    {Q : ConfigurationPolynomial n}
    (hQ : IsSymmetricConfigurationPolynomial Q) :
    IsAlternatingConfigurationPolynomial (polynomialVandermonde n * Q) := by
  intro σ
  rw [map_mul]
  rw [isAlternating_polynomialVandermonde n σ, hQ σ]
  ring

/-- If an alternating polynomial is presented as a Vandermonde multiple,
then its quotient is symmetric. -/
theorem isSymmetric_quotient_of_vandermonde_mul_alternating {n : ℕ}
    {Q : ConfigurationPolynomial n}
    (hAlt : IsAlternatingConfigurationPolynomial
      (polynomialVandermonde n * Q)) :
    IsSymmetricConfigurationPolynomial Q := by
  intro σ
  have h := hAlt σ
  rw [map_mul] at h
  rw [isAlternating_polynomialVandermonde n σ] at h
  have hsign : MvPolynomial.C (permutationSign σ) ≠
      (0 : ConfigurationPolynomial n) := by
    rw [MvPolynomial.C_ne_zero]
    unfold permutationSign
    norm_num
  have hfac : MvPolynomial.C (permutationSign σ) *
      polynomialVandermonde n ≠ 0 :=
    mul_ne_zero hsign (polynomialVandermonde_ne_zero n)
  apply mul_left_cancel₀ hfac
  simpa only [mul_assoc] using h

/-- Division with symmetric quotient, once Vandermonde divisibility has been
established.  This isolates the factor-theorem step from quotient symmetry. -/
theorem alternating_polynomial_division_of_dvd {n : ℕ}
    {P : ConfigurationPolynomial n}
    (hAlt : IsAlternatingConfigurationPolynomial P)
    (hdiv : polynomialVandermonde n ∣ P) :
    ∃ Q : ConfigurationPolynomial n,
      IsSymmetricConfigurationPolynomial Q ∧
        P = polynomialVandermonde n * Q := by
  obtain ⟨Q, rfl⟩ := hdiv
  exact ⟨Q, isSymmetric_quotient_of_vandermonde_mul_alternating hAlt, rfl⟩

/-- Polynomial representing a normalized multivariate Hermite tensor of
zero antiholomorphic degree. -/
def holomorphicHermitePolynomial (n : ℕ) (p : Fin n → ℕ) :
    ConfigurationPolynomial n :=
  ∏ i : Fin n,
    MvPolynomial.C (ComplexHermite.oneDimNormalization n (p i) : ℂ) *
      MvPolynomial.X i ^ p i

/-- Zero-antiholomorphic-degree Hermite tensors are evaluations of genuine
holomorphic configuration polynomials. -/
theorem eval_holomorphicHermitePolynomial (n : ℕ) (hn : 0 < n)
    (p : Fin n → ℕ) (z : Configuration n) :
    MvPolynomial.eval z (holomorphicHermitePolynomial n p) =
      ComplexHermite.multivariateNormalized n hn p 0 z := by
  simp [holomorphicHermitePolynomial,
    ComplexHermite.multivariateNormalized_zero_right]

/-- Identify variable `j` with variable `i`. -/
def identifyVariable {n : ℕ} (i j : Fin n) : Fin n → Fin n :=
  fun k ↦ if k = j then i else k

/-- Identifying a pair of variables annihilates a polynomial which is
alternating under their transposition. -/
theorem rename_identifyVariable_eq_zero_of_swap_alternating {n : ℕ}
    {P : ConfigurationPolynomial n} {i j : Fin n} (hij : i ≠ j)
    (hP : permuteConfigurationPolynomial (Equiv.swap i j) P =
      MvPolynomial.C (permutationSign (Equiv.swap i j)) * P) :
    MvPolynomial.rename (identifyVariable i j) P = 0 := by
  have hcomp : identifyVariable i j ∘ Equiv.swap i j =
      identifyVariable i j := by
    funext k
    by_cases hki : k = i
    · subst k
      simp [identifyVariable, hij]
    · by_cases hkj : k = j
      · subst k
        simp [identifyVariable, hij]
      · simp [identifyVariable, Equiv.swap_apply_of_ne_of_ne hki hkj]
  have h := congrArg (MvPolynomial.rename (identifyVariable i j)) hP
  rw [show permuteConfigurationPolynomial (Equiv.swap i j) P =
      MvPolynomial.rename (Equiv.swap i j) P by rfl,
    MvPolynomial.rename_rename, hcomp] at h
  simp only [permutationSign, Equiv.Perm.sign_swap', hij, ↓reduceIte, Units.val_neg,
    Units.val_one, Int.reduceNeg, Int.cast_neg, Int.cast_one, MvPolynomial.C_1, neg_mul, one_mul,
    map_neg] at h
  have htwo : (2 : ℂ) • MvPolynomial.rename (identifyVariable i j) P = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr h
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Coefficient ring consisting of the variables other than `j`. -/
abbrev ConfigurationPolynomialAway {n : ℕ} (j : Fin n) :=
  MvPolynomial {k : Fin n // k ≠ j} ℂ

/-- Regard a multivariate polynomial as a univariate polynomial in `X j`,
with all other variables in the coefficient ring. -/
def asPolynomialInVariable {n : ℕ} (j : Fin n) :
    ConfigurationPolynomial n ≃ₐ[ℂ]
      Polynomial (ConfigurationPolynomialAway j) :=
  (MvPolynomial.renameEquiv ℂ (Equiv.optionSubtypeNe j).symm).trans
    (MvPolynomial.optionEquivLeft ℂ _)

/-- Constants become constant polynomials over the coefficient ring. -/
@[simp] theorem asPolynomialInVariable_C {n : ℕ} (j : Fin n) (c : ℂ) :
    asPolynomialInVariable j (MvPolynomial.C c) =
      Polynomial.C (MvPolynomial.C c) := by
  unfold asPolynomialInVariable
  simp only [AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_C]
  exact MvPolynomial.optionEquivLeft_C ℂ {k : Fin n // k ≠ j} c

/-- The distinguished variable becomes the univariate indeterminate. -/
@[simp] theorem asPolynomialInVariable_X_self {n : ℕ} (j : Fin n) :
    asPolynomialInVariable j (MvPolynomial.X j) = Polynomial.X := by
  unfold asPolynomialInVariable
  simp only [AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_X]
  have hnone : (Equiv.optionSubtypeNe j).symm j = none := by
    apply (Equiv.optionSubtypeNe j).injective
    simp
  rw [hnone, MvPolynomial.optionEquivLeft_X_none]

/-- Every other variable becomes a coefficient variable. -/
@[simp] theorem asPolynomialInVariable_X_of_ne {n : ℕ}
    {i j : Fin n} (hij : i ≠ j) :
    asPolynomialInVariable j (MvPolynomial.X i) =
      Polynomial.C (MvPolynomial.X ⟨i, hij⟩) := by
  unfold asPolynomialInVariable
  simp only [AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_X]
  have hsome : (Equiv.optionSubtypeNe j).symm i = some ⟨i, hij⟩ := by
    apply (Equiv.optionSubtypeNe j).injective
    simp [hij]
  rw [hsome, MvPolynomial.optionEquivLeft_X_some]

/-- In particular, the variable identified with `j` is represented by its
coefficient-ring indeterminate. -/
theorem asPolynomialInVariable_X_identified {n : ℕ}
    {i j : Fin n} (hij : i ≠ j) :
    asPolynomialInVariable j (MvPolynomial.X i) =
      Polynomial.C (MvPolynomial.X ⟨i, hij⟩) :=
  asPolynomialInVariable_X_of_ne hij

/-- Identifying `X j` with `X i` corresponds, in the univariate view, to
evaluation at the coefficient variable `X i` and reinsertion as a constant
polynomial. -/
theorem asPolynomialInVariable_rename_identifyVariable {n : ℕ}
    (P : ConfigurationPolynomial n) {i j : Fin n} (hij : i ≠ j) :
    asPolynomialInVariable j
        (MvPolynomial.rename (identifyVariable i j) P) =
      Polynomial.C
        ((asPolynomialInVariable j P).eval (MvPolynomial.X ⟨i, hij⟩)) := by
  let L : ConfigurationPolynomial n →+*
      Polynomial (ConfigurationPolynomialAway j) :=
    (asPolynomialInVariable j).toRingEquiv.toRingHom.comp
      (MvPolynomial.rename (identifyVariable i j)).toRingHom
  let R : ConfigurationPolynomial n →+*
      Polynomial (ConfigurationPolynomialAway j) :=
    Polynomial.C.comp
      ((Polynomial.evalRingHom (MvPolynomial.X ⟨i, hij⟩)).comp
        (asPolynomialInVariable j).toRingEquiv.toRingHom)
  have hLR : L = R := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [L, R]
    · intro k
      by_cases hkj : k = j
      · subst k
        simp [L, R, identifyVariable, hij]
      · simp [L, R, identifyVariable, hkj]
  exact DFunLike.congr_fun hLR P

/-- The kernel of identifying `j` with `i` is contained in the principal
ideal generated by `X j - X i`. -/
theorem X_sub_X_dvd_of_rename_identifyVariable_eq_zero {n : ℕ}
    {P : ConfigurationPolynomial n} {i j : Fin n} (hij : i ≠ j)
    (hzero : MvPolynomial.rename (identifyVariable i j) P = 0) :
    MvPolynomial.X j - MvPolynomial.X i ∣ P := by
  let e := asPolynomialInVariable j
  let a : ConfigurationPolynomialAway j := MvPolynomial.X ⟨i, hij⟩
  have heval : (e P).eval a = 0 := by
    have hconst : Polynomial.C ((e P).eval a) = 0 := by
      rw [← asPolynomialInVariable_rename_identifyVariable P hij,
        hzero, map_zero]
    apply Polynomial.C_injective
    simpa using hconst
  have hd : Polynomial.X - Polynomial.C a ∣ e P :=
    (Polynomial.dvd_iff_isRoot).2 heval
  have hmapped := map_dvd e.symm.toRingHom hd
  have hfactor : e.symm (Polynomial.X - Polynomial.C a) =
      MvPolynomial.X j - MvPolynomial.X i := by
    apply e.injective
    rw [e.apply_symm_apply]
    rw [map_sub, asPolynomialInVariable_X_self,
      asPolynomialInVariable_X_of_ne hij]
  change e.symm (Polynomial.X - Polynomial.C a) ∣ e.symm (e P) at hmapped
  rw [hfactor, e.symm_apply_apply] at hmapped
  exact hmapped

/-- A single transposition-antisymmetry forces the corresponding linear
Vandermonde factor. -/
theorem X_sub_X_dvd_of_swap_alternating {n : ℕ}
    {P : ConfigurationPolynomial n} {i j : Fin n} (hij : i ≠ j)
    (hP : permuteConfigurationPolynomial (Equiv.swap i j) P =
      MvPolynomial.C (permutationSign (Equiv.swap i j)) * P) :
    MvPolynomial.X j - MvPolynomial.X i ∣ P :=
  X_sub_X_dvd_of_rename_identifyVariable_eq_zero hij
    (rename_identifyVariable_eq_zero_of_swap_alternating hij hP)

/-- Every pairwise Vandermonde factor divides an alternating polynomial. -/
theorem X_sub_X_dvd_of_alternating {n : ℕ}
    {P : ConfigurationPolynomial n}
    (hP : IsAlternatingConfigurationPolynomial P)
    {i j : Fin n} (hij : i ≠ j) :
    MvPolynomial.X j - MvPolynomial.X i ∣ P :=
  X_sub_X_dvd_of_swap_alternating hij (hP (Equiv.swap i j))

/-- Each linear Vandermonde factor is prime. -/
theorem prime_X_sub_X {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Prime (MvPolynomial.X j - MvPolynomial.X i : ConfigurationPolynomial n) := by
  let e := asPolynomialInVariable j
  have hmap : e (MvPolynomial.X j - MvPolynomial.X i) =
      Polynomial.X - Polynomial.C (MvPolynomial.X ⟨i, hij⟩) := by
    rw [map_sub, asPolynomialInVariable_X_self,
      asPolynomialInVariable_X_of_ne hij]
  apply (MulEquiv.prime_iff e.toMulEquiv).mp
  change Prime (e (MvPolynomial.X j - MvPolynomial.X i))
  rw [hmap]
  exact Polynomial.prime_X_sub_C _

private theorem identifyVariable_ne_of_ordered_pairs_ne {n : ℕ}
    {i j k l : Fin n} (hij : i < j) (hkl : k < l)
    (hpairs : (i, j) ≠ (k, l)) :
    identifyVariable i j k ≠ identifyVariable i j l := by
  intro h
  by_cases hlj : l = j
  · subst l
    have hkj : k ≠ j := ne_of_lt hkl
    have hki : k = i := by simpa [identifyVariable, hkj] using h
    subst k
    exact hpairs rfl
  · by_cases hkj : k = j
    · subst k
      have hli : l = i := by simpa [identifyVariable, hij.ne, hlj] using h.symm
      subst l
      exact lt_asymm hij hkl
    · have : k = l := by simpa [identifyVariable, hkj, hlj] using h
      exact hkl.ne this

/-- Distinct oriented Vandermonde factors do not divide one another. -/
theorem not_dvd_X_sub_X_of_ordered_pairs_ne {n : ℕ}
    {i j k l : Fin n} (hij : i < j) (hkl : k < l)
    (hpairs : (i, j) ≠ (k, l)) :
    ¬(MvPolynomial.X j - MvPolynomial.X i : ConfigurationPolynomial n) ∣
      MvPolynomial.X l - MvPolynomial.X k := by
  intro hdvd
  have hmapped := map_dvd (MvPolynomial.rename (identifyVariable i j)) hdvd
  have hleft : MvPolynomial.rename (identifyVariable i j)
      (MvPolynomial.X j - MvPolynomial.X i : ConfigurationPolynomial n) = 0 := by
    simp [identifyVariable, hij.ne]
  rw [hleft, zero_dvd_iff] at hmapped
  simp only [map_sub, MvPolynomial.rename_X] at hmapped
  have hx : MvPolynomial.X (identifyVariable i j l) =
      (MvPolynomial.X (identifyVariable i j k) : ConfigurationPolynomial n) :=
    sub_eq_zero.mp hmapped
  exact identifyVariable_ne_of_ordered_pairs_ne hij hkl hpairs
    (MvPolynomial.X_injective hx.symm)

/-- Distinct oriented Vandermonde factors are relatively prime. -/
theorem isRelPrime_X_sub_X_of_ordered_pairs_ne {n : ℕ}
    {i j k l : Fin n} (hij : i < j) (hkl : k < l)
    (hpairs : (i, j) ≠ (k, l)) :
    IsRelPrime
      (MvPolynomial.X j - MvPolynomial.X i : ConfigurationPolynomial n)
      (MvPolynomial.X l - MvPolynomial.X k) := by
  rw [(prime_X_sub_X hij.ne).irreducible.isRelPrime_iff_not_dvd]
  exact not_dvd_X_sub_X_of_ordered_pairs_ne hij hkl hpairs

/-- The finite type of strictly ordered particle pairs. -/
abbrev OrderedParticlePair (n : ℕ) :=
  Σ i : Fin n, {j : Fin n // j ∈ Finset.Ioi i}

/-- Linear Vandermonde factor attached to an ordered pair. -/
def orderedPairFactor {n : ℕ} (p : OrderedParticlePair n) :
    ConfigurationPolynomial n :=
  MvPolynomial.X p.2.1 - MvPolynomial.X p.1

theorem pairwise_isRelPrime_orderedPairFactor (n : ℕ) :
    Pairwise (fun p q : OrderedParticlePair n ↦
      IsRelPrime (orderedPairFactor p) (orderedPairFactor q)) := by
  rintro ⟨i, j, hij⟩ ⟨k, l, hkl⟩ hpq
  apply isRelPrime_X_sub_X_of_ordered_pairs_ne
    (Finset.mem_Ioi.mp hij) (Finset.mem_Ioi.mp hkl)
  intro hpairs
  apply hpq
  have hik : i = k := congrArg Prod.fst hpairs
  have hjl : j = l := congrArg Prod.snd hpairs
  subst k
  subst l
  rfl

/-- The product over ordered pairs is the polynomial Vandermonde. -/
theorem prod_orderedPairFactor (n : ℕ) :
    ∏ p : OrderedParticlePair n, orderedPairFactor p =
      polynomialVandermonde n := by
  rw [polynomialVandermonde_eq_product]
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro i hi
  symm
  exact Finset.prod_subtype (Finset.Ioi i) (by simp) _

/-- Every alternating configuration polynomial is divisible by the complete
Vandermonde polynomial. -/
theorem polynomialVandermonde_dvd_of_alternating {n : ℕ}
    {P : ConfigurationPolynomial n}
    (hP : IsAlternatingConfigurationPolynomial P) :
    polynomialVandermonde n ∣ P := by
  rw [← prod_orderedPairFactor n]
  apply Fintype.prod_dvd_of_isRelPrime
    (pairwise_isRelPrime_orderedPairFactor n)
  intro p
  have hp : p.1 < p.2.1 := Finset.mem_Ioi.mp p.2.2
  exact X_sub_X_dvd_of_alternating hP hp.ne

/-- Algebraic Vandermonde division for alternating polynomials, with a
symmetric quotient. -/
theorem alternating_polynomial_vandermonde_division {n : ℕ}
    {P : ConfigurationPolynomial n}
    (hP : IsAlternatingConfigurationPolynomial P) :
    ∃ Q : ConfigurationPolynomial n,
      IsSymmetricConfigurationPolynomial Q ∧
        P = polynomialVandermonde n * Q :=
  alternating_polynomial_division_of_dvd hP
    (polynomialVandermonde_dvd_of_alternating hP)

/-! ## Finite zero-antiholomorphic Hermite sums -/

/-- The holomorphic polynomial attached coefficient-by-coefficient to a
finite linear combination of zero-antiholomorphic Hermite tensors. -/
def finiteZeroAntiholomorphicHermitePolynomial (n : ℕ)
    (S : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ) :
    ConfigurationPolynomial n :=
  ∑ p ∈ S, MvPolynomial.C (c p) * holomorphicHermitePolynomial n p

/-- The corresponding finite Hermite function. -/
def finiteZeroAntiholomorphicHermiteSum (n : ℕ) (hn : 0 < n)
    (S : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ)
    (z : Configuration n) : ℂ :=
  ∑ p ∈ S, c p * ComplexHermite.multivariateNormalized n hn p 0 z

/-- Evaluation commutes exactly with formation of the finite Hermite sum. -/
theorem eval_finiteZeroAntiholomorphicHermitePolynomial (n : ℕ)
    (hn : 0 < n) (S : Finset (Fin n → ℕ))
    (c : (Fin n → ℕ) → ℂ) (z : Configuration n) :
    MvPolynomial.eval z
        (finiteZeroAntiholomorphicHermitePolynomial n S c) =
      finiteZeroAntiholomorphicHermiteSum n hn S c z := by
  unfold finiteZeroAntiholomorphicHermitePolynomial
    finiteZeroAntiholomorphicHermiteSum
  simp only [map_sum, map_mul, MvPolynomial.eval_C]
  apply Finset.sum_congr rfl
  intro p hp
  rw [eval_holomorphicHermitePolynomial n hn p z]

/-- At positive particle number the ground-state normalization is nonzero. -/
theorem groundStateNormalization_ne_zero_of_pos {n : ℕ} (hn : 0 < n) :
    groundStateNormalization n ≠ 0 := by
  apply ne_of_gt
  unfold groundStateNormalization
  apply Real.sqrt_pos.2
  exact ENNReal.toReal_pos (ginibreNormalizingMass_pos hn).ne'
    (ginibreNormalizingMass_lt_top n).ne

/-- Coefficient-level finite Hermite division.  An algebraically alternating
finite zero-antiholomorphic Hermite sum is exactly a Vandermonde times the
evaluation of a symmetric holomorphic polynomial. -/
theorem finiteZeroAntiholomorphicHermiteSum_division {n : ℕ} (hn : 0 < n)
    (S : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ)
    (hAlt : IsAlternatingConfigurationPolynomial
      (finiteZeroAntiholomorphicHermitePolynomial n S c)) :
    ∃ Q : ConfigurationPolynomial n,
      IsSymmetricConfigurationPolynomial Q ∧
      ∀ z : Configuration n,
        finiteZeroAntiholomorphicHermiteSum n hn S c z =
          vandermonde z * MvPolynomial.eval z Q := by
  obtain ⟨Q, hQ, hfactor⟩ := alternating_polynomial_vandermonde_division hAlt
  refine ⟨Q, hQ, fun z ↦ ?_⟩
  rw [← eval_finiteZeroAntiholomorphicHermitePolynomial n hn S c z,
    hfactor, map_mul, eval_polynomialVandermonde]

/-- Functional alternation of a finite zero-antiholomorphic Hermite sum is
equivalent to algebraic alternation of its coefficient polynomial. -/
theorem isAlternatingConfigurationPolynomial_of_finiteHermiteSum
    {n : ℕ} (hn : 0 < n) (S : Finset (Fin n → ℕ))
    (c : (Fin n → ℕ) → ℂ)
    (hAlt : IsAlternating
      (finiteZeroAntiholomorphicHermiteSum n hn S c)) :
    IsAlternatingConfigurationPolynomial
      (finiteZeroAntiholomorphicHermitePolynomial n S c) := by
  intro σ
  apply MvPolynomial.funext
  intro z
  rw [eval_permuteConfigurationPolynomial,
    eval_finiteZeroAntiholomorphicHermitePolynomial n hn S c,
    map_mul, MvPolynomial.eval_C,
    eval_finiteZeroAntiholomorphicHermitePolynomial n hn S c]
  exact hAlt σ z

/-- Thus no alternation information is lost when passing between the finite
Hermite coefficient sum and its holomorphic polynomial representative. -/
theorem finiteHermiteSum_isAlternating_iff {n : ℕ} (hn : 0 < n)
    (S : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ) :
    IsAlternating (finiteZeroAntiholomorphicHermiteSum n hn S c) ↔
      IsAlternatingConfigurationPolynomial
        (finiteZeroAntiholomorphicHermitePolynomial n S c) := by
  constructor
  · exact isAlternatingConfigurationPolynomial_of_finiteHermiteSum hn S c
  · intro hP
    have heval := isAlternating_eval_of_polynomial hP
    intro σ z
    rw [← eval_finiteZeroAntiholomorphicHermitePolynomial n hn S c]
    rw [← eval_finiteZeroAntiholomorphicHermitePolynomial n hn S c]
    exact heval σ z

/-- The preceding factorization is precisely the normalized Vandermonde
transform after multiplying the symmetric quotient by the ground-state
normalization. -/
theorem finiteZeroAntiholomorphicHermiteSum_eq_normalizedTransform
    {n : ℕ} (hn : 0 < n) (S : Finset (Fin n → ℕ))
    (c : (Fin n → ℕ) → ℂ)
    (hAlt : IsAlternatingConfigurationPolynomial
      (finiteZeroAntiholomorphicHermitePolynomial n S c)) :
    ∃ Q : ConfigurationPolynomial n,
      IsSymmetricConfigurationPolynomial Q ∧
      ∀ z : Configuration n,
        finiteZeroAntiholomorphicHermiteSum n hn S c z =
          normalizedVandermondeTransform n
            (fun w ↦ (groundStateNormalization n : ℂ) *
              MvPolynomial.eval w Q) z := by
  obtain ⟨Q, hQ, hsum⟩ :=
    finiteZeroAntiholomorphicHermiteSum_division hn S c hAlt
  refine ⟨Q, hQ, fun z ↦ ?_⟩
  rw [hsum z, normalizedVandermondeTransform_apply]
  have hnorm : (groundStateNormalization n : ℂ) ≠ 0 := by
    exact_mod_cast groundStateNormalization_ne_zero_of_pos hn
  field_simp

/-- Function-level finite-span identification: every alternating finite
zero-antiholomorphic Hermite combination is the normalized Vandermonde
transform of the evaluation of a symmetric holomorphic polynomial (with the
exact ground-state scalar). -/
theorem alternating_finiteZeroAntiholomorphicHermiteSpan
    {n : ℕ} (hn : 0 < n) (S : Finset (Fin n → ℕ))
    (c : (Fin n → ℕ) → ℂ)
    (hAlt : IsAlternating
      (finiteZeroAntiholomorphicHermiteSum n hn S c)) :
    ∃ Q : ConfigurationPolynomial n,
      IsSymmetricConfigurationPolynomial Q ∧
      ∀ z : Configuration n,
        finiteZeroAntiholomorphicHermiteSum n hn S c z =
          normalizedVandermondeTransform n
            (fun w ↦ (groundStateNormalization n : ℂ) *
              MvPolynomial.eval w Q) z :=
  finiteZeroAntiholomorphicHermiteSum_eq_normalizedTransform hn S c
    (isAlternatingConfigurationPolynomial_of_finiteHermiteSum hn S c hAlt)

/-- Away from the collision locus, division by the normalized Vandermonde
recovers the symmetric polynomial quotient pointwise. -/
theorem finiteZeroAntiholomorphicHermiteSum_normalizedInverse
    {n : ℕ} (hn : 0 < n) (S : Finset (Fin n → ℕ))
    (c : (Fin n → ℕ) → ℂ)
    (hAlt : IsAlternatingConfigurationPolynomial
      (finiteZeroAntiholomorphicHermitePolynomial n S c)) :
    ∃ Q : ConfigurationPolynomial n,
      IsSymmetricConfigurationPolynomial Q ∧
      ∀ z : Configuration n, vandermonde z ≠ 0 →
        (groundStateNormalization n : ℂ) *
            finiteZeroAntiholomorphicHermiteSum n hn S c z /
              vandermonde z =
          (groundStateNormalization n : ℂ) * MvPolynomial.eval z Q := by
  obtain ⟨Q, hQ, hsum⟩ :=
    finiteZeroAntiholomorphicHermiteSum_division hn S c hAlt
  refine ⟨Q, hQ, fun z hz ↦ ?_⟩
  rw [hsum z]
  field_simp

end

end GinibrePoincare

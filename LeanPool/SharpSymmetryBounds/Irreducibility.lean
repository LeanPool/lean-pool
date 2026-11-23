/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SharpSymmetryBounds.RotationSupport
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Irreducibility of binary polynomials

Degree facts for divisors of irreducible polynomials, reducibility of binary sums of pure
powers, and the homogeneous endpoint of the anti-invariant support calculation.
-/

@[expose] public section

namespace CurveSymmetry

open MvPolynomial

/-- A nonunit divisor of an irreducible polynomial has the same degree. -/
lemma degree_le_of_nonunit_dvd {P L : BPoly} (hP : Irreducible P)
    (hL : ¬ IsUnit L) (hdiv : L ∣ P) : P.totalDegree ≤ L.totalDegree := by
  obtain ⟨Q, hQ⟩ := hdiv
  have hunit : IsUnit Q := (hP.isUnit_or_isUnit hQ).resolve_left hL
  have hzero := (isUnit_iff_totalDegree_of_isReduced.mp hunit).2
  rw [hQ]
  simpa [hzero] using totalDegree_mul L Q

lemma linear_not_isUnit (c : ℂ) : ¬ IsUnit ((X 0 : BPoly) - C c * X 1) := by
  intro hu
  have h := hu.map (eval₂Hom (RingHom.id ℂ) (fun _ : Fin 2 => 0))
  simp at h

lemma linear_degree_le (c : ℂ) : ((X 0 : BPoly) - C c * X 1).totalDegree ≤ 1 := by
  have hmul := totalDegree_mul (C c : BPoly) (X 1)
  have hsub := totalDegree_sub (X 0 : BPoly) (C c * X 1)
  simp only [totalDegree_C, totalDegree_X, zero_add] at hmul hsub
  omega

/-- A binary sum of pure powers of degree at least two is reducible over `ℂ`. -/
theorem not_irreducible_pure_powers (m : ℕ) (hm : 2 ≤ m) (a b : ℂ) :
    ¬ Irreducible (C a * (X 0 : BPoly) ^ m + C b * X 1 ^ m) := by
  intro hirr
  have hhom : (C a * (X 0 : BPoly) ^ m + C b * X 1 ^ m).IsHomogeneous m :=
    (isHomogeneous_X_pow 0 m).C_mul a |>.add ((isHomogeneous_X_pow 1 m).C_mul b)
  have hdegree := hhom.totalDegree hirr.ne_zero
  by_cases ha : a = 0
  · have hY : ¬ IsUnit (X 1 : BPoly) := by
      intro hu
      have := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
      simp at this
    have hdiv : (X 1 : BPoly) ∣ C a * (X 0 : BPoly) ^ m + C b * X 1 ^ m := by
      simp only [ha, map_zero, zero_mul, zero_add]
      exact dvd_mul_of_dvd_right (dvd_pow_self (X 1) (by omega)) (C b)
    have h := degree_le_of_nonunit_dvd hirr hY hdiv
    simp only [totalDegree_X, hdegree] at h
    omega
  · obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (-b / a) (by omega : 0 < m)
    have hab : a * c ^ m = -b := by rw [hc]; field_simp
    have hform : C a * (X 0 : BPoly) ^ m + C b * X 1 ^ m =
        C a * ((X 0 : BPoly) ^ m - (C c * X 1) ^ m) := by
      rw [mul_pow, ← map_pow C]
      have hab' : (C a : BPoly) * C (c ^ m) = -C b := by rw [← map_mul, hab, map_neg]
      linear_combination hab' * (X 1 : BPoly) ^ m
    have hdiv : ((X 0 : BPoly) - C c * X 1) ∣
        C a * (X 0 : BPoly) ^ m + C b * X 1 ^ m := by
      rw [hform]
      exact dvd_mul_of_dvd_right (sub_dvd_pow_sub_pow _ _ m) (C a)
    have h := (degree_le_of_nonunit_dvd hirr (linear_not_isUnit c) hdiv).trans
      (linear_degree_le c)
    omega

/-- The homogeneous endpoint of the anti-invariant support calculation. -/
lemma anti_two_normal_form {m : ℕ} (hm : 2 ≤ m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * m)) {P : BPoly}
    (hdeg : P.totalDegree ≤ m + 1) (hanti : rotate ζ P = -P) :
    P = C (P.coeff (exponent m 0)) * (X 0 : BPoly) ^ m +
      C (P.coeff (exponent 0 m)) * X 1 ^ m := by
  classical
  have hsupp : ∀ s ∈ P.support, s = exponent m 0 ∨ s = exponent 0 m := by
    intro s hs
    have hd := support_degree hs
    have hw := anti_support (by omega) hζ (by omega) hanti hs
    simp only [exponent_eq_iff]
    omega
  have hne : exponent m 0 ≠ exponent 0 m := by simp [exponent_eq_iff]; omega
  have hform : P = monomial (exponent m 0) (P.coeff (exponent m 0)) +
      monomial (exponent 0 m) (P.coeff (exponent 0 m)) := by
    ext s
    by_cases hs : s ∈ P.support
    · rcases hsupp s hs with rfl | rfl <;> simp [coeff_monomial, hne, Ne.symm hne]
    · have hc : P.coeff s = 0 := notMem_support_iff.mp hs
      simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_monomial]
      split_ifs <;> simp_all
  simpa [monomial_exponent] using hform

/-- Irreducibility now supplies the formerly explicit non-homogeneity exclusion. -/
theorem irreducible_anti_degree_gap {m : ℕ} (hm : 2 ≤ m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * m)) {P : BPoly}
    (hirr : Irreducible P) (hanti : rotate ζ P = -P) : m + 2 ≤ P.totalDegree := by
  by_contra h
  have hform := anti_two_normal_form hm hζ (by omega) hanti
  rw [hform] at hirr
  exact not_irreducible_pure_powers m hm _ _ hirr

/-- Diagonal monomial support is exactly a polynomial in `XY`. -/
lemma radial_representation {P : BPoly}
    (hdiag : ∀ s ∈ P.support, s 0 = s 1) :
    ∃ Q : Polynomial ℂ, P = Polynomial.aeval ((X 0 : BPoly) * X 1) Q := by
  classical
  refine ⟨∑ s ∈ P.support, Polynomial.monomial (s 0) (P.coeff s), ?_⟩
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have he : s = exponent (s 0) (s 0) := exponent_eq_iff.mpr ⟨rfl, (hdiag s hs).symm⟩
  rw [Polynomial.aeval_monomial, he, monomial_exponent]
  simp [mul_pow, mul_assoc]

lemma radial_factor_not_isUnit (r : ℂ) : ¬ IsUnit ((X 0 : BPoly) * X 1 - C r) := by
  intro hu
  have h := hu.map (eval₂Hom (RingHom.id ℂ) (fun i : Fin 2 => if i = 0 then r else 1))
  simp at h

/-- An irreducible radial polynomial is a nonzero constant times `XY-r`. -/
theorem irreducible_radial_form {P : BPoly} (hirr : Irreducible P)
    (hdiag : ∀ s ∈ P.support, s 0 = s 1) :
    ∃ a r : ℂ, a ≠ 0 ∧ P = C a * ((X 0 : BPoly) * X 1 - C r) := by
  obtain ⟨Q, hQ⟩ := radial_representation hdiag
  have hdegree : Q.degree ≠ 0 := by
    intro hd
    have hnat : Q.natDegree = 0 := Polynomial.natDegree_eq_of_degree_eq_some hd
    rw [Polynomial.eq_C_of_natDegree_eq_zero hnat, Polynomial.aeval_C] at hQ
    have hc : Q.coeff 0 ≠ 0 := by
      intro hzero
      apply hirr.ne_zero
      simpa [hzero] using hQ
    apply hirr.not_isUnit
    rw [hQ]
    exact (isUnit_iff_ne_zero.mpr hc).map (algebraMap ℂ BPoly)
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root Q hdegree
  have hdiv : ((X 0 : BPoly) * X 1 - C r) ∣ P := by
    rw [hQ]
    have hroot : (Polynomial.X - Polynomial.C r : Polynomial ℂ) ∣ Q :=
      Polynomial.dvd_iff_isRoot.mpr hr
    have hmap := Polynomial.aeval_dvd ((X 0 : BPoly) * X 1) hroot
    convert hmap using 1
    simp [Polynomial.aeval_def]
  obtain ⟨S, hS⟩ := hdiv
  have hu : IsUnit S := (hirr.isUnit_or_isUnit hS).resolve_left (radial_factor_not_isUnit r)
  obtain ⟨a, ha, hSa⟩ := isUnit_iff_eq_C_of_isReduced.mp hu
  refine ⟨a, r, isUnit_iff_ne_zero.mp ha, ?_⟩
  rw [hS, hSa, mul_comm]

/-- A polynomial version of the bound with irreducibility, not non-homogeneity,
as a hypothesis. The only excluded polynomial shapes are the radial conics. -/
theorem irreducible_rotation_bound {N : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) {P : BPoly} (hirr : Irreducible P)
    (hd : 2 ≤ P.totalDegree)
    (hnonradial : ¬ ∃ a r : ℂ, a ≠ 0 ∧ P = C a * ((X 0 : BPoly) * X 1 - C r))
    (hsign : rotate ζ P = P ∨ rotate ζ P = -P) :
    N ≤ max P.totalDegree (2 * P.totalDegree - 4) := by
  by_cases hsmall : N ≤ P.totalDegree
  · exact le_trans hsmall (le_max_left _ _)
  have hlarge : P.totalDegree < N := by omega
  rcases hsign with hfixed | hanti
  · exact (hnonradial (irreducible_radial_form hirr
      (fun _ hs => fixed_support hζ hlarge hfixed hs))).elim
  · obtain ⟨m, hN⟩ := anti_even_order hζ hirr.ne_zero hanti
    have horder : N = 2 * m := by omega
    have hgap := irreducible_anti_degree_gap (by omega) (horder ▸ hζ) hirr hanti
    exact le_trans (by omega : N ≤ 2 * P.totalDegree - 4) (le_max_right _ _)

end CurveSymmetry

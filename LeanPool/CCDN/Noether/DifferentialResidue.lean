/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.RingTheory.Derivation.MapCoeffs

/-! Residues of closed rational one-forms at simple polynomial roots.
The polynomial proof avoids needing a partial-fraction decomposition. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Differential
open scoped Differential

private lemma polynomial_degree_C_mul_le {K : Type*} [Field K] (a : K) (p : K[X]) :
    (C a * p).degree ≤ p.degree := by
  simpa only [smul_eq_C_mul] using degree_smul_le a p

/-- Coefficientwise differentiation strictly lowers the degree of a monic
polynomial, since its leading coefficient differentiates to zero. -/
private lemma differential_mapCoeffs_degree_lt {K : Type*} [Field K] [Differential K]
    {p : K[X]} (hp : p.Monic) : (Differential.mapCoeffs p).degree < p.degree := by
  rw [degree_eq_natDegree hp.ne_zero, degree_lt_iff_coeff_zero]
  intro n hn
  rw [Differential.coeff_mapCoeffs]
  rcases eq_or_lt_of_le hn with h | h
  · rw [← h, hp.coeff_natDegree]
    exact Derivation.map_one_eq_zero _
  · rw [coeff_eq_zero_of_natDegree_lt h, map_zero]

/-- Coefficientwise differentiation commutes with the formal derivative of polynomials. -/
lemma derivative_differential_mapCoeffs {K : Type*} [Field K] [Differential K]
    (f : K[X]) : (Differential.mapCoeffs f).derivative =
      Differential.mapCoeffs f.derivative := by
  ext n
  simp [coeff_derivative, Derivation.leibniz, smul_eq_mul, mul_comm]

/-- A closed rational one-form has differentially constant residue at every
simple root of its denominator. The equation is written after clearing f². -/
theorem closed_form_residue_deriv_eq_zero
    {K : Type*} [Field K] [Differential K] (f p q : K[X]) (c : K)
    (hroot : aeval c f = 0) (hsimple : aeval c f.derivative ≠ 0)
    (hclosed : Differential.mapCoeffs p * f - p * Differential.mapCoeffs f =
      q.derivative * f - q * f.derivative) :
    (aeval c p / aeval c f.derivative)′ = 0 := by
  have hrootD : aeval c (Differential.mapCoeffs f) + aeval c f.derivative * c′ = 0 := by
    have h := congrArg Differential.deriv hroot
    simpa only [Differential.deriv_aeval_eq, map_zero] using h
  have he := congrArg (aeval c) hclosed
  simp only [map_sub, map_mul, hroot, mul_zero, zero_sub] at he
  have hq : aeval c q + aeval c p * c′ = 0 := by
    apply (mul_eq_zero.mp
      (show aeval c f.derivative * (aeval c q + aeval c p * c′) = 0 from ?_)).resolve_left
      hsimple
    linear_combination (aeval c p) * hrootD + he
  have hd := congrArg Polynomial.derivative hclosed
  simp only [derivative_sub, derivative_mul, derivative_differential_mapCoeffs] at hd
  have hde := congrArg (aeval c) hd
  simp only [map_sub, map_add, map_mul, hroot, mul_zero, zero_add] at hde
  have hn : aeval c f.derivative * (aeval c p)′ - aeval c p * (aeval c f.derivative)′ = 0 := by
    simp only [Differential.deriv_aeval_eq]
    linear_combination hde + (aeval c p.derivative) * hrootD -
      (aeval c f.derivative.derivative) * hq
  rw [Derivation.leibniz_div, smul_eq_mul, smul_eq_mul, smul_eq_mul, hn, mul_zero]

/-- Coefficientwise differentiation commutes with extending coefficients along a differential
algebra `K → L`. -/
lemma differential_mapCoeffs_map {K L : Type*} [Field K] [Field L]
    [Differential K] [Differential L] [Algebra K L] [DifferentialAlgebra K L]
    (p : K[X]) : Differential.mapCoeffs (p.map (algebraMap K L)) =
      (Differential.mapCoeffs p).map (algebraMap K L) := by
  ext n
  simp only [Differential.coeff_mapCoeffs, coeff_map, deriv_algebraMap]

private lemma eq_zero_of_aeval_root_of_degree_lt {K L : Type*} [Field K] [Field L]
    [Algebra K L] {f p : K[X]} (hf : Irreducible f) (hm : f.Monic)
    {c : L} (hc : aeval c f = 0) (hp : aeval c p = 0) (hdeg : p.degree < f.degree) : p = 0 := by
  have hdiv := minpoly.dvd K c hp
  rw [← minpoly.eq_of_irreducible_of_monic hf hc hm] at hdiv
  by_contra hn
  exact (not_le_of_gt hdeg) (degree_le_of_dvd hdiv hn)

/-- For a monic irreducible denominator, a closed form with a single
base-field residue is a constant multiple of its logarithmic differential.
Only the displayed residue must descend, not every differential constant
in the root field. -/
theorem closed_form_eq_constant_gradient_of_residue_mem_base
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
    [Differential K]
    (f p q : K[X]) (hf : Irreducible f) (hm : f.Monic) (c : L)
    (hc : aeval c f = 0) (hsimple : aeval c f.derivative ≠ 0)
    (hpdeg : p.degree < f.degree) (hqdeg : q.degree < f.degree)
    (hclosed : Differential.mapCoeffs p * f - p * Differential.mapCoeffs f =
      q.derivative * f - q * f.derivative)
    (hres : aeval c p / aeval c f.derivative ∈ (algebraMap F L).range) :
    ∃ a : F, p = C (algebraMap F K a) * f.derivative ∧
      q = C (algebraMap F K a) * Differential.mapCoeffs f := by
  obtain ⟨a, ha⟩ := hres
  have hres : algebraMap K L (algebraMap F K a) = aeval c p / aeval c f.derivative := by
    simpa only [← IsScalarTower.algebraMap_apply] using ha
  have hpEval : aeval c p = algebraMap K L (algebraMap F K a) * aeval c f.derivative :=
    ((eq_div_iff hsimple).mp hres).symm
  have hpzero : p - C (algebraMap F K a) * f.derivative = 0 := by
    apply eq_zero_of_aeval_root_of_degree_lt hf hm hc
    · simpa only [map_sub, map_mul, aeval_C, sub_eq_zero] using hpEval
    · exact (degree_sub_le _ _).trans_lt (max_lt hpdeg
        ((polynomial_degree_C_mul_le _ _).trans_lt (degree_derivative_lt hf.ne_zero)))
  have hpEq := sub_eq_zero.mp hpzero
  have he := congrArg (aeval c) hclosed
  simp only [map_sub, map_mul, hc, mul_zero, zero_sub] at he
  have hqEval :
      aeval c q = algebraMap K L (algebraMap F K a) * aeval c (Differential.mapCoeffs f) := by
    apply mul_right_cancel₀ hsimple
    rw [hpEval] at he
    linear_combination he
  have hqzero : q - C (algebraMap F K a) * Differential.mapCoeffs f = 0 := by
    apply eq_zero_of_aeval_root_of_degree_lt hf hm hc
    · simpa only [map_sub, map_mul, aeval_C, sub_eq_zero] using hqEval
    · exact (degree_sub_le _ _).trans_lt (max_lt hqdeg
        ((polynomial_degree_C_mul_le _ _).trans_lt (differential_mapCoeffs_degree_lt hm)))
  exact ⟨a, hpEq, sub_eq_zero.mp hqzero⟩

end
end CCDN

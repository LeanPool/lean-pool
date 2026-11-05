/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.PolynomialLinearDescent
import LeanPool.CCDN.Hilbert.ScalarExtension
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Coefficient-linear descent detects nonmembership in scalar-extended
ideals, and descends degree-bounded separating equations. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma polynomialCoefficientLinear_map_of_one {K L : Type*}
    [Field K] [Field L] [Algebra K L] {n : ℕ}
    (φ : L →ₗ[K] K) (hφ : φ 1 = 1) (f : MvPolynomial (Fin n) K) :
    polynomialCoefficientLinear φ (map (algebraMap K L) f) = f := by
  ext a
  rw [polynomialCoefficientLinear_coeff, coeff_map]
  have hh := φ.map_smul (f.coeff a) (1 : L)
  simpa only [Algebra.smul_def, mul_one, hφ, Algebra.algebraMap_self,
    RingHom.id_apply] using hh

/-- For a field extension `L` of `K`, a polynomial `f` over `K` lies in the extension of the
ideal `I` to polynomials over `L` if and only if `f` lies in `I`. -/
theorem mem_ideal_scalar_extension_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin n) K) :
    map (algebraMap K L) f ∈ I.map (map (algebraMap K L)) ↔ f ∈ I := by
  constructor
  · intro h
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : L) ≠ 0)
    have hh := polynomialCoefficientLinear_mem_scalar_extension I _ h φ
    rwa [polynomialCoefficientLinear_map_of_one φ hφ] at hh
  · exact Ideal.mem_map_of_mem _

/-- Some coefficient functional detects nonmembership in an extended ideal. -/
theorem exists_polynomialCoefficientLinear_not_mem
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (J : Ideal (MvPolynomial (Fin n) K)) (g : MvPolynomial (Fin n) L)
    (hg : g ∉ J.map (map (algebraMap K L))) :
    ∃ φ : L →ₗ[K] K, polynomialCoefficientLinear φ g ∉ J := by
  classical
  let J' := J.map (map (algebraMap K L))
  obtain ⟨r, hrstd, _, hrJ⟩ := Ideal.exists_standard_representative_degLex J' g
  have hr0 : r ≠ 0 := by intro h; exact hg (by simpa only [h, sub_zero] using hrJ)
  obtain ⟨a, ha⟩ := exists_coeff_ne_zero hr0
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero K ha
  refine ⟨φ, ?_⟩
  intro hgJ
  have hdJ := polynomialCoefficientLinear_mem_scalar_extension J (g - r) hrJ φ
  rw [map_sub] at hdJ
  have hrmem : polynomialCoefficientLinear φ r ∈ J := by
    have hh := J.sub_mem hgJ hdJ
    simpa only [sub_sub_cancel] using hh
  have hrstdK : polynomialCoefficientLinear φ r ∈
      restrictSupport K (Ideal.standardExponents J MonomialOrder.degLex) := by
    intro b hb
    have hbr : b ∈ r.support := by
      change b ∈ (polynomialCoefficientLinear φ r).support at hb
      rw [mem_support_iff] at hb ⊢
      intro hzero
      apply hb
      rw [polynomialCoefficientLinear_coeff, hzero, map_zero]
    have hh := hrstd hbr
    simpa only [J', standardExponents_scalar_extension] using hh
  have hrzero :=
    Ideal.eq_zero_of_mem_restrictSupport_standardExponents J MonomialOrder.degLex hrstdK hrmem
  have hc := polynomialCoefficientLinear_coeff φ r a
  have hz : φ (r.coeff a) = 0 := by simpa [hrzero] using hc.symm
  exact hφ hz

end
end CCDN

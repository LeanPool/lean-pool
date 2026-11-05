/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.CharZeroOrGT
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Derivation.MapCoeffs
import LeanPool.CCDN.Noether.DifferentialResidue

/-!
A low-degree algebraic relation detects differential constants.
If t'=1, no nonzero polynomial in t of degree below the characteristic
can have differential-constant coefficients and vanish. Applied to a
bivariate relation, this gives constant descent directly from elimination.

Bounded-degree differential constants, in characteristic zero or above
the degree. In positive characteristic the degree restrictions are essential. These
lemmas isolate the constant-descent step in Gao's differential criterion;
they do not supply the resultant bounds for residues or a Bertini theorem.
-/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Differential
open scoped Differential

/-- A polynomial with zero derivative is constant when its degree is below the characteristic. -/
private lemma polynomial_eq_C_of_derivative_eq_zero_of_degree_lt_char
    {K : Type*} [Field K] (f : K[X]) (hchar : CharZeroOrGT K f.natDegree)
    (hder : f.derivative = 0) :
    f = C (f.coeff 0) := by
  ext i
  by_cases hi : i = 0
  · subst i; simp
  · rw [coeff_C, ite_eq_right hi]
    by_cases hlarge : f.natDegree < i
    · exact coeff_eq_zero_of_natDegree_lt hlarge
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
      have h := congrArg (fun q : K[X] => q.coeff j) hder
      simp only [coeff_derivative, coeff_zero] at h
      exact (mul_eq_zero.mp h).resolve_right (by
        simpa only [Nat.cast_succ] using hchar.natCast_ne_zero hi (Nat.le_of_not_gt hlarge))

end
end CCDN

namespace CCDN
noncomputable section
open Polynomial Differential
open scoped Differential

private theorem polynomial_eq_zero_of_differential_constant_coefficients
    {L : Type*} [Field L] [Differential L]
    (t : L) (ht : t′ = 1) (f : L[X]) (hchar : CharZeroOrGT L f.natDegree)
    (hcoeff : Differential.mapCoeffs f = 0) (hroot : f.eval t = 0) :
    f = 0 := by
  induction hn : f.natDegree using Nat.strong_induction_on generalizing f with
  | h n ih =>
    by_cases hn0 : n = 0
    · have he := eq_C_of_natDegree_eq_zero (hn.trans hn0)
      rw [he, eval_C] at hroot
      rw [he, hroot, C_0]
    · have hderroot : f.derivative.eval t = 0 := by
        have h := Differential.deriv_aeval_eq t f
        simp only [aeval_def, Algebra.algebraMap_self, eval₂_id] at h
        rw [hroot, map_zero, hcoeff, eval_zero, ht, mul_one, zero_add] at h
        exact h.symm
      have hdercoeff : Differential.mapCoeffs f.derivative = 0 := by
        rw [← derivative_differential_mapCoeffs, hcoeff, derivative_zero]
      have hlt : f.derivative.natDegree < n := by
        rw [← hn]
        exact natDegree_derivative_lt (by omega)
      have hdz := ih f.derivative.natDegree hlt f.derivative
        (hchar.mono (by omega)) hdercoeff hderroot rfl
      have he := polynomial_eq_C_of_derivative_eq_zero_of_degree_lt_char f hchar hdz
      rw [he, eval_C] at hroot
      rw [he, hroot, C_0]

private lemma differential_aeval_eq_zero_of_constants
    {F L : Type*} [Field F] [Field L] [Algebra F L] [Differential L]
    (hbase : ∀ a : F, (algebraMap F L a)′ = 0)
    (x : L) (hx : x′ = 0) (f : F[X]) :
    (aeval x f)′ = 0 := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp only [map_add, hf, hg, add_zero]
  | monomial n a =>
    rw [aeval_monomial]
    simp [Derivation.leibniz, hbase, hx]

/-- A differential constant satisfying a nonzero bivariate relation of
t-degree below the characteristic (or in characteristic zero) lies in the algebraically closed base.
The inner variable represents the constant; the outer variable represents t. -/
theorem differential_constant_mem_base_of_relation
    {F L : Type*} [Field F] [IsAlgClosed F] [Field L] [Algebra F L]
    [Differential L]
    (hbase : ∀ a : F, (algebraMap F L a)′ = 0)
    (t x : L) (ht : t′ = 1) (hx : x′ = 0)
    (R : F[X][X]) (hR : R ≠ 0) (hchar : CharZeroOrGT L R.natDegree)
    (hroot : (R.map (aeval x).toRingHom).eval t = 0) :
    x ∈ (algebraMap F L).range := by
  have hmap : Differential.mapCoeffs (R.map (aeval x).toRingHom) = 0 := by
    ext i
    simp only [Differential.coeff_mapCoeffs, coeff_map, coeff_zero]
    exact differential_aeval_eq_zero_of_constants hbase x hx _
  have hz := polynomial_eq_zero_of_differential_constant_coefficients t ht
    (R.map (aeval x).toRingHom) (hchar.mono natDegree_map_le) hmap hroot
  let i := R.natDegree
  have hi : R.coeff i ≠ 0 := by simpa only [i, coeff_natDegree] using leadingCoeff_ne_zero.mpr hR
  have hiRoot : ((R.coeff i).map (algebraMap F L)).IsRoot x := by
    have h := congrArg (fun f : L[X] => f.coeff i) hz
    simpa only [coeff_map, coeff_zero, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      IsRoot, eval_map, aeval_def] using h
  exact (IsAlgClosed.splits (R.coeff i)).mem_range_of_isRoot hi hiRoot

end
end CCDN

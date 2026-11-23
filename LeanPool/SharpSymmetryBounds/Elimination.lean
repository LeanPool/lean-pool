/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SharpSymmetryBounds.RealLocus
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Elimination and divisibility

Clearing denominators in a Bézout identity over `ℂ(Y)[X]`; an irreducible equation dividing any
polynomial that vanishes on an infinite part of its real locus.
-/

@[expose] public section

namespace CurveSymmetry

open MvPolynomial

/-- Complex polynomials in one variable. -/
abbrev UPoly := Polynomial ℂ
/-- Polynomials over `UPoly`: plane polynomials with one variable singled out. -/
abbrev NPoly := Polynomial UPoly
/-- The fraction field `ℂ(Y)` of `UPoly`. -/
abbrev CoeffField := FractionRing UPoly

/-- Plane polynomials as polynomials in `X` with coefficients in `ℂ[Y]`. -/
noncomputable def toNested : BPoly ≃ₐ[ℂ] NPoly :=
  (finSuccEquiv ℂ 1).trans (Polynomial.mapAlgEquiv (uniqueAlgEquiv ℂ (Fin 1)))

/-- Evaluation of a nested polynomial at `X = x`, `Y = y`. -/
noncomputable def nestedEval (x y : ℂ) : NPoly →+* ℂ :=
  Polynomial.eval₂RingHom (Polynomial.evalRingHom y) x

lemma toNested_C (c : ℂ) : toNested (C c) = Polynomial.C (Polynomial.C c) := by
  simp [toNested, finSuccEquiv_apply, uniqueAlgEquiv]

lemma toNested_X_zero : toNested (X 0) = Polynomial.X := by
  simp [toNested, finSuccEquiv_X_zero]

lemma toNested_X_one : toNested (X 1) = Polynomial.C Polynomial.X := by
  change Polynomial.map (uniqueAlgEquiv ℂ (Fin 1)).toRingHom
    (finSuccEquiv ℂ 1 (X (Fin.succ (0 : Fin 1)))) = _
  rw [finSuccEquiv_X_succ]
  simp [uniqueAlgEquiv]

lemma nestedEval_toNested (P : BPoly) (x y : ℂ) :
    nestedEval x y (toNested P) = eval (fun i : Fin 2 => if i = 0 then x else y) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [toNested_C, nestedEval]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP]
      fin_cases i <;> simp [toNested_X_zero, toNested_X_one, nestedEval]

/-- Clearing the two denominators in a Bézout identity over `ℂ(Y)[X]`. -/
lemma elimination_identity {P Q : NPoly} (hP : Irreducible P)
    (hdegree : P.natDegree ≠ 0) (hnot : ¬ P ∣ Q) :
    ∃ A B : NPoly, ∃ r : UPoly, r ≠ 0 ∧ A * P + B * Q = Polynomial.C r := by
  classical
  have : IsPrincipalIdealRing (Polynomial CoeffField) :=
    EuclideanDomain.instIsPrincipalIdealRing (R := Polynomial CoeffField)
  let f : UPoly →+* CoeffField := algebraMap UPoly CoeffField
  have hprim := hP.isPrimitive hdegree
  have hirr : Irreducible (P.map f) :=
    (hprim.irreducible_iff_irreducible_map_fraction_map (K := CoeffField)).mp hP
  have hcoprime : IsCoprime (P.map f) (Q.map f) := by
    rcases hirr.isCoprime_or_dvd (Q.map f) with h | h
    · exact h
    · exact (hnot (hprim.dvd_of_fraction_map_dvd_fraction_map h)).elim
  obtain ⟨A, B, hAB⟩ := hcoprime
  obtain ⟨b, hb, hA⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors UPoly) A
  obtain ⟨d, hd, hB⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors UPoly) B
  let A₀ := IsLocalization.integerNormalization (nonZeroDivisors UPoly) A
  let B₀ := IsLocalization.integerNormalization (nonZeroDivisors UPoly) B
  refine ⟨Polynomial.C d * A₀, Polynomial.C b * B₀, b * d,
    mul_ne_zero (nonZeroDivisors.ne_zero hb) (nonZeroDivisors.ne_zero hd), ?_⟩
  apply Polynomial.map_injective f (IsFractionRing.injective UPoly CoeffField)
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
  rw [hA, hB]
  simp only [Algebra.smul_def, Polynomial.algebraMap_apply, map_mul]
  linear_combination Polynomial.C (f b) * Polynomial.C (f d) * hAB

lemma infinite_conjugate_image {S : Set ℂ} (hS : S.Infinite) :
    (star '' S).Infinite := hS.image star_injective.injOn

/-- A nonzero equation with an infinite real locus cannot depend only on `Y`. -/
lemma nested_degree_ne_zero {P : BPoly} (hP : P ≠ 0)
    (hinf : (realLocus P).Infinite) : (toNested P).natDegree ≠ 0 := by
  intro hdegree
  have hC := Polynomial.eq_C_of_natDegree_eq_zero hdegree
  let r : UPoly := (toNested P).coeff 0
  have hr : r ≠ 0 := by
    intro hr
    have hz : toNested P = 0 := by simpa [r, hr] using hC
    exact hP (toNested.injective (by simpa using hz))
  apply infinite_conjugate_image hinf
  apply (Polynomial.finite_setOfPred_isRoot hr).subset
  rintro _ ⟨z, hz, rfl⟩
  have he := nestedEval_toNested P z (star z)
  rw [hC] at he
  simpa [nestedEval, Polynomial.IsRoot, r, realLocus] using he.trans hz

/-- Infinite real-locus containment implies divisibility of an irreducible equation.

This is the density step needed in the geometric paper. The proof uses a
one-variable elimination identity and injectivity of conjugation, not an
assumed Bézout or Zariski-density assertion.
-/
theorem dvd_of_realLocus_subset {P Q : BPoly} (hP : Irreducible P)
    (hinf : (realLocus P).Infinite) (hsub : realLocus P ⊆ realLocus Q) : P ∣ Q := by
  by_contra hnot
  have hirr : Irreducible (toNested P) := hP.map toNested.toMulEquiv
  have hndvd : ¬ toNested P ∣ toNested Q := by
    intro h
    exact hnot ((map_dvd_iff toNested).mp h)
  obtain ⟨A, B, r, hr, hidentity⟩ := elimination_identity hirr
    (nested_degree_ne_zero hP.ne_zero hinf) hndvd
  apply infinite_conjugate_image hinf
  apply (Polynomial.finite_setOfPred_isRoot hr).subset
  rintro _ ⟨z, hz, rfl⟩
  have hp : nestedEval z (star z) (toNested P) = 0 :=
    (nestedEval_toNested P z (star z)).trans hz
  have hq : nestedEval z (star z) (toNested Q) = 0 :=
    (nestedEval_toNested Q z (star z)).trans (hsub hz)
  have he := congrArg (nestedEval z (star z)) hidentity
  simp only [map_add, map_mul, hp, hq, mul_zero, add_zero] at he
  simpa [nestedEval, Polynomial.IsRoot] using he.symm

/-- A same-degree equation vanishing on the real curve differs by a nonzero scalar. -/
theorem proportional_of_realLocus_subset {P Q : BPoly} (hP : Irreducible P)
    (hQ : Q ≠ 0) (hinf : (realLocus P).Infinite)
    (hsub : realLocus P ⊆ realLocus Q) (hdeg : Q.totalDegree ≤ P.totalDegree) :
    ∃ c : ℂ, c ≠ 0 ∧ Q = C c * P := by
  obtain ⟨S, hS⟩ := dvd_of_realLocus_subset hP hinf hsub
  have hs0 : S ≠ 0 := by intro hs; apply hQ; simp [hS, hs]
  have hdegree := totalDegree_mul_of_isDomain hP.ne_zero hs0
  have hdS : S.totalDegree = 0 := by rw [← hS] at hdegree; omega
  have hcS : S = C (S.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp hdS
  refine ⟨S.coeff 0, ?_, ?_⟩
  · intro hc
    exact hs0 (by simpa [hc] using hcS)
  · rw [hS, hcS, mul_comm]
    simp

end CurveSymmetry

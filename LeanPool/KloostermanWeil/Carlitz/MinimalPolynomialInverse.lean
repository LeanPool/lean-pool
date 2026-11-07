/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import LeanPool.KloostermanWeil.Carlitz.ExtensionDefinitions
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# Minimal polynomials and inverse sums

Minimal-polynomial identities used to express inverse terms in extension-field
Kloosterman sums (Carlitz 1969).
-/

@[expose] public section

namespace KloostermanWeil.Carlitz

open Polynomial

lemma minpoly_coeff_zero_ne_zero_of_ne_zero
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {x : L} (hx : x ≠ 0) :
    (minpoly K x).coeff 0 ≠ 0 := by
  intro h0
  have hXd : (X : Polynomial K) ∣ minpoly K x :=
    Polynomial.X_dvd_iff.mpr h0
  have hminIrred : Irreducible (minpoly K x) :=
    minpoly.irreducible (IsIntegral.of_finite K x)
  have hrev : minpoly K x ∣ (X : Polynomial K) :=
    (irreducible_X : Irreducible (X : Polynomial K)).dvd_symm hminIrred hXd
  obtain ⟨g, hg⟩ := hrev
  have heval := congrArg (fun f : Polynomial K => Polynomial.aeval x f) hg
  simp only [map_mul, aeval_X, minpoly.aeval, zero_mul] at heval
  exact hx heval

lemma adjoin_inv_eq_adjoin
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {x : L} :
    IntermediateField.adjoin K ({x⁻¹} : Set L) =
      IntermediateField.adjoin K ({x} : Set L) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    exact (IntermediateField.adjoin K ({x} : Set L)).inv_mem
      (IntermediateField.mem_adjoin_simple_self K x)
  · rw [IntermediateField.adjoin_le_iff]
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    have hxin :
        x⁻¹ ∈ IntermediateField.adjoin K ({x⁻¹} : Set L) :=
      IntermediateField.mem_adjoin_simple_self K x⁻¹
    have hinv :=
      (IntermediateField.adjoin K ({x⁻¹} : Set L)).inv_mem hxin
    simpa only [inv_inv, SetLike.mem_coe] using hinv

lemma minpoly_inv_natDegree_eq
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {x : L} :
    (minpoly K x⁻¹).natDegree = (minpoly K x).natDegree := by
  have hxint : IsIntegral K x := IsIntegral.of_finite K x
  have hxinvint : IsIntegral K x⁻¹ := IsIntegral.of_finite K x⁻¹
  calc
    (minpoly K x⁻¹).natDegree =
        Module.finrank K
          (IntermediateField.adjoin K ({x⁻¹} : Set L)) := by
      symm
      exact IntermediateField.adjoin.finrank hxinvint
    _ =
        Module.finrank K
          (IntermediateField.adjoin K ({x} : Set L)) := by
      rw [adjoin_inv_eq_adjoin]
    _ = (minpoly K x).natDegree :=
      IntermediateField.adjoin.finrank hxint

noncomputable def invMinpolyCandidate
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (x : L) : Polynomial K :=
  C ((minpoly K x).coeff 0)⁻¹ * (minpoly K x).reverse

lemma invMinpolyCandidate_monic
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {x : L} (hx : x ≠ 0) :
    (invMinpolyCandidate K L x).Monic := by
  let P := minpoly K x
  have hc : P.coeff 0 ≠ 0 := by
    exact minpoly_coeff_zero_ne_zero_of_ne_zero hx
  have htrail : P.trailingCoeff = P.coeff 0 :=
    Polynomial.trailingCoeff_eq_coeff_zero hc
  unfold invMinpolyCandidate
  rw [Polynomial.Monic, Polynomial.leadingCoeff_mul,
    Polynomial.leadingCoeff_C, Polynomial.reverse_leadingCoeff, htrail]
  exact inv_mul_cancel₀ hc

lemma invMinpolyCandidate_aeval_inv
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {x : L} (hx : x ≠ 0) :
    Polynomial.aeval x⁻¹ (invMinpolyCandidate K L x) = 0 := by
  let : Invertible x := invertibleOfNonzero hx
  unfold invMinpolyCandidate
  rw [Polynomial.aeval_mul, Polynomial.aeval_C]
  apply mul_eq_zero_of_right
  change Polynomial.eval₂ (algebraMap K L) x⁻¹ (minpoly K x).reverse = 0
  have h :=
    (Polynomial.eval₂_reverse_eq_zero_iff
      (algebraMap K L) x (minpoly K x)).2
      (by simpa [Polynomial.aeval_def] using minpoly.aeval K x)
  simpa using h

lemma invMinpolyCandidate_natDegree
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {x : L} (hx : x ≠ 0) :
    (invMinpolyCandidate K L x).natDegree =
      (minpoly K x).natDegree := by
  let P := minpoly K x
  have hc : P.coeff 0 ≠ 0 :=
    minpoly_coeff_zero_ne_zero_of_ne_zero hx
  have hrevdeg : P.reverse.natDegree = P.natDegree := by
    rw [Polynomial.reverse_natDegree,
      (Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hc))]
    omega
  unfold invMinpolyCandidate
  rw [Polynomial.natDegree_C_mul (inv_ne_zero hc)]
  exact hrevdeg

theorem minpoly_inv_eq_normalized_reverse
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {x : L} (hx : x ≠ 0) :
    minpoly K x⁻¹ =
      invMinpolyCandidate K L x := by
  symm
  apply minpoly.unique_of_degree_le_degree_minpoly
  · exact invMinpolyCandidate_monic hx
  · exact invMinpolyCandidate_aeval_inv hx
  · rw [Polynomial.degree_eq_natDegree
          (invMinpolyCandidate_monic hx).ne_zero,
      invMinpolyCandidate_natDegree hx,
      Polynomial.degree_eq_natDegree
        (minpoly.monic (IsIntegral.of_finite K x⁻¹)).ne_zero,
      minpoly_inv_natDegree_eq]



lemma reverse_nextCoeff_eq_coeff_one
    {K : Type*} [Field K] {P : Polynomial K}
    (hdeg : 0 < P.natDegree) (hc : P.coeff 0 ≠ 0) :
    P.reverse.nextCoeff = P.coeff 1 := by
  have hrevdeg : P.reverse.natDegree = P.natDegree := by
    rw [Polynomial.reverse_natDegree,
      (Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hc))]
    omega
  rw [Polynomial.nextCoeff_of_natDegree_pos
    (by simpa [hrevdeg] using hdeg)]
  rw [hrevdeg, Polynomial.coeff_reverse]
  rw [Polynomial.revAt_le (Nat.sub_le _ _)]
  have hcalc : P.natDegree - (P.natDegree - 1) = 1 := by omega
  rw [hcalc]

theorem minpoly_inv_nextCoeff_eq_coeff_one_div_coeff_zero
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {x : L} (hx : x ≠ 0) :
    (minpoly K x⁻¹).nextCoeff =
      (minpoly K x).coeff 1 / (minpoly K x).coeff 0 := by
  let P := minpoly K x
  have hc : P.coeff 0 ≠ 0 :=
    minpoly_coeff_zero_ne_zero_of_ne_zero hx
  have hdeg : 0 < P.natDegree :=
    minpoly.natDegree_pos (IsIntegral.of_finite K x)
  rw [minpoly_inv_eq_normalized_reverse hx]
  unfold invMinpolyCandidate
  rw [Polynomial.nextCoeff_C_mul,
    reverse_nextCoeff_eq_coeff_one hdeg hc]
  simp [P, div_eq_mul_inv, mul_comm]


end KloostermanWeil.Carlitz

/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.LowerBound.GridEisenstein
public import LeanPool.CCDN.Noether.BivariateTotalDegree
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-! Exact total degree and coefficient extension for the explicit grid equation. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

private lemma bivariateTotalDegree_add_le {R : Type*} [CommRing R] (f g : R[X][X]) :
    bivariateTotalDegree (f + g) ≤ max (bivariateTotalDegree f) (bivariateTotalDegree g) := by
  unfold bivariateTotalDegree
  rw [map_add]
  exact MvPolynomial.totalDegree_add _ _

private lemma bivariateTotalDegree_C_le {R : Type*} [CommRing R] (f : R[X]) :
    bivariateTotalDegree (C f) ≤ f.natDegree := by
  rw [bivariateTotalDegree_le_iff]
  intro i j hij
  by_cases hi : i = 0
  · subst i
    simpa using le_natDegree_of_ne_zero (by simpa using hij : f.coeff j ≠ 0)
  · simp [coeff_C, hi] at hij

private lemma bivariateTotalDegree_map_C_le {R : Type*} [CommRing R] (f : R[X]) :
    bivariateTotalDegree (f.map C) ≤ f.natDegree := by
  rw [bivariateTotalDegree_le_iff]
  intro i j hij
  by_cases hj : j = 0
  · subst j
    simpa using le_natDegree_of_ne_zero (by simpa using hij : f.coeff i ≠ 0)
  · simp [coeff_map, coeff_C, hj] at hij

private lemma gridEisensteinCorrection_monic_degree {K : Type*} [Field K]
    (V : K[X]) (k : ℕ) (hm : V.Monic) (hk : 2 ≤ k) :
    IsMonicOfDegree (gridEisensteinCorrection V k) (V.natDegree + k) := by
  apply IsMonicOfDegree.mul (show IsMonicOfDegree V V.natDegree from ⟨rfl, hm⟩)
  apply (isMonicOfDegree_X_pow K k).add_right
  have h : (C (V.coeff 1 / V.coeff 0 + 1) * X).natDegree ≤ 1 := by
    simpa using (natDegree_mul_le (p := (C (V.coeff 1 / V.coeff 0 + 1) : K[X])) (q := X))
  omega

private lemma gridEisensteinPolynomial_constantCoeff {K : Type*} [Field K]
    (V : K[X]) (k : ℕ) (h0 : V.coeff 0 ≠ 0) (hd : 0 < V.natDegree) :
    (gridEisensteinPolynomial V k).coeff 0 =
      C (V.coeff 0) - V + gridEisensteinCorrection V k := by
  rw [gridEisensteinPolynomial_coeff]
  simp only [coeff_X_pow, ne_of_lt hd, ite_false, zero_sub, ite_true]
  rw [mul_neg, mul_assoc, ← C_mul, inv_mul_cancel₀ h0, C_1, mul_one]
  rfl

private lemma gridEisensteinPolynomial_highCoeff {K : Type*} [Field K]
    (V : K[X]) (k : ℕ) (hm : V.Monic) (h0 : V.coeff 0 ≠ 0)
    (hd : 0 < V.natDegree) (hk : 2 ≤ k) :
    ((gridEisensteinPolynomial V k).coeff 0).coeff (V.natDegree + k) = 1 := by
  rw [gridEisensteinPolynomial_constantCoeff V k h0 hd, coeff_add, coeff_sub]
  rw [coeff_C, ite_eq_right (by omega : V.natDegree + k ≠ 0)]
  rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_sub, neg_zero, zero_add]
  have h := gridEisensteinCorrection_monic_degree V k hm hk
  rw [← h.natDegree_eq]
  exact h.monic.coeff_natDegree

private lemma gridEisensteinPolynomial_totalDegree_le {K : Type*} [Field K]
    (V : K[X]) (k : ℕ) (hm : V.Monic) (hd : 0 < V.natDegree)
    (hk : 2 ≤ k) (hs : V.natDegree ≤ k + 1) :
    bivariateTotalDegree (gridEisensteinPolynomial V k) ≤ V.natDegree + k := by
  unfold gridEisensteinPolynomial
  apply (bivariateTotalDegree_add_le _ _).trans
  apply max_le
  · apply (bivariateTotalDegree_add_le _ _).trans
    apply max_le
    · exact (bivariateTotalDegree_map_C_le V).trans (by omega)
    · have hsub : (X ^ V.natDegree - V).natDegree < V.natDegree :=
        IsMonicOfDegree.natDegree_sub_lt (ne_of_gt hd)
          (isMonicOfDegree_X_pow K _) ⟨rfl, hm⟩
      have he : (X ^ V.natDegree : K[X][X]) - V.map C =
          (X ^ V.natDegree - V).map C := by simp
      rw [he]
      apply (bivariateTotalDegree_mul_le _ _).trans
      have h₁ := bivariateTotalDegree_C_le (V * C (V.coeff 0)⁻¹)
      have h₂ := bivariateTotalDegree_map_C_le (X ^ V.natDegree - V)
      have h₃ : (V * C (V.coeff 0)⁻¹).natDegree ≤ V.natDegree := natDegree_mul_C_le _ _
      omega
  · exact (bivariateTotalDegree_C_le _).trans
      (gridEisensteinCorrection_monic_degree V k hm hk).natDegree_eq.le

/-- If s≤k+1, the explicit equation has exact total degree s+k. -/
theorem gridEisensteinPolynomial_totalDegree {K : Type*} [Field K]
    (V : K[X]) (k : ℕ) (hm : V.Monic) (hd : 0 < V.natDegree)
    (h0 : V.coeff 0 ≠ 0) (hk : 2 ≤ k) (hs : V.natDegree ≤ k + 1) :
    bivariateTotalDegree (gridEisensteinPolynomial V k) = V.natDegree + k := by
  apply le_antisymm (gridEisensteinPolynomial_totalDegree_le V k hm hd hk hs)
  have hh := bivariateTotalDegree_coeff_le (gridEisensteinPolynomial V k) 0
    (V.natDegree + k)
    (by rw [gridEisensteinPolynomial_highCoeff V k hm h0 hd hk]; exact one_ne_zero)
  simpa using hh

private lemma gridEisensteinCorrection_map {K L : Type*} [Field K] [Field L]
    (φ : K →+* L) (V : K[X]) (k : ℕ) :
    (gridEisensteinCorrection V k).map φ = gridEisensteinCorrection (V.map φ) k := by
  simp [gridEisensteinCorrection]

private lemma gridEisensteinPolynomial_map {K L : Type*} [Field K] [Field L]
    (φ : K →+* L) (V : K[X]) (k : ℕ) :
    bivariateMap φ (gridEisensteinPolynomial V k) = gridEisensteinPolynomial (V.map φ) k := by
  have he : (Polynomial.mapRingHom φ).comp C = C.comp φ := by ext a; simp
  change (gridEisensteinPolynomial V k).map (Polynomial.mapRingHom φ) = _
  simp only [gridEisensteinPolynomial, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, coe_mapRingHom, map_map, he, gridEisensteinCorrection_map,
    coeff_map, natDegree_map_eq_of_injective φ.injective, map_inv₀]

/-- Absolute irreducibility is stable under every field extension here because
Eisenstein applies to the same explicit equation after coefficient extension. -/
theorem gridEisensteinPolynomial_map_irreducible {K L : Type*} [Field K] [Field L]
    (φ : K →+* L) (V : K[X]) (k : ℕ) (hm : V.Monic)
    (hd : 0 < V.natDegree) (h0 : V.coeff 0 ≠ 0) (hk : 2 ≤ k) :
    Irreducible (bivariateMap φ (gridEisensteinPolynomial V k)) := by
  rw [gridEisensteinPolynomial_map]
  apply gridEisensteinPolynomial_irreducible _ k (hm.map φ)
  · rwa [natDegree_map_eq_of_injective φ.injective]
  · simpa only [coeff_map, map_ne_zero_iff φ φ.injective] using h0
  · exact hk

end
end CCDN

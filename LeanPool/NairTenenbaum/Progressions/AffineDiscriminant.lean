/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Progressions.AffinePolynomialSystem
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Discriminants under affine substitution

The resultant formula follows from the permutation of roots under the affine
map. Applying it to a polynomial and its derivative gives equation (38),
including degrees zero and one.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial

/-- Simultaneous affine substitution in a resultant over a splitting field. -/
theorem resultant_comp_linear_of_splits {K : Type*} [Field K]
    (f g : K[X]) (n : ℕ) (hg : g.natDegree ≤ n) (hf : f.Splits)
    (a b : K) (ha : a ≠ 0) :
    (f.comp (C a * X + C b)).resultant (g.comp (C a * X + C b)) f.natDegree n =
      a ^ (f.natDegree * n) * f.resultant g f.natDegree n := by
  let L : K[X] := C a * X + C b
  have hL : L.natDegree = 1 := Polynomial.natDegree_linear ha
  have hfdeg : (f.comp L).natDegree = f.natDegree := by rw [Polynomial.natDegree_comp, hL, mul_one]
  have hgdeg : (g.comp L).natDegree ≤ n := by
    simpa only [Polynomial.natDegree_comp, hL, mul_one] using hg
  have hsplit : (f.comp L).Splits := hf.comp_of_natDegree_le_one hL.le
  have hroots : ((f.comp L).roots.map (g.comp L).eval).prod = (f.roots.map g.eval).prod := by
    have H := congrArg (fun s : Multiset K => (s.map g.eval).prod)
      (Polynomial.map_roots_comp_C_mul_X_add_C f a b (isUnit_iff_ne_zero.mpr ha))
    simpa only [Multiset.map_map, Function.comp_def, Polynomial.eval_comp, L,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] using H
  change (f.comp L).resultant (g.comp L) f.natDegree n = _
  rw [← hfdeg, Polynomial.resultant_eq_prod_eval _ _ n hgdeg hsplit, hfdeg,
    Polynomial.resultant_eq_prod_eval f g n hg hf, hroots,
    Polynomial.leadingCoeff_comp (by omega : L.natDegree ≠ 0)]
  have hlc : L.leadingCoeff = a := Polynomial.leadingCoeff_linear ha
  rw [hlc, mul_pow, ← pow_mul]
  ring

/-- The integral resultant identity, transported through the complex numbers.
The bound on the second degree permits applying this with the derivative. -/
theorem resultant_comp_affine (f g : ℤ[X]) (n : ℕ) (hg : g.natDegree ≤ n)
    (q : ℕ) (a : ℤ) (hq : q ≠ 0) :
    (f.comp (affinePolynomial q a)).resultant (g.comp (affinePolynomial q a)) f.natDegree n =
      (q : ℤ) ^ (f.natDegree * n) * f.resultant g f.natDegree n := by
  let φ := Int.castRingHom ℂ
  have hφ : Function.Injective φ := Int.cast_injective
  apply hφ
  have H := resultant_comp_linear_of_splits (f.map φ) (g.map φ) n
    (by simpa only [Polynomial.natDegree_map_eq_of_injective hφ] using hg)
    (IsAlgClosed.splits _) (q : ℂ) (a : ℂ) (by exact_mod_cast hq)
  have hmap (Q : ℤ[X]) : (Q.comp (affinePolynomial q a)).map φ =
      (Q.map φ).comp (C (q : ℂ) * X + C (a : ℂ)) := by
    simp only [Polynomial.map_comp, affinePolynomial, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
    congr 2
  rw [← hmap f, ← hmap g] at H
  simpa only [Polynomial.natDegree_map_eq_of_injective hφ, Polynomial.resultant_map_map,
    map_mul, map_pow, map_natCast, φ] using H

/-- Equation (38), for every integral polynomial and every nonzero natural
slope. No monicity or separability hypothesis is required. -/
theorem discr_comp_affine (f : ℤ[X]) (q : ℕ) (a : ℤ) (hq : q ≠ 0) :
    (f.comp (affinePolynomial q a)).discr =
      (q : ℤ) ^ (f.natDegree * (f.natDegree - 1)) * f.discr := by
  by_cases hd : f.natDegree = 0
  · rw [Polynomial.eq_C_of_natDegree_eq_zero hd]
    simp
  have hf : f ≠ 0 := by intro h; simp [h] at hd
  let F := f.comp (affinePolynomial q a)
  have hdeg : F.natDegree = f.natDegree := by
    dsimp [F]
    rw [Polynomial.natDegree_comp, natDegree_affinePolynomial hq, mul_one]
  have hq₀ : (q : ℤ) ≠ 0 := by exact_mod_cast hq
  have hlc : F.leadingCoeff = f.leadingCoeff * (q : ℤ) ^ f.natDegree := by
    dsimp [F]
    rw [Polynomial.leadingCoeff_comp (by rw [natDegree_affinePolynomial hq]; decide)]
    rw [affinePolynomial, Polynomial.leadingCoeff_linear hq₀]
  have hderiv : F.derivative = C (q : ℤ) * f.derivative.comp (affinePolynomial q a) := by
    simp [F, affinePolynomial, Polynomial.derivative_comp]
  have H := Polynomial.resultant_deriv
    (Polynomial.natDegree_pos_iff_degree_pos.mp (show 0 < F.natDegree by omega))
  rw [hdeg, hderiv, Polynomial.resultant_C_mul_right,
    resultant_comp_affine f f.derivative (f.natDegree - 1) (Polynomial.natDegree_derivative_le f)
        q a hq,
    Polynomial.resultant_deriv (Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero
        hd)), hlc] at H
  have hn : (-1 : ℤ) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.leadingCoeff *
      (q : ℤ) ^ f.natDegree ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (Polynomial.leadingCoeff_ne_zero.mpr hf))
      (pow_ne_zero _ hq₀)
  apply mul_left_cancel₀ hn
  change (-1 : ℤ) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.leadingCoeff *
      (q : ℤ) ^ f.natDegree * F.discr = _
  calc
    _ = _ := by simpa only [mul_assoc] using H.symm
    _ = _ := by ring

end NairTenenbaum

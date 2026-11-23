/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SharpSymmetryBounds.IsometryInterface

/-!
# Cartesian coordinates

The mutually inverse linear substitutions between the complex coordinates `z`, `conj z` and the
Cartesian coordinates `(x, y)`, and their effect on the total degree.
-/

@[expose] public section

namespace CurveSymmetry

open MvPolynomial

/-- The substitution `x = (X + Y)/2`, `y = -i (X - Y)/2` from Cartesian to complex coordinates. -/
noncomputable def complexify : BPoly →+* BPoly :=
  eval₂Hom C (fun i : Fin 2 => if i = 0 then C (1 / 2 : ℂ) * (X 0 + X 1)
    else -C Complex.I * C (1 / 2 : ℂ) * (X 0 - X 1))

/-- The substitution `X = x + i y`, `Y = x - i y` from complex to Cartesian coordinates. -/
noncomputable def cartesianize : BPoly →+* BPoly :=
  eval₂Hom C (fun i : Fin 2 => if i = 0 then X 0 + C Complex.I * X 1
    else X 0 - C Complex.I * X 1)

@[simp] lemma complexify_C (c : ℂ) : complexify (C c) = C c := by simp [complexify]
@[simp] lemma cartesianize_C (c : ℂ) : cartesianize (C c) = C c := by simp [cartesianize]
@[simp] lemma complexify_X_zero : complexify (X 0) = C (1 / 2 : ℂ) * (X 0 + X 1) := by
  simp [complexify]
@[simp] lemma complexify_X_one :
    complexify (X 1) = -C Complex.I * C (1 / 2 : ℂ) * (X 0 - X 1) := by
  simp [complexify]
@[simp] lemma cartesianize_X_zero : cartesianize (X 0) = X 0 + C Complex.I * X 1 := by
  simp [cartesianize]
@[simp] lemma cartesianize_X_one : cartesianize (X 1) = X 0 - C Complex.I * X 1 := by
  simp [cartesianize]

lemma cartesianize_complexify (P : BPoly) : cartesianize (complexify P) = P := by
  have hI : (C Complex.I : BPoly) ^ 2 = -1 := by rw [← map_pow, Complex.I_sq]; simp
  have hhalf : (2 : BPoly) * C (1 / 2 : ℂ) = 1 := by
    have h := congrArg (C : ℂ →+* BPoly) (show (2 : ℂ) * (1 / 2) = 1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using h
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP]
      fin_cases i
      · change P * cartesianize (complexify (X 0)) = P * X 0
        rw [complexify_X_zero, map_mul, cartesianize_C, map_add, cartesianize_X_zero,
          cartesianize_X_one]
        linear_combination P * (X 0 : BPoly) * hhalf
      · change P * cartesianize (complexify (X 1)) = P * X 1
        rw [complexify_X_one, map_mul, map_mul, map_neg, cartesianize_C, cartesianize_C,
          map_sub, cartesianize_X_zero, cartesianize_X_one]
        linear_combination P * (X 1 : BPoly) * hhalf -
          2 * P * (X 1 : BPoly) * C (1 / 2 : ℂ) * hI

lemma complexify_cartesianize (P : BPoly) : complexify (cartesianize P) = P := by
  have hI : (C Complex.I : BPoly) ^ 2 = -1 := by rw [← map_pow, Complex.I_sq]; simp
  have hhalf : (2 : BPoly) * C (1 / 2 : ℂ) = 1 := by
    have h := congrArg (C : ℂ →+* BPoly) (show (2 : ℂ) * (1 / 2) = 1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using h
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP]
      fin_cases i
      · change P * complexify (cartesianize (X 0)) = P * X 0
        rw [cartesianize_X_zero, map_add, map_mul, complexify_C, complexify_X_zero,
          complexify_X_one]
        linear_combination P * (X 0 : BPoly) * hhalf -
          P * C (1 / 2 : ℂ) * ((X 0 : BPoly) - X 1) * hI
      · change P * complexify (cartesianize (X 1)) = P * X 1
        rw [cartesianize_X_one, map_sub, map_mul, complexify_C, complexify_X_zero, complexify_X_one]
        linear_combination P * (X 1 : BPoly) * hhalf +
          P * C (1 / 2 : ℂ) * ((X 0 : BPoly) - X 1) * hI

/-- `complexify` as a ring isomorphism, with inverse `cartesianize`. -/
noncomputable def complexifyEquiv : BPoly ≃+* BPoly :=
  { complexify with
    invFun := cartesianize
    left_inv := cartesianize_complexify
    right_inv := complexify_cartesianize }

lemma linear_substitution_degree_le (v : Fin 2 → BPoly) (hv : ∀ i, (v i).totalDegree ≤ 1)
    (P : BPoly) : (eval₂Hom C v P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum, map_sum]
  apply totalDegree_sum_le
  intro s hs
  rw [eval₂Hom_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
  have h0 := (totalDegree_pow (v 0) (s 0)).trans (Nat.mul_le_mul_left (s 0) (hv 0))
  have h1 := (totalDegree_pow (v 1) (s 1)).trans (Nat.mul_le_mul_left (s 1) (hv 1))
  have hm := totalDegree_mul (v 0 ^ s 0) (v 1 ^ s 1)
  have hc := totalDegree_mul (C (P.coeff s) : BPoly) (v 0 ^ s 0 * v 1 ^ s 1)
  simp only [totalDegree_C, zero_add, Nat.mul_one] at h0 h1 hc
  have hd := support_degree hs
  omega

lemma complexify_degree_le (P : BPoly) : (complexify P).totalDegree ≤ P.totalDegree := by
  apply linear_substitution_degree_le
  intro i
  have hsum := totalDegree_add (X 0 : BPoly) (X 1)
  have hsub := totalDegree_sub (X 0 : BPoly) (X 1)
  have hc0 := totalDegree_mul (C (1 / 2 : ℂ) : BPoly) (X 0 + X 1)
  have hc1 := totalDegree_mul (-C Complex.I * C (1 / 2 : ℂ) : BPoly) (X 0 - X 1)
  have hc2 := totalDegree_mul (-C Complex.I : BPoly) (C (1 / 2 : ℂ))
  simp only [totalDegree_C, totalDegree_neg, totalDegree_X, zero_add, max_self]
    at hsum hsub hc0 hc1 hc2
  split_ifs <;> omega

lemma cartesianize_degree_le (P : BPoly) : (cartesianize P).totalDegree ≤ P.totalDegree := by
  apply linear_substitution_degree_le
  intro i
  have hc := totalDegree_mul (C Complex.I : BPoly) (X 1)
  have hsum := totalDegree_add (X 0 : BPoly) (C Complex.I * X 1)
  have hsub := totalDegree_sub (X 0 : BPoly) (C Complex.I * X 1)
  simp only [totalDegree_C, totalDegree_X, zero_add] at hc hsum hsub
  split_ifs <;> omega

lemma complexify_degree (P : BPoly) : (complexify P).totalDegree = P.totalDegree := by
  apply le_antisymm (complexify_degree_le P)
  have h := cartesianize_degree_le (complexify P)
  rwa [cartesianize_complexify] at h

lemma eval_complexify (P : BPoly) (z : ℂ) :
    eval (fun i : Fin 2 => if i = 0 then z else star z) (complexify P) =
      eval (fun i : Fin 2 => if i = 0 then (z.re : ℂ) else (z.im : ℂ)) P := by
  have hsum : z + star z = 2 * (z.re : ℂ) := by simpa using Complex.add_conj z
  have hsub : z - star z = 2 * (z.im : ℂ) * Complex.I := by simpa using Complex.sub_conj z
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP]
      congr 1
      fin_cases i
      · change eval (fun j : Fin 2 => if j = 0 then z else star z) (complexify (X 0)) =
          eval (fun j : Fin 2 => if j = 0 then (z.re : ℂ) else (z.im : ℂ)) (X 0)
        rw [complexify_X_zero]
        simp only [map_mul, map_add, eval_C, eval_X, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte,
          hsum]
        ring
      · change eval (fun j : Fin 2 => if j = 0 then z else star z) (complexify (X 1)) =
          eval (fun j : Fin 2 => if j = 0 then (z.re : ℂ) else (z.im : ℂ)) (X 1)
        rw [complexify_X_one]
        simp only [map_mul, map_sub, map_neg, eval_C, eval_X, show (1 : Fin 2) ≠ 0 by decide,
          ↓reduceIte, hsub]
        ring_nf
        rw [Complex.I_sq]
        ring

end CurveSymmetry

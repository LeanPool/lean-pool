/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/
module


public import Mathlib.Data.List.Basic
public import Mathlib.Tactic
public import LeanPool.FullyDynamicMatching.FD1D.DensePolynomial
meta import LeanPool.FullyDynamicMatching.FD1D.DensePolynomial

/-!
# Sparse exact polynomial certificate

This module implements a computable dense representation of trivariate
integer polynomials. Its proved evaluator is used to kernel-check every
coefficient in the four Bellman charts without materializing enormous
`ring_nf` goals.
-/

@[expose] public section

namespace FD1D

namespace BellmanCertificate

namespace DPoly

/-- Horner evaluation of a coefficient list after applying the coefficient map. -/
def evalCoeffs [Zero S] [Add S] [Mul S]
    (f : R → S) (x : S) : List R → S
  | [] => 0
  | a :: p => f a + x * evalCoeffs f x p

/-- Evaluation of a dense polynomial using the given coefficient map. -/
def eval [Zero S] [Add S] [Mul S]
    (f : R → S) (x : S) (p : DPoly R) : S :=
  evalCoeffs f x p.coeffs

@[simp] theorem evalCoeffs_nil [Zero S] [Add S] [Mul S]
    (f : R → S) (x : S) :
    evalCoeffs f x [] = 0 := rfl

@[simp] theorem evalCoeffs_cons [Zero S] [Add S] [Mul S]
    (f : R → S) (x : S) (a : R) (p : List R) :
    evalCoeffs f x (a :: p) = f a + x * evalCoeffs f x p := rfl

theorem evalCoeffs_add [Add R] [CommRing S]
    (f : R → S)
    (hfadd : ∀ a b, f (a + b) = f a + f b)
    (x : S) (p q : List R) :
    evalCoeffs f x (addCoeffs p q) =
      evalCoeffs f x p + evalCoeffs f x q := by
  induction p generalizing q with
  | nil =>
      simp [addCoeffs, evalCoeffs]
  | cons a p ih =>
      cases q with
      | nil =>
          simp [addCoeffs, evalCoeffs]
      | cons b q =>
          simp only [addCoeffs, evalCoeffs, hfadd, ih]
          ring

theorem evalCoeffs_neg [Neg R] [CommRing S]
    (f : R → S) (hfneg : ∀ a, f (-a) = -f a)
    (x : S) (p : List R) :
    evalCoeffs f x (p.map (-·)) = -evalCoeffs f x p := by
  induction p with
  | nil => simp [evalCoeffs]
  | cons a p ih =>
      simp only [List.map_cons, evalCoeffs, hfneg, ih]
      ring

theorem evalCoeffs_scale [Mul R] [CommRing S]
    (f : R → S)
    (hfmul : ∀ a b, f (a * b) = f a * f b)
    (x : S) (a : R) (p : List R) :
    evalCoeffs f x (p.map (a * ·)) =
      f a * evalCoeffs f x p := by
  induction p with
  | nil => simp [evalCoeffs]
  | cons b p ih =>
      simp only [List.map_cons, evalCoeffs, hfmul, ih]
      ring

theorem evalCoeffs_mul [Zero R] [Add R] [Mul R] [CommRing S]
    (f : R → S) (hf0 : f 0 = 0)
    (hfadd : ∀ a b, f (a + b) = f a + f b)
    (hfmul : ∀ a b, f (a * b) = f a * f b)
    (x : S) (p q : List R) :
    evalCoeffs f x (mulCoeffs p q) =
      evalCoeffs f x p * evalCoeffs f x q := by
  induction p with
  | nil => simp [mulCoeffs, evalCoeffs]
  | cons a p ih =>
      rw [mulCoeffs, evalCoeffs_add f hfadd]
      rw [evalCoeffs_scale f hfmul]
      simp only [evalCoeffs, hf0, zero_add, ih]
      ring

@[simp] theorem eval_zero [CommRing S]
    (f : R → S) (x : S) :
    eval f x (0 : DPoly R) = 0 := rfl

@[simp] theorem eval_const [CommRing S]
    (f : R → S) (x : S) (a : R) :
    eval f x (const a) = f a := by
  simp [eval, const, evalCoeffs]

theorem eval_add [Add R] [CommRing S]
    (f : R → S)
    (hfadd : ∀ a b, f (a + b) = f a + f b)
    (x : S) (p q : DPoly R) :
    eval f x (add p q) = eval f x p + eval f x q := by
  exact evalCoeffs_add f hfadd x p.coeffs q.coeffs

theorem eval_neg [Neg R] [CommRing S]
    (f : R → S) (hfneg : ∀ a, f (-a) = -f a)
    (x : S) (p : DPoly R) :
    eval f x (neg p) = -eval f x p := by
  exact evalCoeffs_neg f hfneg x p.coeffs

theorem eval_mul [Zero R] [Add R] [Mul R] [CommRing S]
    (f : R → S) (hf0 : f 0 = 0)
    (hfadd : ∀ a b, f (a + b) = f a + f b)
    (hfmul : ∀ a b, f (a * b) = f a * f b)
    (x : S) (p q : DPoly R) :
    eval f x (mul p q) = eval f x p * eval f x q := by
  exact evalCoeffs_mul f hf0 hfadd hfmul x p.coeffs q.coeffs

theorem eval_pow [Zero R] [One R] [Add R] [Mul R] [CommRing S]
    (f : R → S) (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (hfadd : ∀ a b, f (a + b) = f a + f b)
    (hfmul : ∀ a b, f (a * b) = f a * f b)
    (x : S) (p : DPoly R) (n : ℕ) :
    eval f x (pow p n) = eval f x p ^ n := by
  induction n with
  | zero =>
      rw [DPoly.pow, eval_const, hf1, pow_zero]
  | succ n ih =>
      rw [pow, eval_mul f hf0 hfadd hfmul, ih, pow_succ]

end DPoly

/-- Integer polynomials in three variables, represented by nested dense polynomials. -/
abbrev Poly3 := DPoly (DPoly (DPoly ℤ))

/-- The outermost variable of a three-variable polynomial. -/
def U : Poly3 := DPoly.X
/-- The middle variable of a three-variable polynomial. -/
def V : Poly3 := DPoly.const DPoly.X
/-- The innermost variable of a three-variable polynomial. -/
def Z : Poly3 := DPoly.const (DPoly.const DPoly.X)

/-- Real evaluation of an integer polynomial at its single argument. -/
def eval1 (p : DPoly ℤ) (z : ℝ) : ℝ :=
  DPoly.eval (fun c : ℤ => (c : ℝ)) z p

/-- Real evaluation of a nested polynomial at the middle and innermost variables. -/
def eval2 (p : DPoly (DPoly ℤ)) (v z : ℝ) : ℝ :=
  DPoly.eval (fun q => eval1 q z) v p

/-- Real evaluation of a three-variable integer polynomial. -/
def eval3 (p : Poly3) (u v z : ℝ) : ℝ :=
  DPoly.eval (fun q => eval2 q v z) u p

@[simp] theorem eval1_zero (z : ℝ) : eval1 0 z = 0 := rfl

@[simp] theorem eval1_one (z : ℝ) : eval1 1 z = 1 := by
  simp [eval1, DPoly.eval, DPoly.evalCoeffs]

@[simp] theorem eval1_add (p q : DPoly ℤ) (z : ℝ) :
    eval1 (p + q) z = eval1 p z + eval1 q z := by
  apply DPoly.eval_add
  simp

@[simp] theorem eval1_neg (p : DPoly ℤ) (z : ℝ) :
    eval1 (-p) z = -eval1 p z := by
  apply DPoly.eval_neg
  simp

@[simp] theorem eval1_mul (p q : DPoly ℤ) (z : ℝ) :
    eval1 (p * q) z = eval1 p z * eval1 q z := by
  apply DPoly.eval_mul
  · simp
  · simp
  · simp

@[simp] theorem eval1_pow (p : DPoly ℤ) (z : ℝ) (n : ℕ) :
    eval1 (p ^ n) z = eval1 p z ^ n := by
  apply DPoly.eval_pow
  · simp
  · simp
  · simp
  · simp

@[simp] theorem eval2_zero (v z : ℝ) : eval2 0 v z = 0 := rfl

@[simp] theorem eval2_one (v z : ℝ) : eval2 1 v z = 1 := by
  simp [eval2, DPoly.eval, DPoly.evalCoeffs]

@[simp] theorem eval2_add (p q : DPoly (DPoly ℤ)) (v z : ℝ) :
    eval2 (p + q) v z = eval2 p v z + eval2 q v z := by
  apply DPoly.eval_add
  intro a b
  exact eval1_add a b z

@[simp] theorem eval2_neg (p : DPoly (DPoly ℤ)) (v z : ℝ) :
    eval2 (-p) v z = -eval2 p v z := by
  apply DPoly.eval_neg
  intro a
  exact eval1_neg a z

@[simp] theorem eval2_mul (p q : DPoly (DPoly ℤ)) (v z : ℝ) :
    eval2 (p * q) v z = eval2 p v z * eval2 q v z := by
  apply DPoly.eval_mul
  · exact eval1_zero z
  · intro a b
    exact eval1_add a b z
  · intro a b
    exact eval1_mul a b z

@[simp] theorem eval2_pow (p : DPoly (DPoly ℤ)) (v z : ℝ) (n : ℕ) :
    eval2 (p ^ n) v z = eval2 p v z ^ n := by
  apply DPoly.eval_pow
  · exact eval1_zero z
  · exact eval1_one z
  · intro a b
    exact eval1_add a b z
  · intro a b
    exact eval1_mul a b z

@[simp] theorem eval3_zero (u v z : ℝ) : eval3 0 u v z = 0 := rfl

@[simp] theorem eval3_one (u v z : ℝ) : eval3 1 u v z = 1 := by
  simp [eval3, DPoly.eval, DPoly.evalCoeffs]

@[simp] theorem eval3_add (p q : Poly3) (u v z : ℝ) :
    eval3 (p + q) u v z = eval3 p u v z + eval3 q u v z := by
  apply DPoly.eval_add
  intro a b
  exact eval2_add a b v z

@[simp] theorem eval3_neg (p : Poly3) (u v z : ℝ) :
    eval3 (-p) u v z = -eval3 p u v z := by
  apply DPoly.eval_neg
  intro a
  exact eval2_neg a v z

@[simp] theorem eval3_mul (p q : Poly3) (u v z : ℝ) :
    eval3 (p * q) u v z = eval3 p u v z * eval3 q u v z := by
  apply DPoly.eval_mul
  · exact eval2_zero v z
  · intro a b
    exact eval2_add a b v z
  · intro a b
    exact eval2_mul a b v z

@[simp] theorem eval3_pow (p : Poly3) (u v z : ℝ) (n : ℕ) :
    eval3 (p ^ n) u v z = eval3 p u v z ^ n := by
  apply DPoly.eval_pow
  · exact eval2_zero v z
  · exact eval2_one v z
  · intro a b
    exact eval2_add a b v z
  · intro a b
    exact eval2_mul a b v z

@[simp] theorem eval3_sub (p q : Poly3) (u v z : ℝ) :
    eval3 (p - q) u v z = eval3 p u v z - eval3 q u v z := by
  change eval3 (p + -q) u v z = _
  rw [eval3_add, eval3_neg]
  rfl

@[simp] theorem eval3_U (u v z : ℝ) : eval3 U u v z = u := by
  simp [eval3, eval2, eval1, U, DPoly.X, DPoly.eval, DPoly.evalCoeffs]

@[simp] theorem eval3_V (u v z : ℝ) : eval3 V u v z = v := by
  simp [eval3, eval2, eval1, V, DPoly.X, DPoly.const,
    DPoly.eval, DPoly.evalCoeffs]

@[simp] theorem eval3_Z (u v z : ℝ) : eval3 Z u v z = z := by
  simp [eval3, eval2, eval1, Z, DPoly.X, DPoly.const,
    DPoly.eval, DPoly.evalCoeffs]

@[simp] theorem eval3_two (u v z : ℝ) :
    eval3 (2 : Poly3) u v z = 2 := by
  change
    eval3 (DPoly.const (DPoly.const (DPoly.const (2 : ℤ)))) u v z = 2
  norm_num [eval3, eval2, eval1, DPoly.eval, DPoly.const,
    DPoly.evalCoeffs]

@[simp] theorem eval3_three (u v z : ℝ) :
    eval3 (3 : Poly3) u v z = 3 := by
  change
    eval3 (DPoly.const (DPoly.const (DPoly.const (3 : ℤ)))) u v z = 3
  norm_num [eval3, eval2, eval1, DPoly.eval, DPoly.const,
    DPoly.evalCoeffs]

@[simp] theorem eval3_four (u v z : ℝ) :
    eval3 (4 : Poly3) u v z = 4 := by
  change
    eval3 (DPoly.const (DPoly.const (DPoly.const (4 : ℤ)))) u v z = 4
  norm_num [eval3, eval2, eval1, DPoly.eval, DPoly.const,
    DPoly.evalCoeffs]

@[simp] theorem eval3_seven (u v z : ℝ) :
    eval3 (7 : Poly3) u v z = 7 := by
  change
    eval3 (DPoly.const (DPoly.const (DPoly.const (7 : ℤ)))) u v z = 7
  norm_num [eval3, eval2, eval1, DPoly.eval, DPoly.const,
    DPoly.evalCoeffs]

@[simp] theorem eval3_twelve (u v z : ℝ) :
    eval3 (12 : Poly3) u v z = 12 := by
  change
    eval3 (DPoly.const (DPoly.const (DPoly.const (12 : ℤ)))) u v z = 12
  norm_num [eval3, eval2, eval1, DPoly.eval, DPoly.const,
    DPoly.evalCoeffs]

@[simp] theorem eval3_twentyFive (u v z : ℝ) :
    eval3 (25 : Poly3) u v z = 25 := by
  change
    eval3 (DPoly.const (DPoly.const (DPoly.const (25 : ℤ)))) u v z = 25
  norm_num [eval3, eval2, eval1, DPoly.eval, DPoly.const,
    DPoly.evalCoeffs]

@[simp] theorem eval3_fifty (u v z : ℝ) :
    eval3 (50 : Poly3) u v z = 50 := by
  change
    eval3 (DPoly.const (DPoly.const (DPoly.const (50 : ℤ)))) u v z = 50
  norm_num [eval3, eval2, eval1, DPoly.eval, DPoly.const,
    DPoly.evalCoeffs]

@[simp] theorem eval3_sixHundred (u v z : ℝ) :
    eval3 (600 : Poly3) u v z = 600 := by
  change
    eval3 (DPoly.const (DPoly.const (DPoly.const (600 : ℤ)))) u v z = 600
  norm_num [eval3, eval2, eval1, DPoly.eval, DPoly.const,
    DPoly.evalCoeffs]

/-- Polynomial numerator used to certify the Bellman inequality in affine coordinates. -/
def bellmanAt (s r v : Poly3) : Poly3 :=
  let A := 1 + v
  let S := s + 2
  let BB := s + 1
  let C := s + r
  let M := s + 2 + 2 * v
  let W0 := s * A * v
  let dB := BB ^ 3 + 7 * C ^ 3
  let dM := M ^ 3 + 7 * C ^ 3
  let bp :=
    -2 * BB ^ 2 * r ^ 2 + (4 * BB ^ 2 - BB * C) * r +
      3 * C ^ 2 - 4 * BB * C
  let bc :=
    -M ^ 2 * (r ^ 2 * S + 4 * W0) +
      M * (4 * M - C) * (r * A * S + 2 * W0) +
      2 * C * (3 * C - 4 * M) * (A ^ 2 * S + W0)
  600 * BB ^ 5 * M ^ 4 * C * (r * A * S + 2 * W0) +
    25 * BB ^ 5 * dM * bc -
    50 * S * M ^ 5 * dB * bp -
    12 * BB ^ 5 * M ^ 5 * (S * (A ^ 2 - 1) + W0)

/-- Homogenized Bellman polynomial for a rational coordinate with the given denominator. -/
def projectiveBellmanAt (den s num v : Poly3) : Poly3 :=
  let A := 1 + v
  let S := s + 2
  let BB := s + 1
  let C := den * s + num
  let M := s + 2 + 2 * v
  let W0 := s * A * v
  let dB := den ^ 3 * BB ^ 3 + 7 * C ^ 3
  let dM := den ^ 3 * M ^ 3 + 7 * C ^ 3
  let bp :=
    -2 * BB ^ 2 * num ^ 2 +
      (4 * den * BB ^ 2 - BB * C) * num +
      3 * C ^ 2 - 4 * den * BB * C
  let bc :=
    -M ^ 2 * (num ^ 2 * S + 4 * den ^ 2 * W0) +
      M * (4 * den * M - C) * (num * A * S + 2 * den * W0) +
      2 * C * (3 * C - 4 * den * M) * (A ^ 2 * S + W0)
  600 * den ^ 3 * BB ^ 5 * M ^ 4 * C *
      (num * A * S + 2 * den * W0) +
    25 * BB ^ 5 * dM * bc -
    50 * S * M ^ 5 * dB * bp -
    12 * den ^ 5 * BB ^ 5 * M ^ 5 * (S * (A ^ 2 - 1) + W0)

/-- Real-valued expression corresponding to the affine Bellman polynomial. -/
def bellmanRealAt (s r v : ℝ) : ℝ :=
  let A := 1 + v
  let S := s + 2
  let BB := s + 1
  let C := s + r
  let M := s + 2 + 2 * v
  let W0 := s * A * v
  let dB := BB ^ 3 + 7 * C ^ 3
  let dM := M ^ 3 + 7 * C ^ 3
  let bp :=
    -2 * BB ^ 2 * r ^ 2 + (4 * BB ^ 2 - BB * C) * r +
      3 * C ^ 2 - 4 * BB * C
  let bc :=
    -M ^ 2 * (r ^ 2 * S + 4 * W0) +
      M * (4 * M - C) * (r * A * S + 2 * W0) +
      2 * C * (3 * C - 4 * M) * (A ^ 2 * S + W0)
  600 * BB ^ 5 * M ^ 4 * C * (r * A * S + 2 * W0) +
    25 * BB ^ 5 * dM * bc -
    50 * S * M ^ 5 * dB * bp -
    12 * BB ^ 5 * M ^ 5 * (S * (A ^ 2 - 1) + W0)

/-- Real-valued expression corresponding to the homogenized Bellman polynomial. -/
def projectiveBellmanRealAt (den s num v : ℝ) : ℝ :=
  let A := 1 + v
  let S := s + 2
  let BB := s + 1
  let C := den * s + num
  let M := s + 2 + 2 * v
  let W0 := s * A * v
  let dB := den ^ 3 * BB ^ 3 + 7 * C ^ 3
  let dM := den ^ 3 * M ^ 3 + 7 * C ^ 3
  let bp :=
    -2 * BB ^ 2 * num ^ 2 +
      (4 * den * BB ^ 2 - BB * C) * num +
      3 * C ^ 2 - 4 * den * BB * C
  let bc :=
    -M ^ 2 * (num ^ 2 * S + 4 * den ^ 2 * W0) +
      M * (4 * den * M - C) * (num * A * S + 2 * den * W0) +
      2 * C * (3 * C - 4 * den * M) * (A ^ 2 * S + W0)
  600 * den ^ 3 * BB ^ 5 * M ^ 4 * C *
      (num * A * S + 2 * den * W0) +
    25 * BB ^ 5 * dM * bc -
    50 * S * M ^ 5 * dB * bp -
    12 * den ^ 5 * BB ^ 5 * M ^ 5 * (S * (A ^ 2 - 1) + W0)

theorem eval3_bellmanAt (s r v : Poly3) (u₀ v₀ z₀ : ℝ) :
    eval3 (bellmanAt s r v) u₀ v₀ z₀ =
      bellmanRealAt (eval3 s u₀ v₀ z₀)
        (eval3 r u₀ v₀ z₀) (eval3 v u₀ v₀ z₀) := by
  simp [bellmanAt, bellmanRealAt]

theorem eval3_projectiveBellmanAt
    (den s num v : Poly3) (u₀ v₀ z₀ : ℝ) :
    eval3 (projectiveBellmanAt den s num v) u₀ v₀ z₀ =
      projectiveBellmanRealAt (eval3 den u₀ v₀ z₀)
        (eval3 s u₀ v₀ z₀) (eval3 num u₀ v₀ z₀)
        (eval3 v u₀ v₀ z₀) := by
  simp [projectiveBellmanAt, projectiveBellmanRealAt]

theorem projectiveBellmanRealAt_eq
    {den s num v : ℝ} (hden : den ≠ 0) :
    projectiveBellmanRealAt den s num v =
      den ^ 5 * bellmanRealAt s (num / den) v := by
  dsimp [projectiveBellmanRealAt, bellmanRealAt]
  field_simp [hden]

/-- Bellman certificate in the positive projective chart. -/
def chartPlus : Poly3 :=
  projectiveBellmanAt (2 * (1 + U)) (2 * V + Z) U V

/-- Bellman certificate after the first negative-coordinate chart substitution. -/
def chartOne : Poly3 :=
  bellmanAt (2 * U + 2 * V + Z) (-U) (U + V)

/-- Bellman certificate after the second negative-coordinate chart substitution. -/
def chartTwo : Poly3 :=
  bellmanAt (2 * U + 2 * V + Z) (-2 * U - V) (U + V)

/-- Bellman certificate after the third negative-coordinate chart substitution. -/
def chartThree : Poly3 :=
  bellmanAt (U + 2 * V + Z) (-U - 2 * V) V

/-- Projective Bellman certificate at the endpoint coordinate `1 / 2`. -/
def chartEndpoint : Poly3 :=
  projectiveBellmanAt 2 (2 * V + Z) 1 V

/-- Decidable check that every integer coefficient is nonnegative. -/
def allNonnegative1 (p : DPoly ℤ) : Bool :=
  p.coeffs.all fun c => decide (0 ≤ c)

/-- Decidable check of nonnegativity of every coefficient in two variables. -/
def allNonnegative2 (p : DPoly (DPoly ℤ)) : Bool :=
  p.coeffs.all allNonnegative1

/-- Decidable check of nonnegativity of every coefficient in three variables. -/
def allNonnegative3 (p : Poly3) : Bool :=
  p.coeffs.all allNonnegative2

/-- Number of nonzero coefficients in a dense polynomial. -/
def nonzeroCount1 (p : DPoly ℤ) : Nat :=
  p.coeffs.countP (· ≠ 0)

/-- Number of nonzero integer coefficients in a two-variable polynomial. -/
def nonzeroCount2 (p : DPoly (DPoly ℤ)) : Nat :=
  (p.coeffs.map nonzeroCount1).sum

/-- Number of nonzero integer coefficients in a three-variable polynomial. -/
def nonzeroCount3 (p : Poly3) : Nat :=
  (p.coeffs.map nonzeroCount2).sum

theorem DPoly.eval_nonnegative_of_all
    {R : Type} (good : R → Bool) (f : R → ℝ)
    (hgood : ∀ a, good a = true → 0 ≤ f a)
    {x : ℝ} (hx : 0 ≤ x) (p : DPoly R)
    (hp : p.coeffs.all good = true) :
    0 ≤ DPoly.eval f x p := by
  rcases p with ⟨p⟩
  change p.all good = true at hp
  change 0 ≤ DPoly.evalCoeffs f x p
  induction p with
  | nil => simp [DPoly.evalCoeffs]
  | cons a p ih =>
      change (good a && p.all good) = true at hp
      rw [Bool.and_eq_true_iff] at hp
      rw [DPoly.evalCoeffs]
      exact add_nonneg (hgood a hp.1) (mul_nonneg hx (ih hp.2))

theorem eval1_nonnegative
    {p : DPoly ℤ} (hp : allNonnegative1 p = true)
    {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ eval1 p z := by
  apply DPoly.eval_nonnegative_of_all
    (fun c : ℤ => decide (0 ≤ c)) (fun c : ℤ => (c : ℝ)) ?_ hz p hp
  intro c hc
  exact_mod_cast of_decide_eq_true hc

theorem eval2_nonnegative
    {p : DPoly (DPoly ℤ)} (hp : allNonnegative2 p = true)
    {v z : ℝ} (hv : 0 ≤ v) (hz : 0 ≤ z) :
    0 ≤ eval2 p v z := by
  apply DPoly.eval_nonnegative_of_all
    allNonnegative1 (fun q => eval1 q z) ?_ hv p hp
  intro q hq
  exact eval1_nonnegative hq hz

theorem eval3_nonnegative
    {p : Poly3} (hp : allNonnegative3 p = true)
    {u v z : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hz : 0 ≤ z) :
    0 ≤ eval3 p u v z := by
  apply DPoly.eval_nonnegative_of_all
    allNonnegative2 (fun q => eval2 q v z) ?_ hu p hp
  intro q hq
  exact eval2_nonnegative hq hv hz

private meta instance {R : Type} [Lean.ToExpr R] : Lean.ToExpr (DPoly R) where
  toExpr p :=
    let ⟨coefficients⟩ := p
    Lean.mkApp2 (Lean.mkConst ``DPoly.mk) (Lean.toTypeExpr R) (Lean.toExpr coefficients)
  toTypeExpr := Lean.mkApp (Lean.mkConst ``DPoly) (Lean.toTypeExpr R)

private meta def readBellmanNat (expression : Lean.Expr) : Lean.MetaM (Option Nat) := do
  let expression := expression.consumeMData
  if expression.isConstOf ``Nat.zero then return some 0
  Lean.Meta.getNatValue? expression

private meta def exposeBellmanUntil (isTerminal : Lean.Expr → Bool) (expression : Lean.Expr) :
    Lean.MetaM Lean.Expr := do
  let expression := expression.consumeMData
  if isTerminal expression then return expression
  let expose := fun term => Lean.Meta.whnfHeadPred term fun head => return !isTerminal head
  let expression ← expose expression
  if isTerminal expression then return expression
  Lean.Meta.withTransparency .all (expose expression)

-- Select enclosing fields without reducing the selected expression.
private meta def exposeBellmanProjections (expose : Lean.Expr → Lean.MetaM Lean.Expr)
    (preserve : Lean.Name → Nat → Bool) (expression : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let mut next := expression
  repeat
    Lean.Core.checkSystem "Bellman projections"
    let term ← Lean.Meta.withConfig (fun configuration => { configuration with proj := .no }) <|
      expose next
    let .proj name index _ := term | return term
    if preserve name index then return term
    if let some field ← Lean.Meta.reduceProj? term then
      next := field
    else if let some field ← Lean.Meta.withTransparency .all (Lean.Meta.reduceProj? term) then
      next := field
    else
      return term

-- Keep the coefficient projection visible for polynomial eta and append normalization.
private meta def exposeBellmanField (expression : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let preserve (name : Lean.Name) (index : Nat) := name == ``DPoly && index == 0
  let isTerminal (term : Lean.Expr) : Bool :=
    match term with
    | .proj name index _ => preserve name index
    | _ => term.isAppOfArity ``DPoly.coeffs 2 || term.isAppOfArity ``List.nil 1 ||
        term.isAppOfArity ``List.cons 3 || term.isAppOfArity ``List.append 3 ||
        term.isAppOfArity ``HAppend.hAppend 6 || term.isAppOfArity ``Append.append 4
  exposeBellmanProjections (exposeBellmanUntil isTerminal) preserve expression

-- Stop at heads the staged reader handles so other helpers unfold in any namespace.
private meta def isBellmanHead (term : Lean.Expr) : Bool :=
  match term.getAppFn.constName? with
  | some head =>
    #[``DPoly.mk, ``DPoly.const, ``DPoly.X, ``DPoly.add, ``DPoly.mul, ``DPoly.pow, ``DPoly.neg,
      ``DPoly.scale, ``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HPow.hPow, ``Neg.neg,
      ``OfNat.ofNat, ``Int.ofNat, ``Int.negSucc, ``U, ``V, ``Z].contains head
  | none => false

private meta def exposeBellmanHead (expression : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let mut next := expression
  repeat
    let mut term ← exposeBellmanUntil isBellmanHead next
    -- A constructor applied to the same polynomial's projection exposes
    -- that polynomial before the leaf reader evaluates its coefficient list.
    if term.isAppOfArity ``DPoly.mk 2 then
      term := Lean.mkApp term.appFn! (← exposeBellmanField term.appArg!)
      if let some polynomial ← Lean.Meta.etaStruct? term (· == ``DPoly) then
        next := polynomial
        continue
    return term

private theorem repackBellmanBranch (p : DPoly R) (branch : List R → DPoly R)
    (identity : ∀ coefficients, branch coefficients = DPoly.mk coefficients) :
    (match p with | ⟨coefficients⟩ => branch coefficients) = p := by
  cases p with
  | mk coefficients => exact identity coefficients

-- Match an identity over a variable so conversion cannot evaluate the concrete argument.
private meta def specializeBellmanIdentity (rule : Lean.Name) (argument : Lean.Expr)
    (repack : Lean.Expr → Lean.Expr) : Lean.MetaM (Option Lean.Expr) := do
  let type ← Lean.Meta.inferType argument
  unless (← Lean.Meta.whnfD type).isAppOfArity ``List 1 do return none
  Lean.Meta.withLocalDeclD `argument type fun localArgument => do
    let target ← Lean.Meta.mkEq (repack localArgument) localArgument
    let proof ← Lean.Meta.mkAppM rule #[localArgument]
    let proofType ← Lean.Meta.inferType proof
    unless ← Lean.Meta.withTransparency .all (Lean.Meta.isDefEqGuarded proofType target) do
      return none
    let proof ← Lean.Meta.mkExpectedTypeHint proof target
    let abstractProof ← Lean.Meta.mkLambdaFVars #[localArgument] proof
    return some (Lean.mkApp abstractProof argument)

private meta def peelBellmanAppend (operator left right : Lean.Expr) :
    Lean.MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let (rule, survivor, rebuild) ←
    if right.isAppOfArity ``List.nil 1 then
      pure (``List.append_nil, left, fun term => Lean.mkApp2 operator term right)
    else if left.isAppOfArity ``List.nil 1 then
      pure (``List.nil_append, right, fun term => Lean.mkApp2 operator left term)
    else
      return none
  let some proof ← specializeBellmanIdentity rule survivor rebuild | return none
  return some (survivor, proof)

private meta inductive BellmanAppendWork where
  | visit (expression : Lean.Expr)
  | combine (operator left right : Lean.Expr)

private meta def combineBellmanAppends (operator oldLeft oldRight : Lean.Expr)
    (left right : Lean.Expr × Option Lean.Expr) :
    Lean.MetaM (Lean.Expr × Option Lean.Expr) := do
  let (newLeft, leftProof) := left
  let (newRight, rightProof) := right
  let proof ← match leftProof, rightProof with
    | none, none => pure none
    | none, some h => some <$> Lean.Meta.mkCongrArg (Lean.mkApp operator oldLeft) h
    | some h, none =>
      some <$> Lean.Meta.mkCongrFun (← Lean.Meta.mkCongrArg operator h) oldRight
    | some hl, some hr => some <$> Lean.Meta.mkCongr (← Lean.Meta.mkCongrArg operator hl) hr
  let some (survivor, identity) ← peelBellmanAppend operator newLeft newRight
    | return (Lean.mkApp2 operator newLeft newRight, proof)
  return (survivor, ← Lean.Meta.mkEqTrans? proof (some identity))

-- Visit only the append tree. Coefficient projections and list cells remain opaque.
private meta def normalizeBellmanAppends (expression : Lean.Expr) :
    Lean.MetaM (Lean.Expr × Option Lean.Expr) := do
  let mut work := [BellmanAppendWork.visit expression]
  let mut results : List (Lean.Expr × Option Lean.Expr) := []
  repeat
    Lean.Core.checkSystem "Bellman coefficient appends"
    let task :: pending := work | break
    work := pending
    match task with
    | .visit expression =>
      let term ← exposeBellmanField expression
      if term.isAppOfArity ``List.append 3 || term.isAppOfArity ``HAppend.hAppend 6 ||
          term.isAppOfArity ``Append.append 4 then
        let left := term.appFn!.appArg!
        let right := term.appArg!
        work := .visit left :: .visit right :: .combine term.appFn!.appFn! left right :: work
      else
        results := (term, none) :: results
    | .combine operator left right =>
      let newRight :: newLeft :: rest := results | Lean.throwError "missing append operands"
      results := (← combineBellmanAppends operator left right newLeft newRight) :: rest
  let [(normalized, proof)] := results | Lean.throwError "incomplete append normalization"
  let proof ← proof.mapM fun proof => do
    let equality ← Lean.Meta.mkEq expression normalized
    return Lean.Meta.mkExpectedPropHint proof equality
  return (normalized, proof)

-- Prove the branch identity on its local field before applying it to a chart.
private meta def proveBellmanRepackBranch (branch : Lean.Expr) :
    Lean.MetaM (Option Lean.Expr) :=
  Lean.Meta.lambdaTelescope branch fun fields body => do
    let #[field] := fields | return none
    let expose := exposeBellmanUntil (·.isAppOfArity ``DPoly.mk 2)
    let body ← exposeBellmanProjections expose (fun _ _ => false) body
    unless body.isAppOfArity ``DPoly.mk 2 do return none
    let (coefficients, proof) ← normalizeBellmanAppends body.appArg!
    unless coefficients == field do return none
    let proof ← match proof with
      | some proof => pure proof
      | none => Lean.Meta.mkEqRefl coefficients
    let proof ← Lean.Meta.mkCongrArg body.appFn! proof
    return some (← Lean.Meta.mkLambdaFVars fields proof)

private meta def bellmanMatcherIdentity (expression : Lean.Expr) :
    Lean.MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let some matcher ← Lean.Meta.matchMatcherApp? expression.consumeMData (alsoCasesOn := true)
    | return none
  let #[polynomial] := matcher.discrs | return none
  let #[branch] := matcher.alts | return none
  unless matcher.remaining.isEmpty do return none
  let type ← Lean.Meta.inferType polynomial
  unless (← Lean.Meta.whnfD type).getAppFn.isConstOf ``DPoly do return none
  let some branchProof ← proveBellmanRepackBranch branch | return none
  Lean.Meta.withLocalDeclD `polynomial type fun localPolynomial => do
    let repacked := { matcher with discrs := #[localPolynomial] }.toExpr
    let target ← Lean.Meta.mkEq repacked localPolynomial
    let proof ← Lean.Meta.mkAppM ``repackBellmanBranch #[localPolynomial, branch, branchProof]
    let proofType ← Lean.Meta.inferType proof
    unless ← Lean.Meta.withTransparency .all (Lean.Meta.isDefEqGuarded proofType target) do
      return none
    let proof ← Lean.Meta.mkExpectedTypeHint proof target
    let abstractProof ← Lean.Meta.mkLambdaFVars #[localPolynomial] proof
    return some (polynomial, Lean.mkApp abstractProof polynomial)

private meta def exposeBellmanIdentityHead (expression : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let isReady (term : Lean.Expr) : Lean.MetaM Bool := do
    if isBellmanHead term then return true
    return (← Lean.Meta.matchMatcherApp? term.consumeMData (alsoCasesOn := true)).isSome
  let expose (term : Lean.Expr) := Lean.Meta.withConfig (fun cfg => { cfg with iota := false }) do
    let head (term : Lean.Expr) := Lean.Meta.whnfHeadPred term fun candidate => do
      return !(← isReady candidate)
    let exposed ← head term.consumeMData
    if ← isReady exposed then return exposed
    Lean.Meta.withTransparency .all (head exposed)
  exposeBellmanProjections expose (fun _ _ => false) expression

-- Apply these identities before an operand constructor can force its coefficients.
private meta def prepareBellmanPolynomial (expression : Lean.Expr) :
    Lean.MetaM (Lean.Expr × Option Lean.Expr) := do
  let mut next := expression
  let mut prefixProof := none
  repeat
    Lean.Core.checkSystem "Bellman polynomial identities"
    let exposed ← exposeBellmanIdentityHead next
    let identity ← if exposed.isAppOfArity ``DPoly.mk 2 then do
        let coefficients ← exposeBellmanField exposed.appArg!
        let constructor := exposed.appFn!
        if let some polynomial ← Lean.Meta.etaStruct?
            (Lean.mkApp constructor coefficients) (· == ``DPoly) then
          next := polynomial
          continue
        let (normalized, proof) ← normalizeBellmanAppends coefficients
        if let some proof := proof then
          pure (some (Lean.mkApp constructor normalized, ← Lean.Meta.mkCongrArg constructor proof))
        else pure none
      else bellmanMatcherIdentity exposed
    let some (polynomial, proof) := identity | do
      -- An enclosing match can reveal a constructor only after iota reduction.
      let reduced ← exposeBellmanHead exposed
      if reduced == exposed then return (reduced, prefixProof)
      next := reduced
      continue
    prefixProof ← match prefixProof with
      | some previous => some <$> Lean.Meta.mkEqTrans previous proof
      | none => pure (some proof)
    next := polynomial

-- Compute closed coefficients after direct decoding fails. The outer chart
-- still uses the staged operations.
private meta def readBellmanClosedValue {R : Type}
    (readHead : Lean.Expr → Lean.MetaM (Option R)) (expression : Lean.Expr) :
    Lean.MetaM (Option R) := do
  if let some value ← readHead expression then return some value
  if expression.hasFVar || expression.hasMVar || expression.hasLooseBVars then return none
  let reduced ← Lean.Meta.whnfD expression
  if let some value ← readHead reduced then return some value
  Lean.Meta.withTransparency .all do
    readHead (← Lean.Meta.whnf reduced)

private meta def readBellmanInteger (expression : Lean.Expr) : Lean.MetaM (Option Int) := do
  let readHead (term : Lean.Expr) : Lean.MetaM (Option Int) := do
    if let some integer ← Lean.Meta.getIntValue? term then return some integer
    match_expr term with
    | Int.ofNat n => return (← readBellmanClosedValue readBellmanNat n).map Int.ofNat
    | Int.negSucc n => return (← readBellmanClosedValue readBellmanNat n).map Int.negSucc
    | _ => return none
  readBellmanClosedValue readHead (← exposeBellmanHead expression)

-- Expose each list cell separately so wrappers around the list or its tail are harmless.
private meta def readBellmanList {R : Type}
    (read : Lean.Expr → Lean.MetaM (Option R)) (expression : Lean.Expr) :
    Lean.MetaM (Option (List R)) := do
  let readCell (term : Lean.Expr) : Lean.MetaM (Option Lean.Expr) :=
    pure (if term.isAppOfArity ``List.nil 1 || term.isAppOfArity ``List.cons 3 then
      some term else none)
  let mut next := expression
  let mut values : Array R := #[]
  repeat
    Lean.Core.checkSystem "Bellman coefficient list"
    let some cell ← readBellmanClosedValue readCell next.consumeMData | return none
    match_expr cell with
    | List.nil _ => return some values.toList
    | List.cons _ head tail =>
      let some coefficient ← read head | return none
      values := values.push coefficient
      next := tail
    | _ => return none

private meta def readBellmanCoefficients {R : Type} [Zero R] [One R]
    (read : Lean.Expr → Lean.MetaM (Option R)) (fromNat : Nat → R)
    (evaluateCoefficient : Bool) (expression : Lean.Expr) : Lean.MetaM (Option (DPoly R)) := do
  let expression ← exposeBellmanHead expression
  let readHead (term : Lean.Expr) : Lean.MetaM (Option (DPoly R)) := do
    match_expr term with
    | OfNat.ofNat type n _ =>
        unless (← Lean.Meta.whnfD type).getAppFn.isConstOf ``DPoly do return none
        return (← readBellmanClosedValue readBellmanNat n).map fun value =>
          if value == 0 then 0 else DPoly.const (fromNat value)
    | DPoly.X _ _ _ => return some DPoly.X
    | DPoly.const _ coefficient => return (← read coefficient).map DPoly.const
    | DPoly.mk _ coefficients =>
        return (← readBellmanList read coefficients).map fun values => ⟨values⟩
    | _ => return none
  if evaluateCoefficient then readBellmanClosedValue readHead expression else readHead expression

-- Compute on coefficient data, then have the kernel verify the explicit reduction.
-- The meta code produces the proposed value; only the checked equality is reused.
private meta def checkBellmanReduction (operands value : Lean.Expr) :
    Lean.MetaM Lean.Expr := do
  let equality ← Lean.Meta.mkEq operands value
  let reflexivity ← Lean.Meta.mkEqRefl value
  let certificate ← Lean.Meta.mkAuxLemma [] equality reflexivity
    (kind? := some `polynomialReduction)
  -- Await kernel insertion before reusing the equality. The kernel reports any mismatch.
  let kernelEnv := (← Lean.getEnv).toKernelEnv
  let some (.thmInfo _) := kernelEnv.find? certificate
    | throwError "kernel rejected staged Bellman reduction"
  return Lean.mkConst certificate

private meta def bellmanBinaryOperation (expression : Lean.Expr) :
    Option (Poly3 → Poly3 → Poly3) :=
  if expression.isAppOfArity ``HAdd.hAdd 6 || expression.isAppOfArity ``DPoly.add 4 then
    some (· + ·)
  else if expression.isAppOfArity ``HSub.hSub 6 then some (· - ·)
  else if expression.isAppOfArity ``HMul.hMul 6 || expression.isAppOfArity ``DPoly.mul 6 then
    some (· * ·)
  else none

private meta def isBellmanPower (expression : Lean.Expr) : Bool :=
  expression.isAppOfArity ``HPow.hPow 6 || expression.isAppOfArity ``DPoly.pow 7

private meta def isBellmanNegation (expression : Lean.Expr) : Bool :=
  expression.isAppOfArity ``Neg.neg 3 || expression.isAppOfArity ``DPoly.neg 3

private meta def readBellmanBivariate (expression : Lean.Expr) :
    Lean.MetaM (Option (DPoly (DPoly ℤ))) :=
  readBellmanCoefficients
    (readBellmanCoefficients readBellmanInteger Int.ofNat true) (DPoly.const ∘ Int.ofNat)
    true expression

private meta def readBellmanLeaf (expression : Lean.Expr) : Lean.MetaM (Option Poly3) := do
  if expression.isConstOf ``U then return some DPoly.X
  if expression.isConstOf ``V then return some (DPoly.const DPoly.X)
  if expression.isConstOf ``Z then return some (DPoly.const (DPoly.const DPoly.X))
  readBellmanCoefficients readBellmanBivariate (DPoly.const ∘ DPoly.const ∘ Int.ofNat)
    false expression

private meta def readBellmanScaleFactor (expression : Lean.Expr) :
    Lean.MetaM (DPoly (DPoly ℤ)) := do
  let some factor ← readBellmanBivariate expression
    | throwError "unsupported Bellman scale factor {expression}"
  return factor

private meta def readBellmanPower (expression : Lean.Expr) : Lean.MetaM Nat := do
  let some power ← readBellmanClosedValue readBellmanNat expression
    | throwError "unsupported Bellman exponent {expression}: expected a closed natural power"
  return power

private inductive BellmanStep where
  | binary (operator left right : Lean.Expr) (evaluate : Poly3 → Poly3 → Poly3)
  | power (operator base exponent : Lean.Expr) (value : Nat)
  | scale (operator child : Lean.Expr) (factor : DPoly (DPoly ℤ))
  | negate (operator child : Lean.Expr)
  | leaf (value : Poly3)

private structure PreparedBellmanPolynomial where
  expression : Lean.Expr
  identityProof : Option Lean.Expr
  step : BellmanStep

private meta def BellmanStep.operands : BellmanStep → Array Lean.Expr
  | .binary _ left right _ => #[left, right]
  | .power _ base _ _ => #[base]
  | .scale _ child _ | .negate _ child => #[child]
  | .leaf _ => #[]

private meta def parseBellmanStep (expression : Lean.Expr) : Lean.MetaM BellmanStep := do
  let args := expression.getAppArgs
  let operator (arity : Nat) := Lean.mkAppN expression.getAppFn (args.extract 0 (args.size - arity))
  if let some evaluate := bellmanBinaryOperation expression then
    return .binary (operator 2) args[args.size - 2]! args[args.size - 1]! evaluate
  if isBellmanPower expression then
    let exponent := args[args.size - 1]!
    return .power (operator 2) args[args.size - 2]! exponent (← readBellmanPower exponent)
  if expression.isAppOfArity ``DPoly.scale 4 then
    let factor ← readBellmanScaleFactor args[args.size - 2]!
    return .scale (operator 1) args[args.size - 1]! factor
  if isBellmanNegation expression then
    return .negate (operator 1) args[args.size - 1]!
  let some value ← readBellmanLeaf expression
    | throwError "unsupported Bellman polynomial term {expression}"
  return .leaf value

-- Visit operands before their parents and reuse depths across shared expressions.
private meta def bellmanReductionDepth
    (prepare : Lean.Expr → Lean.MetaM PreparedBellmanPolynomial)
    (expression : Lean.Expr) : Lean.MetaM Nat := do
  let mut depths : Lean.ExprStructMap Nat := {}
  let mut pending : Array (Lean.Expr × Option (Array Lean.Expr)) := #[(expression, none)]
  while let some (term, operands) := pending.back? do
    Lean.Core.checkSystem "Bellman depth"
    pending := pending.pop
    let key : Lean.ExprStructEq := ⟨term⟩
    if (depths[key]?).isNone then
      if let some children := operands then
        let mut depth := 1
        for child in children do
          let childKey : Lean.ExprStructEq := ⟨child⟩
          let some childDepth := depths[childKey]?
            | throwError "Bellman operand depth is missing"
          depth := max depth (childDepth + 1)
        depths := depths.insert key depth
      else
        let children := (← prepare term).step.operands
        pending := pending.push (term, some children)
        for child in children do
          let childKey : Lean.ExprStructEq := ⟨child⟩
          if (depths[childKey]?).isNone then
            pending := pending.push (child, none)
  let rootKey : Lean.ExprStructEq := ⟨expression⟩
  let some depth := depths[rootKey]?
    | throwError "Bellman polynomial depth is missing"
  return depth

-- The cache is local to one closed chart and includes the kernel proof of each value.
private meta def normalizeBellmanPolynomial
    (prepare : Lean.Expr → Lean.MetaM PreparedBellmanPolynomial)
    (cache : IO.Ref (Lean.ExprStructMap (Poly3 × Lean.Expr × Lean.Expr)))
    (fuel : Nat) (expression : Lean.Expr) : Lean.MetaM (Poly3 × Lean.Expr × Lean.Expr) := do
  match fuel with
  | 0 => throwError "invalid Bellman reduction tree"
  | fuel + 1 =>
    let key : Lean.ExprStructEq := ⟨expression⟩
    if let some result := (← cache.get)[key]? then return result
    let prepared ← prepare expression
    let (value, operands, congruence) ← match prepared.step with
      | .binary operator left right evaluate => do
        let (left, leftExpr, leftProof) ← normalizeBellmanPolynomial prepare cache fuel left
        let (right, rightExpr, rightProof) ← normalizeBellmanPolynomial prepare cache fuel right
        let firstProof ← Lean.Meta.mkCongrArg operator leftProof
        let congruence ← Lean.Meta.mkCongr firstProof rightProof
        pure (evaluate left right, Lean.mkApp2 operator leftExpr rightExpr, congruence)
      | .power operator base exponent power => do
        let (base, baseExpr, baseProof) ← normalizeBellmanPolynomial prepare cache fuel base
        let firstProof ← Lean.Meta.mkCongrArg operator baseProof
        let congruence ← Lean.Meta.mkCongrFun firstProof exponent
        pure (base ^ power, Lean.mkApp2 operator baseExpr exponent, congruence)
      | .scale operator child factor => do
        let (value, valueExpr, proof) ← normalizeBellmanPolynomial prepare cache fuel child
        pure (DPoly.scale factor value, Lean.mkApp operator valueExpr,
          ← Lean.Meta.mkCongrArg operator proof)
      | .negate operator child => do
        let (value, valueExpr, proof) ← normalizeBellmanPolynomial prepare cache fuel child
        pure (-value, Lean.mkApp operator valueExpr, ← Lean.Meta.mkCongrArg operator proof)
      | .leaf value =>
        pure (value, prepared.expression, ← Lean.Meta.mkEqRefl prepared.expression)
    let quoted := Lean.toExpr value
    let reduction ← checkBellmanReduction operands quoted
    let proof ← Lean.Meta.mkEqTrans congruence reduction
    let proof ← match prepared.identityProof with
      | some identityProof => Lean.Meta.mkEqTrans identityProof proof
      | none => pure proof
    let result := (value, quoted, proof)
    cache.modify (·.insert key result)
    return result
termination_by structural fuel

local elab "reduceBellmanPolynomial" : conv => Lean.Elab.Tactic.withMainContext do
  let expression ← Lean.Elab.Tactic.Conv.getLhs
  let cache ← IO.mkRef ({} : Lean.ExprStructMap (Poly3 × Lean.Expr × Lean.Expr))
  let preparations ← IO.mkRef ({} : Lean.ExprStructMap PreparedBellmanPolynomial)
  let prepare term := do
    let key : Lean.ExprStructEq := ⟨term⟩
    if let some prepared := (← preparations.get)[key]? then return prepared
    let (expression, identityProof) ← prepareBellmanPolynomial term
    let step ← parseBellmanStep expression
    let prepared : PreparedBellmanPolynomial := ⟨expression, identityProof, step⟩
    preparations.modify (·.insert key prepared)
    return prepared
  let (_, value, proof) ← normalizeBellmanPolynomial prepare cache
    (← bellmanReductionDepth prepare expression) expression
  Lean.Elab.Tactic.Conv.updateLhs value proof

local elab "rewriteBellmanIdentities" : conv => Lean.Elab.Tactic.withMainContext do
  let (polynomial, proof) ← prepareBellmanPolynomial (← Lean.Elab.Tactic.Conv.getLhs)
  if let some equality := proof then
    Lean.Elab.Tactic.Conv.updateLhs polynomial equality

-- Keep these charts on the staged path so unsupported edits fail at the offending term.
local elab "checkBellmanChart" : tactic => Lean.Elab.Tactic.withoutRecover do
  Lean.Elab.Tactic.evalTactic (← `(tactic| (
    conv_lhs => { arg 1; reduceBellmanPolynomial }
    rfl)))

@[irreducible]
private def wrapBellmanValue {α : Type} (value : α) : α := value

-- Exercise expanded variables, computed coefficients and wrapped coefficient lists.
example :
    allNonnegative3
      (DPoly.X + DPoly.const (id DPoly.X) + DPoly.const (DPoly.const DPoly.X) +
        DPoly.const (2 : DPoly (DPoly ℤ)) + DPoly.const (DPoly.X + 0) +
        DPoly.mk (wrapBellmanValue (1 :: wrapBellmanValue [2])) +
        DPoly.const (DPoly.const (DPoly.const (1 + 1 : ℤ))) +
        DPoly.const (DPoly.const (DPoly.const (Int.ofNat (wrapBellmanValue 2)))) +
        U ^ wrapBellmanValue (1 : Nat) +
        wrapBellmanValue (DPoly.scale 2 (1 + U)) : Poly3) = true := by
  checkBellmanChart

-- A constructor/projection round trip preserves staging of the helper.
example :
    allNonnegative3
      (DPoly.mk
        (id ((DPoly.eval (id : Poly3 → Poly3) 0 (DPoly.const U)).coeffs, ()).1)) = true := by
  checkBellmanChart

private def emptyBellmanCoefficients : List (DPoly (DPoly ℤ)) := []

private theorem chartPlus_repacked_check :
    allNonnegative3
      (match chartPlus with
      | ⟨coefficients⟩ => DPoly.mk ((coefficients ++ emptyBellmanCoefficients) ++ [])) = true := by
  checkBellmanChart

-- Preserve the existing auxiliary lemma names of the public chart checks.
private theorem chartPlus_normalized_check : allNonnegative3 chartPlus = true := by
  have h := chartPlus_repacked_check
  conv_lhs at h => { arg 1; rewriteBellmanIdentities }
  exact h

theorem chartPlus_check : allNonnegative3 chartPlus = true := by
  as_aux_lemma => exact chartPlus_normalized_check

private def chartOneWithEmptyAppend : Poly3 :=
  match (chartOne, ()) with
  | (polynomial, _) => DPoly.mk ([] ++ (polynomial.coeffs ++ ([] ++ [])))

private theorem chartOne_appended_check : allNonnegative3 chartOneWithEmptyAppend = true := by
  checkBellmanChart

private theorem chartOne_normalized_check : allNonnegative3 chartOne = true := by
  have h := chartOne_appended_check
  conv_lhs at h => { arg 1; rewriteBellmanIdentities }
  exact h

theorem chartOne_check : allNonnegative3 chartOne = true := by
  as_aux_lemma => exact chartOne_normalized_check

private theorem chartTwo_normalized_check : allNonnegative3 chartTwo = true := by
  checkBellmanChart

theorem chartTwo_check : allNonnegative3 chartTwo = true := by
  as_aux_lemma => exact chartTwo_normalized_check

private theorem chartThree_normalized_check : allNonnegative3 chartThree = true := by
  checkBellmanChart

theorem chartThree_check : allNonnegative3 chartThree = true := by
  as_aux_lemma => exact chartThree_normalized_check

private theorem chartEndpoint_normalized_check : allNonnegative3 chartEndpoint = true := by
  checkBellmanChart

theorem chartEndpoint_check : allNonnegative3 chartEndpoint = true := by
  as_aux_lemma => exact chartEndpoint_normalized_check

theorem chartPlus_nonnegative
    {u v z : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hz : 0 ≤ z) :
    0 ≤ projectiveBellmanRealAt (2 * (1 + u)) (2 * v + z) u v := by
  have heval :
      eval3 chartPlus u v z =
        projectiveBellmanRealAt (2 * (1 + u)) (2 * v + z) u v := by
    simp [chartPlus, eval3_projectiveBellmanAt]
  rw [← heval]
  exact eval3_nonnegative chartPlus_check hu hv hz

theorem chartOne_nonnegative
    {u v z : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hz : 0 ≤ z) :
    0 ≤ bellmanRealAt (2 * u + 2 * v + z) (-u) (u + v) := by
  have heval :
      eval3 chartOne u v z =
        bellmanRealAt (2 * u + 2 * v + z) (-u) (u + v) := by
    simp [chartOne, eval3_bellmanAt]
  rw [← heval]
  exact eval3_nonnegative chartOne_check hu hv hz

theorem chartTwo_nonnegative
    {u v z : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hz : 0 ≤ z) :
    0 ≤ bellmanRealAt (2 * u + 2 * v + z) (-2 * u - v) (u + v) := by
  have heval :
      eval3 chartTwo u v z =
        bellmanRealAt (2 * u + 2 * v + z) (-2 * u - v) (u + v) := by
    simp [chartTwo, eval3_bellmanAt]
  rw [← heval]
  exact eval3_nonnegative chartTwo_check hu hv hz

theorem chartThree_nonnegative
    {u v z : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hz : 0 ≤ z) :
    0 ≤ bellmanRealAt (u + 2 * v + z) (-u - 2 * v) v := by
  have heval :
      eval3 chartThree u v z =
        bellmanRealAt (u + 2 * v + z) (-u - 2 * v) v := by
    simp [chartThree, eval3_bellmanAt]
  rw [← heval]
  exact eval3_nonnegative chartThree_check hu hv hz

theorem chartEndpoint_nonnegative
    {v z : ℝ} (hv : 0 ≤ v) (hz : 0 ≤ z) :
    0 ≤ projectiveBellmanRealAt 2 (2 * v + z) 1 v := by
  have heval :
      eval3 chartEndpoint 0 v z =
        projectiveBellmanRealAt 2 (2 * v + z) 1 v := by
    simp [chartEndpoint, eval3_projectiveBellmanAt]
  rw [← heval]
  exact eval3_nonnegative chartEndpoint_check (by positivity) hv hz

end BellmanCertificate

end FD1D

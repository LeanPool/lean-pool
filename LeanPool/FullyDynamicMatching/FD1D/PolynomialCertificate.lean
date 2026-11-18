/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/
module


public import Mathlib.Data.List.Basic
public import Mathlib.Tactic

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

/-- A dense polynomial represented by its coefficient list, in increasing degree order. -/
structure DPoly (R : Type) where
  /-- Coefficients in increasing degree order; trailing zero coefficients are permitted. -/
  coeffs : List R
deriving DecidableEq, Repr

namespace DPoly

/-- The dense representation of a constant polynomial. -/
def const (a : R) : DPoly R := ⟨[a]⟩

/-- Coefficientwise addition, extending the shorter list by zeros. -/
def addCoeffs [Add R] : List R → List R → List R
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: addCoeffs p q

/-- Negation of every coefficient. -/
def neg [Neg R] (p : DPoly R) : DPoly R :=
  ⟨p.coeffs.map (-·)⟩

/-- Addition of dense polynomials by their coefficient lists. -/
def add [Add R] (p q : DPoly R) : DPoly R :=
  ⟨addCoeffs p.coeffs q.coeffs⟩

/-- Left multiplication of every coefficient by the given scalar. -/
def scale [Mul R] (a : R) (p : DPoly R) : DPoly R :=
  ⟨p.coeffs.map (a * ·)⟩

/-- Convolution of coefficient lists for polynomial multiplication. -/
def mulCoeffs [Zero R] [Add R] [Mul R] : List R → List R → List R
  | [], _ => []
  | a :: p, q =>
      addCoeffs (q.map (a * ·)) (0 :: mulCoeffs p q)

/-- Multiplication of dense polynomials by coefficient convolution. -/
def mul [Zero R] [Add R] [Mul R] (p q : DPoly R) : DPoly R :=
  ⟨mulCoeffs p.coeffs q.coeffs⟩

/-- Natural powers computed by repeated polynomial multiplication. -/
def pow [Zero R] [One R] [Add R] [Mul R] (p : DPoly R) : ℕ → DPoly R
  | 0 => const 1
  | n + 1 => mul (pow p n) p

instance : Zero (DPoly R) := ⟨⟨[]⟩⟩
instance [One R] : One (DPoly R) := ⟨const 1⟩
instance [Add R] : Add (DPoly R) := ⟨add⟩
instance [Neg R] : Neg (DPoly R) := ⟨neg⟩
instance [Neg R] [Add R] : Sub (DPoly R) := ⟨fun p q => p + -q⟩
instance [Zero R] [Add R] [Mul R] : Mul (DPoly R) := ⟨mul⟩
instance [Zero R] [One R] [Add R] [Mul R] : Pow (DPoly R) Nat := ⟨pow⟩
instance (n : ℕ) [OfNat R (n + 2)] : OfNat (DPoly R) (n + 2) :=
  ⟨const (OfNat.ofNat (n + 2))⟩

@[simp] theorem coeffs_zero :
    (0 : DPoly R).coeffs = [] := rfl

@[simp] theorem coeffs_one [One R] :
    (1 : DPoly R).coeffs = [1] := rfl

@[simp] theorem coeffs_ofNat (n : ℕ) [OfNat R (n + 2)] :
    (OfNat.ofNat (n + 2) : DPoly R).coeffs =
      [OfNat.ofNat (n + 2)] := rfl

/-- The indeterminate, with coefficient list `[0, 1]`. -/
def X [Zero R] [One R] : DPoly R := ⟨[0, 1]⟩

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

-- Share normalizations of closed operands within one chart, and keep each
-- reduction as a kernel-checked equality for the surrounding convolution.
local elab "reduceBellmanPolynomial" : conv => Lean.Elab.Tactic.withMainContext do
  let cache ← IO.mkRef ({} : Lean.ExprStructMap (Lean.Expr × Lean.Expr))
  let rec normalize (fuel : Nat) (expression : Lean.Expr) :
      Lean.Elab.Tactic.TacticM (Lean.Expr × Lean.Expr) := do
    match fuel with
    | 0 => throwError "invalid Bellman reduction tree"
    | fuel + 1 =>
      let closed := !expression.hasFVar && !expression.hasMVar && !expression.hasLooseBVars
      let key : Lean.ExprStructEq := ⟨expression⟩
      if closed then
        if let some result := (← cache.get)[key]? then return result
      let isOperation := expression.isAppOf ``HAdd.hAdd ||
          expression.isAppOf ``HSub.hSub ||
          expression.isAppOf ``HMul.hMul ||
          expression.isAppOf ``HPow.hPow ||
          expression.isAppOf ``Neg.neg
      let (operands, congruence) ← if isOperation then
        Lean.Elab.Tactic.Conv.convert expression do
          Lean.Elab.Tactic.evalTactic (← `(conv| congr))
          for child in ← Lean.Elab.Tactic.getGoals do
            Lean.Elab.Tactic.setGoals [child]
            let (value, proof) ← normalize fuel (← Lean.Elab.Tactic.Conv.getLhs)
            Lean.Elab.Tactic.Conv.updateLhs value proof
            (← Lean.Elab.Tactic.getMainGoal).refl
          Lean.Elab.Tactic.setGoals []
      else
        pure (expression, ← Lean.Meta.mkEqRefl expression)
      let reduced ← Lean.Meta.reduce operands
      let proof ← if operands == reduced then pure congruence else do
        let equality ← Lean.Meta.mkEq operands reduced
        let reflexivity ← Lean.Meta.mkEqRefl reduced
        let reductionName ← Lean.Meta.mkAuxLemma [] equality reflexivity
          (kind? := some `polynomialReduction)
        Lean.Meta.mkEqTrans congruence (Lean.mkConst reductionName)
      let result := (reduced, proof)
      if closed then cache.modify (·.insert key result)
      return result
  let expression ← Lean.Elab.Tactic.Conv.getLhs
  let (value, proof) ← normalize (expression.sizeWithoutSharing + 1) expression
  Lean.Elab.Tactic.Conv.updateLhs value proof

local macro "checkBellmanChart" chart:ident formula:ident : tactic =>
  `(tactic| {
    unfold $chart $formula;
    conv_lhs => { arg 1; zeta; reduceBellmanPolynomial };
    rfl
  })

-- The affine formula ends in two subtractions. Expose the three
-- summands so the large positive sum and each subtrahend can be checked separately.
local elab "bellmanOperand% " chart:ident index:num : term => do
  let definition ← Lean.Meta.unfoldDefinition (← Lean.Elab.Term.elabTerm chart none)
  unless definition.isAppOf ``bellmanAt do
    throwError "expected an affine Bellman chart"
  let expression ← Lean.Meta.zetaReduce (← Lean.Meta.unfoldDefinition definition)
  let subtraction (value : Lean.Expr) : Lean.Elab.Term.TermElabM (Lean.Expr × Lean.Expr) := do
    unless value.isAppOf ``HSub.hSub do
      throwError "the Bellman polynomial no longer ends in two subtractions"
    let .app (.app _ left) right := value | throwError "expected a binary subtraction"
    return (left, right)
  let (leftGroup, lastNegative) ← subtraction expression
  let (positive, firstNegative) ← subtraction leftGroup
  match index.getNat with
  | 0 => return positive
  | 1 => return firstNegative
  | 2 => return lastNegative
  | _ => throwError "expected Bellman operand 0, 1 or 2"

-- Store the normalized value with its equality to the original operand.
local elab "recordBellmanOperand" : tactic => Lean.Elab.Tactic.withMainContext do
  let target ← (← Lean.Elab.Tactic.getMainGoal).getType
  unless target.isAppOf ``Subtype do throwError "expected a checked Bellman operand"
  let args := target.getAppArgs
  let predicate := args[1]!
  let .lam _ _ body _ := predicate | throwError "expected an operand equality"
  let some (_, original, _) := body.eq? | throwError "expected an operand equality"
  let (value, proof) ← Lean.Elab.Tactic.Conv.convert original do
    Lean.Elab.Tactic.evalTactic (← `(conv| reduceBellmanPolynomial))
  let checked ← Lean.Meta.mkAppOptM ``Subtype.mk #[some args[0]!, some predicate, some value,
    some proof]
  Lean.Elab.Tactic.closeMainGoal `recordBellmanOperand checked

-- Keep the existing auxiliary lemma names in the public chart checks.
private theorem chartPlus_normalized_check : allNonnegative3 chartPlus = true := by
  checkBellmanChart chartPlus projectiveBellmanAt

theorem chartPlus_check : allNonnegative3 chartPlus = true := by
  as_aux_lemma => exact chartPlus_normalized_check

private def chartOneOperand0 : {p : Poly3 // bellmanOperand% chartOne 0 = p} := by
  recordBellmanOperand

private def chartOneOperand1 : {p : Poly3 // bellmanOperand% chartOne 1 = p} := by
  recordBellmanOperand

private def chartOneOperand2 : {p : Poly3 // bellmanOperand% chartOne 2 = p} := by
  recordBellmanOperand

private theorem chartOne_normalized_check : allNonnegative3 chartOne = true := by
  change allNonnegative3
    ((bellmanOperand% chartOne 0) - (bellmanOperand% chartOne 1)
      - (bellmanOperand% chartOne 2)) = true
  rw [chartOneOperand0.property, chartOneOperand1.property, chartOneOperand2.property]
  rfl

theorem chartOne_check : allNonnegative3 chartOne = true := by
  as_aux_lemma => exact chartOne_normalized_check

private def chartTwoOperand0 : {p : Poly3 // bellmanOperand% chartTwo 0 = p} := by
  recordBellmanOperand

private def chartTwoOperand1 : {p : Poly3 // bellmanOperand% chartTwo 1 = p} := by
  recordBellmanOperand

private def chartTwoOperand2 : {p : Poly3 // bellmanOperand% chartTwo 2 = p} := by
  recordBellmanOperand

private theorem chartTwo_normalized_check : allNonnegative3 chartTwo = true := by
  change allNonnegative3
    ((bellmanOperand% chartTwo 0) - (bellmanOperand% chartTwo 1)
      - (bellmanOperand% chartTwo 2)) = true
  rw [chartTwoOperand0.property, chartTwoOperand1.property, chartTwoOperand2.property]
  rfl

theorem chartTwo_check : allNonnegative3 chartTwo = true := by
  as_aux_lemma => exact chartTwo_normalized_check

private def chartThreeOperand0 : {p : Poly3 // bellmanOperand% chartThree 0 = p} := by
  recordBellmanOperand

private def chartThreeOperand1 : {p : Poly3 // bellmanOperand% chartThree 1 = p} := by
  recordBellmanOperand

private def chartThreeOperand2 : {p : Poly3 // bellmanOperand% chartThree 2 = p} := by
  recordBellmanOperand

private theorem chartThree_normalized_check : allNonnegative3 chartThree = true := by
  change allNonnegative3
    ((bellmanOperand% chartThree 0) - (bellmanOperand% chartThree 1)
      - (bellmanOperand% chartThree 2)) = true
  rw [chartThreeOperand0.property, chartThreeOperand1.property, chartThreeOperand2.property]
  rfl

theorem chartThree_check : allNonnegative3 chartThree = true := by
  as_aux_lemma => exact chartThree_normalized_check

private theorem chartEndpoint_normalized_check : allNonnegative3 chartEndpoint = true := by
  checkBellmanChart chartEndpoint projectiveBellmanAt

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

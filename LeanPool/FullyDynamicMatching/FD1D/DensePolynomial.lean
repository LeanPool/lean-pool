/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/
module

/-!
# Dense polynomial arithmetic

The Bellman certificate uses nested dense polynomials. Both the certificate
and its elaborator use these same coefficient operations.
-/

@[expose] public section

namespace FD1D.BellmanCertificate

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
def pow [Zero R] [One R] [Add R] [Mul R] (p : DPoly R) : Nat → DPoly R
  | 0 => const 1
  | n + 1 => mul (pow p n) p

instance : Zero (DPoly R) := ⟨⟨[]⟩⟩
instance [One R] : One (DPoly R) := ⟨const 1⟩
instance [Add R] : Add (DPoly R) := ⟨add⟩
instance [Neg R] : Neg (DPoly R) := ⟨neg⟩
instance [Neg R] [Add R] : Sub (DPoly R) := ⟨fun p q => p + -q⟩
instance [Zero R] [Add R] [Mul R] : Mul (DPoly R) := ⟨mul⟩
instance [Zero R] [One R] [Add R] [Mul R] : Pow (DPoly R) Nat := ⟨pow⟩
instance (n : Nat) [OfNat R (n + 2)] : OfNat (DPoly R) (n + 2) :=
  ⟨const (OfNat.ofNat (n + 2))⟩

@[simp] theorem coeffs_zero :
    (0 : DPoly R).coeffs = [] := rfl

@[simp] theorem coeffs_one [One R] :
    (1 : DPoly R).coeffs = [1] := rfl

@[simp] theorem coeffs_ofNat (n : Nat) [OfNat R (n + 2)] :
    (OfNat.ofNat (n + 2) : DPoly R).coeffs =
      [OfNat.ofNat (n + 2)] := rfl

/-- The indeterminate, with coefficient list `[0, 1]`. -/
def X [Zero R] [One R] : DPoly R := ⟨[0, 1]⟩

end DPoly

end FD1D.BellmanCertificate

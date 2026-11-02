/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.Weights
public import Mathlib.Data.Int.NatAbs
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! # Polynomial families in §2

Factorizations retain unit signs, since the left side of Theorem 1 uses absolute
values. The factors are irreducible over `ℚ` and pairwise nonassociated there.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

/-- The data of equation (9), including its arithmetic hypotheses. -/
structure PolynomialSystem (k r : ℕ) where
  /-- The original integer polynomial family. -/
  Q : Fin k → ℤ[X]
  /-- The distinct rationally irreducible factors. -/
  R : Fin r → ℤ[X]
  /-- Multiplicity of each irreducible factor in each original polynomial. -/
  exponent : Fin k → Fin r → ℕ
  /-- The unit coefficient in each polynomial's factorization. -/
  sign : Fin k → ℤ
  sign_abs : ∀ j, (sign j).natAbs = 1
  factorization : ∀ j, Q j = C (sign j) * ∏ h, R h ^ exponent j h
  irreducible : ∀ h, Irreducible ((R h).map (Int.castRingHom ℚ))
  nonassociated : ∀ i j, i ≠ j →
    ¬ Associated ((R i).map (Int.castRingHom ℚ)) ((R j).map (Int.castRingHom ℚ))
  exponent_pos : ∀ h, 0 < totalExponent exponent h
  noFixedPrime : NoFixedPrimeDivisor (∏ j, Q j)

namespace PolynomialSystem

/-- The product of the original polynomials of the system. -/
noncomputable def total {k r : ℕ} (P : PolynomialSystem k r) : ℤ[X] := ∏ j, P.Q j

/-- The product of the distinct irreducible factors of the system. -/
noncomputable def radical {k r : ℕ} (P : PolynomialSystem k r) : ℤ[X] := ∏ h, P.R h

/-- Absolute discriminant `|D*|`. -/
noncomputable def discriminant {k r : ℕ} (P : PolynomialSystem k r) : ℕ :=
  P.radical.discr.natAbs

/-- The factor `D` in §2, retaining exactly the bad primes where `Q` has roots. -/
noncomputable def badDiscriminant {k r : ℕ} (P : PolynomialSystem k r) : ℕ :=
  ∏ p ∈ P.discriminant.primeFactors.filter (fun p => rootCount P.total p ≠ 0),
    p ^ P.discriminant.factorization p

/-- The root count vector in (10). -/
noncomputable def rootVector {k r : ℕ} (P : PolynomialSystem k r) (h : Fin r) (n : ℕ) : ℝ :=
  rootCount (P.R h) n

/-- The weight (16) for the actual factorization of `Q`. -/
noncomputable def weight {k r : ℕ} (P : PolynomialSystem k r) (F : ArithmeticMap k)
    (N : ℕ+) : ℝ := NairTenenbaum.weight P.exponent P.discriminant F P.rootVector N

theorem weight_nonneg {k r : ℕ} (P : PolynomialSystem k r) {F : ArithmeticMap k}
    (hF : ∀ n, 0 ≤ F n) (N : ℕ+) : 0 ≤ P.weight F N :=
  NairTenenbaum.weight_nonneg _ _ hF (fun _ _ => Nat.cast_nonneg _) N

theorem abs_eval_factorization {k r : ℕ} (P : PolynomialSystem k r) (j : Fin k) (n : ℤ) :
    ((P.Q j).eval n).natAbs = ∏ h, ((P.R h).eval n).natAbs ^ P.exponent j h := by
  rw [P.factorization j]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_pow,
    Int.natAbs_mul, P.sign_abs, one_mul]
  change Int.natAbsHom (∏ h, (P.R h).eval n ^ P.exponent j h) = _
  rw [map_prod]
  simp

theorem badDiscriminant_pos {k r : ℕ} (P : PolynomialSystem k r) :
    0 < P.badDiscriminant := by
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos _

end PolynomialSystem

/-- Coefficient height `‖Q‖ = max_i |a_i|`. -/
def polynomialHeight (Q : ℤ[X]) : ℕ := Q.support.sup fun i => (Q.coeff i).natAbs

/-- Extension by zero when a coordinate is zero. This makes polynomial-root terms
explicit; on positive tuples it is precisely the original arithmetic function. -/
noncomputable def extendArithmeticMap {k : ℕ} (F : ArithmeticMap k) (n : Fin k → ℕ) : ℝ :=
  if h : ∀ j, 0 < n j then F (fun j => ⟨n j, h j⟩) else 0

@[simp] theorem extendArithmeticMap_coe {k : ℕ} (F : ArithmeticMap k) (n : Tuple k) :
    extendArithmeticMap F (fun j => (n j : ℕ)) = F n := by
  unfold extendArithmeticMap
  rw [dite_eq_left (fun j => (n j).pos)]
  rfl

theorem extendArithmeticMap_nonneg {k : ℕ} {F : ArithmeticMap k} (hF : ∀ n, 0 ≤ F n)
    (n : Fin k → ℕ) : 0 ≤ extendArithmeticMap F n := by
  unfold extendArithmeticMap
  split_ifs
  · exact hF _
  · rfl

/-- Natural numbers in `(x,x+y]`, for the positive real ranges in the theorems. -/
noncomputable def shortInterval (x y : ℝ) : Finset ℕ := Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊

/-- Left side of (18). -/
noncomputable def shortSum {k : ℕ} (Q : Fin k → ℤ[X]) (F : ArithmeticMap k) (x y : ℝ) : ℝ :=
  ∑ n ∈ shortInterval x y, extendArithmeticMap F (fun j => ((Q j).eval (n : ℤ)).natAbs)

/-- Positive integers at most `x`. The filter also handles `x < 1` correctly. -/
noncomputable def positiveUpTo (x : ℝ) : Finset ℕ+ :=
  (Finset.Icc 1 (Nat.toPNat' ⌊x⌋₊)).filter fun n => (n : ℝ) ≤ x

@[simp] theorem mem_positiveUpTo (n : ℕ+) (x : ℝ) :
    n ∈ positiveUpTo x ↔ (n : ℝ) ≤ x := by
  classical
  simp only [positiveUpTo, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨fun h => h.2, fun h => ⟨⟨one_le, ?_⟩, h⟩⟩
  have hx : 0 ≤ x := le_trans (by positivity : (0 : ℝ) ≤ n) h
  have hn : (n : ℕ) ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx).mpr h
  have hp : 0 < ⌊x⌋₊ := lt_of_lt_of_le n.pos hn
  change (n : ℕ) ≤ (Nat.toPNat' ⌊x⌋₊ : ℕ)
  rwa [PNat.toPNat'_coe hp]

theorem positiveUpTo_eq_Icc {x : ℝ} (hx : 1 ≤ x) :
    positiveUpTo x = Finset.Icc 1 (Nat.toPNat' ⌊x⌋₊) := by
  classical
  have hfloor : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr hx
  ext n
  rw [mem_positiveUpTo, Finset.mem_Icc]
  have hn : (n : ℝ) ≤ x ↔ (n : ℕ) ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith)).symm
  rw [hn]
  change (n : ℕ) ≤ ⌊x⌋₊ ↔ 1 ≤ n ∧ (n : ℕ) ≤ (Nat.toPNat' ⌊x⌋₊ : ℕ)
  rw [PNat.toPNat'_coe hfloor]
  exact ⟨fun h => ⟨one_le, h⟩, And.right⟩

theorem positiveUpTo_eq_empty {x : ℝ} (hx : x < 1) : positiveUpTo x = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  have h := (mem_positiveUpTo n x).mp hn
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  linarith

/-- The right side of (18), without the implicit constant. -/
noncomputable def mainTerm {k r : ℕ} (P : PolynomialSystem k r)
    (F : ArithmeticMap k) (x y : ℝ) : ℝ :=
  y * sieveProduct P.total x * ∑ n ∈ positiveUpTo x, P.weight F n

theorem mainTerm_nonneg {k r : ℕ} (P : PolynomialSystem k r) {F : ArithmeticMap k}
    (hF : ∀ n, 0 ≤ F n) (x : ℝ) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ mainTerm P F x y :=
  mul_nonneg (mul_nonneg hy (sieveProduct_pos P.noFixedPrime x).le)
    (Finset.sum_nonneg fun n _ => P.weight_nonneg hF n)

end NairTenenbaum

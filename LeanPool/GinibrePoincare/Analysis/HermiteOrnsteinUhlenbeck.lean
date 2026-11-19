/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/HermiteOrnsteinUhlenbeck.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.NormalizedComplexHermite
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.Basic

/-!
# Hermite ornstein uhlenbeck

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `ornsteinUhlenbeck_normalized`.
-/

@[expose] public section

open scoped BigOperators
namespace GinibrePoincare.ComplexHermite
noncomputable section

private def rawCoefficient (ρ : ℝ) (p q k : ℕ) : ℂ :=
  (-(ρ : ℂ))^k * (k.factorial : ℂ) * (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ)

private def weightedRaw (ρ : ℝ) (p q : ℕ) : Poly :=
  ∑ k ∈ Finset.range (min p q + 1),
    (k : Poly) * (MvPolynomial.C (rawCoefficient ρ p q k) * Z^(p-k) * W^(q-k))

private theorem euler_monomial (c : ℂ) (a b : ℕ) :
    Z * MvPolynomial.pderiv 0 (MvPolynomial.C c * Z^a * W^b) +
    W * MvPolynomial.pderiv 1 (MvPolynomial.C c * Z^a * W^b) =
      ((a + b : ℕ) : Poly) * (MvPolynomial.C c * Z^a * W^b) := by
  have hm : MvPolynomial.C c * Z^a * W^b =
      MvPolynomial.monomial (Finsupp.single 0 a + Finsupp.single 1 b) c := by
    rw [MvPolynomial.monomial_add_single, ← MvPolynomial.C_mul_X_pow_eq_monomial]
    rfl
  rw [hm]
  simp only [Z, W, MvPolynomial.X_mul_pderiv_monomial, Finsupp.add_apply,
    Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
    Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), add_zero, zero_add,
    nsmul_eq_mul, Nat.cast_add]
  ring

private theorem euler_raw (ρ : ℝ) (p q : ℕ) :
    Z * MvPolynomial.pderiv 0 (raw ρ p q) + W * MvPolynomial.pderiv 1 (raw ρ p q) =
      ((p + q : ℕ) : Poly) * raw ρ p q - 2 * weightedRaw ρ p q := by
  simp only [raw, weightedRaw, rawCoefficient, map_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [euler_monomial]
  have hkp : k ≤ p := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)).trans (min_le_left _ _)
  have hkq : k ≤ q := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)).trans (min_le_right _ _)
  rw [Nat.cast_add, Nat.cast_sub hkp, Nat.cast_sub hkq, Nat.cast_add]
  ring

private theorem coefficient_shift (ρ : ℝ) (p q k : ℕ) :
    (k + 1 : ℂ) * rawCoefficient ρ (p+1) (q+1) (k+1) =
      -(ρ : ℂ) * (p+1 : ℂ) * (q+1 : ℂ) * rawCoefficient ρ p q k := by
  have hp := congrArg (fun t : ℕ => (t : ℂ)) (Nat.add_one_mul_choose_eq p k)
  have hq := congrArg (fun t : ℕ => (t : ℂ)) (Nat.add_one_mul_choose_eq q k)
  push_cast at hp hq
  simp only [rawCoefficient, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  calc
    _ = -(ρ : ℂ) * (-(ρ : ℂ))^k * (k.factorial : ℂ) *
        ((Nat.choose (p+1) (k+1) : ℂ) * (k+1)) *
        ((Nat.choose (q+1) (k+1) : ℂ) * (k+1)) := by ring
    _ = _ := by rw [← hp, ← hq]; ring

private theorem weightedRaw_succ (ρ : ℝ) (p q : ℕ) :
    weightedRaw ρ (p+1) (q+1) =
      MvPolynomial.C (-(ρ : ℂ) * (p+1) * (q+1)) * raw ρ p q := by
  rw [weightedRaw, show min (p+1) (q+1) = min p q + 1 by omega, Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero]
  rw [raw, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [show p + 1 - (k+1) = p-k by omega, show q + 1 - (k+1) = q-k by omega]
  have hc := congrArg (MvPolynomial.C : ℂ →+* Poly) (coefficient_shift ρ p q k)
  simp only [MvPolynomial.C_mul] at hc
  change ((k+1 : ℕ) : Poly) * (MvPolynomial.C (rawCoefficient ρ (p+1) (q+1) (k+1)) * _ * _) = _
  rw [mul_assoc, mul_assoc, ← mul_assoc (((k+1 : ℕ) : Poly))]
  rw [show ((k+1 : ℕ) : Poly) = MvPolynomial.C (k+1 : ℂ) by simp]
  rw [hc]
  simp only [rawCoefficient, mul_assoc, map_mul]

/-- The exact two-variable Ornstein–Uhlenbeck equation for raw complex Hermite polynomials. -/
theorem ornsteinUhlenbeck_raw (ρ : ℝ) (p q : ℕ) :
    2 * MvPolynomial.C (ρ : ℂ) * MvPolynomial.pderiv 1 (MvPolynomial.pderiv 0 (raw ρ p q)) -
      (Z * MvPolynomial.pderiv 0 (raw ρ p q) + W * MvPolynomial.pderiv 1 (raw ρ p q)) =
        -((p+q : ℕ) : Poly) * raw ρ p q := by
  rw [euler_raw]
  have hmixed : MvPolynomial.C (ρ : ℂ) *
      MvPolynomial.pderiv 1 (MvPolynomial.pderiv 0 (raw ρ p q)) = -weightedRaw ρ p q := by
    cases p with
    | zero => simp [raw_zero_left, W, weightedRaw]
    | succ p =>
      cases q with
      | zero => simp [raw_zero_right, Z, weightedRaw]
      | succ q =>
        rw [pderiv_Z_raw, MvPolynomial.pderiv_mul, pderiv_W_raw]
        simp only [Nat.succ_sub_one, Derivation.map_natCast, zero_mul, zero_add]
        rw [weightedRaw_succ]
        simp only [map_mul, map_neg, map_add, map_one, map_natCast, Nat.cast_add, Nat.cast_one]
        ring
  linear_combination 2 * hmixed

/-- The normalized variance-one Hermite polynomial has OU eigenvalue `-2(a+b)`. -/
theorem ornsteinUhlenbeck_normalized (p q : ℕ) :
    4 * MvPolynomial.pderiv 1 (MvPolynomial.pderiv 0 (normalized 1 (by decide) p q)) -
      2 * (Z * MvPolynomial.pderiv 0 (normalized 1 (by decide) p q) +
        W * MvPolynomial.pderiv 1 (normalized 1 (by decide) p q)) =
      -2 * ((p+q : ℕ) : Poly) * normalized 1 (by decide) p q := by
  have h := ornsteinUhlenbeck_raw 1 p q
  simp only [Complex.ofReal_one, MvPolynomial.C_1, mul_one] at h
  unfold normalized
  simp only [Nat.cast_one, inv_one, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C,
    zero_mul, zero_add]
  linear_combination 2 * MvPolynomial.C
    ((oneDimNormalization 1 p * oneDimNormalization 1 q : ℝ) : ℂ) * h

end
end GinibrePoincare.ComplexHermite

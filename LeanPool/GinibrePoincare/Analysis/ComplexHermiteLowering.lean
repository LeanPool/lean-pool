/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/ComplexHermiteLowering.lean.
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

public import LeanPool.GinibrePoincare.Analysis.ComplexHermite

/-!
# Formal lowering identities for complex Hermite polynomials

The two formal partial derivatives lower the corresponding bidegree of the
raw complex Hermite polynomial, with coefficients `p` and `q`.  These are the
algebraic identities underlying the Wirtinger lowering relations after
specializing the two variables to `z` and `conj z`.
-/


@[expose] public section


namespace GinibrePoincare

open scoped BigOperators

namespace ComplexHermite

private theorem raw_eq_sum_range_right (ρ : ℝ) (p q : ℕ) :
    raw ρ p q =
      ∑ k ∈ Finset.range (q + 1),
        MvPolynomial.C (((-(ρ : ℂ)) ^ k) * (k.factorial : ℂ) *
          (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ)) *
          Z ^ (p - k) * W ^ (q - k) := by
  rw [raw]
  apply Finset.sum_subset
  · exact Finset.range_mono (Nat.succ_le_succ (min_le_right p q))
  · intro k hkq hkmin
    have hkq' : k ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hkq)
    have hpk : p < k := by
      by_contra h
      have hkp : k ≤ p := Nat.le_of_not_gt h
      exact hkmin (Finset.mem_range.mpr (Nat.lt_succ_of_le (le_min hkp hkq')))
    simp [Nat.choose_eq_zero_of_lt hpk]

private theorem raw_eq_sum_range_left (ρ : ℝ) (p q : ℕ) :
    raw ρ p q =
      ∑ k ∈ Finset.range (p + 1),
        MvPolynomial.C (((-(ρ : ℂ)) ^ k) * (k.factorial : ℂ) *
          (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ)) *
          Z ^ (p - k) * W ^ (q - k) := by
  rw [raw]
  apply Finset.sum_subset
  · exact Finset.range_mono (Nat.succ_le_succ (min_le_left p q))
  · intro k hkp hkmin
    have hkp' : k ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hkp)
    have hqk : q < k := by
      by_contra h
      have hkq : k ≤ q := Nat.le_of_not_gt h
      exact hkmin (Finset.mem_range.mpr (Nat.lt_succ_of_le (le_min hkp' hkq)))
    simp [Nat.choose_eq_zero_of_lt hqk]

/-- Formal differentiation in the holomorphic variable lowers the first
bidegree, with the exact unnormalized coefficient `p`. -/
theorem pderiv_Z_raw (ρ : ℝ) (p q : ℕ) :
    MvPolynomial.pderiv (0 : ComplexHermiteIndex) (raw ρ p q) =
      (p : Poly) * raw ρ (p - 1) q := by
  cases p with
  | zero => rw [pderiv_Z_raw_zero_left]; simp
  | succ p =>
      rw [raw_eq_sum_range_right, raw_eq_sum_range_right]
      simp only [map_sum, MvPolynomial.pderiv_C, MvPolynomial.pderiv_mul,
        MvPolynomial.pderiv_pow, Z, W, MvPolynomial.pderiv_X_self,
        MvPolynomial.pderiv_X_of_ne (by decide : (1 : ComplexHermiteIndex) ≠ 0),
        mul_zero, add_zero, mul_one, Nat.succ_sub_one, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hnat : Nat.choose (p + 1) k * (p + 1 - k) =
          (p + 1) * Nat.choose p k := by
        simpa [Nat.mul_comm] using (Nat.choose_mul_succ_eq p k).symm
      have hcoef := congrArg (fun n : ℕ => (n : ℂ)) hnat
      simp only [Nat.cast_mul] at hcoef
      rw [show p + 1 - k - 1 = p - k by omega]
      push_cast at hcoef
      simp only [zero_mul, zero_add]
      have hc :
          MvPolynomial.C ((-(ρ : ℂ)) ^ k * (k.factorial : ℂ) *
              (Nat.choose (p + 1) k : ℂ) * (Nat.choose q k : ℂ)) *
              ((p + 1 - k : ℕ) : Poly) =
            ((p + 1 : ℕ) : Poly) *
              MvPolynomial.C ((-(ρ : ℂ)) ^ k * (k.factorial : ℂ) *
                (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ)) := by
        rw [show ((p + 1 - k : ℕ) : Poly) =
              MvPolynomial.C ((p + 1 - k : ℕ) : ℂ) by rfl,
          show ((p + 1 : ℕ) : Poly) = MvPolynomial.C ((p + 1 : ℕ) : ℂ) by rfl,
          ← MvPolynomial.C_mul, ← MvPolynomial.C_mul]
        congr 1
        calc
          _ = ((-(ρ : ℂ)) ^ k * (k.factorial : ℂ) *
                (Nat.choose q k : ℂ)) *
              ((Nat.choose (p + 1) k : ℂ) * (p + 1 - k : ℕ)) := by ring
          _ = ((-(ρ : ℂ)) ^ k * (k.factorial : ℂ) *
                (Nat.choose q k : ℂ)) *
              (((p : ℂ) + 1) * (Nat.choose p k : ℂ)) := by rw [hcoef]
          _ = _ := by
            simp only [Nat.cast_add, Nat.cast_one]
            ring
      calc
        _ = (MvPolynomial.C ((-(ρ : ℂ)) ^ k * (k.factorial : ℂ) *
              (Nat.choose (p + 1) k : ℂ) * (Nat.choose q k : ℂ)) *
              ((p + 1 - k : ℕ) : Poly)) *
              MvPolynomial.X 0 ^ (p - k) * MvPolynomial.X 1 ^ (q - k) := by ring
        _ = (((p + 1 : ℕ) : Poly) *
              MvPolynomial.C ((-(ρ : ℂ)) ^ k * (k.factorial : ℂ) *
                (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ))) *
              MvPolynomial.X 0 ^ (p - k) * MvPolynomial.X 1 ^ (q - k) := by rw [hc]
        _ = _ := by push_cast; ring

/-- Formal differentiation in the antiholomorphic variable lowers the second
bidegree, with the exact unnormalized coefficient `q`. -/
theorem pderiv_W_raw (ρ : ℝ) (p q : ℕ) :
    MvPolynomial.pderiv (1 : ComplexHermiteIndex) (raw ρ p q) =
      (q : Poly) * raw ρ p (q - 1) := by
  cases q with
  | zero => rw [pderiv_W_raw_zero_right]; simp
  | succ q =>
      rw [raw_eq_sum_range_left, raw_eq_sum_range_left]
      simp only [map_sum, MvPolynomial.pderiv_C, MvPolynomial.pderiv_mul,
        MvPolynomial.pderiv_pow, Z, W, MvPolynomial.pderiv_X_self,
        MvPolynomial.pderiv_X_of_ne (by decide : (0 : ComplexHermiteIndex) ≠ 1),
        mul_zero, zero_mul, add_zero, mul_one, Nat.succ_sub_one, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hnat : Nat.choose (q + 1) k * (q + 1 - k) =
          (q + 1) * Nat.choose q k := by
        simpa [Nat.mul_comm] using (Nat.choose_mul_succ_eq q k).symm
      have hcoef := congrArg (fun n : ℕ => (n : ℂ)) hnat
      simp only [Nat.cast_mul] at hcoef
      rw [show q + 1 - k - 1 = q - k by omega]
      push_cast at hcoef
      simp only [zero_add]
      have hc :
          MvPolynomial.C ((-(ρ : ℂ)) ^ k * (k.factorial : ℂ) *
              (Nat.choose p k : ℂ) * (Nat.choose (q + 1) k : ℂ)) *
              ((q + 1 - k : ℕ) : Poly) =
            ((q + 1 : ℕ) : Poly) *
              MvPolynomial.C ((-(ρ : ℂ)) ^ k * (k.factorial : ℂ) *
                (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ)) := by
        rw [show ((q + 1 - k : ℕ) : Poly) =
              MvPolynomial.C ((q + 1 - k : ℕ) : ℂ) by rfl,
          show ((q + 1 : ℕ) : Poly) = MvPolynomial.C ((q + 1 : ℕ) : ℂ) by rfl,
          ← MvPolynomial.C_mul, ← MvPolynomial.C_mul]
        congr 1
        calc
          _ = ((-(ρ : ℂ)) ^ k * (k.factorial : ℂ) *
                (Nat.choose p k : ℂ)) *
              ((Nat.choose (q + 1) k : ℂ) * (q + 1 - k : ℕ)) := by ring
          _ = ((-(ρ : ℂ)) ^ k * (k.factorial : ℂ) *
                (Nat.choose p k : ℂ)) *
              (((q : ℂ) + 1) * (Nat.choose q k : ℂ)) := by rw [hcoef]
          _ = _ := by
            simp only [Nat.cast_add, Nat.cast_one]
            ring
      calc
        _ = (MvPolynomial.C ((-(ρ : ℂ)) ^ k * (k.factorial : ℂ) *
              (Nat.choose p k : ℂ) * (Nat.choose (q + 1) k : ℂ)) *
              ((q + 1 - k : ℕ) : Poly)) *
              MvPolynomial.X 0 ^ (p - k) * MvPolynomial.X 1 ^ (q - k) := by ring
        _ = (((q + 1 : ℕ) : Poly) *
              MvPolynomial.C ((-(ρ : ℂ)) ^ k * (k.factorial : ℂ) *
                (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ))) *
              MvPolynomial.X 0 ^ (p - k) * MvPolynomial.X 1 ^ (q - k) := by rw [hc]
        _ = _ := by push_cast; ring

end ComplexHermite
end GinibrePoincare

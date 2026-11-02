/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hilbert.FilteredIntersection

/-!
# The affine Hilbert degree of a curve

An affine algebraic set is represented by an ideal in `ℚ[x₁,…,xₙ]`. For an integral curve,
its degree is the slope of the eventually linear affine Hilbert function: the dimension
of polynomials of total degree at most `M` in its coordinate ring is `d*M + c` for large `M`.
The slope of an eventually linear function is unique, and a pointwise inequality between two
eventually linear functions compares their slopes (`eventual_linear_slope_le`).
-/

@[expose] public section

namespace CCDN

/-- The polynomial ring `ℚ[x₁, …, xₙ]` in which affine algebraic sets are cut out. -/
abbrev CoordinatePolynomial (n : ℕ) := MvPolynomial (Fin n) ℚ

/-- The affine Hilbert function: the dimension of the polynomials of total degree at
most `M` in the coordinate ring. -/
noncomputable def affineHilbertFunction {n : ℕ} (I : Ideal (CoordinatePolynomial n))
    (M : ℕ) : ℕ := Module.finrank ℚ (filteredCoordinateSpace I M)

/-- Degree via the eventual affine Hilbert polynomial. This condition is mathematical
data about the coordinate ring, and contains no point-counting estimate. -/
def HasAffineCurveDegree {n : ℕ} (I : Ideal (CoordinatePolynomial n)) (d : ℕ) : Prop :=
  ∃ N : ℕ, ∃ c : ℤ, ∀ M : ℕ, N ≤ M →
    (affineHilbertFunction I M : ℤ) = (d : ℤ) * M + c

/-- The affine Hilbert degree of a curve is unique: if `I` has affine curve degree `d` and `e`, then
`d = e`. -/
theorem affineCurveDegree_unique {n : ℕ} {I : Ideal (CoordinatePolynomial n)} {d e : ℕ}
    (hd : HasAffineCurveDegree I d) (he : HasAffineCurveDegree I e) : d = e := by
  obtain ⟨N, c, hN⟩ := hd
  obtain ⟨P, k, hP⟩ := he
  have hN0 := hN (max N P) (le_max_left _ _)
  have hP0 := hP (max N P) (le_max_right _ _)
  have hN1 := hN (max N P + 1) (by omega)
  have hP1 := hP (max N P + 1) (by omega)
  push_cast at hN0 hP0 hN1 hP1
  have hde : (d : ℤ) = e := by nlinarith
  exact_mod_cast hde

/-- Pointwise domination of eventually linear functions compares their slopes. -/
lemma eventual_linear_slope_le (f g : ℕ → ℕ) (a b : ℕ)
    (hf : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N, (f n : ℤ) = (a : ℤ) * n + c)
    (hg : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N, (g n : ℤ) = (b : ℤ) * n + c)
    (hle : ∀ n, f n ≤ g n) : a ≤ b := by
  obtain ⟨N₀, c, hc⟩ := hf
  obtain ⟨N₁, e, he⟩ := hg
  by_contra hbad
  have hab : b + 1 ≤ a := by omega
  let N := N₀ + N₁ + c.natAbs + e.natAbs + 1
  have hN₀ : N₀ ≤ N := by dsimp [N]; omega
  have hN₁ : N₁ ≤ N := by dsimp [N]; omega
  have hh : (a : ℤ) * N + c ≤ (b : ℤ) * N + e := by
    rw [← hc N hN₀, ← he N hN₁]
    exact_mod_cast hle N
  have hmul : ((b : ℤ) + 1) * N ≤ (a : ℤ) * N := by
    exact_mod_cast Nat.mul_le_mul_right N hab
  have hce : -(c.natAbs : ℤ) ≤ c := by
    have hh : -c ≤ ((-c).natAbs : ℤ) := Int.le_natAbs
    simp only [Int.natAbs_neg] at hh
    omega
  have hee : e ≤ (e.natAbs : ℤ) := Int.le_natAbs
  have hNeq : (N : ℤ) = N₀ + N₁ + c.natAbs + e.natAbs + 1 := by
    simp only [N, Nat.cast_add, Nat.cast_one]
  nlinarith

end CCDN

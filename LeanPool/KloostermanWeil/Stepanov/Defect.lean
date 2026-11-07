/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import LeanPool.KloostermanWeil.Stepanov.Parameters
public import LeanPool.KloostermanWeil.Stepanov.CurveCount
public import Mathlib.FieldTheory.Separable


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# Square-root point-count estimates

Combines the auxiliary polynomial with Euler’s criterion to bound two combinations of
the curve’s point-count fibers. Reference: Harcos (2015), §5, equations (11)–(14);
Stepanov (1972).
-/

@[expose] public section

open Polynomial

namespace KloostermanWeil.Stepanov

/-- A polynomial of the form `h²-k` with `h'=-1`, nonzero `k`, and odd
characteristic is separable.  The proof supplies the Bézout identity
explicitly. -/
theorem separable_sq_sub_C_of_derivative_eq_neg_one
    {F : Type*} [Field F] (h : F[X]) (k : F)
    (hh : derivative h = -1) (hk : k ≠ 0)
    (h2 : (2 : F) ≠ 0) : (h ^ 2 - C k).Separable := by
  rw [separable_def']
  let A : F[X] := C (-k⁻¹)
  let B : F[X] := C (-(2 * k)⁻¹) * h
  refine ⟨A, B, ?_⟩
  have hk2 : (2 : F) * k ≠ 0 := mul_ne_zero h2 hk
  have hder : derivative (h ^ 2 - C k) = C (-2) * h := by
    rw [derivative_sub, derivative_pow, derivative_C, hh]
    simp only [Nat.cast_ofNat, pow_succ, pow_zero, sub_zero]
    simp [C_neg]
  rw [hder]
  dsimp [A, B]
  have hkinv : k⁻¹ * k = 1 := inv_mul_cancel₀ hk
  have hcoef : (-(2 * k)⁻¹) * (-2) = k⁻¹ := by
    field_simp
  have hneg : (-k⁻¹) * k = -1 := by rw [neg_mul, hkinv]
  calc
    C (-k⁻¹) * (h ^ 2 - C k) +
        C (-(2 * k)⁻¹) * h * (C (-2) * h) =
      C (-k⁻¹) * h ^ 2 - C ((-k⁻¹) * k) +
        C ((-(2 * k)⁻¹) * (-2)) * h ^ 2 := by
          rw [C_mul, C_mul]
          ring
    _ = C (-k⁻¹) * h ^ 2 - C (-1) + C k⁻¹ * h ^ 2 := by
      rw [hcoef, hneg]
    _ = 1 := by
      simp [C_neg]

/-- A separable polynomial of positive degree cannot be a nonzero scalar
times a square. -/
theorem not_isScalarSquare_of_separable
    {F : Type*} [Field F] (f : F[X])
    (hsep : f.Separable) (hdeg : 0 < f.natDegree) :
    ¬ IsScalarSquare f := by
  intro hs
  obtain ⟨c, hc, g, rfl⟩ := hs
  have hgunit : IsUnit g := by
    apply isUnit_of_self_mul_dvd_separable hsep
    refine ⟨C c, ?_⟩
    ring
  have hfun : IsUnit (C c * g ^ 2) :=
    (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)).mul
      (hgunit.pow 2)
  have hndeg := natDegree_eq_zero_of_isUnit hfun
  omega

/-- The raw one-sided Stepanov bound for `N₀+N₁`. -/
theorem stepanov_zero_or_one_raw_bound
    {F : Type*} [Field F] [Fintype F]
    {p n : ℕ} [Fact p.Prime] [CharP F p]
    (hcard : Fintype.card F = p ^ n)
    (hpodd : Odd p)
    (f : F[X]) (hf : f ≠ 0) (hm : 3 < f.natDegree)
    (hlarge : 100 * (f.natDegree + 1) *
      (Nat.sqrt (p ^ n) + 1) < p ^ n)
    (hf0 : f.coeff 0 ≠ 0) (hnsq : ¬ IsScalarSquare f) :
    let q := p ^ n
    let l := Nat.sqrt q + 1
    let d := (q - f.natDegree) ⌈/⌉ 2
    let J := (l + 1) / 2 + 10 * (f.natDegree + 1)
    l * (quadraticZeroOrValueFinset f 1).card <
      f.natDegree * (l + ((q - 1) / 2)) + d + J * q := by
  classical
  dsimp
  have hqodd : Odd (p ^ n) := hpodd.pow
  have hqoddF : Odd (Fintype.card F) := by simpa [hcard] using hqodd
  have hF : ringChar F ≠ 2 := by
    rw [ringChar.eq F p]
    obtain ⟨k, hk⟩ := hpodd
    omega
  rw [quadraticZeroOrOne_eq_stepanovValueFinset hF hqoddF]
  unfold stepanovValueFinset
  simpa only [hcard] using
    stepanov_point_set_sqrt_bound hcard f (1 : F) hf hm hqodd
      hlarge hf0 hnsq

/-- The raw one-sided Stepanov bound for `N₀+N₋₁`. -/
theorem stepanov_zero_or_neg_one_raw_bound
    {F : Type*} [Field F] [Fintype F]
    {p n : ℕ} [Fact p.Prime] [CharP F p]
    (hcard : Fintype.card F = p ^ n)
    (hpodd : Odd p)
    (f : F[X]) (hf : f ≠ 0) (hm : 3 < f.natDegree)
    (hlarge : 100 * (f.natDegree + 1) *
      (Nat.sqrt (p ^ n) + 1) < p ^ n)
    (hf0 : f.coeff 0 ≠ 0) (hnsq : ¬ IsScalarSquare f) :
    let q := p ^ n
    let l := Nat.sqrt q + 1
    let d := (q - f.natDegree) ⌈/⌉ 2
    let J := (l + 1) / 2 + 10 * (f.natDegree + 1)
    l * (quadraticZeroOrValueFinset f (-1)).card <
      f.natDegree * (l + ((q - 1) / 2)) + d + J * q := by
  classical
  dsimp
  have hqodd : Odd (p ^ n) := hpodd.pow
  have hqoddF : Odd (Fintype.card F) := by simpa [hcard] using hqodd
  have hF : ringChar F ≠ 2 := by
    rw [ringChar.eq F p]
    obtain ⟨k, hk⟩ := hpodd
    omega
  rw [quadraticZeroOrNegOne_eq_stepanovValueFinset hF hqoddF]
  unfold stepanovValueFinset
  simpa only [hcard] using
    stepanov_point_set_sqrt_bound hcard f (-1 : F) hf hm hqodd
      hlarge hf0 hnsq

/-- Explicit square-root form of the `N₀+N₁` estimate. -/
theorem stepanov_zero_or_one_sqrt_bound
    {F : Type*} [Field F] [Fintype F]
    {p n : ℕ} [Fact p.Prime] [CharP F p]
    (hcard : Fintype.card F = p ^ n)
    (hpodd : Odd p)
    (f : F[X]) (hf : f ≠ 0) (hm : 3 < f.natDegree)
    (hlarge : 100 * (f.natDegree + 1) *
      (Nat.sqrt (p ^ n) + 1) < p ^ n)
    (hf0 : f.coeff 0 ≠ 0) (hnsq : ¬ IsScalarSquare f) :
    (quadraticZeroOrValueFinset f 1).card <
      (p ^ n + 1) / 2 +
        40 * (f.natDegree + 1) * (Nat.sqrt (p ^ n) + 1) := by
  classical
  apply stepanov_raw_bound_to_sqrt hm hlarge
  exact stepanov_zero_or_one_raw_bound hcard hpodd f hf hm
    hlarge hf0 hnsq

/-- Explicit square-root form of the `N₀+N₋₁` estimate. -/
theorem stepanov_zero_or_neg_one_sqrt_bound
    {F : Type*} [Field F] [Fintype F]
    {p n : ℕ} [Fact p.Prime] [CharP F p]
    (hcard : Fintype.card F = p ^ n)
    (hpodd : Odd p)
    (f : F[X]) (hf : f ≠ 0) (hm : 3 < f.natDegree)
    (hlarge : 100 * (f.natDegree + 1) *
      (Nat.sqrt (p ^ n) + 1) < p ^ n)
    (hf0 : f.coeff 0 ≠ 0) (hnsq : ¬ IsScalarSquare f) :
    (quadraticZeroOrValueFinset f (-1)).card <
      (p ^ n + 1) / 2 +
        40 * (f.natDegree + 1) * (Nat.sqrt (p ^ n) + 1) := by
  classical
  apply stepanov_raw_bound_to_sqrt hm hlarge
  exact stepanov_zero_or_neg_one_raw_bound hcard hpodd f hf hm
    hlarge hf0 hnsq

/-- Pure arithmetic form of the passage from the two one-sided estimates to
the square-versus-nonsquare defect. -/
theorem abs_character_fiber_defect_lt
    {q A B N0 N1 Nm E : ℕ}
    (hqodd : Odd q)
    (hpart : N0 + N1 + Nm = q)
    (hAeq : A = N0 + N1) (hBeq : B = N0 + Nm)
    (hA : A < (q + 1) / 2 + E)
    (hB : B < (q + 1) / 2 + E) :
    |(N1 : ℤ) - (Nm : ℤ)| < (2 * E + 1 : ℕ) := by
  obtain ⟨k, hk⟩ := hqodd
  by_cases hle : N1 ≤ Nm
  · rw [abs_of_nonpos]
    · push_cast
      omega
    · exact sub_nonpos.mpr (by exact_mod_cast hle)
  · rw [abs_of_pos]
    · push_cast
      omega
    · exact sub_pos.mpr (by exact_mod_cast (Nat.lt_of_not_ge hle))

/-- Uniform high-extension-field point-count estimate obtained from the two
Stepanov fibers.  Its constant is independent of the extension degree. -/
theorem stepanov_hyperelliptic_defect_high_field
    {F : Type*} [Field F] [Fintype F]
    {p n : ℕ} [Fact p.Prime] [CharP F p]
    (hcard : Fintype.card F = p ^ n)
    (hpodd : Odd p)
    (f : F[X]) (hf : f ≠ 0) (hm : 3 < f.natDegree)
    (hlarge : 100 * (f.natDegree + 1) *
      (Nat.sqrt (p ^ n) + 1) < p ^ n)
    (hf0 : f.coeff 0 ≠ 0) (hnsq : ¬ IsScalarSquare f) :
    |((hyperellipticAffinePointFinset f).card : ℤ) - (p ^ n : ℕ)| <
      (80 * (f.natDegree + 1) * (Nat.sqrt (p ^ n) + 1) + 1 : ℕ) := by
  classical
  have hqodd : Odd (p ^ n) := hpodd.pow
  have hF : ringChar F ≠ 2 := by
    rw [ringChar.eq F p]
    obtain ⟨k, hk⟩ := hpodd
    omega
  have hcardZ : ((p ^ n : ℕ) : ℤ) = (Fintype.card F : ℤ) := by
    exact_mod_cast hcard.symm
  rw [hcardZ, hyperellipticAffinePoint_defect_eq hF]
  have hpart := quadraticValueFinset_card_partition f
  rw [hcard] at hpart
  have hAeq := quadraticZeroOrValueFinset_card f (by norm_num : (1 : ℤ) ≠ 0)
  have hBeq := quadraticZeroOrValueFinset_card f (by norm_num : (-1 : ℤ) ≠ 0)
  have hA := stepanov_zero_or_one_sqrt_bound hcard hpodd f hf hm
    hlarge hf0 hnsq
  have hB := stepanov_zero_or_neg_one_sqrt_bound hcard hpodd f hf hm
    hlarge hf0 hnsq
  have h := abs_character_fiber_defect_lt hqodd hpart hAeq hBeq hA hB
  have herr : 2 * (40 * (f.natDegree + 1) *
      (Nat.sqrt (p ^ n) + 1)) + 1 =
      80 * (f.natDegree + 1) * (Nat.sqrt (p ^ n) + 1) + 1 := by
    ring
  rw [herr] at h
  exact h

end KloostermanWeil.Stepanov

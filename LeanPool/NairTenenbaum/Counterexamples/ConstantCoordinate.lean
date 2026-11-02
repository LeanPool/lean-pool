/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Polynomials.LinearCase
public import LeanPool.NairTenenbaum.PrimeArguments.PrimeArgumentEuler
public import LeanPool.NairTenenbaum.Smooth.SmoothValueRankin

/-! # The constant-coordinate obstruction to an unrestricted Corollary 6 -/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial

/-- The polynomial system exhibiting the obstruction from a constant coordinate. -/
noncomputable def constantCoordinateSystem : PolynomialSystem 2 1 where
  Q := ![X, 1]
  R := fun _ => X
  exponent := ![fun _ => 1, fun _ => 0]
  sign := fun _ => 1
  sign_abs := by simp
  factorization := by intro j; fin_cases j <;> simp
  irreducible := by intro i; simpa using (Polynomial.irreducible_X (R := ℚ))
  nonassociated := by intro i j hij; exact (hij (Subsingleton.elim _ _)).elim
  exponent_pos := by intro i; norm_num [totalExponent, Fin.sum_univ_two]
  noFixedPrime := by simpa using noFixedPrimeDivisor_X

@[simp] theorem constantCoordinateSystem_total : constantCoordinateSystem.total = (X : ℤ[X]) := by
  simp [PolynomialSystem.total, constantCoordinateSystem]

@[simp] theorem constantCoordinateSystem_radical : constantCoordinateSystem.radical = (X : ℤ[X])
    := by
  simp [PolynomialSystem.radical, constantCoordinateSystem]

@[simp] theorem constantCoordinateSystem_discriminant : constantCoordinateSystem.discriminant = 1
    := by
  rw [PolynomialSystem.discriminant, constantCoordinateSystem_radical,
    Polynomial.discr_of_degree_eq_one (by simp)]
  rfl

@[simp] theorem constantCoordinateSystem_badDiscriminant :
    constantCoordinateSystem.badDiscriminant = 1 := by
  simp [PolynomialSystem.badDiscriminant]

@[simp] theorem constantCoordinateSystem_weight_one (n : ℕ+) :
    constantCoordinateSystem.weight (fun _ => 1) n = (n : ℝ)⁻¹ := by
  have Hfiber : weightFiber constantCoordinateSystem.exponent 1 n =
      weightFiber (identityExponents 1) 1 n := by
    unfold weightFiber
    congr 1
  unfold PolynomialSystem.weight
  rw [constantCoordinateSystem_discriminant]
  change weight constantCoordinateSystem.exponent 1 (fun _ => 1)
    (fun _ n => (rootCount (X : ℤ[X]) n : ℝ)) n = _
  unfold weight
  rw [Hfiber, weightFiber_one_variable, ite_eq_left (Nat.coprime_one_right _)]
  simp [pullback]

theorem admissible_constant_one {k : ℕ} {σ : ℝ} (hσ : 0 ≤ σ) :
    Admissible 1 1 σ (fun _ : Tuple k => 1) := by
  refine ⟨fun _ => zero_le_one, ?_⟩
  intro m n hmn
  have H : 1 ≤ (mass m : ℝ) ^ σ := Real.one_le_rpow (by exact_mod_cast mass_pos m) hσ
  simpa only [growthBound, one_pow, one_mul, mul_one, le_min_iff] using And.intro le_rfl H

/-- The finite harmonic sum times the one-root Euler product is at most one. -/
theorem sieveProduct_X_mul_reciprocal_sum_le_one (x : ℝ) :
    sieveProduct (X : ℤ[X]) x * ∑ n ∈ positiveUpTo x, (n : ℝ)⁻¹ ≤ 1 := by
  let s := range (⌊x⌋₊ + 1)
  have hs (n : ℕ+) (hn : n ∈ positiveUpTo x) : (n : ℕ) ∈ Nat.factoredNumbers s := by
    apply Nat.mem_factoredNumbers_of_primeFactors_subset n.ne_zero
    intro p hp
    have hnx : (n : ℝ) ≤ x := (mem_positiveUpTo n x).mp hn
    have hx : 0 ≤ x := (show (0 : ℝ) ≤ n by positivity).trans hnx
    have hpn : p ≤ (n : ℕ) := Nat.le_of_dvd n.pos (Nat.dvd_of_mem_primeFactors hp)
    exact mem_range.mpr (Nat.lt_succ_of_le (hpn.trans ((Nat.le_floor_iff hx).mpr hnx)))
  have Hseries := reciprocal_smooth_hasSum s
  have H := (sum_positive_factored_le_tsum (fun n => by positivity : ∀ n : ℕ, 0 ≤ (n : ℝ)⁻¹)
    s Hseries.summable (positiveUpTo x) hs).trans_eq Hseries.tsum_eq
  have Hprod : (∏ p ∈ s.filter Nat.Prime, (1 - 1 / (p : ℝ))⁻¹) =
      (sieveProduct (X : ℤ[X]) x)⁻¹ := by
    simp only [s, sieveProduct, rootCount_X, Nat.cast_one, prod_inv_distrib]
  rw [Hprod] at H
  have hS := sieveProduct_pos noFixedPrimeDivisor_X x
  simpa only [mul_inv_cancel₀ hS.ne'] using mul_le_mul_of_nonneg_left H hS.le

theorem constantCoordinateSystem_mainTerm_one_le {x y : ℝ} (hy : 0 ≤ y) :
    mainTerm constantCoordinateSystem (fun _ => 1) x y ≤ y := by
  have H := mul_le_mul_of_nonneg_left (sieveProduct_X_mul_reciprocal_sum_le_one x) hy
  simpa only [mainTerm, constantCoordinateSystem_total, constantCoordinateSystem_weight_one,
    mul_assoc, mul_one] using H

theorem constantCoordinateSystem_smooth_sum (N : ℕ) (z : ℝ) :
    smoothShortSum constantCoordinateSystem.Q (fun _ => 1) 1 N N z = N := by
  have hext (n : ℕ) (hn : n ∈ shortInterval (N : ℝ) N) :
      extendArithmeticMap (fun _ : Tuple 2 => 1)
        (fun i => ((constantCoordinateSystem.Q i).eval (n : ℤ)).natAbs) = 1 := by
    have hn₀ : 0 < n := by
      have H := (mem_Ioc.mp hn).1
      simp only [Nat.floor_natCast] at H
      omega
    unfold extendArithmeticMap
    rw [dite_eq_left (show ∀ i, 0 < ((constantCoordinateSystem.Q i).eval (n : ℤ)).natAbs from by
      intro i
      fin_cases i <;> simp [constantCoordinateSystem, hn₀])]
  unfold smoothShortSum
  have hfilter : (shortInterval (N : ℝ) N).filter (fun n : ℕ =>
      ((constantCoordinateSystem.Q 1).eval (n : ℤ)).natAbs ∈ Nat.factoredNumbers (Icc 0 ⌊z⌋₊)) =
      shortInterval (N : ℝ) N := by
    apply filter_eq_self.mpr
    intro n hn
    simp [constantCoordinateSystem, Nat.mem_factoredNumbers]
  rw [hfilter]
  simp_rw [Finset.sum_congr rfl hext]
  simp only [sum_const, nsmul_eq_mul, mul_one, shortInterval, Nat.floor_natCast,
    ← Nat.cast_add, Nat.card_Ioc, Nat.add_sub_cancel_left]

end NairTenenbaum

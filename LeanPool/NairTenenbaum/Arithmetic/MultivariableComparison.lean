/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.ScalarComparison
public import LeanPool.NairTenenbaum.Arithmetic.WeightTruncation

/-! # Corrected multivariable totient comparison

The comparison is proved for the full weight (16), including exponent
substitution, the weighted-mass cutoff, and all dagger restrictions.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

/-- The pullback arithmetic weight multiplied by the coordinate root densities. -/
noncomputable def rootTupleWeight {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (F : ArithmeticMap k) (Q : Fin r → ℤ[X]) (n : Tuple r) : ℝ :=
  pullback γ F n * ∏ i, (rootCount (Q i) (n i) : ℝ) / (n i : ℝ)

theorem rootTupleWeight_nonneg {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    {F : ArithmeticMap k} (hF : ∀ n, 0 ≤ F n) (Q : Fin r → ℤ[X]) (n : Tuple r) :
    0 ≤ rootTupleWeight γ F Q n :=
  mul_nonneg (hF _) (Finset.prod_nonneg (fun _ _ => by positivity))

/-- Cross-coprimality lets the arithmetic majorant survive exponent substitution. -/
theorem Admissible.pullback_mul_le_auxiliary {k r : ℕ} {A B ε : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 1 ≤ B)
    (γ : Fin k → Fin r → ℕ) (a b : Tuple r) (hab : ∀ i j, Nat.Coprime (a i) (b j)) :
    pullback γ F (a * b) ≤ (∏ i, auxiliary A B ε (totalExponent γ i) (a i)) * pullback γ F b := by
  have H := hF.le_minimalMajorant_mul hA (zero_le_one.trans hB)
    (substitute γ a) (substitute γ b) (substitute_coprime γ hab)
  rw [← substitute_mul] at H
  exact H.trans (mul_le_mul_of_nonneg_right
    (hF.pullback_minimalMajorant_le_auxiliary hA hB γ a) (hF.nonneg _))

/-- The root-weighted tuple summand has the product of the proved local
auxiliaries as a majorant under cross-coprime multiplication. -/
theorem Admissible.rootTupleWeight_mul_le {k r : ℕ} {A B ε : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 1 ≤ B)
    (γ : Fin k → Fin r → ℕ) (Q : Fin r → ℤ[X]) (a b : Tuple r)
    (hab : ∀ i j, Nat.Coprime (a i) (b j)) :
    rootTupleWeight γ F Q (a * b) ≤
      (∏ i, rootAuxiliary A B ε (totalExponent γ i) (Q i) (a i)) * rootTupleWeight γ F Q b := by
  have hprod : (∏ i, (rootCount (Q i) ((a * b) i) : ℝ) / ((a * b) i : ℝ)) =
      (∏ i, (rootCount (Q i) (a i) : ℝ) / (a i : ℝ)) *
        ∏ i, (rootCount (Q i) (b i) : ℝ) / (b i : ℝ) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    change (rootCount (Q i) ((a i : ℕ) * (b i : ℕ)) : ℝ) / _ = _
    rw [rootCount_mul (Q i) (hab i i)]
    simp only [Pi.mul_apply, PNat.mul_coe, Nat.cast_mul]
    ring
  have haux : (∏ i, rootAuxiliary A B ε (totalExponent γ i) (Q i) (a i)) =
      (∏ i, auxiliary A B ε (totalExponent γ i) (a i)) *
        ∏ i, (rootCount (Q i) (a i) : ℝ) / (a i : ℝ) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    simp only [rootAuxiliary]
    ring
  rw [rootTupleWeight, hprod]
  calc
    _ ≤ ((∏ i, auxiliary A B ε (totalExponent γ i) (a i)) * pullback γ F b) *
        ((∏ i, (rootCount (Q i) (a i) : ℝ) / (a i : ℝ)) *
          ∏ i, (rootCount (Q i) (b i) : ℝ) / (b i : ℝ)) := by
      apply mul_le_mul_of_nonneg_right (hF.pullback_mul_le_auxiliary hA hB γ a b hab)
      exact mul_nonneg (Finset.prod_nonneg (fun _ _ => by positivity))
        (Finset.prod_nonneg (fun _ _ => by positivity))
    _ = _ := by rw [haux, rootTupleWeight]; ring

/-- A tuple-dependent twist factors out of the root-weighted summand. -/
theorem sum_weight_twist_eq_sum_weightUpTo {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i) (D : ℕ) (F : ArithmeticMap k)
    (Q : Fin r → ℤ[X]) (θ : Fin r → ℕ → ℝ) (N : ℕ+) :
    (∑ m ∈ Finset.Icc 1 N, weight γ D F (fun i n => (rootCount (Q i) n : ℝ) * θ i n) m) =
      ∑ n ∈ weightUpTo γ D N, rootTupleWeight γ F Q n * ∏ i, θ i (n i) := by
  rw [sum_weight_eq_sum_weightUpTo γ hγ]
  apply Finset.sum_congr rfl
  intro n _
  rw [rootTupleWeight, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  ring

/-- The corrected global comparison with the full multivariable weight. -/
theorem multivariable_totient_comparison {k r : ℕ} {A B ε : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (γ : Fin k → Fin r → ℕ) (hγ : ∀ i, 0 < totalExponent γ i)
    (hγε : ∀ i, (totalExponent γ i : ℝ) * ε < 1) (D : ℕ) (Q : Fin r → ℤ[X])
    (g : ℕ) (C : Fin r → ℕ) (hρ : ∀ i p, p.Prime → ∀ ν, rootCount (Q i) (p ^ ν) ≤ C i) (N : ℕ+) :
    (∑ n ∈ Finset.Icc 1 N, weight γ D F (fun i m => (rootCount (Q i) m : ℝ) * totientTwist g m) n) ≤
      (∏ i, Real.exp (∑' p : Nat.Primes,
        localComparisonError A B ε (totalExponent γ i) (Q i) (totientTwist g) p)) *
          ∑ n ∈ Finset.Icc 1 N, weight γ D F (fun i m => (rootCount (Q i) m : ℝ)) n := by
  let U := fun i => rootAuxiliary A B ε (totalExponent γ i) (Q i)
  let l := fun (_i : Fin r) p => |totientTwist g p - 1|
  have heq (i : Fin r) : (fun p : Nat.Primes => kernelLocalError (U i) (l i) p) =
      (fun p : Nat.Primes => localComparisonError A B ε (totalExponent γ i) (Q i) (totientTwist g)
          p) :=
    funext (fun p => totient_kernelLocalError A B ε _ _ g p.prop)
  have hE (i : Fin r) : Summable (fun p : Nat.Primes => kernelLocalError (U i) (l i) p) := by
    rw [heq]
    exact localComparisonError_summable hA hB hε
      (show 0 ≤ 2 * ((2 : ℝ) ^ g - 1) from mul_nonneg (by norm_num)
        (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))) _ (hγε i) _ (totientTwist_one g)
      (fun p hp ν => by rw [totientTwist_prime_pow g hp ν, totientTwist_prime g hp])
      (fun _ hp => totientTwist_prime_sub_one_le g hp) (C i) (hρ i)
  have H := tuple_comparison_uniform (rootTupleWeight_nonneg γ hF.nonneg Q)
    (show ∀ i, U i 0 = 0 by intro i; simp [U, rootAuxiliary])
    (fun i => rootAuxiliary_one A B ε _ _) (fun i => rootAuxiliary_nonneg hA (zero_le_one.trans
        hB) _ _)
    (fun i p => abs_nonneg (totientTwist g p - 1))
    (fun i m n h => rootAuxiliary_mul A B ε _ _ h)
    (fun i p hp => rootAuxiliary_prime_pow_summable hA hB hε _ (hγε i) _ hp (C i) (hρ i p hp))
    hE (weightUpTo γ D N) N (fun n hn i => weightUpTo_coordinate_le γ D N hn i)
    (fun n hn t _ => tupleUnitaryRest_mem_weightUpTo γ hγ D N hn t)
    (fun n hn t _ => by
      have hd := ((mem_weightUpTo γ hγ D N n).mp hn).2
      have hb := hF.rootTupleWeight_mul_le hA hB γ Q
        (tupleUnitaryPart n t) (tupleUnitaryRest n t) (hd.unitary_cross_coprime t)
      simpa only [tupleUnitaryPart_mul_rest] using hb)
  have hprod : (∏ i, Real.exp (∑' p : Nat.Primes, kernelLocalError (U i) (l i) p)) =
      ∏ i, Real.exp (∑' p : Nat.Primes,
        localComparisonError A B ε (totalExponent γ i) (Q i) (totientTwist g) p) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [heq i]
  rw [hprod] at H
  rw [sum_weight_twist_eq_sum_weightUpTo γ hγ, sum_weight_eq_sum_weightUpTo γ hγ]
  simpa only [l, ← totientTwist_eq_radicalProduct g (PNat.ne_zero _), rootTupleWeight] using H

/-- The same multivariable comparison at an arbitrary real cutoff, including
cutoffs below one. -/
theorem multivariable_totient_comparison_real {k r : ℕ} {A B ε : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (γ : Fin k → Fin r → ℕ) (hγ : ∀ i, 0 < totalExponent γ i)
    (hγε : ∀ i, (totalExponent γ i : ℝ) * ε < 1) (D : ℕ) (Q : Fin r → ℤ[X])
    (g : ℕ) (C : Fin r → ℕ) (hρ : ∀ i p, p.Prime → ∀ ν, rootCount (Q i) (p ^ ν) ≤ C i) (x : ℝ) :
    (∑ n ∈ positiveUpTo x, weight γ D F (fun i m => (rootCount (Q i) m : ℝ) * totientTwist g m) n) ≤
      (∏ i, Real.exp (∑' p : Nat.Primes,
        localComparisonError A B ε (totalExponent γ i) (Q i) (totientTwist g) p)) *
          ∑ n ∈ positiveUpTo x, weight γ D F (fun i m => (rootCount (Q i) m : ℝ)) n := by
  by_cases hx : 1 ≤ x
  · rw [positiveUpTo_eq_Icc hx]
    exact multivariable_totient_comparison hF hA hB hε γ hγ hγε D Q g C hρ _
  · simp [positiveUpTo_eq_empty (lt_of_not_ge hx)]

/-- A coefficient-independent product of explicit comparison constants. -/
theorem multivariable_totient_comparison_explicit {k r : ℕ} {A B ε : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (γ : Fin k → Fin r → ℕ) (hγ : ∀ i, 0 < totalExponent γ i)
    (hγε : ∀ i, (totalExponent γ i : ℝ) * ε < 1) (D : ℕ) (Q : Fin r → ℤ[X])
    (g : ℕ) (C : Fin r → ℕ) (hρ : ∀ i p, p.Prime → ∀ ν, rootCount (Q i) (p ^ ν) ≤ C i) (x : ℝ) :
    (∑ n ∈ positiveUpTo x, weight γ D F (fun i m => (rootCount (Q i) m : ℝ) * totientTwist g m) n) ≤
      (∏ i, scalarComparisonBound B ((totalExponent γ i : ℝ) * ε) g (C i)) *
        ∑ n ∈ positiveUpTo x, weight γ D F (fun i m => (rootCount (Q i) m : ℝ)) n := by
  refine (multivariable_totient_comparison_real hF hA hB hε γ hγ hγε D Q g C hρ x).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun n _ =>
    weight_nonneg _ _ hF.nonneg (fun i m => Nat.cast_nonneg (rootCount (Q i) m)) n))
  apply Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le)
  intro i _
  apply Real.exp_le_exp.mpr
  exact localComparisonError_tsum_le hA hB hε
    (show 0 ≤ 2 * ((2 : ℝ) ^ g - 1) from mul_nonneg (by norm_num)
      (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))) _ (hγε i) _ (totientTwist_one g)
    (fun p hp ν => by rw [totientTwist_prime_pow g hp ν, totientTwist_prime g hp])
    (fun _ hp => totientTwist_prime_sub_one_le g hp) (C i) (hρ i)

/-- The full comparison for an actual polynomial system, with its root bounds
discharged and its exponent substitution and dagger restrictions unchanged. -/
theorem PolynomialSystem.totient_comparison {k r : ℕ} (P : PolynomialSystem k r)
    {A B ε : ℝ} {F : ArithmeticMap k} (hF : Admissible A B ε F)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (hγε : ∀ i, (totalExponent P.exponent i : ℝ) * ε < 1) (g : ℕ) (x : ℝ) :
    (∑ n ∈ positiveUpTo x, NairTenenbaum.weight P.exponent P.discriminant F
      (fun i m => P.rootVector i m * totientTwist g m) n) ≤
      (∏ i, scalarComparisonBound B ((totalExponent P.exponent i : ℝ) * ε) g
        (max (P.R i).natDegree (P.badDiscriminant ^ 3))) *
          ∑ n ∈ positiveUpTo x, P.weight F n :=
  multivariable_totient_comparison_explicit hF hA hB hε P.exponent P.exponent_pos hγε
    P.discriminant P.R g (fun i => max (P.R i).natDegree (P.badDiscriminant ^ 3))
    (fun i _ hp ν => P.factor_rootCount_prime_pow_uniform hp ν i) x

end NairTenenbaum

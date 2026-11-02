/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.ComparisonKernel
public import LeanPool.NairTenenbaum.Arithmetic.TotientTwist

/-! # Corrected comparison for a single arithmetic variable

The finite convolution comparison and the weighted Euler-product bounds are
instantiated with the paper's admissible functions, polynomial root counts,
dagger restriction, and reciprocal-totient correction.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

/-- The totient correction is a product of nonnegative prime increments. -/
theorem totientTwist_eq_radicalProduct (g : ℕ) {n : ℕ} (hn : n ≠ 0) :
    totientTwist g n = radicalProduct (fun p => 1 + |totientTwist g p - 1|) n := by
  rw [Nat.multiplicative_factorization (totientTwist g)
    (fun _ _ h => totientTwist_mul g h) (totientTwist_one g) hn,
    Finsupp.prod, Nat.support_factorization, radicalProduct]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hν : 0 < n.factorization p := by
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (by
      simpa only [Nat.support_factorization] using hp))
  obtain ⟨ν, hν⟩ := Nat.exists_eq_succ_of_ne_zero hν.ne'
  rw [hν, totientTwist_prime_pow g hpp, totientTwist_prime g hpp]
  have hp₁ : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
  have ht : 1 ≤ (p : ℝ) / (p - 1) := (le_div_iff₀ (by linarith)).mpr (by linarith)
  rw [abs_of_nonneg (sub_nonneg.mpr (one_le_pow₀ ht))]
  ring

/-- Coprime multiplication is controlled by the actual auxiliary function. -/
theorem Admissible.scalar_mul_le_auxiliary {A B ε : ℝ} {F : ArithmeticMap 1}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 1 ≤ B) (a b : ℕ+)
    (hab : Nat.Coprime a b) :
    F (fun _ => a * b) ≤ auxiliary A B ε 1 a * F (fun _ => b) := by
  have h := hF.le_minimalMajorant_mul hA (zero_le_one.trans hB)
    (fun _ => a) (fun _ => b) (fun _ => hab)
  have hG : minimalMajorant F (fun _ => a) ≤ auxiliary A B ε 1 a := by
    simpa only [pullback, substitute_identity, totalExponent_identity, Fin.prod_univ_one] using
      hF.pullback_minimalMajorant_le_auxiliary hA hB (identityExponents 1) (fun _ => a)
  exact h.trans (mul_le_mul_of_nonneg_right hG (hF.nonneg _))

/-- The dagger-restricted scalar weight inherits a coprime majorant. -/
theorem Admissible.scalar_weight_mul_le {A B ε : ℝ} {F : ArithmeticMap 1}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 1 ≤ B) (D : ℕ) (Q : ℤ[X])
    (a b : ℕ+) (hab : Nat.Coprime a b) :
    weight (identityExponents 1) D F (fun _ n => (rootCount Q n : ℝ)) (a * b) ≤
      rootAuxiliary A B ε 1 Q a * weight (identityExponents 1) D F
        (fun _ n => (rootCount Q n : ℝ)) b := by
  by_cases hD : Nat.Coprime (a * b : ℕ+) D
  · have hbD : Nat.Coprime b D := (Nat.coprime_mul_iff_left.mp hD).2
    simp only [weight_one_variable, ite_eq_left hD, ite_eq_left hbD, rootAuxiliary]
    have hρ : rootCount Q ((a * b : ℕ+) : ℕ) = rootCount Q a * rootCount Q b :=
      rootCount_mul Q hab
    rw [hρ, Nat.cast_mul]
    have hbound := mul_le_mul_of_nonneg_right (hF.scalar_mul_le_auxiliary hA hB a b hab)
      (show 0 ≤ (rootCount Q a : ℝ) * rootCount Q b / ((a * b : ℕ+) : ℝ) by positivity)
    convert hbound using 1 <;> push_cast <;> ring
  · rw [weight_one_variable, ite_eq_right hD]
    exact mul_nonneg (rootAuxiliary_nonneg hA (zero_le_one.trans hB) _ _ _)
      (weight_nonneg _ _ hF.nonneg (fun _ _ => Nat.cast_nonneg _) _)

/-- Multiplying the root vector by a scalar twist multiplies the scalar weight. -/
theorem scalar_weight_twist (D : ℕ) (F : ArithmeticMap 1) (Q : ℤ[X])
    (θ : ℕ → ℝ) (n : ℕ+) :
    weight (identityExponents 1) D F (fun _ m => (rootCount Q m : ℝ) * θ m) n =
      weight (identityExponents 1) D F (fun _ m => (rootCount Q m : ℝ)) n * θ n := by
  simp only [weight_one_variable]
  split_ifs <;> ring

/-- The generic convolution local error is precisely the repaired local error
for the totient correction. -/
theorem totient_kernelLocalError (A B ε : ℝ) (γ : ℕ) (Q : ℤ[X]) (g : ℕ)
    {p : ℕ} (hp : p.Prime) :
    kernelLocalError (rootAuxiliary A B ε γ Q) (fun p => |totientTwist g p - 1|) p =
      localComparisonError A B ε γ Q (totientTwist g) p := by
  rw [localComparisonError_eq A B ε γ Q (totientTwist_one g)
    (fun ν => by rw [totientTwist_prime_pow g hp, totientTwist_prime g hp])]
  rfl

/-- A proved replacement for the printed comparison in the scalar case.
The coefficient is independent of `N` and of the admissible function `F`. -/
theorem scalar_totient_comparison {A B ε : ℝ} {F : ArithmeticMap 1}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hε₁ : ε < 1)
    (D : ℕ) (Q : ℤ[X]) (g C : ℕ)
    (hρ : ∀ p : ℕ, p.Prime → ∀ ν, rootCount Q (p ^ ν) ≤ C) (N : ℕ+) :
    (∑ n ∈ Finset.Icc 1 N,
      weight (identityExponents 1) D F (fun _ m => (rootCount Q m : ℝ) * totientTwist g m) n) ≤
      Real.exp (∑' p : Nat.Primes, localComparisonError A B ε 1 Q (totientTwist g) p) *
        ∑ n ∈ Finset.Icc 1 N,
          weight (identityExponents 1) D F (fun _ m => (rootCount Q m : ℝ)) n := by
  have hγε : ((1 : ℕ) : ℝ) * ε < 1 := by simpa using hε₁
  have hE := localComparisonError_summable hA hB hε
    (show 0 ≤ 2 * ((2 : ℝ) ^ g - 1) from mul_nonneg (by norm_num)
      (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))) 1 hγε Q (totientTwist_one g)
    (fun p hp ν => by rw [totientTwist_prime_pow g hp ν, totientTwist_prime g hp])
    (fun _ hp => totientTwist_prime_sub_one_le g hp) C hρ
  have heq : (fun p : Nat.Primes => kernelLocalError (rootAuxiliary A B ε 1 Q)
      (fun p => |totientTwist g p - 1|) p) =
      (fun p : Nat.Primes => localComparisonError A B ε 1 Q (totientTwist g) p) :=
    funext (fun p => totient_kernelLocalError A B ε 1 Q g p.prop)
  have hE' : Summable (fun p : Nat.Primes => kernelLocalError (rootAuxiliary A B ε 1 Q)
      (fun p => |totientTwist g p - 1|) p) := heq.symm ▸ hE
  have H := unitary_comparison_uniform
    (fun n => weight_nonneg (identityExponents 1) D hF.nonneg (fun _ n => Nat.cast_nonneg
        (rootCount Q n)) n)
    (show rootAuxiliary A B ε 1 Q 0 = 0 by simp [rootAuxiliary])
    (rootAuxiliary_one A B ε 1 Q) (rootAuxiliary_nonneg hA (zero_le_one.trans hB) 1 Q)
    (fun p => abs_nonneg (totientTwist g p - 1))
    (fun m n h => rootAuxiliary_mul A B ε 1 Q h)
    (hF.scalar_weight_mul_le hA hB D Q)
    (fun p hp => rootAuxiliary_prime_pow_summable hA hB hε 1 hγε Q hp C (hρ p hp)) hE' N
  rw [heq] at H
  simpa only [← totientTwist_eq_radicalProduct g (PNat.ne_zero _), ← scalar_weight_twist] using H

/-- A comparison constant expressed solely in the growth parameters, the
power of the totient correction, and a uniform root-count bound. -/
noncomputable def scalarComparisonBound (B ε : ℝ) (g C : ℕ) : ℝ :=
  Real.exp ((2 * ((2 : ℝ) ^ g - 1) * C * B / (1 - (2 : ℝ) ^ (ε - 1))) *
    ∑' n : ℕ, (n : ℝ) ^ (ε - 2))

theorem scalarComparisonBound_pos (B ε : ℝ) (g C : ℕ) : 0 < scalarComparisonBound B ε g C :=
  Real.exp_pos _

/-- The scalar comparison with a coefficient-independent explicit constant. -/
theorem scalar_totient_comparison_uniform {A B ε : ℝ} {F : ArithmeticMap 1}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hε₁ : ε < 1)
    (D : ℕ) (Q : ℤ[X]) (g C : ℕ)
    (hρ : ∀ p : ℕ, p.Prime → ∀ ν, rootCount Q (p ^ ν) ≤ C) (N : ℕ+) :
    (∑ n ∈ Finset.Icc 1 N,
      weight (identityExponents 1) D F (fun _ m => (rootCount Q m : ℝ) * totientTwist g m) n) ≤
      scalarComparisonBound B ε g C * ∑ n ∈ Finset.Icc 1 N,
        weight (identityExponents 1) D F (fun _ m => (rootCount Q m : ℝ)) n := by
  refine (scalar_totient_comparison hF hA hB hε hε₁ D Q g C hρ N).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun n _ =>
    weight_nonneg _ _ hF.nonneg (fun _ m => Nat.cast_nonneg (rootCount Q m)) n))
  apply Real.exp_le_exp.mpr
  have H := localComparisonError_tsum_le hA hB hε
    (show 0 ≤ 2 * ((2 : ℝ) ^ g - 1) from mul_nonneg (by norm_num)
      (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))) 1 (by simpa using hε₁) Q (totientTwist_one g)
    (fun p hp ν => by rw [totientTwist_prime_pow g hp ν, totientTwist_prime g hp])
    (fun _ hp => totientTwist_prime_sub_one_le g hp) C hρ
  simpa only [auxiliaryRatio, Nat.cast_one, Nat.cast_ofNat, one_mul] using H

/-- Each actual irreducible polynomial factor satisfies the scalar comparison;
no root-count estimate is left as an extra hypothesis. -/
theorem PolynomialSystem.factor_scalar_totient_comparison {k r : ℕ} (P : PolynomialSystem k r)
    {A B ε : ℝ} {F : ArithmeticMap 1} (hF : Admissible A B ε F)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hε₁ : ε < 1) (g : ℕ) (h : Fin r) (N : ℕ+) :
    (∑ n ∈ Finset.Icc 1 N, NairTenenbaum.weight (identityExponents 1) P.discriminant F
      (fun _ m => (rootCount (P.R h) m : ℝ) * totientTwist g m) n) ≤
      scalarComparisonBound B ε g (max (P.R h).natDegree (P.badDiscriminant ^ 3)) *
        ∑ n ∈ Finset.Icc 1 N, NairTenenbaum.weight (identityExponents 1) P.discriminant F
          (fun _ m => (rootCount (P.R h) m : ℝ)) n :=
  scalar_totient_comparison_uniform hF hA hB hε hε₁ P.discriminant (P.R h) g
    (max (P.R h).natDegree (P.badDiscriminant ^ 3))
    (fun _ hp ν => P.factor_rootCount_prime_pow_uniform hp ν h) N

end NairTenenbaum

/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Counterexamples.LemmaOneObstruction
public import LeanPool.NairTenenbaum.Counterexamples.PrimeSupportedFunction
public import LeanPool.NairTenenbaum.Polynomials.LinearCase
public import Mathlib.Algebra.Order.Ring.Star

/-! # Counterexample to the printed Lemma 1

For `1<a<2`, the admissible function supported on powers of two has finite
untwisted total mass. The completely multiplicative twist `(2/a)^v₂(n)`
satisfies (23), while its twisted partial sums are unbounded. The final theorem
uses the weight (16) for the explicit polynomial system `Q=X`.

This refutes the lemma as stated, not the main theorems of the paper. Their
proofs require a corrected comparison with hypotheses verified at each use.
-/

@[expose] public section

namespace NairTenenbaum

namespace LemmaOneObstruction

private theorem two_pow_injective : Function.Injective (fun ν : ℕ => (2 : ℕ+) ^ ν) := by
  intro i j h
  apply Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ))
  exact congrArg (fun n : ℕ+ => (n : ℕ)) h

/-- The untwisted arithmetic series has a finite geometric sum. -/
theorem twoSupported_hasSum {a : ℝ} (ha₀ : 0 ≤ a) (ha₂ : a < 2) :
    HasSum (fun n : ℕ+ => twoSupported a n / (n : ℝ)) (1 - a / 2)⁻¹ := by
  apply (two_pow_injective.hasSum_iff ?_).mp
  · simpa only [Function.comp_def, twoSupported_pow, PNat.pow_coe, PNat.val_ofNat,
      Nat.cast_pow, Nat.cast_ofNat, ← div_pow] using
      hasSum_geometric_of_lt_one (show 0 ≤ a / 2 by positivity) (show a / 2 < 1 by linarith)
  · intro n hn
    have h : ¬ TwoPower n := by
      rintro ⟨ν, hν⟩
      apply hn
      exact ⟨ν, PNat.coe_injective hν.symm⟩
    simp [twoSupported, h]

/-- Every partial untwisted sum is bounded independently of its endpoint. -/
theorem twoSupported_sum_le {a : ℝ} (ha₀ : 0 ≤ a) (ha₂ : a < 2) (x : ℝ) :
    ∑ n ∈ positiveUpTo x, twoSupported a n / (n : ℝ) ≤ (1 - a / 2)⁻¹ := by
  have hs := twoSupported_hasSum ha₀ ha₂
  rw [← hs.tsum_eq]
  exact hs.summable.sum_le_tsum _ (fun n _ => div_nonneg (twoSupported_nonneg ha₀ n) (by
    positivity))

/-- The twist cancels each nonzero term of the arithmetic series. -/
theorem twoSupported_twisted_pow {a : ℝ} (ha : a ≠ 0) (ν : ℕ) :
    twoSupported a ((2 : ℕ+) ^ ν) * twoTwist a (((2 : ℕ+) ^ ν) : ℕ) /
      (((2 : ℕ+) ^ ν) : ℝ) = 1 := by
  simpa only [twoSupported_pow, PNat.pow_coe, PNat.val_ofNat, twoTwist_two_pow,
    Nat.cast_pow, Nat.cast_ofNat, theta] using twisted_model_term ha ν

/-- There are at least `N` nonzero twisted terms below `2^N`. -/
theorem twoSupported_twisted_sum_ge {a : ℝ} (ha : 0 < a) (N : ℕ) :
    (N : ℝ) ≤ ∑ n ∈ positiveUpTo ((2 : ℝ) ^ N),
      twoSupported a n * twoTwist a n / (n : ℝ) := by
  classical
  let s := (Finset.range N).image (fun ν => (2 : ℕ+) ^ ν)
  have hsub : s ⊆ positiveUpTo ((2 : ℝ) ^ N) := by
    intro n hn
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.mp hn
    rw [mem_positiveUpTo]
    change (((2 : ℕ) ^ ν : ℕ) : ℝ) ≤ (2 : ℝ) ^ N
    exact_mod_cast (pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (Finset.mem_range.mp hν).le)
  have heq : (∑ n ∈ s, twoSupported a n * twoTwist a n / (n : ℝ)) = N := by
    rw [Finset.sum_image]
    · calc
        _ = ∑ _ν ∈ Finset.range N, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro ν _
          simpa only [PNat.pow_coe, Nat.cast_pow] using twoSupported_twisted_pow ha.ne' ν
        _ = _ := by simp
    · exact fun _ _ _ _ h => two_pow_injective h
  rw [← heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro n _ _
  exact div_nonneg (mul_nonneg (twoSupported_nonneg ha.le n) (by unfold twoTwist; positivity))
    (by positivity)

/-- No constant compares the twisted and untwisted partial arithmetic sums. -/
theorem twoSupported_comparison_fails {a : ℝ} (ha₀ : 0 < a) (ha₂ : a < 2)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ x : ℝ, 0 < x ∧
      C * (∑ n ∈ positiveUpTo x, twoSupported a n / (n : ℝ)) <
        ∑ n ∈ positiveUpTo x, twoSupported a n * twoTwist a n / (n : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (C * (1 - a / 2)⁻¹)
  refine ⟨(2 : ℝ) ^ N, by positivity, ?_⟩
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (twoSupported_sum_le ha₀.le ha₂ _) hC)
    (lt_of_lt_of_le hN (twoSupported_twisted_sum_ge ha₀ N))

/-- The prime-power difference series appearing in the printed equation (23). -/
noncomputable def primeDifference (a : ℝ) (p ν : ℕ) : ℝ :=
  |twoTwist a (p ^ (ν + 1)) - twoTwist a (p ^ ν)| / (p : ℝ) ^ (ν + 1)

theorem primeDifference_eq {a : ℝ} {p : ℕ} (hp : p.Prime) (ν : ℕ) :
    primeDifference a p ν = if p = 2 then localDifference a ν else 0 := by
  by_cases h : p = 2
  · subst p
    simp [primeDifference, localDifference, theta]
  · simp [primeDifference, twoTwist_other_prime_pow a hp h, h]

/-- All primes other than two contribute zero to (23). -/
theorem primeDifference_summable {a : ℝ} (ha₁ : 1 < a) (ha₂ : a < 2)
    {p : ℕ} (hp : p.Prime) : Summable (primeDifference a p) := by
  simp_rw [show primeDifference a p = fun ν => if p = 2 then localDifference a ν else 0
    from funext (primeDifference_eq hp)]
  split_ifs
  · exact unweighted_summable ha₁ ha₂
  · exact summable_zero

/-- Equation (23) holds uniformly over every finite set of primes. -/
theorem primeDifference_sum_le (a : ℝ)
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ∑ p ∈ s, ∑' ν, primeDifference a p ν ≤ ∑' ν, localDifference a ν := by
  classical
  have heq : (∑ p ∈ s, ∑' ν, primeDifference a p ν) =
      if 2 ∈ s then ∑' ν, localDifference a ν else 0 := by
    calc
      _ = ∑ p ∈ s, if p = 2 then ∑' ν, localDifference a ν else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        simp_rw [primeDifference_eq (hs p hp)]
        split_ifs <;> simp
      _ = _ := by simp
  rw [heq]
  split_ifs
  · exact le_rfl
  · exact tsum_nonneg (fun ν => by unfold localDifference; positivity)

/-- The actual weight (16) for `Q=X`, with and without the twist. -/
theorem linear_twisted_weight (a : ℝ) (n : ℕ+) :
    weight (identityExponents 1) 1 (twoSupportedMap a) (fun _ => twoTwist a) n =
      twoSupported a n * twoTwist a n / (n : ℝ) := by
  simp [weight_one_variable, twoSupportedMap]

theorem linear_untwisted_weight (a : ℝ) (n : ℕ+) :
    weight (identityExponents 1) 1 (twoSupportedMap a) (fun _ _ => 1) n =
      twoSupported a n / (n : ℝ) := by
  simp [weight_one_variable, twoSupportedMap]

/-- The printed comparison fails for admissible functions with arbitrarily
small positive growth exponent, despite satisfying its prime-difference hypothesis. -/
theorem admissible_counterexample {η : ℝ} (hη₀ : 0 < η) (hη₁ : η < 1) :
    let a := (2 : ℝ) ^ η
    Admissible a 1 η (twoSupportedMap a) ∧
    (∀ n : ℕ, 0 < twoTwist a n) ∧
    twoTwist a 1 = 1 ∧
    (∀ m n : ℕ, m ≠ 0 → n ≠ 0 →
      twoTwist a (m * n) = twoTwist a m * twoTwist a n) ∧
    (∀ p : ℕ, p.Prime → Summable (primeDifference a p)) ∧
    (∃ K : ℝ, ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) →
      (∑ p ∈ s, ∑' ν, primeDifference a p ν) ≤ K) ∧
    (∀ C : ℝ, 0 ≤ C → ∃ x : ℝ, 0 < x ∧
      C * (∑ n ∈ positiveUpTo x,
        weight (identityExponents 1) 1 (twoSupportedMap a) (fun _ _ => 1) n) <
      ∑ n ∈ positiveUpTo x,
        weight (identityExponents 1) 1 (twoSupportedMap a) (fun _ => twoTwist a) n) := by
  dsimp only
  have ha₁ : 1 < (2 : ℝ) ^ η := Real.one_lt_rpow (by norm_num) hη₀
  have ha₂ : (2 : ℝ) ^ η < 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hη₁
  refine ⟨twoSupported_admissible η, fun n => twoTwist_pos (by positivity) n,
    twoTwist_one _, fun m n hm hn => twoTwist_mul _ hm hn,
    fun p hp => primeDifference_summable ha₁ ha₂ hp,
    ⟨_, fun s hs => primeDifference_sum_le _ s hs⟩, ?_⟩
  intro C hC
  simp_rw [linear_untwisted_weight, linear_twisted_weight]
  exact twoSupported_comparison_fails (lt_trans zero_lt_one ha₁) ha₂ C hC

/-- The same failure written with the polynomial system and its root vector,
so that all polynomial hypotheses and both weights are instantiated explicitly. -/
theorem linearSystem_comparison_fails {η : ℝ} (hη₀ : 0 < η) (hη₁ : η < 1)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ x : ℝ, 0 < x ∧
      C * (∑ n ∈ positiveUpTo x, linearSystem.weight (twoSupportedMap ((2 : ℝ) ^ η)) n) <
        ∑ n ∈ positiveUpTo x,
          weight linearSystem.exponent linearSystem.discriminant
            (twoSupportedMap ((2 : ℝ) ^ η))
            (fun h n => linearSystem.rootVector h n * twoTwist ((2 : ℝ) ^ η) n) n := by
  have h := (admissible_counterexample hη₀ hη₁).2.2.2.2.2.2 C hC
  have hρ : linearSystem.rootVector = fun _ _ => 1 := by
    funext h n
    simp [PolynomialSystem.rootVector, linearSystem]
  simpa only [PolynomialSystem.weight, linearSystem_discriminant, hρ,
    show linearSystem.exponent = identityExponents 1 from rfl, one_mul] using h

end LemmaOneObstruction
end NairTenenbaum

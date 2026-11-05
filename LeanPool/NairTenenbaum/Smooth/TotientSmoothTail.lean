/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Smooth.TiltedTotientComparison

/-! # Smooth tails with the totient correction

The corrected comparison for tilted weights, followed by the root-weighted
moment and truncation estimates, proves the version of the smooth tail needed
for the sieve correction. The right side uses the unmodified root weight.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

/-- The totient-modified moment is bounded by an untwisted smooth sum. -/
theorem smooth_totient_moment_le {k r : ℕ} {A B ε κ σ z : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (hκ : 0 ≤ κ) (hσ : σ < 1) (hz : 2 ≤ z) (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i)
    (hshift : ∀ i, (totalExponent γ i : ℝ) * (ε + κ / Real.log z) ≤ σ)
    (Q : Fin r → ℤ[X]) (C : Fin r → ℕ)
    (hρ : ∀ i p, p.Prime → ∀ ν, rootCount (Q i) (p ^ ν) ≤ C i) (g D : ℕ) (N : ℕ+) :
    (∑ n ∈ smoothWeightUpTo γ D (Finset.Icc 0 ⌊z⌋₊) N,
      (rootTupleWeight γ F Q n * ∏ i, totientTwist g (n i)) * (weightedMass γ n : ℝ) ^ (κ /
          Real.log z)) ≤
      ((∏ i, tiltedTotientBound B σ g (C i)) *
        ∏ i, Real.exp (momentPrimeBound A B κ σ (totalExponent γ i) (C i))) *
          ∑ n ∈ smoothWeightUpTo γ D (Finset.Icc 0 ⌊z⌋₊) N, rootTupleWeight γ F Q n := by
  classical
  have H := tilted_totient_comparison hF hA hB hε hσ γ hshift Q C hρ g D
    (smoothWeightUpTo γ D (Finset.Icc 0 ⌊z⌋₊) N) N
    (fun _ hn => weightUpTo_coordinate_le γ D N (Finset.mem_filter.mp hn).1)
    (fun n hn => ((mem_smoothWeightUpTo γ hγ D _ N n).mp hn).1.2)
    (fun _ hn t _ => tupleUnitaryRest_mem_smoothWeightUpTo γ hγ D _ N hn t)
  have H' := H.trans (mul_le_mul_of_nonneg_left
    (smoothWeightUpTo_moment_uniform hF hA hB hε hκ hσ hz γ hγ hshift Q C hρ D N)
    (Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le)))
  simpa only [mul_assoc, mul_left_comm, mul_comm] using H'

/-- The scalar tail with the totient twist is exactly its dagger-tuple sum. -/
theorem sum_smooth_totient_weight_tail_eq {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i) (D : ℕ) (F : ArithmeticMap k)
    (Q : Fin r → ℤ[X]) (g : ℕ) (s : Finset ℕ) (N : ℕ+) (x : ℝ) :
    (∑ m ∈ (Finset.Icc 1 N).filter
        (fun m : ℕ+ => (m : ℕ) ∈ Nat.factoredNumbers s ∧ x < (m : ℝ)),
      weight γ D F (fun i m => (rootCount (Q i) m : ℝ) * totientTwist g m) m) =
      ∑ n ∈ (smoothWeightUpTo γ D s N).filter (fun n => x < (weightedMass γ n : ℝ)),
        rootTupleWeight γ F Q n * ∏ i, totientTwist g (n i) := by
  classical
  rw [sum_weight_filter_eq γ hγ]
  simp only [PNat.mk_coe, weightedMass_mem_factoredNumbers_iff γ hγ, smoothWeightUpTo,
    Finset.filter_filter]
  apply Finset.sum_congr rfl
  intro n _
  rw [rootTupleWeight, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  ring

/-- Uniform constant for the totient-modified smooth-tail estimate. -/
noncomputable def totientSmoothTailBound {k r : ℕ} (A B κ : ℝ)
    (γ : Fin k → Fin r → ℕ) (C : Fin r → ℕ) (G g : ℕ) : ℝ :=
  (∏ i, tiltedTotientBound B (7 / 8) g (C i)) * rootSmoothTailBound A B κ γ C G

/-- Finite smooth tail with the sieve's totient correction, bounded by a
truncated sum of the original root weight. -/
theorem totient_weight_smooth_tail_finite {k r : ℕ} {A B ε κ z x : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (hκ : 0 ≤ κ) (hz : 2 ≤ z) (hx : 0 < x)
    (γ : Fin k → Fin r → ℕ) (hγ : ∀ i, 0 < totalExponent γ i)
    (hγε : ∀ i, (totalExponent γ i : ℝ) * ε ≤ 1 / 8)
    (Q : Fin r → ℤ[X]) (C : Fin r → ℕ)
    (hρ : ∀ i p, p.Prime → ∀ ν, rootCount (Q i) (p ^ ν) ≤ C i)
    (G : ℕ) (hG : ∀ i, totalExponent γ i ≤ G) (hzκ : (4 : ℝ) ^ ((G : ℝ) * κ) ≤ z)
    (g D : ℕ) (N : ℕ+) :
    (∑ m ∈ (Finset.Icc 1 N).filter (fun m : ℕ+ =>
        (m : ℕ) ∈ Nat.factoredNumbers (Finset.Icc 0 ⌊z⌋₊) ∧ x < (m : ℝ)),
      weight γ D F (fun i m => (rootCount (Q i) m : ℝ) * totientTwist g m) m) ≤
      totientSmoothTailBound A B κ γ C G g * Real.exp (-κ * Real.log x / Real.log z) *
        ∑ m ∈ positiveUpTo z, weight γ D F (fun i m => (rootCount (Q i) m : ℝ)) m := by
  classical
  have hshift (i : Fin r) : (totalExponent γ i : ℝ) * (ε + κ / Real.log z) ≤ 7 / 8 := by
    apply moment_exponent_gap _ (hγε i) hκ hz
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hG i) hκ)).trans hzκ
  have hβ : 0 ≤ κ / Real.log z := div_nonneg hκ (Real.log_pos (by linarith : 1 < z)).le
  rw [sum_smooth_totient_weight_tail_eq γ hγ]
  have H := sum_tail_le_moment (smoothWeightUpTo γ D (Finset.Icc 0 ⌊z⌋₊) N)
    (fun n => rootTupleWeight γ F Q n * ∏ i, totientTwist g (n i))
    (fun n => (weightedMass γ n : ℝ))
    (fun n => mul_nonneg (rootTupleWeight_nonneg γ hF.nonneg Q n)
      (Finset.prod_nonneg (fun i _ => totientTwist_nonneg g (n i))))
    (fun _ => Nat.cast_nonneg _) hx hβ
  have heq : x ^ (-(κ / Real.log z)) = Real.exp (-κ * Real.log x / Real.log z) := by
    rw [Real.rpow_def_of_pos hx]
    congr 1
    ring
  rw [heq] at H
  have HM := smooth_totient_moment_le hF hA hB hε hκ (by norm_num : (7 / 8 : ℝ) < 1)
    hz γ hγ hshift Q C hρ g D N
  have HT := (smoothWeightUpTo_truncation_uniform hF hA hB hε hz γ hγ hγε Q C hρ G hG D N).trans
    (mul_le_mul_of_nonneg_left (truncated_rootTupleWeight_sum_le hF.nonneg γ hγ Q D N z)
      (smoothTruncationBound_pos (zero_le_one.trans hB) γ C G).le)
  have HMT := HM.trans (mul_le_mul_of_nonneg_left HT
    (mul_nonneg (Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le))
      (Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le))))
  refine (H.trans (mul_le_mul_of_nonneg_left HMT (Real.exp_pos _).le)).trans_eq ?_
  unfold totientSmoothTailBound rootSmoothTailBound
  ring

/-- Infinite smooth tail for the totient-modified root vector. Convergence is
proved from the uniform finite bound, and the right side is untwisted. -/
theorem totient_weight_smooth_tail {k r : ℕ} {A B ε κ z x : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (hκ : 0 ≤ κ) (hz : 2 ≤ z) (hx : 0 < x)
    (γ : Fin k → Fin r → ℕ) (hγ : ∀ i, 0 < totalExponent γ i)
    (hγε : ∀ i, (totalExponent γ i : ℝ) * ε ≤ 1 / 8)
    (Q : Fin r → ℤ[X]) (C : Fin r → ℕ)
    (hρ : ∀ i p, p.Prime → ∀ ν, rootCount (Q i) (p ^ ν) ≤ C i)
    (G : ℕ) (hG : ∀ i, totalExponent γ i ≤ G) (hzκ : (4 : ℝ) ^ ((G : ℝ) * κ) ≤ z) (g D : ℕ) :
    let f := fun m : ℕ+ => if (m : ℕ) ∈ Nat.factoredNumbers (Finset.Icc 0 ⌊z⌋₊) ∧ x < (m : ℝ)
      then weight γ D F (fun i m => (rootCount (Q i) m : ℝ) * totientTwist g m) m else 0
    Summable f ∧ (∑' m, f m) ≤
      totientSmoothTailBound A B κ γ C G g * Real.exp (-κ * Real.log x / Real.log z) *
        ∑ m ∈ positiveUpTo z, weight γ D F (fun i m => (rootCount (Q i) m : ℝ)) m := by
  classical
  apply pnat_summable_and_tsum_le
  · intro m
    split_ifs
    · exact weight_nonneg γ D hF.nonneg
        (fun i m => mul_nonneg (Nat.cast_nonneg _) (totientTwist_nonneg g m)) m
    · rfl
  · intro N
    rw [← Finset.sum_filter]
    exact totient_weight_smooth_tail_finite hF hA hB hε hκ hz hx γ hγ hγε Q C hρ G hG hzκ g D N

/-- The totient-modified smooth tail needed by the main proof, for an actual
polynomial system and with all root-count assumptions discharged. -/
theorem PolynomialSystem.totient_smooth_tail {k r : ℕ} (P : PolynomialSystem k r)
    {A B ε κ z x : ℝ} {F : ArithmeticMap k} (hF : Admissible A B ε F)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hκ : 0 ≤ κ) (hz : 2 ≤ z) (hx : 0 < x)
    (hzκ : (4 : ℝ) ^ ((P.total.natDegree : ℝ) * κ) ≤ z)
    (hγε : ∀ i, (totalExponent P.exponent i : ℝ) * ε ≤ 1 / 8) (g : ℕ) :
    let f := fun m : ℕ+ => if (m : ℕ) ∈ Nat.factoredNumbers (Finset.Icc 0 ⌊z⌋₊) ∧ x < (m : ℝ)
      then NairTenenbaum.weight P.exponent P.discriminant F
        (fun i m => P.rootVector i m * totientTwist g m) m else 0
    Summable f ∧ (∑' m, f m) ≤
      totientSmoothTailBound A B κ P.exponent
        (fun i => max (P.R i).natDegree (P.badDiscriminant ^ 3)) P.total.natDegree g *
          Real.exp (-κ * Real.log x / Real.log z) * ∑ m ∈ positiveUpTo z, P.weight F m :=
  totient_weight_smooth_tail hF hA hB hε hκ hz hx P.exponent P.exponent_pos hγε P.R
    (fun i => max (P.R i).natDegree (P.badDiscriminant ^ 3))
    (fun i _ hp ν => P.factor_rootCount_prime_pow_uniform hp ν i)
    P.total.natDegree P.totalExponent_le_degree hzκ g P.discriminant

end NairTenenbaum

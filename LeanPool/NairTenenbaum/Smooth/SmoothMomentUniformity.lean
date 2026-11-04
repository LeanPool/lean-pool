/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Smooth.SmoothTailUniformity

/-! # Uniform smooth moments before taking the tail

Keeping the positive moment explicit allows it to be combined with the moment
of the full bad-prime part before applying the mass-tail inequality.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

theorem totient_weight_smooth_moment_finite {k r : ℕ} {A B ε κ z : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (hκ : 0 ≤ κ) (hz : 2 ≤ z)
    (γ : Fin k → Fin r → ℕ) (hγ : ∀ i, 0 < totalExponent γ i)
    (hγε : ∀ i, (totalExponent γ i : ℝ) * ε ≤ 1 / 8)
    (Q : Fin r → ℤ[X]) (C : Fin r → ℕ)
    (hρ : ∀ i p, p.Prime → ∀ ν, rootCount (Q i) (p ^ ν) ≤ C i)
    (G : ℕ) (hG : ∀ i, totalExponent γ i ≤ G) (hzκ : (4 : ℝ) ^ ((G : ℝ) * κ) ≤ z)
    (g D : ℕ) (N : ℕ+) :
    (∑ n ∈ smoothWeightUpTo γ D (Finset.Icc 0 ⌊z⌋₊) N,
      (rootTupleWeight γ F Q n * ∏ i, totientTwist g (n i)) * (weightedMass γ n : ℝ) ^ (κ /
          Real.log z)) ≤
      totientSmoothTailBound A B κ γ C G g *
        ∑ m ∈ positiveUpTo z, weight γ D F (fun i m => (rootCount (Q i) m : ℝ)) m := by
  have hshift (i : Fin r) : (totalExponent γ i : ℝ) * (ε + κ / Real.log z) ≤ 7 / 8 := by
    apply moment_exponent_gap _ (hγε i) hκ hz
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hG i) hκ)).trans hzκ
  have HM := smooth_totient_moment_le hF hA hB hε hκ (by norm_num : (7 / 8 : ℝ) < 1)
    hz γ hγ hshift Q C hρ g D N
  have HT := (smoothWeightUpTo_truncation_uniform hF hA hB hε hz γ hγ hγε Q C hρ G hG D N).trans
    (mul_le_mul_of_nonneg_left (truncated_rootTupleWeight_sum_le hF.nonneg γ hγ Q D N z)
      (smoothTruncationBound_pos (zero_le_one.trans hB) γ C G).le)
  have HMT := HM.trans (mul_le_mul_of_nonneg_left HT
    (mul_nonneg (Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le))
      (Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le))))
  convert HMT using 1
  unfold totientSmoothTailBound rootSmoothTailBound
  ring

/-- Coefficient-uniform smooth moment for the totient-modified weight. -/
theorem PolynomialSystem.totient_smooth_moment_uniform {k r : ℕ} (P : PolynomialSystem k r)
    {A B ε κ z : ℝ} {F : ArithmeticMap k} (hF : Admissible A B ε F)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hκ : 0 ≤ κ) (hz : 2 ≤ z)
    (hzκ : (4 : ℝ) ^ ((P.total.natDegree : ℝ) * κ) ≤ z)
    (hgε : (P.total.natDegree : ℝ) * ε ≤ 1 / 8) (N : ℕ+) :
    (∑ n ∈ smoothWeightUpTo P.exponent P.discriminant (Finset.Icc 0 ⌊z⌋₊) N,
      (rootTupleWeight P.exponent F P.R n * ∏ i, totientTwist P.total.natDegree (n i)) *
        (weightedMass P.exponent n : ℝ) ^ (κ / Real.log z)) ≤
      smoothTailUniformBound A B κ P.total.natDegree P.badDiscriminant *
        ∑ m ∈ positiveUpTo z, P.weight F m := by
  have H := totient_weight_smooth_moment_finite hF hA hB hε hκ hz P.exponent P.exponent_pos
    (fun i => (mul_le_mul_of_nonneg_right (by
      exact_mod_cast P.totalExponent_le_degree i) hε.le).trans hgε)
    P.R (fun i => max (P.R i).natDegree (P.badDiscriminant ^ 3))
    (fun i _ hp ν => P.factor_rootCount_prime_pow_uniform hp ν i)
    P.total.natDegree P.totalExponent_le_degree hzκ P.total.natDegree P.discriminant N
  apply H.trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun n _ => P.weight_nonneg hF.nonneg n))
  exact (smoothTailBounds_le_uniform A B κ P.total.natDegree P.badDiscriminant P.exponent
    (fun i => max (P.R i).natDegree (P.badDiscriminant ^ 3)) P.factor_count_le_degree
    P.totalExponent_le_degree (fun i => max_le_max
      (Polynomial.natDegree_le_of_dvd (P.factor_dvd_total i) P.total_ne_zero) le_rfl)).2

end NairTenenbaum

/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Smooth.SmoothTruncationUniform

/-! # The smooth tail estimate for the root vector

The moment bound, prime-band comparison, and absorption argument give the
root-vector specialization of Lemma 2. The infinite tail is a proved convergent
series. The totient-modified root vector is treated separately in `TotientSmoothTail`;
general twists in the paper's class `M` are not covered by this module.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

/-- Uniform constant in the root-weighted smooth-tail bound. -/
noncomputable def rootSmoothTailBound {k r : ℕ} (A B κ : ℝ)
    (γ : Fin k → Fin r → ℕ) (C : Fin r → ℕ) (G : ℕ) : ℝ :=
  (∏ i, Real.exp (momentPrimeBound A B κ (7 / 8) (totalExponent γ i) (C i))) *
    smoothTruncationBound A B γ C G

theorem rootSmoothTailBound_pos {k r : ℕ} {A B κ : ℝ} (hB : 0 ≤ B)
    (γ : Fin k → Fin r → ℕ) (C : Fin r → ℕ) (G : ℕ) : 0 < rootSmoothTailBound A B κ γ C G :=
  mul_pos (Finset.prod_pos (fun _ _ => Real.exp_pos _)) (smoothTruncationBound_pos hB γ C G)

/-- Removing the auxiliary finite mass bound only enlarges the truncated sum. -/
theorem truncated_rootTupleWeight_sum_le {k r : ℕ} {F : ArithmeticMap k}
    (hF : ∀ n, 0 ≤ F n) (γ : Fin k → Fin r → ℕ) (hγ : ∀ i, 0 < totalExponent γ i)
    (Q : Fin r → ℤ[X]) (D : ℕ) (N : ℕ+) (z : ℝ) :
    (∑ n ∈ (weightUpTo γ D N).filter (fun n => (weightedMass γ n : ℝ) ≤ z),
      rootTupleWeight γ F Q n) ≤
      ∑ m ∈ positiveUpTo z, weight γ D F (fun i m => (rootCount (Q i) m : ℝ)) m := by
  classical
  have H := sum_weight_filter_eq γ hγ D F (fun i m => (rootCount (Q i) m : ℝ))
    (fun m : ℕ+ => (m : ℝ) ≤ z) N
  simp only [PNat.mk_coe] at H
  refine H.symm.le.trans ?_
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact (mem_positiveUpTo n z).mpr (Finset.mem_filter.mp hn).2
  · exact fun n _ _ => weight_nonneg γ D hF (fun i m => Nat.cast_nonneg _) n

/-- The complete finite root-vector tail estimate, with a sum truncated at `z`
on the right and a constant independent of `N`, `x`, and `z`. -/
theorem root_weight_smooth_tail_finite {k r : ℕ} {A B ε κ z x : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (hκ : 0 ≤ κ) (hz : 2 ≤ z) (hx : 0 < x)
    (γ : Fin k → Fin r → ℕ) (hγ : ∀ i, 0 < totalExponent γ i)
    (hγε : ∀ i, (totalExponent γ i : ℝ) * ε ≤ 1 / 8)
    (Q : Fin r → ℤ[X]) (C : Fin r → ℕ)
    (hρ : ∀ i p, p.Prime → ∀ ν, rootCount (Q i) (p ^ ν) ≤ C i)
    (G : ℕ) (hG : ∀ i, totalExponent γ i ≤ G) (hzκ : (4 : ℝ) ^ ((G : ℝ) * κ) ≤ z)
    (D : ℕ) (N : ℕ+) :
    (∑ m ∈ (Finset.Icc 1 N).filter (fun m : ℕ+ =>
        (m : ℕ) ∈ Nat.factoredNumbers (Finset.Icc 0 ⌊z⌋₊) ∧ x < (m : ℝ)),
      weight γ D F (fun i m => (rootCount (Q i) m : ℝ)) m) ≤
      rootSmoothTailBound A B κ γ C G * Real.exp (-κ * Real.log x / Real.log z) *
        ∑ m ∈ positiveUpTo z, weight γ D F (fun i m => (rootCount (Q i) m : ℝ)) m := by
  classical
  have hshift (i : Fin r) : (totalExponent γ i : ℝ) * (ε + κ / Real.log z) ≤ 7 / 8 := by
    apply moment_exponent_gap _ (hγε i) hκ hz
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hG i) hκ)).trans hzκ
  rw [sum_smooth_weight_tail_eq γ hγ]
  have H := smoothWeightUpTo_tail_uniform hF hA hB hε hκ (by norm_num : (7 / 8 : ℝ) < 1)
    hz hx γ hγ hshift Q C hρ D N
  have HT := (smoothWeightUpTo_truncation_uniform hF hA hB hε hz γ hγ hγε Q C hρ G hG D N).trans
    (mul_le_mul_of_nonneg_left (truncated_rootTupleWeight_sum_le hF.nonneg γ hγ Q D N z)
      (smoothTruncationBound_pos (zero_le_one.trans hB) γ C G).le)
  refine H.trans ?_
  calc
    _ ≤ Real.exp (-κ * Real.log x / Real.log z) *
        ((∏ i, Real.exp (momentPrimeBound A B κ (7 / 8) (totalExponent γ i) (C i))) *
          (smoothTruncationBound A B γ C G *
            ∑ m ∈ positiveUpTo z, weight γ D F (fun i m => (rootCount (Q i) m : ℝ)) m)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left HT
        (Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le))) (Real.exp_pos _).le
    _ = _ := by unfold rootSmoothTailBound; ring

/-- Uniform bounds on initial positive-integer sums imply convergence and
bound the infinite sum. This avoids using an unproved formal limit of partial sums. -/
theorem pnat_summable_and_tsum_le {f : ℕ+ → ℝ} {c : ℝ} (hf : ∀ n, 0 ≤ f n)
    (hbound : ∀ N : ℕ+, (∑ n ∈ Finset.Icc 1 N, f n) ≤ c) : Summable f ∧ (∑' n, f n) ≤ c := by
  classical
  have hfinite (T : Finset ℕ+) : (∑ n ∈ T, f n) ≤ c := by
    let N : ℕ+ := ⟨(∑ n ∈ T, (n : ℕ)) + 1, by omega⟩
    have hsub : T ⊆ Finset.Icc 1 N := by
      intro n hn
      apply Finset.mem_Icc.mpr
      refine ⟨one_le, ?_⟩
      have H := Finset.single_le_sum (fun (m : ℕ+) _ => Nat.zero_le (m : ℕ)) hn
      exact H.trans (Nat.le_succ _)
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf n)).trans (hbound N)
  have hs := summable_of_sum_le hf hfinite
  exact ⟨hs, hs.tsum_le_of_sum_le hfinite⟩

/-- Root-vector specialization of Lemma 2, as a convergent infinite series.
The finite upper mass cutoff has disappeared, while the right-hand sum stops
at `z`. The two coprimality restrictions are retained in `weight`. -/
theorem root_weight_smooth_tail {k r : ℕ} {A B ε κ z x : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (hκ : 0 ≤ κ) (hz : 2 ≤ z) (hx : 0 < x)
    (γ : Fin k → Fin r → ℕ) (hγ : ∀ i, 0 < totalExponent γ i)
    (hγε : ∀ i, (totalExponent γ i : ℝ) * ε ≤ 1 / 8)
    (Q : Fin r → ℤ[X]) (C : Fin r → ℕ)
    (hρ : ∀ i p, p.Prime → ∀ ν, rootCount (Q i) (p ^ ν) ≤ C i)
    (G : ℕ) (hG : ∀ i, totalExponent γ i ≤ G) (hzκ : (4 : ℝ) ^ ((G : ℝ) * κ) ≤ z) (D : ℕ) :
    let f := fun m : ℕ+ => if (m : ℕ) ∈ Nat.factoredNumbers (Finset.Icc 0 ⌊z⌋₊) ∧ x < (m : ℝ)
      then weight γ D F (fun i m => (rootCount (Q i) m : ℝ)) m else 0
    Summable f ∧ (∑' m, f m) ≤
      rootSmoothTailBound A B κ γ C G * Real.exp (-κ * Real.log x / Real.log z) *
        ∑ m ∈ positiveUpTo z, weight γ D F (fun i m => (rootCount (Q i) m : ℝ)) m := by
  classical
  apply pnat_summable_and_tsum_le
  · intro m
    split_ifs
    · exact weight_nonneg γ D hF.nonneg (fun i m => Nat.cast_nonneg _) m
    · rfl
  · intro N
    rw [← Finset.sum_filter]
    exact root_weight_smooth_tail_finite hF hA hB hε hκ hz hx γ hγ hγε Q C hρ G hG hzκ D N

/-- The infinite smooth tail for an actual polynomial system. Root-count
bounds are discharged, and the constant is independent of the coefficients
apart from the listed degree and restricted-discriminant data. -/
theorem PolynomialSystem.root_smooth_tail {k r : ℕ} (P : PolynomialSystem k r)
    {A B ε κ z x : ℝ} {F : ArithmeticMap k} (hF : Admissible A B ε F)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hκ : 0 ≤ κ) (hz : 2 ≤ z) (hx : 0 < x)
    (hzκ : (4 : ℝ) ^ ((P.total.natDegree : ℝ) * κ) ≤ z)
    (hγε : ∀ i, (totalExponent P.exponent i : ℝ) * ε ≤ 1 / 8) :
    let f := fun m : ℕ+ => if (m : ℕ) ∈ Nat.factoredNumbers (Finset.Icc 0 ⌊z⌋₊) ∧ x < (m : ℝ)
      then P.weight F m else 0
    Summable f ∧ (∑' m, f m) ≤
      rootSmoothTailBound A B κ P.exponent
        (fun i => max (P.R i).natDegree (P.badDiscriminant ^ 3)) P.total.natDegree *
          Real.exp (-κ * Real.log x / Real.log z) * ∑ m ∈ positiveUpTo z, P.weight F m :=
  root_weight_smooth_tail hF hA hB hε hκ hz hx P.exponent P.exponent_pos hγε P.R
    (fun i => max (P.R i).natDegree (P.badDiscriminant ^ 3))
    (fun i _ hp ν => P.factor_rootCount_prime_pow_uniform hp ν i)
    P.total.natDegree P.totalExponent_le_degree hzκ P.discriminant

end NairTenenbaum

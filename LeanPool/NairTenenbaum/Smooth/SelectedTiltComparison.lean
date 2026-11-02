/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Smooth.SelectedTilt
public import LeanPool.NairTenenbaum.Smooth.SmoothTailUniformity

/-! # The corrected weighted comparison for Corollary 6

Only small prime factors are tilted, while the weight sum ranges over all
integers up to its cutoff. The proof uses the selected-prime convolution
moment, with constants uniform in the polynomial coefficients.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial

theorem selectedMoment_substitute {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (n : Tuple r) (j : Fin k) (s : Finset ℕ) (β : ℝ) :
    selectedMoment s β (substitute γ n j) =
      ∏ i, selectedMoment s ((γ j i : ℝ) * β) (n i) := by
  simp only [substitute, PNat.coe_prod, PNat.pow_coe]
  rw [selectedMoment_prod s β _ _ (fun i _ => pow_ne_zero _ (n i).ne_zero)]
  simp only [selectedMoment_pow]

theorem rootTupleWeight_selectedTilt_le {k r : ℕ} {F : ArithmeticMap k}
    (hF : ∀ n, 0 ≤ F n) (γ : Fin k → Fin r → ℕ) (Q : Fin r → ℤ[X])
    (j : Fin k) (s : Finset ℕ) {β : ℝ} (hβ : 0 ≤ β) (n : Tuple r) :
    rootTupleWeight γ (selectedTilt F j s β) Q n ≤
      rootTupleWeight γ F Q n * ∏ i, selectedMoment s ((totalExponent γ i : ℝ) * β) (n i) := by
  have H : selectedMoment s β (substitute γ n j) ≤
      ∏ i, selectedMoment s ((totalExponent γ i : ℝ) * β) (n i) := by
    rw [selectedMoment_substitute]
    apply Finset.prod_le_prod₀ (fun i _ => selectedMoment_nonneg _ _ _)
    intro i hi
    apply selectedMoment_mono_exponent
    apply mul_le_mul_of_nonneg_right _ hβ
    exact_mod_cast (Finset.single_le_sum (fun j _ => Nat.zero_le (γ j i)) (mem_univ j))
  calc
    _ = rootTupleWeight γ F Q n * selectedMoment s β (substitute γ n j) := by
      unfold rootTupleWeight pullback selectedTilt
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left H (rootTupleWeight_nonneg γ hF Q n)

/-- The base constant for uniform selected-coordinate moment estimates. -/
noncomputable def selectedMomentUniformBase (A B κ σ : ℝ) (g D : ℕ) : ℝ :=
  1 + ∑ e ∈ range (g + 1), ∑ c ∈ range (max g (D ^ 3) + 1),
    Real.exp (momentPrimeBound A B κ σ e c)

/-- Uniform bound for the selected-coordinate moment. -/
noncomputable def selectedMomentUniformBound (A B κ σ : ℝ) (g D : ℕ) : ℝ :=
  (selectedMomentUniformBase A B κ σ g D) ^ g

theorem selectedMomentUniformBase_one_le (A B κ σ : ℝ) (g D : ℕ) :
    1 ≤ selectedMomentUniformBase A B κ σ g D :=
  le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
      (Real.exp_pos _).le)))

theorem selectedMomentUniformBound_pos (A B κ σ : ℝ) (g D : ℕ) :
    0 < selectedMomentUniformBound A B κ σ g D :=
  pow_pos (lt_of_lt_of_le zero_lt_one (selectedMomentUniformBase_one_le A B κ σ g D)) _

theorem prod_moment_bound_le_uniform {r : ℕ} (A B κ σ : ℝ) (g D : ℕ)
    (e C : Fin r → ℕ) (hr : r ≤ g) (he : ∀ i, e i ≤ g) (hC : ∀ i, C i ≤ max g (D ^ 3)) :
    (∏ i, Real.exp (momentPrimeBound A B κ σ (e i) (C i))) ≤
      selectedMomentUniformBound A B κ σ g D := by
  have H (i : Fin r) : Real.exp (momentPrimeBound A B κ σ (e i) (C i)) ≤
      selectedMomentUniformBase A B κ σ g D := by
    calc
      _ ≤ ∑ c ∈ range (max g (D ^ 3) + 1), Real.exp (momentPrimeBound A B κ σ (e i) c) :=
        single_le_sum (fun _ _ => (Real.exp_pos _).le) (mem_range.mpr (Nat.lt_succ_of_le (hC i)))
      _ ≤ ∑ e ∈ range (g + 1), ∑ c ∈ range (max g (D ^ 3) + 1),
          Real.exp (momentPrimeBound A B κ σ e c) :=
        single_le_sum (fun _ _ => Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le))
          (mem_range.mpr (Nat.lt_succ_of_le (he i)))
      _ ≤ _ := le_add_of_nonneg_left zero_le_one
  calc
    _ ≤ ∏ _i : Fin r, selectedMomentUniformBase A B κ σ g D :=
      Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le) (fun i _ => H i)
    _ = (selectedMomentUniformBase A B κ σ g D) ^ r := by simp
    _ ≤ _ := pow_le_pow_right₀ (selectedMomentUniformBase_one_le A B κ σ g D) hr

theorem PolynomialSystem.selectedTilt_weightSum_le {k r : ℕ} (P : PolynomialSystem k r)
    {A B ε κ z : ℝ} {F : ArithmeticMap k} (hF : Admissible A B ε F)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hκ : 0 ≤ κ) (hz : 2 ≤ z)
    (hzκ : (4 : ℝ) ^ ((P.total.natDegree : ℝ) * κ) ≤ z)
    (hgε : (P.total.natDegree : ℝ) * ε ≤ 1 / 8) (j : Fin k) (N : ℕ+) :
    (∑ n ∈ Icc 1 N, P.weight (selectedTilt F j (Icc 0 ⌊z⌋₊) (κ / Real.log z)) n) ≤
      selectedMomentUniformBound A B κ (7 / 8) P.total.natDegree P.badDiscriminant *
        ∑ n ∈ Icc 1 N, P.weight F n := by
  have hβ : 0 ≤ κ / Real.log z := div_nonneg hκ (Real.log_pos (by linarith : 1 < z)).le
  have hshift (i : Fin r) : (totalExponent P.exponent i : ℝ) * (ε + κ / Real.log z) ≤ 7 / 8 := by
    apply moment_exponent_gap _
      ((mul_le_mul_of_nonneg_right (by
        exact_mod_cast P.totalExponent_le_degree i) hε.le).trans hgε) hκ hz
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
      (mul_le_mul_of_nonneg_right (by exact_mod_cast P.totalExponent_le_degree i) hκ)).trans hzκ
  have Hmoment := weightUpTo_selectedMoment_uniform hF hA hB hε hκ (by norm_num) hz
    P.exponent P.exponent_pos hshift P.R (fun i => max (P.R i).natDegree (P.badDiscriminant ^ 3))
    (fun i _ hp ν => P.factor_rootCount_prime_pow_uniform hp ν i) P.discriminant N
  have Hconstant := prod_moment_bound_le_uniform A B κ (7 / 8) P.total.natDegree P.badDiscriminant
    (totalExponent P.exponent) (fun i => max (P.R i).natDegree (P.badDiscriminant ^ 3))
    P.factor_count_le_degree P.totalExponent_le_degree (fun i => max_le_max
      (Polynomial.natDegree_le_of_dvd (P.factor_dvd_total i) P.total_ne_zero) le_rfl)
  have Hsum := Finset.sum_le_sum (fun n (_hn : n ∈ weightUpTo P.exponent P.discriminant N) =>
    rootTupleWeight_selectedTilt_le hF.nonneg P.exponent P.R j (Icc 0 ⌊z⌋₊) hβ n)
  have H := Hsum.trans (Hmoment.trans (mul_le_mul_of_nonneg_right Hconstant
    (Finset.sum_nonneg (fun n _ => rootTupleWeight_nonneg P.exponent hF.nonneg P.R n))))
  simpa only [PolynomialSystem.weight, PolynomialSystem.rootVector,
    sum_weight_eq_sum_weightUpTo P.exponent P.exponent_pos, rootTupleWeight] using H

/-- The comparison in equation (41), including the original discriminant
uniformity, proved without the false general form of Lemma 1. -/
theorem PolynomialSystem.selectedTilt_weightSum_real_le {k r : ℕ} (P : PolynomialSystem k r)
    {A B ε κ z : ℝ} {F : ArithmeticMap k} (hF : Admissible A B ε F)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hκ : 0 ≤ κ) (hz : 2 ≤ z)
    (hzκ : (4 : ℝ) ^ ((P.total.natDegree : ℝ) * κ) ≤ z)
    (hgε : (P.total.natDegree : ℝ) * ε ≤ 1 / 8) (j : Fin k) (x : ℝ) :
    (∑ n ∈ positiveUpTo x, P.weight (selectedTilt F j (Icc 0 ⌊z⌋₊) (κ / Real.log z)) n) ≤
      selectedMomentUniformBound A B κ (7 / 8) P.total.natDegree P.badDiscriminant *
        ∑ n ∈ positiveUpTo x, P.weight F n := by
  by_cases hx : 1 ≤ x
  · simpa only [positiveUpTo_eq_Icc hx] using
      P.selectedTilt_weightSum_le hF hA hB hε hκ hz hzκ hgε j (Nat.toPNat' ⌊x⌋₊)
  · simp only [positiveUpTo_eq_empty (lt_of_not_ge hx), Finset.sum_empty, mul_zero, le_refl]

end NairTenenbaum

/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Smooth.SmoothMoment

/-! # Moments restricted to a selected set of primes

The tilt used in Corollary 6 affects small primes only. Its comparison must
hold on the entire truncated weight sum, including nonsmooth integers.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial

/-- The moment weight attached to the selected coordinates. -/
noncomputable def selectedMoment (s : Finset ℕ) (β : ℝ) (n : ℕ) : ℝ :=
  primePowerProduct (fun p ν => if p ∈ s then ((p : ℝ) ^ ν) ^ β else 1) n

theorem selectedMoment_nonneg (s : Finset ℕ) (β : ℝ) (n : ℕ) :
    0 ≤ selectedMoment s β n := by
  apply primePowerProduct_nonneg
  intro p hp ν
  split_ifs <;> positivity

@[simp] theorem selectedMoment_one (s : Finset ℕ) (β : ℝ) : selectedMoment s β 1 = 1 :=
  primePowerProduct_one _

theorem selectedMoment_eq_rpow {s : Finset ℕ} (β : ℝ) {n : ℕ}
    (hn : n ∈ Nat.factoredNumbers s) : selectedMoment s β n = (n : ℝ) ^ β := by
  rw [← primePowerProduct_rpow β (Nat.ne_zero_of_mem_factoredNumbers hn)]
  unfold selectedMoment primePowerProduct
  apply Finset.prod_congr rfl
  intro p hp
  exact ite_eq_left (Nat.primeFactors_subset_of_mem_factoredNumbers hn hp)

theorem selectedMoment_le_rpow (s : Finset ℕ) {β : ℝ} (hβ : 0 ≤ β) (n : ℕ+) :
    selectedMoment s β n ≤ (n : ℝ) ^ β := by
  rw [← primePowerProduct_rpow β n.ne_zero]
  unfold selectedMoment primePowerProduct
  apply Finset.prod_le_prod₀
  · intro p hp
    dsimp only
    split_ifs <;> positivity
  · intro p hp
    dsimp only
    split_ifs
    · exact le_rfl
    · exact Real.one_le_rpow (one_le_pow₀ (by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le)) hβ

theorem primePowerProduct_one_add_selectedIncrement (s : Finset ℕ) (β : ℝ) (n : ℕ) :
    primePowerProduct (fun p ν => 1 + if p ∈ s then momentIncrement β p ν else 0) n =
      selectedMoment s β n := by
  apply Finset.prod_congr rfl
  intro p hp
  dsimp only
  split_ifs <;> simp [momentIncrement]

theorem primePowerProduct_restrict (s : Finset ℕ) (l : ℕ → ℕ → ℝ) (n : ℕ+) :
    primePowerProduct (fun p ν => if p ∈ s then l p ν else 0) n =
      if (n : ℕ) ∈ Nat.factoredNumbers s then primePowerProduct l n else 0 := by
  classical
  by_cases hn : (n : ℕ) ∈ Nat.factoredNumbers s
  · rw [ite_eq_left hn]
    apply Finset.prod_congr rfl
    intro p hp
    exact ite_eq_left (Nat.primeFactors_subset_of_mem_factoredNumbers hn hp)
  · rw [ite_eq_right hn]
    have hnot : ¬(n : ℕ).primeFactors ⊆ s :=
      fun h => hn (Nat.mem_factoredNumbers_of_primeFactors_subset n.ne_zero h)
    obtain ⟨p, hp, hps⟩ := Finset.not_subset.mp hnot
    apply Finset.prod_eq_zero hp
    exact ite_eq_right hps

theorem selectedMomentKernel_sum_le_product {A B ε β : ℝ}
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hβ : 0 ≤ β)
    (γ : ℕ) (hγ : (γ : ℝ) * (ε + β) < 1) (Q : ℤ[X])
    (C : ℕ) (hρ : ∀ p, p.Prime → ∀ ν, rootCount Q (p ^ ν) ≤ C)
    (s : Finset ℕ) (T : Finset ℕ+) :
    (∑ n ∈ T, rootAuxiliary A B ε γ Q n *
      primePowerProduct (fun p ν => if p ∈ s then momentIncrement ((γ : ℝ) * β) p ν else 0) n) ≤
        ∏ p ∈ s.filter Nat.Prime, (1 + localMomentError A B ε β γ Q p) := by
  classical
  have H := momentKernel_sum_le_product hA hB hε hβ γ hγ Q C hρ s
    (T.filter (fun n => (n : ℕ) ∈ Nat.factoredNumbers s)) (fun _ hn => (mem_filter.mp hn).2)
  rw [sum_filter] at H
  convert H using 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [primePowerProduct_restrict]
  split_ifs <;> simp [momentKernel]

/-- The selected-prime moment comparison on any finite domain closed under
removal of whole prime powers. The domain itself need not be smooth. -/
theorem rootTupleWeight_selectedMoment_le_product {k r : ℕ} {A B ε β : ℝ}
    {F : ArithmeticMap k} (hF : Admissible A B ε F)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hβ : 0 ≤ β)
    (γ : Fin k → Fin r → ℕ) (hγ : ∀ i, (totalExponent γ i : ℝ) * (ε + β) < 1)
    (Q : Fin r → ℤ[X]) (C : Fin r → ℕ)
    (hρ : ∀ i p, p.Prime → ∀ ν, rootCount (Q i) (p ^ ν) ≤ C i)
    (D : ℕ) (s : Finset ℕ) (S : Finset (Tuple r)) (N : ℕ+)
    (hbox : ∀ n ∈ S, ∀ i, n i ≤ N) (hdagger : ∀ n ∈ S, Dagger D n)
    (hrest : ∀ n ∈ S, ∀ t ∈ unitaryChoices n, tupleUnitaryRest n t ∈ S) :
    (∑ n ∈ S, rootTupleWeight γ F Q n *
      ∏ i, selectedMoment s ((totalExponent γ i : ℝ) * β) (n i)) ≤
      (∏ i, ∏ p ∈ s.filter Nat.Prime,
        (1 + localMomentError A B ε β (totalExponent γ i) (Q i) p)) *
          ∑ n ∈ S, rootTupleWeight γ F Q n := by
  classical
  let l := fun i p ν => if p ∈ s then momentIncrement ((totalExponent γ i : ℝ) * β) p ν else 0
  let K := fun i (n : ℕ+) => rootAuxiliary A B ε (totalExponent γ i) (Q i) n * primePowerProduct
      (l i) n
  have hl : ∀ i p, p.Prime → ∀ ν, 0 ≤ l i p ν := by
    intro i p hp ν
    dsimp [l]
    split_ifs
    · exact momentIncrement_nonneg (mul_nonneg (Nat.cast_nonneg _) hβ) hp ν
    · exact le_rfl
  have hK : ∀ i n, 0 ≤ K i n := fun i n => mul_nonneg
    (rootAuxiliary_nonneg hA (zero_le_one.trans hB) _ _ _) (primePowerProduct_nonneg (hl i) n)
  have H := tuple_unitary_convolution_sum (rootTupleWeight_nonneg γ hF.nonneg Q) hK
    S (fun _ => Finset.Icc 1 N)
    (fun n hn t _ i => mem_Icc.mpr ⟨one_le, (unitaryPart_le _ _).trans (hbox n hn i)⟩)
    hrest (v := fun n => rootTupleWeight γ F Q n *
      ∏ i, selectedMoment s ((totalExponent γ i : ℝ) * β) (n i)) (by
      intro n hn
      have H := tuple_primePower_comparison_pointwise hl n
        (w := rootTupleWeight γ F Q)
        (U := fun i n => rootAuxiliary A B ε (totalExponent γ i) (Q i) n) (by
          intro t ht
          have H := hF.rootTupleWeight_mul_le hA hB γ Q
            (tupleUnitaryPart n t) (tupleUnitaryRest n t) ((hdagger n hn).unitary_cross_coprime t)
          simpa only [tupleUnitaryPart_mul_rest] using H)
      simpa only [l, primePowerProduct_one_add_selectedIncrement, K] using H)
  refine H.trans (mul_le_mul_of_nonneg_right ?_
    (Finset.sum_nonneg (fun n _ => rootTupleWeight_nonneg γ hF.nonneg Q n)))
  apply Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg (fun n _ => hK i n))
  intro i hi
  exact selectedMomentKernel_sum_le_product hA hB hε hβ _ (hγ i) _ (C i) (hρ i) s _

/-- Uniformity in the prime cutoff and in the full weighted-mass truncation. -/
theorem weightUpTo_selectedMoment_uniform {k r : ℕ} {A B ε κ σ z : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (hκ : 0 ≤ κ) (hσ : σ < 1) (hz : 2 ≤ z) (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i)
    (hshift : ∀ i, (totalExponent γ i : ℝ) * (ε + κ / Real.log z) ≤ σ)
    (Q : Fin r → ℤ[X]) (C : Fin r → ℕ)
    (hρ : ∀ i p, p.Prime → ∀ ν, rootCount (Q i) (p ^ ν) ≤ C i) (D : ℕ) (N : ℕ+) :
    (∑ n ∈ weightUpTo γ D N, rootTupleWeight γ F Q n *
      ∏ i, selectedMoment (Icc 0 ⌊z⌋₊) ((totalExponent γ i : ℝ) * (κ / Real.log z)) (n i)) ≤
      (∏ i, Real.exp (momentPrimeBound A B κ σ (totalExponent γ i) (C i))) *
        ∑ n ∈ weightUpTo γ D N, rootTupleWeight γ F Q n := by
  have hβ : 0 ≤ κ / Real.log z := div_nonneg hκ (Real.log_pos (by linarith : 1 < z)).le
  have H := rootTupleWeight_selectedMoment_le_product hF hA hB hε hβ γ
    (fun i => (hshift i).trans_lt hσ) Q C hρ D (Icc 0 ⌊z⌋₊) (weightUpTo γ D N) N
    (fun n hn => weightUpTo_coordinate_le γ D N hn)
    (fun n hn => ((mem_weightUpTo γ hγ D N n).mp hn).2)
    (fun n hn t _ => tupleUnitaryRest_mem_weightUpTo γ hγ D N hn t)
  refine H.trans (mul_le_mul_of_nonneg_right ?_
    (Finset.sum_nonneg (fun n _ => rootTupleWeight_nonneg γ hF.nonneg Q n)))
  apply Finset.prod_le_prod₀
  · intro i hi
    apply Finset.prod_nonneg
    intro p hp
    exact add_nonneg zero_le_one (tsum_nonneg
      (fun ν => localMomentTerm_nonneg hA (zero_le_one.trans hB) hβ _ _ (mem_filter.mp hp).2 ν))
  · intro i hi
    exact localMomentError_product_uniform hA hB hε hκ hσ hz _ (hshift i) _ (C i) (hρ i)

end NairTenenbaum

/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.MultivariableComparison
public import LeanPool.NairTenenbaum.Smooth.MomentKernel

/-! # Global exponential moments on smooth dagger tuples

The finite moment comparison retains the weighted-mass truncation, the finite
prime support, and every dagger restriction. The resulting constant is uniform
in the truncation and the smoothness cutoff. These are the root-weighted
moment and Rankin steps of Lemma 2, before its final truncation argument.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

/-- The real power of the weighted mass separates over the coordinates. -/
theorem weightedMass_rpow {k r : ℕ} (γ : Fin k → Fin r → ℕ) (n : Tuple r) (β : ℝ) :
    (weightedMass γ n : ℝ) ^ β = ∏ i, (n i : ℝ) ^ ((totalExponent γ i : ℝ) * β) := by
  simp only [weightedMass, Nat.cast_prod, Nat.cast_pow]
  rw [← Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Real.rpow_natCast_mul (by positivity)]

/-- Moment comparison on any finite domain closed under unitary removal. -/
theorem rootTupleWeight_moment_le_product {k r : ℕ} {A B ε β : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hβ : 0 ≤ β)
    (γ : Fin k → Fin r → ℕ) (hγ : ∀ i, (totalExponent γ i : ℝ) * (ε + β) < 1)
    (Q : Fin r → ℤ[X]) (C : Fin r → ℕ)
    (hρ : ∀ i p, p.Prime → ∀ ν, rootCount (Q i) (p ^ ν) ≤ C i)
    (D : ℕ) (s : Finset ℕ) (S : Finset (Tuple r)) (N : ℕ+)
    (hbox : ∀ n ∈ S, ∀ i, n i ≤ N)
    (hsmooth : ∀ n ∈ S, ∀ i, (n i : ℕ) ∈ Nat.factoredNumbers s)
    (hdagger : ∀ n ∈ S, Dagger D n)
    (hrest : ∀ n ∈ S, ∀ t ∈ unitaryChoices n, tupleUnitaryRest n t ∈ S) :
    (∑ n ∈ S, rootTupleWeight γ F Q n * (weightedMass γ n : ℝ) ^ β) ≤
      (∏ i, ∏ p ∈ s.filter Nat.Prime,
        (1 + localMomentError A B ε β (totalExponent γ i) (Q i) p)) *
          ∑ n ∈ S, rootTupleWeight γ F Q n := by
  classical
  let T := (Finset.Icc 1 N).filter (fun a : ℕ+ => (a : ℕ) ∈ Nat.factoredNumbers s)
  let K := fun i n => momentKernel A B ε β (totalExponent γ i) (Q i) n
  have hK : ∀ i n, 0 ≤ K i n := fun i n =>
    momentKernel_nonneg hA (zero_le_one.trans hB) hβ _ _ n
  have H := tuple_unitary_convolution_sum (rootTupleWeight_nonneg γ hF.nonneg Q)
    (fun i n => hK i n) S (fun _ => T)
    (fun n hn t _ i => Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨one_le, (unitaryPart_le _ _).trans (hbox n hn i)⟩,
      Nat.mem_factoredNumbers_of_dvd (hsmooth n hn i) (unitaryPart_dvd _ _)⟩)
    hrest (v := fun n => rootTupleWeight γ F Q n * (weightedMass γ n : ℝ) ^ β) (by
      intro n hn
      have H := tuple_primePower_comparison_pointwise
        (U := fun i n => rootAuxiliary A B ε (totalExponent γ i) (Q i) n)
        (l := fun i => momentIncrement ((totalExponent γ i : ℝ) * β))
        (fun i _ hp ν => momentIncrement_nonneg (mul_nonneg (Nat.cast_nonneg _) hβ) hp ν) n
        (w := rootTupleWeight γ F Q) (by
          intro t _
          have H := hF.rootTupleWeight_mul_le hA hB γ Q
            (tupleUnitaryPart n t) (tupleUnitaryRest n t) ((hdagger n hn).unitary_cross_coprime t)
          simpa only [tupleUnitaryPart_mul_rest] using H)
      simpa only [primePowerProduct_one_add_momentIncrement, ← weightedMass_rpow, K, momentKernel]
          using H)
  refine H.trans (mul_le_mul_of_nonneg_right ?_
    (Finset.sum_nonneg (fun n _ => rootTupleWeight_nonneg γ hF.nonneg Q n)))
  apply Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg (fun (n : ℕ+) _ => hK i n))
  intro i _
  exact momentKernel_sum_le_product hA hB hε hβ _ (hγ i) _ (C i) (hρ i) s T
    (fun _ hn => (Finset.mem_filter.mp hn).2)

/-- Smooth tuples with a weighted-mass bound, retaining the full dagger condition. -/
noncomputable def smoothWeightUpTo {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (D : ℕ) (s : Finset ℕ) (N : ℕ+) : Finset (Tuple r) := by
  classical
  exact (weightUpTo γ D N).filter (fun n => ∀ i, (n i : ℕ) ∈ Nat.factoredNumbers s)

theorem mem_smoothWeightUpTo {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i) (D : ℕ) (s : Finset ℕ) (N : ℕ+) (n : Tuple r) :
    n ∈ smoothWeightUpTo γ D s N ↔
      (weightedMass γ n ≤ N ∧ Dagger D n) ∧ ∀ i, (n i : ℕ) ∈ Nat.factoredNumbers s := by
  classical
  simp only [smoothWeightUpTo, Finset.mem_filter, mem_weightUpTo γ hγ]

theorem tupleUnitaryRest_mem_smoothWeightUpTo {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i) (D : ℕ) (s : Finset ℕ) (N : ℕ+)
    {n : Tuple r} (hn : n ∈ smoothWeightUpTo γ D s N) (t : Fin r → Finset ℕ) :
    tupleUnitaryRest n t ∈ smoothWeightUpTo γ D s N := by
  classical
  obtain ⟨hn, hs⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_filter.mpr ⟨tupleUnitaryRest_mem_weightUpTo γ hγ D N hn t,
    fun i => Nat.mem_factoredNumbers_of_dvd (hs i) (unitaryRest_dvd _ _)⟩

/-- Global smooth moment estimate, uniform in both finite cutoffs. -/
theorem smoothWeightUpTo_moment_uniform {k r : ℕ} {A B ε κ σ z : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (hκ : 0 ≤ κ) (hσ : σ < 1) (hz : 2 ≤ z) (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i)
    (hshift : ∀ i, (totalExponent γ i : ℝ) * (ε + κ / Real.log z) ≤ σ)
    (Q : Fin r → ℤ[X]) (C : Fin r → ℕ)
    (hρ : ∀ i p, p.Prime → ∀ ν, rootCount (Q i) (p ^ ν) ≤ C i) (D : ℕ) (N : ℕ+) :
    (∑ n ∈ smoothWeightUpTo γ D (Finset.Icc 0 ⌊z⌋₊) N,
      rootTupleWeight γ F Q n * (weightedMass γ n : ℝ) ^ (κ / Real.log z)) ≤
      (∏ i, Real.exp (momentPrimeBound A B κ σ (totalExponent γ i) (C i))) *
        ∑ n ∈ smoothWeightUpTo γ D (Finset.Icc 0 ⌊z⌋₊) N, rootTupleWeight γ F Q n := by
  classical
  have hβ : 0 ≤ κ / Real.log z := div_nonneg hκ (Real.log_pos (by linarith : 1 < z)).le
  have H := rootTupleWeight_moment_le_product hF hA hB hε hβ γ
    (fun i => (hshift i).trans_lt hσ) Q C hρ D (Finset.Icc 0 ⌊z⌋₊)
    (smoothWeightUpTo γ D (Finset.Icc 0 ⌊z⌋₊) N) N
    (fun _ hn => weightUpTo_coordinate_le γ D N (Finset.mem_filter.mp hn).1)
    (fun _ hn => (Finset.mem_filter.mp hn).2)
    (fun n hn => ((mem_smoothWeightUpTo γ hγ D _ N n).mp hn).1.2)
    (fun _ hn t _ => tupleUnitaryRest_mem_smoothWeightUpTo γ hγ D _ N hn t)
  refine H.trans (mul_le_mul_of_nonneg_right ?_
    (Finset.sum_nonneg (fun n _ => rootTupleWeight_nonneg γ hF.nonneg Q n)))
  apply Finset.prod_le_prod₀
  · intro i _
    exact Finset.prod_nonneg (fun p hp => add_nonneg zero_le_one (tsum_nonneg
      (fun ν => localMomentTerm_nonneg hA (zero_le_one.trans hB) hβ _ _ (Finset.mem_filter.mp
          hp).2 ν)))
  · intro i _
    exact localMomentError_product_uniform hA hB hε hκ hσ hz _ (hshift i) _ (C i) (hρ i)

/-- Finite Rankin inequality, valid for every nonnegative weight. -/
theorem sum_tail_le_moment {ι : Type*} (S : Finset ι)
    (w m : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hm : ∀ i, 0 ≤ m i)
    {x β : ℝ} (hx : 0 < x) (hβ : 0 ≤ β) :
    (∑ i ∈ S.filter (fun i => x < m i), w i) ≤ x ^ (-β) * ∑ i ∈ S, w i * m i ^ β := by
  classical
  have hxp : 0 < x ^ β := Real.rpow_pos_of_pos hx β
  have hxn : 0 ≤ x ^ (-β) := Real.rpow_nonneg hx.le _
  calc
    _ ≤ ∑ i ∈ S.filter (fun i => x < m i), x ^ (-β) * (w i * m i ^ β) := by
      apply Finset.sum_le_sum
      intro i hi
      have hpow := Real.rpow_le_rpow hx.le (Finset.mem_filter.mp hi).2.le hβ
      calc
        w i = (x ^ (-β) * x ^ β) * w i := by
          rw [Real.rpow_neg hx.le, inv_mul_cancel₀ hxp.ne', one_mul]
        _ ≤ (x ^ (-β) * m i ^ β) * w i :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hxn) (hw i)
        _ = _ := by ring
    _ = x ^ (-β) * ∑ i ∈ S.filter (fun i => x < m i), w i * m i ^ β := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => mul_nonneg (hw i) (Real.rpow_nonneg (hm i) β))) hxn

/-- Rankin's inequality on a family of finite sets with a common mass cutoff. -/
theorem sum_sum_tail_le_moment {ι υ : Type*} (V : Finset ι) (U : ι → Finset υ)
    (w m : ι → υ → ℝ) (hw : ∀ v u, 0 ≤ w v u) (hm : ∀ v u, 0 ≤ m v u)
    {x β : ℝ} (hx : 0 < x) (hβ : 0 ≤ β) :
    (∑ v ∈ V, ∑ u ∈ (U v).filter (fun u => x < m v u), w v u) ≤
      x ^ (-β) * ∑ v ∈ V, ∑ u ∈ U v, w v u * m v u ^ β := by
  have H := Finset.sum_le_sum (fun v (_ : v ∈ V) =>
    sum_tail_le_moment (U v) (w v) (m v) (hw v) (hm v) hx hβ)
  simpa only [Finset.mul_sum] using H

/-- Multiply a uniform moment bound for each bad part by the good-part moment. -/
theorem sum_split_weightedMass_moment_le {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (V : Finset (Tuple r)) (U : Tuple r → Finset (Tuple r))
    (w W : Tuple r → ℝ) {β B : ℝ} (hW : ∀ v, 0 ≤ W v)
    (hlocal : ∀ v ∈ V, (∑ u ∈ U v, w u * (weightedMass γ u : ℝ) ^ β) ≤ B) :
    (∑ v ∈ V, ∑ u ∈ U v, (w u * W v) * (weightedMass γ (u * v) : ℝ) ^ β) ≤
      B * ∑ v ∈ V, W v * (weightedMass γ v : ℝ) ^ β := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  have H := mul_le_mul_of_nonneg_right (hlocal v hv)
    (mul_nonneg (hW v) (Real.rpow_nonneg (Nat.cast_nonneg (weightedMass γ v)) β))
  rw [Finset.sum_mul] at H
  convert H using 1
  apply Finset.sum_congr rfl
  intro u _
  rw [weightedMass_mul, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

/-- The Rankin saving with the paper's logarithmic moment exponent. -/
theorem smoothWeightUpTo_tail_uniform {k r : ℕ} {A B ε κ σ z x : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (hκ : 0 ≤ κ) (hσ : σ < 1) (hz : 2 ≤ z) (hx : 0 < x) (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i)
    (hshift : ∀ i, (totalExponent γ i : ℝ) * (ε + κ / Real.log z) ≤ σ)
    (Q : Fin r → ℤ[X]) (C : Fin r → ℕ)
    (hρ : ∀ i p, p.Prime → ∀ ν, rootCount (Q i) (p ^ ν) ≤ C i) (D : ℕ) (N : ℕ+) :
    (∑ n ∈ (smoothWeightUpTo γ D (Finset.Icc 0 ⌊z⌋₊) N).filter
        (fun n => x < (weightedMass γ n : ℝ)), rootTupleWeight γ F Q n) ≤
      Real.exp (-κ * Real.log x / Real.log z) *
        ((∏ i, Real.exp (momentPrimeBound A B κ σ (totalExponent γ i) (C i))) *
          ∑ n ∈ smoothWeightUpTo γ D (Finset.Icc 0 ⌊z⌋₊) N, rootTupleWeight γ F Q n) := by
  classical
  have hβ : 0 ≤ κ / Real.log z := div_nonneg hκ (Real.log_pos (by linarith : 1 < z)).le
  have H := sum_tail_le_moment (smoothWeightUpTo γ D (Finset.Icc 0 ⌊z⌋₊) N)
    (rootTupleWeight γ F Q) (fun n => (weightedMass γ n : ℝ))
    (rootTupleWeight_nonneg γ hF.nonneg Q) (fun _ => Nat.cast_nonneg _) hx hβ
  have heq : x ^ (-(κ / Real.log z)) = Real.exp (-κ * Real.log x / Real.log z) := by
    rw [Real.rpow_def_of_pos hx]
    congr 1
    ring
  rw [heq] at H
  exact H.trans (mul_le_mul_of_nonneg_left
    (smoothWeightUpTo_moment_uniform hF hA hB hε hκ hσ hz γ hγ hshift Q C hρ D N)
    (Real.exp_pos _).le)

/-- Actual polynomial systems satisfy the root-weighted smooth tail estimate
with all root-count hypotheses discharged. The denominator still contains the
full finite smooth sum, not the final `n ≤ z` truncation of Lemma 2. -/
theorem PolynomialSystem.smooth_tail_bound {k r : ℕ} (P : PolynomialSystem k r)
    {A B ε κ z x : ℝ} {F : ArithmeticMap k} (hF : Admissible A B ε F)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hκ : 0 ≤ κ) (hz : 2 ≤ z) (hx : 0 < x)
    (hzκ : (4 : ℝ) ^ ((P.total.natDegree : ℝ) * κ) ≤ z)
    (hεγ : ∀ i, (totalExponent P.exponent i : ℝ) * ε ≤ 1 / 8) (N : ℕ+) :
    (∑ n ∈ (smoothWeightUpTo P.exponent P.discriminant (Finset.Icc 0 ⌊z⌋₊) N).filter
        (fun n => x < (weightedMass P.exponent n : ℝ)), rootTupleWeight P.exponent F P.R n) ≤
      Real.exp (-κ * Real.log x / Real.log z) *
        ((∏ i, Real.exp (momentPrimeBound A B κ (7 / 8) (totalExponent P.exponent i)
          (max (P.R i).natDegree (P.badDiscriminant ^ 3)))) *
            ∑ n ∈ smoothWeightUpTo P.exponent P.discriminant (Finset.Icc 0 ⌊z⌋₊) N,
              rootTupleWeight P.exponent F P.R n) := by
  apply smoothWeightUpTo_tail_uniform hF hA hB hε hκ (by norm_num) hz hx
    P.exponent P.exponent_pos
  · intro i
    apply moment_exponent_gap _ (hεγ i) hκ hz
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
      (mul_le_mul_of_nonneg_right (by exact_mod_cast P.totalExponent_le_degree i) hκ)).trans hzκ
  · exact fun i _ hp ν => P.factor_rootCount_prime_pow_uniform hp ν i

end NairTenenbaum

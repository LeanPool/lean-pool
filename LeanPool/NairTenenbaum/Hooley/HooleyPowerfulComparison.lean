/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.PowerfulSummability
public import LeanPool.NairTenenbaum.Hooley.HooleyShortSum
public import LeanPool.NairTenenbaum.Hooley.HooleySquarefreeMean

/-! # Removing the squarefree restriction from the Hooley mean

The coprime squarefree/powerful decomposition injects into a product of finite
sets. Its powerful weight is summed using the proved convergent series.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Real Polynomial

theorem hooleyRootWeight_mul_le (Q : ℤ[X]) {t : ℝ} (ht : 0 ≤ t)
    {a b : ℕ} (hab : a.Coprime b) :
    (hooleyDelta (a * b) : ℝ) ^ t * ((rootCount Q (a * b) : ℝ) / (a * b : ℕ)) ≤
      ((a.divisors.card : ℝ) ^ t * (rootCount Q a : ℝ) / a) *
        ((hooleyDelta b : ℝ) ^ t * (rootCount Q b : ℝ) / b) := by
  have H := Real.rpow_le_rpow (Nat.cast_nonneg (hooleyDelta (a * b)))
    (by exact_mod_cast hooleyDelta_mul_le hab :
      (hooleyDelta (a * b) : ℝ) ≤ (a.divisors.card : ℝ) * (hooleyDelta b : ℝ)) ht
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)] at H
  rw [rootCount_mul Q hab, Nat.cast_mul, Nat.cast_mul]
  apply (mul_le_mul_of_nonneg_right H (by positivity)).trans_eq
  ring

theorem hooleyRootSum_le_powerful_mul_squarefree {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    (hirr : Irreducible (Q.map (Int.castRingHom ℚ))) {t : ℝ} (ht : 0 ≤ t)
    (x : ℝ) :
    hooleyRootSum Q t x ≤ (∑' n : {n : ℕ // Powerful n}, powerfulRootWeight Q t n) *
      squarefreeHooleyRootSum Q t x := by
  classical
  let S := positiveUpTo x
  let T := (Icc 1 ⌊x⌋₊).filter Squarefree
  let r (n : ℕ+) : {m : ℕ // Powerful m} := ⟨repeatedPrimePart n, powerful_repeatedPrimePart n⟩
  let e (n : ℕ+) : {m : ℕ // Powerful m} × ℕ := (r n, singlePrimePart n)
  let R := S.image r
  have hprod (n : ℕ+) : (r n).1 * (singlePrimePart n : ℕ) = n := by
    rw [mul_comm]
    exact congrArg PNat.val (singlePrimePart_mul_repeatedPrimePart n)
  have he : Function.Injective e := by
    intro n m h
    apply PNat.coe_injective
    rw [← hprod n, ← hprod m]
    exact congrArg (fun v : {m : ℕ // Powerful m} × ℕ => v.1.1 * v.2) h
  have hT (n : ℕ+) (hn : n ∈ S) : (singlePrimePart n : ℕ) ∈ T := by
    have hs : (singlePrimePart n : ℕ) ≤ n := by
      have H := Nat.le_mul_of_pos_right (singlePrimePart n : ℕ) (repeatedPrimePart n).pos
      have Hprod := congrArg PNat.val (singlePrimePart_mul_repeatedPrimePart n)
      exact H.trans_eq Hprod
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨(singlePrimePart n).pos, ?_⟩, squarefree_singlePrimePart n⟩
    exact Nat.le_floor ((Nat.cast_le.mpr hs).trans ((mem_positiveUpTo n x).mp hn))
  have Hsum : hooleyRootSum Q t x ≤ ∑ z ∈ R ×ˢ T,
      powerfulRootWeight Q t z.1 * ((hooleyDelta z.2 : ℝ) ^ t * (rootCount Q z.2 : ℝ) / z.2) := by
    apply sum_le_sum_of_injOn e (fun _ _ _ _ h => he h)
    · intro z hz
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hz
      exact mem_product.mpr ⟨mem_image.mpr ⟨n, hn, rfl⟩, hT n hn⟩
    · intro n _
      have H := hooleyRootWeight_mul_le Q ht (singlePrimePart_coprime_repeatedPrimePart n).symm
      change (hooleyDelta ((r n).1 * (singlePrimePart n : ℕ)) : ℝ) ^ t *
        ((rootCount Q ((r n).1 * (singlePrimePart n : ℕ)) : ℝ) / ((r n).1 * (singlePrimePart n :
            ℕ) : ℕ)) ≤ _ at H
      rw [hprod n] at H
      exact H
    · intro z _ _
      exact mul_nonneg (powerfulRootWeight_nonneg Q t _) (by positivity)
  have HR := (summable_powerfulRootWeight hQ hirr ht).sum_le_tsum R
    (fun n _ => powerfulRootWeight_nonneg Q t n)
  have HT : 0 ≤ squarefreeHooleyRootSum Q t x :=
    sum_nonneg (fun _ _ => by positivity)
  apply Hsum.trans
  rw [sum_product]
  simp_rw [← mul_sum]
  rw [← sum_mul]
  exact mul_le_mul_of_nonneg_right HR HT

end NairTenenbaum

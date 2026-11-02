/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.DivisorBounds
public import LeanPool.NairTenenbaum.Arithmetic.PowerfulDecomposition
public import LeanPool.NairTenenbaum.Polynomials.RootCountSubpolynomial
public import Mathlib.Analysis.PSeries

/-! # Summing the repeated-prime contribution

The representation `a²b³` proves convergence of `Σ n^(−s)` on powerful
integers for `s>1/2`. Subpolynomial divisor and root bounds then give the
convergent weight `τ(n)^t ρ_Q(n)/n` needed to remove the squarefree restriction.
-/

@[expose] public section

namespace NairTenenbaum

open Real Polynomial

theorem summable_powerful_rpow {s : ℝ} (hs : 1 / 2 < s) :
    Summable (fun n : {n : ℕ // Powerful n} => (n.1 : ℝ) ^ (-s)) := by
  have H₂ := Real.summable_nat_rpow.mpr (by linarith : -(2 * s) < -1)
  have H₃ := Real.summable_nat_rpow.mpr (by linarith : -(3 * s) < -1)
  have H := (H₂.mul_of_nonneg H₃
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _) (fun n => Real.rpow_nonneg (Nat.cast_nonneg
        n) _)).comp_injective
    powerful_bases_injective
  apply H.congr
  intro n
  dsimp only [Function.comp_def]
  have hn : (n.1 : ℝ) = (powerfulSquareBase n.1 : ℝ) ^ 2 * (powerfulCubeBase n.1 : ℝ) ^ 3 := by
    exact_mod_cast (powerful_eq_square_mul_cube n.2).symm
  rw [hn, Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_natCast (powerfulSquareBase n.1 : ℝ) 2,
    ← Real.rpow_natCast (powerfulCubeBase n.1 : ℝ) 3,
    ← Real.rpow_mul (Nat.cast_nonneg _), ← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num

theorem exists_divisorRootWeight_le_rpow {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    (hirr : Irreducible (Q.map (Int.castRingHom ℚ))) {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, n ≠ 0 →
      (n.divisors.card : ℝ) ^ t * (rootCount Q n : ℝ) ≤ C * (n : ℝ) ^ ε := by
  have ht₁ : 0 < t + 1 := by linarith
  let δ := ε / (t + 1)
  have hδ : 0 < δ := div_pos hε ht₁
  obtain ⟨A, hA, HA⟩ := exists_card_divisors_le_rpow hδ
  obtain ⟨B, hB, HB⟩ := exists_rootCount_le_rpow hQ hirr hδ
  have hAt : 1 ≤ A ^ t := Real.one_le_rpow hA ht
  refine ⟨A ^ t * B, one_le_mul_of_one_le_of_one_le hAt hB, fun n hn => ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  calc
    _ ≤ (A * (n : ℝ) ^ δ) ^ t * (B * (n : ℝ) ^ δ) :=
      mul_le_mul (Real.rpow_le_rpow (Nat.cast_nonneg _) (HA n hn) ht) (HB n hn)
        (Nat.cast_nonneg _) (Real.rpow_nonneg (by positivity) _)
    _ = _ := by
      rw [Real.mul_rpow (zero_le_one.trans hA) (Real.rpow_nonneg hn'.le _), ← Real.rpow_mul hn'.le]
      calc
        _ = (A ^ t * B) * ((n : ℝ) ^ (δ * t) * (n : ℝ) ^ δ) := by ring
        _ = _ := by
          rw [← Real.rpow_add hn', show δ * t + δ = ε by dsimp [δ]; field_simp]

/-- The root weight restricted to powerful integers. -/
noncomputable def powerfulRootWeight (Q : ℤ[X]) (t : ℝ) (n : {n : ℕ // Powerful n}) : ℝ :=
  (n.1.divisors.card : ℝ) ^ t * (rootCount Q n.1 : ℝ) / n.1

theorem powerfulRootWeight_nonneg (Q : ℤ[X]) (t : ℝ) (n : {n : ℕ // Powerful n}) :
    0 ≤ powerfulRootWeight Q t n := by
  unfold powerfulRootWeight
  positivity

theorem summable_powerfulRootWeight {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    (hirr : Irreducible (Q.map (Int.castRingHom ℚ))) {t : ℝ} (ht : 0 ≤ t) :
    Summable (powerfulRootWeight Q t) := by
  obtain ⟨C, hC, HC⟩ := exists_divisorRootWeight_le_rpow hQ hirr ht (by norm_num : (0 : ℝ) < 1 / 4)
  apply Summable.of_nonneg_of_le (powerfulRootWeight_nonneg Q t) _
    ((summable_powerful_rpow (by norm_num : (1 / 2 : ℝ) < 3 / 4)).mul_left C)
  intro n
  have hn : (0 : ℝ) < n.1 := by exact_mod_cast Nat.pos_of_ne_zero n.2.1
  unfold powerfulRootWeight
  calc
    _ ≤ (C * (n.1 : ℝ) ^ (1 / 4 : ℝ)) / n.1 := div_le_div_of_nonneg_right (HC n.1 n.2.1) hn.le
    _ = C * (n.1 : ℝ) ^ (-(3 / 4 : ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one, mul_assoc, ← Real.rpow_add hn]
      norm_num

end NairTenenbaum

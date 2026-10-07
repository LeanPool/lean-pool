/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The factorial majorant of the interior analyticity induction

The sequence `b₀ = M`, `b_{k+1} = M K^k (k+1)!/(k+2)` bounds the weighted derivatives of order
`k` in the proof of `thm:analytic:interior`. This file proves that it closes the recursion
produced by one derivative step: the linear term, the convective and pressure products (whose
binomial convolutions stay within a constant multiple of the majorant), and the analytic force.
-/

public section


noncomputable section

namespace CIV

/-- The majorant of the induction on the derivative order in the proof of
`thm:analytic:interior`: `b₀ = M` and `b_{k+1} = M K^k (k+1)! / (k+2)`. -/
@[expose] def kahaneMajorant (M K : ℝ) : ℕ → ℝ
  | 0 => M
  | k + 1 => M * K ^ k * ((k + 1).factorial : ℝ) / ((k : ℝ) + 2)

/-- The majorant is below `M K^k k!`. -/
theorem kahaneMajorant_le {M K : ℝ} (hM : 0 ≤ M) (hK : 1 ≤ K) (k : ℕ) :
    kahaneMajorant M K k ≤ M * K ^ k * (k.factorial : ℝ) := by
  rcases k with _ | k
  · simp [kahaneMajorant]
  · simp only [kahaneMajorant]
    have hK0 : 0 ≤ K := by linarith only [hK]
    have hKk : K ^ k ≤ K ^ (k + 1) := pow_le_pow_right₀ hK (Nat.le_succ k)
    have hfac : (0 : ℝ) ≤ ((k + 1).factorial : ℝ) := Nat.cast_nonneg _
    have hk2 : (1 : ℝ) ≤ (k : ℝ) + 2 := by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith only [this]
    rw [div_le_iff₀ (by linarith only [hk2])]
    have h1 : M * K ^ k * ((k + 1).factorial : ℝ) ≤ M * K ^ (k + 1) * ((k + 1).factorial : ℝ) := by
      gcongr
    have h2 : 0 ≤ M * K ^ (k + 1) * ((k + 1).factorial : ℝ) := by positivity
    nlinarith only [h1, h2, hk2]

/-- Each convective product in the recursion is below `M² K^{k-1} k!/2`. -/
theorem kahaneMajorant_convective_term_le {M K : ℝ} (hK : 1 ≤ K) {k m : ℕ}
    (hm1 : 1 ≤ m) (hmk : m ≤ k) :
    (k.choose m : ℝ) * (kahaneMajorant M K m * kahaneMajorant M K (k + 1 - m)) ≤
      M ^ 2 * K ^ (k - 1) * (k.factorial : ℝ) / 2 := by
  obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, k = a + 1 + n := ⟨k - (a + 1), by omega⟩
  have hkm : a + 1 + n + 1 - (a + 1) = n + 1 := by omega
  have hk1 : a + 1 + n - 1 = a + n := by omega
  rw [hkm, hk1]
  simp only [kahaneMajorant]
  have hfac : ((a + 1 + n).choose (a + 1) : ℝ) * ((a + 1).factorial : ℝ) * (n.factorial : ℝ) =
      ((a + 1 + n).factorial : ℝ) := by
    have := Nat.choose_mul_factorial_mul_factorial (n := a + 1 + n) (k := a + 1) (by omega)
    rw [show a + 1 + n - (a + 1) = n by omega] at this
    exact_mod_cast this
  have hn1 : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
    push_cast [Nat.factorial_succ]; ring
  have hK0 : 0 ≤ K := by linarith only [hK]
  set X : ℝ := M ^ 2 * K ^ (a + n) * ((a + 1 + n).factorial : ℝ) with hX
  have hX0 : 0 ≤ X := by positivity
  have hid : ((a + 1 + n).choose (a + 1) : ℝ) *
      (M * K ^ a * ((a + 1).factorial : ℝ) / ((a : ℝ) + 2) *
        (M * K ^ n * ((n + 1).factorial : ℝ) / ((n : ℝ) + 2))) =
      X * (((n : ℝ) + 1) / (((a : ℝ) + 2) * ((n : ℝ) + 2))) := by
    rw [hX, ← hfac, hn1, pow_add]
    field_simp
  rw [hid]
  have hq : ((n : ℝ) + 1) / (((a : ℝ) + 2) * ((n : ℝ) + 2)) ≤ 1 / 2 := by
    have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith only [ha, hn]
  calc X * (((n : ℝ) + 1) / (((a : ℝ) + 2) * ((n : ℝ) + 2))) ≤ X * (1 / 2) :=
        mul_le_mul_of_nonneg_left hq hX0
    _ = X / 2 := by ring

/-- Each pressure product in the recursion is below `M² K^k k!`. -/
theorem kahaneMajorant_pressure_term_le {M K : ℝ} (hK : 1 ≤ K) {k m : ℕ}
    (hm1 : 1 ≤ m) (hmk : m + 1 ≤ k) :
    (k.choose m : ℝ) * (kahaneMajorant M K (m + 1) * kahaneMajorant M K (k + 1 - m)) ≤
      M ^ 2 * K ^ k * (k.factorial : ℝ) := by
  obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, k = a + 1 + (n + 1) := ⟨k - (a + 2), by omega⟩
  have hkm : a + 1 + (n + 1) + 1 - (a + 1) = n + 1 + 1 := by omega
  rw [hkm]
  simp only [kahaneMajorant]
  have hfac : ((a + 1 + (n + 1)).choose (a + 1) : ℝ) * ((a + 1).factorial : ℝ) *
      ((n + 1).factorial : ℝ) = ((a + 1 + (n + 1)).factorial : ℝ) := by
    have := Nat.choose_mul_factorial_mul_factorial (n := a + 1 + (n + 1)) (k := a + 1) (by omega)
    rw [show a + 1 + (n + 1) - (a + 1) = n + 1 by omega] at this
    exact_mod_cast this
  have ha1 : ((a + 1 + 1).factorial : ℝ) = ((a : ℝ) + 2) * ((a + 1).factorial : ℝ) := by
    push_cast [Nat.factorial_succ]; ring
  have hn1 : ((n + 1 + 1).factorial : ℝ) = ((n : ℝ) + 2) * ((n + 1).factorial : ℝ) := by
    push_cast [Nat.factorial_succ]; ring
  have hK0 : 0 ≤ K := by linarith only [hK]
  set X : ℝ := M ^ 2 * K ^ (a + 1 + (n + 1)) * ((a + 1 + (n + 1)).factorial : ℝ) with hX
  have hX0 : 0 ≤ X := by positivity
  have hid : ((a + 1 + (n + 1)).choose (a + 1) : ℝ) *
      (M * K ^ (a + 1) * ((a + 1 + 1).factorial : ℝ) / (((a + 1 : ℕ) : ℝ) + 2) *
        (M * K ^ (n + 1) * ((n + 1 + 1).factorial : ℝ) / (((n + 1 : ℕ) : ℝ) + 2))) =
      X * ((((a : ℝ) + 2) * ((n : ℝ) + 2)) / (((a : ℝ) + 3) * ((n : ℝ) + 3))) := by
    rw [hX, ← hfac, ha1, hn1, pow_add]
    push_cast
    field_simp
    ring
  rw [hid]
  have hq : (((a : ℝ) + 2) * ((n : ℝ) + 2)) / (((a : ℝ) + 3) * ((n : ℝ) + 3)) ≤ 1 := by
    have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [div_le_one (by positivity)]
    nlinarith only [ha, hn]
  calc X * ((((a : ℝ) + 2) * ((n : ℝ) + 2)) / (((a : ℝ) + 3) * ((n : ℝ) + 3))) ≤ X * 1 :=
        mul_le_mul_of_nonneg_left hq hX0
    _ = X := mul_one X

/-- The majorant closes the one-step recursion of the derivative estimates: with
`θ = 1 / (400 C (1 + M))` and `K ≥ 12800 C² (1 + M)`, twice the step bound at order `k` is below
`b_{k+1}`. -/
theorem kahaneMajorant_step_le {C M K θ Mf af : ℝ} (hC : 1 ≤ C) (hM : 1 ≤ M) (haf : 0 < af)
    (hMf : 0 ≤ Mf) (hMfM : Mf * (1 + 3 / af) ≤ M) (hθ : θ = 1 / (400 * C * (1 + M)))
    (hK : 12800 * C ^ 2 * (1 + M) ≤ K) (hKaf : 1 / af ≤ K) (hK1 : 1 ≤ K) {k : ℕ} (hk : 1 ≤ k) :
    2 * (C * (θ / (k + 1) * (Mf * af ^ (-(k : ℝ)) * (k.factorial : ℝ) +
        3 * (Mf * af ^ (-((k + 1 : ℕ) : ℝ)) * ((k + 1).factorial : ℝ)) +
        6 * ∑ m ∈ Finset.Icc 1 k, (k.choose m : ℝ) *
          (kahaneMajorant M K m * kahaneMajorant M K (k + 1 - m)) +
        18 * ∑ m ∈ Finset.Icc 1 (k - 1), (k.choose m : ℝ) *
          (kahaneMajorant M K (m + 1) * kahaneMajorant M K (k + 1 - m))) +
      2 * (k + 1) * kahaneMajorant M K k / θ)) ≤ kahaneMajorant M K (k + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hM0 : 0 ≤ M := by linarith only [hM]
  have hK0 : 0 ≤ K := by linarith only [hK1]
  have hC0 : 0 < C := by linarith only [hC]
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  set P : ℝ := K ^ j with hP
  set F : ℝ := ((j + 1).factorial : ℝ) with hF
  have hP0 : 0 ≤ P := by positivity
  have hF0 : 0 ≤ F := by positivity
  set Q : ℝ := M * P * F with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hθpos : 0 < θ := by rw [hθ]; positivity
  have hCθ : C * θ = 1 / (400 * (1 + M)) := by rw [hθ]; field_simp
  -- the sums
  have hV : ∑ m ∈ Finset.Icc 1 (j + 1), ((j + 1).choose m : ℝ) *
      (kahaneMajorant M K m * kahaneMajorant M K (j + 1 + 1 - m)) ≤
      ((j : ℝ) + 1) * (M * Q / 2) := by
    calc _ ≤ ∑ _m ∈ Finset.Icc 1 (j + 1), M ^ 2 * K ^ (j + 1 - 1) *
          ((j + 1).factorial : ℝ) / 2 :=
          Finset.sum_le_sum fun m hm => kahaneMajorant_convective_term_le hK1
            (Finset.mem_Icc.1 hm).1 (Finset.mem_Icc.1 hm).2
      _ = ((j : ℝ) + 1) * (M * Q / 2) := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, hQ, hP, hF,
            show j + 1 - 1 = j by omega]
          push_cast
          ring
  have hPn : ∑ m ∈ Finset.Icc 1 (j + 1 - 1), ((j + 1).choose m : ℝ) *
      (kahaneMajorant M K (m + 1) * kahaneMajorant M K (j + 1 + 1 - m)) ≤
      (j : ℝ) * (M * K * Q) := by
    calc _ ≤ ∑ _m ∈ Finset.Icc 1 (j + 1 - 1), M ^ 2 * K ^ (j + 1) *
          ((j + 1).factorial : ℝ) :=
          Finset.sum_le_sum fun m hm => kahaneMajorant_pressure_term_le hK1
            (Finset.mem_Icc.1 hm).1 (by have := (Finset.mem_Icc.1 hm).2; omega)
      _ = (j : ℝ) * (M * K * Q) := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, hQ, hP, hF,
            show j + 1 - 1 + 1 - 1 = j by omega, pow_succ]
          ring
  -- the force
  set A : ℝ := (1 / af) ^ (j + 1) with hA
  have hA0 : 0 ≤ A := by positivity
  have hAK : A ≤ K * P := by
    rw [hA, hP, ← pow_succ']
    exact pow_le_pow_left₀ (by positivity) hKaf _
  have hr1 : af ^ (-((j + 1 : ℕ) : ℝ)) = A := by
    rw [Real.rpow_neg haf.le, Real.rpow_natCast, hA, one_div_pow, one_div]
  have hr2 : af ^ (-((j + 1 + 1 : ℕ) : ℝ)) = A * (1 / af) := by
    rw [Real.rpow_neg haf.le, Real.rpow_natCast, hA, ← pow_succ, one_div_pow, one_div]
  have hfs : ((j + 1 + 1).factorial : ℝ) = ((j : ℝ) + 2) * F := by
    rw [hF]; push_cast [Nat.factorial_succ]; ring
  have hΦ : θ / ((j + 1 : ℕ) + 1) * (Mf * af ^ (-((j + 1 : ℕ) : ℝ)) * ((j + 1).factorial : ℝ) +
      3 * (Mf * af ^ (-((j + 1 + 1 : ℕ) : ℝ)) * ((j + 1 + 1).factorial : ℝ))) ≤
      θ * (M * K * P * F) := by
    rw [hr1, hr2, hfs, ← hF]
    have hk2 : (0 : ℝ) < (j + 1 : ℕ) + 1 := by positivity
    have e : θ / ((j + 1 : ℕ) + 1) * (Mf * A * F + 3 * (Mf * (A * (1 / af)) * (((j : ℝ) + 2) * F)))
        = θ * (A * F) * (Mf * (1 / ((j + 1 : ℕ) + 1)) + Mf * (3 / af)) := by
      push_cast
      field_simp
      ring
    rw [e]
    have hinv : 1 / (((j + 1 : ℕ) : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hk2]; push_cast; linarith only [hj]
    have h1 : Mf * (1 / ((j + 1 : ℕ) + 1)) + Mf * (3 / af) ≤ M := by
      have := mul_le_mul_of_nonneg_left hinv hMf
      nlinarith only [this, hMfM]
    have h2 : θ * (A * F) * (Mf * (1 / ((j + 1 : ℕ) + 1)) + Mf * (3 / af)) ≤ θ * (A * F) * M :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : θ * (A * F) * M ≤ θ * (K * P * F) * M := by gcongr
    nlinarith only [h2, h3]
  -- assemble
  have hbk : kahaneMajorant M K (j + 1) = Q / ((j : ℝ) + 2) := by
    simp only [kahaneMajorant, hQ, hP, hF]
  have hbk1 : kahaneMajorant M K (j + 1 + 1) = K * Q * ((j : ℝ) + 2) / ((j : ℝ) + 3) := by
    simp only [kahaneMajorant, hQ, hP, hF]
    push_cast [Nat.factorial_succ]
    field_simp
    ring
  rw [hbk1, hbk]
  set Vs := ∑ m ∈ Finset.Icc 1 (j + 1), ((j + 1).choose m : ℝ) *
      (kahaneMajorant M K m * kahaneMajorant M K (j + 1 + 1 - m)) with hVs
  set Ps := ∑ m ∈ Finset.Icc 1 (j + 1 - 1), ((j + 1).choose m : ℝ) *
      (kahaneMajorant M K (m + 1) * kahaneMajorant M K (j + 1 + 1 - m)) with hPs
  set Φs := Mf * af ^ (-((j + 1 : ℕ) : ℝ)) * ((j + 1).factorial : ℝ) +
      3 * (Mf * af ^ (-((j + 1 + 1 : ℕ) : ℝ)) * ((j + 1 + 1).factorial : ℝ)) with hΦs
  have hD : ((j + 1 : ℕ) : ℝ) + 1 = (j : ℝ) + 2 := by push_cast; ring
  rw [hD] at hΦ ⊢
  have hD0 : (0 : ℝ) < (j : ℝ) + 2 := by positivity
  have hVs0 : Vs ≤ ((j : ℝ) + 1) * (M * Q / 2) := hV
  have hB2 : θ / ((j : ℝ) + 2) * (6 * Vs) ≤ 3 * (θ * (M * Q)) := by
    have h1 : θ / ((j : ℝ) + 2) * (6 * Vs) ≤
        θ / ((j : ℝ) + 2) * (6 * (((j : ℝ) + 1) * (M * Q / 2))) :=
      mul_le_mul_of_nonneg_left (by linarith only [hVs0]) (by positivity)
    have h2 : θ / ((j : ℝ) + 2) * (6 * (((j : ℝ) + 1) * (M * Q / 2))) =
        3 * (θ * (M * Q)) * (((j : ℝ) + 1) / ((j : ℝ) + 2)) := by
      field_simp
      ring
    have h3 : ((j : ℝ) + 1) / ((j : ℝ) + 2) ≤ 1 := by
      rw [div_le_one hD0]; linarith only
    have h4 : 0 ≤ 3 * (θ * (M * Q)) := by positivity
    nlinarith only [h1, h2, h3, h4]
  have hB3 : θ / ((j : ℝ) + 2) * (18 * Ps) ≤ 18 * (θ * (M * K * Q)) := by
    have h1 : θ / ((j : ℝ) + 2) * (18 * Ps) ≤ θ / ((j : ℝ) + 2) * (18 * ((j : ℝ) * (M * K * Q))) :=
      mul_le_mul_of_nonneg_left (by linarith only [hPn]) (by positivity)
    have h2 : θ / ((j : ℝ) + 2) * (18 * ((j : ℝ) * (M * K * Q))) =
        18 * (θ * (M * K * Q)) * ((j : ℝ) / ((j : ℝ) + 2)) := by
      field_simp
    have h3 : (j : ℝ) / ((j : ℝ) + 2) ≤ 1 := by
      rw [div_le_one hD0]; linarith only
    have h4 : 0 ≤ 18 * (θ * (M * K * Q)) := by positivity
    nlinarith only [h1, h2, h3, h4]
  have hB1 : θ / ((j : ℝ) + 2) * Φs ≤ θ * (K * Q) := by
    have : θ * (M * K * P * F) = θ * (K * Q) := by rw [hQ]; ring
    linarith only [hΦ, this]
  have hB4 : 2 * ((j : ℝ) + 2) * (Q / ((j : ℝ) + 2)) / θ = 2 * Q / θ := by
    field_simp
  -- the constants
  have hCθM : C * θ * M ≤ 1 / 400 := by
    rw [hCθ, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith only
  have hCθ1 : C * θ ≤ 1 / 400 := by
    rw [hCθ, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith only [hM0]
  have hCdθ : C / θ ≤ K / 32 := by
    rw [hθ, div_div_eq_mul_div, div_one]
    nlinarith only [hK]
  have hKQ : Q ≤ K * Q := by nlinarith only [hK1, hQ0]
  have hRHS : 2 / 3 * (K * Q) ≤ K * Q * ((j : ℝ) + 2) / ((j : ℝ) + 3) := by
    rw [le_div_iff₀ (by positivity)]
    have : 0 ≤ K * Q := by positivity
    nlinarith only [this, hj]
  have hKQ0 : 0 ≤ K * Q := by positivity
  have e1 : 2 * (C * (θ / ((j : ℝ) + 2) * (Φs + 6 * Vs + 18 * Ps) +
      2 * ((j : ℝ) + 2) * (Q / ((j : ℝ) + 2)) / θ)) =
      2 * C * (θ / ((j : ℝ) + 2) * Φs) + 2 * C * (θ / ((j : ℝ) + 2) * (6 * Vs)) +
        2 * C * (θ / ((j : ℝ) + 2) * (18 * Ps)) + 2 * C * (2 * Q / θ) := by
    rw [hB4]; ring
  rw [e1]
  have t1 : 2 * C * (θ / ((j : ℝ) + 2) * Φs) ≤ 2 * (C * θ) * (K * Q) := by
    have := mul_le_mul_of_nonneg_left hB1 (by positivity : (0 : ℝ) ≤ 2 * C)
    linarith only [this]
  have t2 : 2 * C * (θ / ((j : ℝ) + 2) * (6 * Vs)) ≤ 6 * (C * θ * M) * Q := by
    have := mul_le_mul_of_nonneg_left hB2 (by positivity : (0 : ℝ) ≤ 2 * C)
    linarith only [this]
  have t3 : 2 * C * (θ / ((j : ℝ) + 2) * (18 * Ps)) ≤ 36 * (C * θ * M) * (K * Q) := by
    have := mul_le_mul_of_nonneg_left hB3 (by positivity : (0 : ℝ) ≤ 2 * C)
    linarith only [this]
  have t4 : 2 * C * (2 * Q / θ) = 4 * (C / θ) * Q := by ring
  have u1 : 2 * (C * θ) * (K * Q) ≤ 2 * (1 / 400) * (K * Q) :=
    mul_le_mul_of_nonneg_right (by linarith only [hCθ1]) hKQ0
  have u2 : 6 * (C * θ * M) * Q ≤ 6 * (1 / 400) * (K * Q) := by
    have h := mul_le_mul_of_nonneg_right hCθM hQ0
    nlinarith only [h, hKQ]
  have u3 : 36 * (C * θ * M) * (K * Q) ≤ 36 * (1 / 400) * (K * Q) := by
    have h := mul_le_mul_of_nonneg_right hCθM hKQ0
    linarith only [h]
  have u4 : 4 * (C / θ) * Q ≤ 4 * (K / 32) * Q := by
    have h := mul_le_mul_of_nonneg_right hCdθ hQ0
    linarith only [h]
  have u4' : 4 * (K / 32) * Q = (K * Q) / 8 := by ring
  linarith only [t1, t2, t3, t4, u1, u2, u3, u4, u4', hRHS, hKQ0]

end CIV

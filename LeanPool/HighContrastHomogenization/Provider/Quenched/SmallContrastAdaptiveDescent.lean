/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAdaptiveDepthGate
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCadenceFloor

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastAdaptiveDescent

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The adaptive-depth descent: rounds of the floor cadence at doubling lag

  the stated condition mechanism as an
iteration: the family clause is consumed one step at a time, each step a
proved `cadence_profile_descent_floor` (the corresponding clause) instance on the shifted
sequence, with

* the round's quadratic anchored at the FIXED round lag `L`, so the anchor
  value is the previous level schedule level by antitonicity (`F (r+k−L) ≤ F r`),
  and the `∀ m` slot of the corresponding clause is discharged by weakening;
* the pre-round drop history entering as the geometric echo
  `A·ra^k·DS(r) ≤ A·ra^T·δ₀` (the shift recurrence
  `iterationDropSum_shift`), absorbed into the round's constant error;
* the level-adapted source bound `src (r+k) (r+k−L) ≤ sE` — the round's
  own `M_λ` charge.

The level schedule induction (`the descent induction theorem`) then propagates levels
across rounds: any level schedule whose arithmetic is consistent (each next level
covers the round's floor, each next start covers the round's firing
region) yields `F n ≤ lam j` for `n ≥ r j`.  The explicit level schedule and the
geometric conversion are
-/

namespace HCPolySupport.HighContrast.Quenched

noncomputable section

/-- The drop history of a shifted sequence: the pre-history enters as one
geometric echo. -/
theorem iterationDropSum_shift (ra : ℝ) (F : ℕ → ℝ) (r : ℕ) :
    ∀ k, iterationDropSum ra F (r + k) =
      ra ^ k * iterationDropSum ra F r +
        iterationDropSum ra (fun j => F (r + j)) k := by
  intro k
  induction k with
  | zero =>
      have h0 : iterationDropSum ra (fun j => F (r + j)) 0 = 0 := by
        rw [iterationDropSum, Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      rw [Nat.add_zero, h0, pow_zero]
      ring
  | succ k ih =>
      have h1 : r + (k + 1) = (r + k) + 1 := by omega
      have h2 : iterationDropSum ra (fun j => F (r + j)) (k + 1) =
          ra * iterationDropSum ra (fun j => F (r + j)) k +
            (F (r + k) - F (r + (k + 1))) := by
        have h3 := iterationDropSum_succ ra (fun j => F (r + j)) k
        simpa using h3
      rw [h1, iterationDropSum_succ, ih, h2, pow_succ, ← h1]
      ring

/-- **One round of the adaptive descent.**  From entry level `lam` at the
round start `r`, the family clause at the fixed round lag `L`, the memory
margin `T`, and the level-adapted source charge `sE`, the proved floor
cadence grinds the level along the round's windows. -/
theorem adaptive_descent_stage {A alpha lam d0 sE : ℝ} {F : ℕ → ℝ}
    {src : ℕ → ℕ → ℝ} {ns r L T cA : ℕ}
    (hA : 1 ≤ A) (halpha : 0 < alpha)
    (hlam0 : 0 ≤ lam) (hsmall : 9 * A * lam ≤ 1)
    (hcA : 24 * A ≤ (3 : ℝ) ^ (alpha * (cA : ℝ)))
    (hFnn : ∀ n, 0 ≤ F n)
    (hFmono : ∀ p q : ℕ, p ≤ q → F q ≤ F p)
    (hFd0 : F 0 ≤ d0) (hd0 : 0 ≤ d0) (hsE : 0 ≤ sE)
    (hnsr : ns ≤ r) (hentry : F r ≤ lam)
    (hfam : ∀ n m : ℕ, ns ≤ m → m ≤ n →
      F n ≤ A * iterationDropSum ((3 : ℝ) ^ (-alpha)) F n +
        A * F m ^ 2 + src n m)
    (hsrcL : ∀ k : ℕ, L ≤ k → src (r + k) (r + k - L) ≤ sE) :
    ∀ i : ℕ, ∀ k : ℕ, max L T + i * (cA + 1) ≤ k →
      F (r + k) ≤ lam * (2 * A / (2 * A + 1)) ^ i +
        8 * A * (A * ((3 : ℝ) ^ (-alpha)) ^ T * d0 + A * lam ^ 2 + sE) := by
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le one_pos hA
  set ra : ℝ := (3 : ℝ) ^ (-alpha) with hradef
  have hra0 : (0 : ℝ) < ra := Real.rpow_pos_of_pos (by norm_num) _
  have hra1 : ra ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by linarith only [halpha])
  have hE00 : 0 ≤ A * ra ^ T * d0 + A * lam ^ 2 + sE := by
    have h1 : (0 : ℝ) ≤ ra ^ T := pow_nonneg hra0.le T
    positivity
  have hDSr : iterationDropSum ra F r ≤ d0 := by
    have h1 := iterationDropSum_le_total hFmono hra0.le hra1 r
    have h2 := hFnn r
    linarith only [h1, h2, hFd0]
  have hDSr0 : 0 ≤ iterationDropSum ra F r :=
    iterationDropSum_nonneg hFmono hra0.le r
  have hrec356 : ∀ k : ℕ, max L T ≤ k → ∀ m' : ℕ, max L T ≤ m' → m' ≤ k →
      F (r + k) ≤ A * iterationDropSum ra (fun j => F (r + j)) k +
        A * F (r + m') ^ 2 + (A * ra ^ T * d0 + A * lam ^ 2 + sE) := by
    intro k hk m' hm'1 hm'2
    have hkL : L ≤ k := le_trans (le_max_left L T) hk
    have hkT : T ≤ k := le_trans (le_max_right L T) hk
    have h1 := hfam (r + k) (r + k - L) (by omega) (by omega)
    have hanchor : F (r + k - L) ≤ lam :=
      le_trans (hFmono r (r + k - L) (by omega)) hentry
    have hFnn' := hFnn (r + k - L)
    have hsq : F (r + k - L) ^ 2 ≤ lam ^ 2 := by
      nlinarith only [hanchor, hFnn', hlam0]
    have hquad : A * F (r + k - L) ^ 2 ≤ A * lam ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hA0.le
    have hshift := iterationDropSum_shift ra F r k
    have hrak : ra ^ k ≤ ra ^ T :=
      pow_le_pow_of_le_one hra0.le hra1 hkT
    have hecho : A * (ra ^ k * iterationDropSum ra F r) ≤
        A * ra ^ T * d0 := by
      have h4 : (0 : ℝ) ≤ ra ^ k := pow_nonneg hra0.le k
      have h5 : (0 : ℝ) ≤ ra ^ T := pow_nonneg hra0.le T
      have h3 : ra ^ k * iterationDropSum ra F r ≤ ra ^ T * d0 := by
        nlinarith only [hrak, hDSr, hDSr0, h4, h5]
      calc A * (ra ^ k * iterationDropSum ra F r) ≤ A * (ra ^ T * d0) :=
            mul_le_mul_of_nonneg_left h3 hA0.le
        _ = A * ra ^ T * d0 := by ring
    have hsrc := hsrcL k hkL
    have hquad' : (0 : ℝ) ≤ A * F (r + m') ^ 2 := by positivity
    have hDSsh : A * iterationDropSum ra F (r + k) =
        A * (ra ^ k * iterationDropSum ra F r) +
          A * iterationDropSum ra (fun j => F (r + j)) k := by
      rw [hshift]
      ring
    linarith only [h1, hDSsh, hquad, hquad', hsrc, hecho]
  have hmain := cadence_profile_descent_floor (F := fun k => F (r + k))
    (ns := max L T) (cA := cA)
    hA halpha hlam0 hE00 hsmall hcA
    (fun k => hFnn (r + k))
    (fun p q hpq => hFmono (r + p) (r + q) (by omega))
    (by simpa using hentry)
    hrec356
  intro i k hk
  exact (hmain i).2 k hk

/-- **The level schedule induction.**  An arithmetically consistent level schedule of
levels, starts, lags, memories, and window counts propagates: the level
`lam j` holds from the start `r j` on. -/
theorem adaptive_descent_ledger {A alpha d0 : ℝ} {F : ℕ → ℝ}
    {src : ℕ → ℕ → ℝ} {ns cA : ℕ}
    {lam sE : ℕ → ℝ} {r L T ii : ℕ → ℕ}
    (hA : 1 ≤ A) (halpha : 0 < alpha) (hd0 : 0 ≤ d0)
    (hcA : 24 * A ≤ (3 : ℝ) ^ (alpha * (cA : ℝ)))
    (hFnn : ∀ n, 0 ≤ F n)
    (hFmono : ∀ p q : ℕ, p ≤ q → F q ≤ F p)
    (hFd0 : ∀ n, F n ≤ d0)
    (hfam : ∀ n m : ℕ, ns ≤ m → m ≤ n →
      F n ≤ A * iterationDropSum ((3 : ℝ) ^ (-alpha)) F n +
        A * F m ^ 2 + src n m)
    (hlam0 : ∀ j, 0 ≤ lam j)
    (hlamsmall : ∀ j, 9 * A * lam j ≤ 1)
    (hbase : d0 ≤ lam 0)
    (hr0 : ns ≤ r 0)
    (hsrcL : ∀ j, ∀ k : ℕ, L j ≤ k →
      src (r j + k) (r j + k - L j) ≤ sE j)
    (hsE0 : ∀ j, 0 ≤ sE j)
    (hstep : ∀ j,
      lam j * (2 * A / (2 * A + 1)) ^ ii j +
        8 * A * (A * ((3 : ℝ) ^ (-alpha)) ^ T j * d0 +
          A * lam j ^ 2 + sE j) ≤ lam (j + 1))
    (hspace : ∀ j, r j + (max (L j) (T j) + ii j * (cA + 1)) ≤ r (j + 1)) :
    ∀ j, ∀ n : ℕ, r j ≤ n → F n ≤ lam j := by
  have hns_all : ∀ j, ns ≤ r j := by
    intro j
    induction j with
    | zero => exact hr0
    | succ j ihj =>
        have := hspace j
        omega
  intro j
  induction j with
  | zero =>
      intro n _
      exact le_trans (hFd0 n) hbase
  | succ j ih =>
      intro n hn
      have hentry : F (r j) ≤ lam j := ih (r j) le_rfl
      have hround := adaptive_descent_stage (src := src) (L := L j) (T := T j)
        hA halpha (hlam0 j) (hlamsmall j) hcA hFnn hFmono (hFd0 0) hd0
        (hsE0 j) (hns_all j) hentry hfam (hsrcL j)
      have hk : max (L j) (T j) + ii j * (cA + 1) ≤ n - r j := by
        have := hspace j
        omega
      have hn' : r j + (n - r j) = n := by
        have := hspace j
        omega
      have hval := hround (ii j) (n - r j) hk
      rw [hn'] at hval
      exact le_trans hval (hstep j)

end

end HCPolySupport.HighContrast.Quenched

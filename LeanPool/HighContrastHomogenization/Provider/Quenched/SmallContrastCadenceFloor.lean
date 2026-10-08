/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCadenceProfile

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastCadenceFloor

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The cadence descent at a constant error floor

The repair: the tree's family recursion carries a positive generation-independent
source component in its error slot, so the `deltaRec·ra^n` clause of row 351
is not the producible shape.  That induction, repeated stage-by-stage at a
CONSTANT error `E₀`, closes with the descent terminating at the floor
`8A·E₀`:

```
F n ≤ delta·θ^i + 8A·E₀        for every n ≥ ns + i·(c_A+1),
```

with the same `24A` margin and the law-free bookkeeping constants `(8A, 16A)`
— the Q-step closes from `8A + 2/3 ≤ 16A` and the collapse branch from
`(8/3)A + 4 ≤ 8A`, both true at `A ≥ 1`.  The descent to the floor takes
`⌈log(δ/(8A·E₀))/log(1/θ)⌉` stages — a length proportional to the level's
logarithm, which is what makes the outer bootstrap's total threshold linear:
instantiating the design at the improved floor gives stage lengths that
sum geometrically to the final level's logarithm.
-/

namespace HCPolySupport.HighContrast.Quenched

/-- **The cadence descent at a constant floor.** -/
theorem cadence_profile_descent_floor {A alpha delta E0 : ℝ} {F : ℕ → ℝ}
    {ns cA : ℕ}
    (hA : 1 ≤ A) (halpha : 0 < alpha) (hd0 : 0 ≤ delta) (hE0 : 0 ≤ E0)
    (hsmall : 9 * A * delta ≤ 1)
    (hcA : 24 * A ≤ (3 : ℝ) ^ (alpha * (cA : ℝ)))
    (hFnn : ∀ n, 0 ≤ F n)
    (hFmono : ∀ p q : ℕ, p ≤ q → F q ≤ F p)
    (hFinit : F 0 ≤ delta)
    (hrec : ∀ n : ℕ, ns ≤ n → ∀ m : ℕ, ns ≤ m → m ≤ n →
      F n ≤ A * iterationDropSum ((3 : ℝ) ^ (-alpha)) F n +
        A * F m ^ 2 + E0) :
    ∀ i : ℕ,
      iterationDropSum ((3 : ℝ) ^ (-alpha)) F (ns + i * (cA + 1)) ≤
          2 * delta * (2 * A / (2 * A + 1)) ^ i + 16 * A * E0 ∧
        ∀ n : ℕ, ns + i * (cA + 1) ≤ n →
          F n ≤ delta * (2 * A / (2 * A + 1)) ^ i + 8 * A * E0 := by
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le one_pos hA
  set ra : ℝ := (3 : ℝ) ^ (-alpha) with hradef
  have hra0 : (0 : ℝ) < ra := Real.rpow_pos_of_pos (by norm_num) _
  have hra1 : ra ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by linarith only [halpha])
  set th : ℝ := 2 * A / (2 * A + 1) with hthdef
  have hden : (0 : ℝ) < 2 * A + 1 := by linarith only [hA0]
  have hth0 : 0 < th := div_pos (by linarith only [hA0]) hden
  have hth1 : th ≤ 1 := by
    rw [hthdef, div_le_one hden]
    linarith only []
  have hth23 : 2 / 3 ≤ th := by
    rw [hthdef, le_div_iff₀ hden]
    linarith only [hA]
  have hAra : A * ra ^ (cA + 1) ≤ 1 / 24 := cadence_head_margin24 hA halpha hcA
  have hra_cA : ra ^ (cA + 1) ≤ 1 / 24 := by
    have h1 : ra ^ (cA + 1) ≤ A * ra ^ (cA + 1) := by
      have := pow_nonneg hra0.le (cA + 1)
      nlinarith only [hA, this]
    linarith only [h1, hAra]
  have hFdelta : ∀ n : ℕ, F n ≤ delta := fun n =>
    le_trans (hFmono 0 n (Nat.zero_le n)) hFinit
  intro i
  induction i with
  | zero =>
    constructor
    · have h1 := iterationDropSum_le_total_drop hra0.le hra1 hFmono
        (ns + 0 * (cA + 1))
      have h2 := hFnn (ns + 0 * (cA + 1))
      rw [pow_zero]
      nlinarith only [h1, h2, hFinit, hE0, hA, hd0]
    · intro n _
      rw [pow_zero, mul_one]
      have := hFdelta n
      nlinarith only [this, hE0, hA, hd0]
  | succ i ih =>
    obtain ⟨Qi, Pi⟩ := ih
    set ai : ℕ := ns + i * (cA + 1) with haidef
    set ai1 : ℕ := ns + (i + 1) * (cA + 1) with hai1def
    have hstep : ai1 = ai + (cA + 1) := by rw [haidef, hai1def]; ring
    have hPai : F ai ≤ delta * th ^ i + 8 * A * E0 := Pi ai (le_refl ai)
    have hthpow0 : (0 : ℝ) ≤ th ^ i := pow_nonneg hth0.le i
    have hthpow0' : (0 : ℝ) ≤ delta * th ^ i := mul_nonneg hd0 hthpow0
    have hQ1 : iterationDropSum ra F ai1 ≤
        2 * delta * th ^ (i + 1) + 16 * A * E0 := by
      have hanch := iterationDropSum_anchored hra0.le hra1 hFmono
        (show ai ≤ ai1 by omega)
      have hDSnn : 0 ≤ iterationDropSum ra F ai :=
        iterationDropSum_nonneg hFmono (le_of_lt hra0) ai
      have hhead : ra ^ (ai1 - ai) * iterationDropSum ra F ai ≤
          ra ^ (cA + 1) * (2 * delta * th ^ i + 16 * A * E0) := by
        have hexp : ai1 - ai = cA + 1 := by omega
        rw [hexp]
        exact mul_le_mul_of_nonneg_left Qi (pow_nonneg hra0.le _)
      have hdropw : F ai - F ai1 ≤ delta * th ^ i + 8 * A * E0 := by
        have := hFnn ai1
        linarith only [hPai, this]
      have hquarter : ra ^ (cA + 1) * (2 * delta * th ^ i + 16 * A * E0) ≤
          (1 / 12) * (delta * th ^ i) + (2 / 3) * E0 := by
        have h2d : ra ^ (cA + 1) * (2 * delta * th ^ i) ≤
            (1 / 12) * (delta * th ^ i) := by
          nlinarith only [hra_cA, hthpow0', hA]
        have h16 : ra ^ (cA + 1) * (16 * A * E0) ≤ (2 / 3) * E0 := by
          have h1 : ra ^ (cA + 1) * A ≤ 1 / 24 := by
            have := hAra
            nlinarith only [this]
          nlinarith only [h1, hE0, pow_nonneg hra0.le (cA + 1)]
        nlinarith only [h2d, h16]
      have hth2 : (13 / 12 : ℝ) ≤ 2 * th := by linarith only [hth23]
      have hkey : delta * th ^ i + 8 * A * E0 +
          ((1 / 12) * (delta * th ^ i) + (2 / 3) * E0) ≤
          2 * delta * th ^ (i + 1) + 16 * A * E0 := by
        have hpow : 2 * delta * th ^ (i + 1) = (2 * th) * (delta * th ^ i) := by
          rw [pow_succ]
          ring
        have h1 : (13 / 12) * (delta * th ^ i) ≤ (2 * th) * (delta * th ^ i) :=
          mul_le_mul_of_nonneg_right hth2 hthpow0'
        have h2 : 8 * A * E0 + (2 / 3) * E0 ≤ 16 * A * E0 := by
          nlinarith only [hA, hE0]
        linarith only [h1, h2, hpow.le, hpow.ge]
      linarith only [hanch, hhead, hdropw, hquarter, hkey]
    refine ⟨hQ1, ?_⟩
    intro n hn
    have hain : ai ≤ n := by omega
    have hnsn : ns ≤ n := by omega
    have hnsai : ns ≤ ai := by omega
    have hrecn := hrec n hnsn ai hnsai hain
    have hDSb := iterationDropSum_anchored hra0.le hra1 hFmono hain
    have hdich := cadence_one_window_dichotomy (A := A) (Fn := F n)
      (FW := F ai) (DS := iterationDropSum ra F n)
      (hd := ra ^ (n - ai) * iterationDropSum ra F ai)
      (err := E0) hA (hFnn n) (hFnn ai)
      (by
        have := hFdelta n
        nlinarith only [this, hsmall, hA0.le, hFnn n])
      hrecn hDSb
    have hhd : ra ^ (n - ai) * iterationDropSum ra F ai ≤
        ra ^ (cA + 1) * (2 * delta * th ^ i + 16 * A * E0) := by
      have hDSnn : 0 ≤ iterationDropSum ra F ai :=
        iterationDropSum_nonneg hFmono (le_of_lt hra0) ai
      have hw : ra ^ (n - ai) ≤ ra ^ (cA + 1) := by
        refine pow_le_pow_of_le_one hra0.le hra1 ?_
        omega
      calc ra ^ (n - ai) * iterationDropSum ra F ai
          ≤ ra ^ (cA + 1) * iterationDropSum ra F ai :=
            mul_le_mul_of_nonneg_right hw hDSnn
        _ ≤ ra ^ (cA + 1) * (2 * delta * th ^ i + 16 * A * E0) :=
            mul_le_mul_of_nonneg_left Qi (pow_nonneg hra0.le _)
    rcases hdich with hcol | hprog
    · -- collapse branch
      have hshare : 4 * (A * (ra ^ (n - ai) * iterationDropSum ra F ai)) ≤
          (1 / 3) * (delta * th ^ i) + (8 / 3) * A * E0 := by
        have h1 : A * (ra ^ (n - ai) * iterationDropSum ra F ai) ≤
            A * (ra ^ (cA + 1) * (2 * delta * th ^ i + 16 * A * E0)) :=
          mul_le_mul_of_nonneg_left hhd hA0.le
        have h2 : A * (ra ^ (cA + 1) * (2 * delta * th ^ i + 16 * A * E0)) =
            (A * ra ^ (cA + 1)) * (2 * delta * th ^ i) +
              (A * ra ^ (cA + 1)) * (16 * A * E0) := by ring
        have h3 : (A * ra ^ (cA + 1)) * (2 * delta * th ^ i) ≤
            (1 / 24) * (2 * delta * th ^ i) := by
          refine mul_le_mul_of_nonneg_right hAra ?_
          linarith only [hthpow0']
        have h4 : (A * ra ^ (cA + 1)) * (16 * A * E0) ≤
            (1 / 24) * (16 * A * E0) := by
          refine mul_le_mul_of_nonneg_right hAra ?_
          nlinarith only [hA, hE0]
        linarith only [h1, h2.le, h2.ge, h3, h4]
      have hstep13 : (1 / 3) * (delta * th ^ i) ≤
          (1 / 2) * (delta * th ^ (i + 1)) := by
        have hkey : (1 : ℝ) / 3 ≤ (1 / 2) * th := by linarith only [hth23]
        have h1 : (1 / 3) * (delta * th ^ i) ≤
            ((1 / 2) * th) * (delta * th ^ i) :=
          mul_le_mul_of_nonneg_right hkey hthpow0'
        have h2 : ((1 / 2) * th) * (delta * th ^ i) =
            (1 / 2) * (delta * th ^ (i + 1)) := by
          rw [pow_succ]
          ring
        linarith only [h1, h2.le, h2.ge]
      have hpos1 : (0 : ℝ) ≤ delta * th ^ (i + 1) :=
        mul_nonneg hd0 (pow_nonneg hth0.le _)
      have hEfin : (8 / 3) * A * E0 + 4 * E0 ≤ 8 * A * E0 := by
        nlinarith only [hA, hE0]
      linarith only [hcol, hshare, hstep13, hpos1, hEfin]
    · -- progress branch
      have hth_inv : th * (1 + 1 / (2 * A)) = 1 := by
        rw [hthdef]
        field_simp
      have hFn : F n ≤ th * F ai := by
        have h1 : th * ((1 + 1 / (2 * A)) * F n) ≤ th * F ai :=
          mul_le_mul_of_nonneg_left (le_of_lt hprog) hth0.le
        have h2 : th * ((1 + 1 / (2 * A)) * F n) = F n := by
          rw [← mul_assoc, hth_inv, one_mul]
        linarith only [h1, h2.le, h2.ge]
      have hfin : th * F ai ≤ th * (delta * th ^ i + 8 * A * E0) :=
        mul_le_mul_of_nonneg_left hPai hth0.le
      have hsplit : th * (delta * th ^ i + 8 * A * E0) =
          delta * th ^ (i + 1) + th * (8 * A * E0) := by
        rw [pow_succ]
        ring
      have hlast : th * (8 * A * E0) ≤ 8 * A * E0 := by
        have h80 : (0 : ℝ) ≤ 8 * A * E0 := by nlinarith only [hA, hE0]
        nlinarith only [hth1, h80, hth0.le]
      linarith only [hFn, hfin, hsplit.le, hsplit.ge, hlast]

end HCPolySupport.HighContrast.Quenched

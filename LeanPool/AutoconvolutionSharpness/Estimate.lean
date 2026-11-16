/-
Copyright (c) 2026 Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić
-/
module

public import LeanPool.AutoconvolutionSharpness.Definitions
public import LeanPool.AutoconvolutionSharpness.Parameters
public import LeanPool.AutoconvolutionSharpness.Digits
public import LeanPool.AutoconvolutionSharpness.Levels

/-!
# Summing the extremal blocks

The analytic inputs below are the three bounds on the norms of the genuine
autoconvolution. The finite sums count the square integral contributed by all
disjoint plateaus at levels zero through `K`. The algebra here also explains
why the positive common scale `(r * b) ^ (2 * n)` cancels.
-/

@[expose] public section

open Finset

namespace Autoconvolutions.Estimate

/-- The upper bound on block heights at level `s`. -/
def height (n s : ℕ) : ℝ :=
  ((2 * n - s).factorial : ℝ) * ((2 * n + s).factorial : ℝ)

/-- The number of blocks at level `s` whose letters were all drawn distinctly. -/
def count (n r b s : ℕ) : ℝ :=
  (r.choose (2 * n - s) : ℝ) * (b.choose (2 * n + s) : ℝ)

theorem height_pos (n s : ℕ) : 0 < height n s := by
  unfold height
  positivity

theorem count_nonneg (n r b s : ℕ) : 0 ≤ count n r b s := by
  unfold count
  positivity

/-- Monotonicity up to `2n`, so that levels in the construction are controlled
above by `A_{2K}` and below by `A_0`. -/
theorem height_mono {n i j : ℕ} (hij : i ≤ j) (hj : j ≤ 2 * n) :
    height n i ≤ height n j := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
    refine (ih (by omega)).trans ?_
    have hsub : 2 * n - j = (2 * n - (j + 1)) + 1 := by omega
    have hadd : 2 * n + (j + 1) = (2 * n + j) + 1 := by omega
    have hcmp : ((2 * n - (j + 1) + 1 : ℕ) : ℝ) ≤ ((2 * n + j + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 2 * n - (j + 1) + 1 ≤ 2 * n + j + 1)
    unfold height
    rw [hsub, hadd, Nat.factorial_succ, Nat.factorial_succ]
    push_cast at hcmp ⊢
    calc
      _ = ((2 * n - (j + 1) : ℕ) + 1 : ℝ) * (((2 * n - (j + 1)).factorial : ℝ) *
          ((2 * n + j).factorial : ℝ)) := by ring
      _ ≤ ((2 * n + j : ℕ) + 1 : ℝ) * (((2 * n - (j + 1)).factorial : ℝ) *
          ((2 * n + j).factorial : ℝ)) := mul_le_mul_of_nonneg_right (by simpa using hcmp) (by
              positivity)
      _ = _ := by push_cast; ring

/-- The geometric mass bound with the alphabet sizes and factorial height
used by the polynomial construction. -/
theorem mass_lower {r b n s : ℕ} (hn : 0 < n) (hb : 8 * n ^ 3 ≤ b) (hbr : b ≤ r)
    (hs : s ≤ 2 * n) :
    (1 - 1 / (n : ℝ)) * ((r : ℝ) * b) ^ (2 * n) * ((b : ℝ) / r) ^ s ≤ count n r b s * height n s
        := by
  have hr : 0 < r := lt_of_lt_of_le (by positivity : 0 < 8 * n ^ 3) (hb.trans hbr)
  have h := Digits.good_mass (u := 2 * n - s) (v := 2 * n + s) hn hb hbr (by omega)
  rw [Construction.weight_eq (r : ℝ) (b : ℝ) (by positivity) hs] at h
  simpa only [count, height, mul_assoc] using h

/-- Sum the contributions of the good plateaus, after lowering one copy of
their height to the common minimum `A_0`. -/
theorem plateau_sum_lower {r b n K : ℕ} (hn : 0 < n) (hK : K ≤ n)
    (hb : 8 * n ^ 3 ≤ b) (hbr : b ≤ r) :
    height n 0 * (1 - 1 / (n : ℝ)) * ((r : ℝ) * b) ^ (2 * n) *
      (∑ s ∈ range (K + 1), (s : ℝ) * ((b : ℝ) / r) ^ s) ≤
    ∑ s ∈ range (K + 1), (s : ℝ) * count n r b s * (height n s) ^ 2 := by
  rw [Finset.mul_sum]
  apply sum_le_sum
  intro s hs
  have hs' : s ≤ 2 * n := by have := mem_range.mp hs; omega
  have h := mass_lower hn hb hbr hs'
  have hh := height_mono (n := n) (i := 0) (Nat.zero_le s) hs'
  have hmin := mul_le_mul_of_nonneg_right hh (mul_nonneg (count_nonneg n r b s) (height_pos n s).le)
  calc
    _ = (s : ℝ) * (height n 0 * ((1 - 1 / (n : ℝ)) * ((r : ℝ) * b) ^ (2 * n) * ((b : ℝ) / r) ^ s))
        := by ring
    _ ≤ (s : ℝ) * (height n 0 * (count n r b s * height n s)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h (height_pos n 0).le) (by positivity)
    _ ≤ (s : ℝ) * (height n s * (count n r b s * height n s)) :=
      mul_le_mul_of_nonneg_left hmin (by positivity)
    _ = _ := by ring

/-- Equation (lower) from the actual three norm bounds.
`square` denotes the square of the L² norm, `one` the L¹ norm,
and `peak` the L∞ norm. All assumptions are explicit. -/
theorem norm_ratio_lower {r b n K : ℕ} (hn : 0 < n) (hK : K ≤ n)
    (hb : 8 * n ^ 3 ≤ b) (hbr : b ≤ r) {square one peak : ℝ}
    (hOne : one = (((r : ℝ) * b) ^ n * ∑ s ∈ range (K + 1), ((b : ℝ) / r) ^ s) ^ 2)
    (hPeakPos : 0 < peak) (hPeak : peak ≤ height n (2 * K))
    (hSq : (∑ s ∈ range (K + 1), (s : ℝ) * count n r b s * (height n s) ^ 2) ≤ square) :
    (1 - 1 / (n : ℝ)) * Parameters.factorialRatio (2 * n) (2 * K) *
      Parameters.geomRatio ((b : ℝ) / r) K ≤ square / (one * peak) := by
  let q : ℝ := (b : ℝ) / r
  let S := ∑ s ∈ range (K + 1), q ^ s
  let T := ∑ s ∈ range (K + 1), (s : ℝ) * q ^ s
  let C := ((r : ℝ) * b) ^ n
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) hb
  have hr0 : 0 < r := lt_of_lt_of_le hb0 hbr
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hS : 0 < S := by
    have h := single_le_sum (f := fun s : ℕ => q ^ s) (fun s _ => pow_nonneg hq s)
      (a := 0) (by simp : 0 ∈ range (K + 1))
    change 0 < ∑ s ∈ range (K + 1), q ^ s
    exact lt_of_lt_of_le (by positivity) h
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hOne' : one = (C * S) ^ 2 := hOne
  have hOnePos : 0 < one := hOne' ▸ (by positivity)
  have hfac : Parameters.factorialRatio (2 * n) (2 * K) = height n 0 / height n (2 * K) := by
    simp [Parameters.factorialRatio, height, pow_two]
  rw [hfac]
  change (1 - 1 / (n : ℝ)) * (height n 0 / height n (2 * K)) * (T / S ^ 2) ≤ _
  have hden : 0 < one * peak := mul_pos hOnePos hPeakPos
  apply (le_div_iff₀ hden).2
  have hf : 0 ≤ 1 - 1 / (n : ℝ) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    exact_mod_cast hn
  have hE : 0 ≤ (1 - 1 / (n : ℝ)) * (height n 0 / height n (2 * K)) * (T / S ^ 2) := by
    have h₀ := height_pos n 0
    have h₁ := height_pos n (2 * K)
    positivity
  have hApos := height_pos n (2 * K)
  calc
    _ ≤ (1 - 1 / (n : ℝ)) * (height n 0 / height n (2 * K)) * (T / S ^ 2) * (one * height n (2 *
        K)) := by gcongr
    _ = height n 0 * (1 - 1 / (n : ℝ)) * ((r : ℝ) * b) ^ (2 * n) * T := by
      rw [hOne', show ((r : ℝ) * b) ^ (2 * n) = C ^ 2 by rw [Nat.mul_comm, pow_mul]]
      field_simp
    _ ≤ _ := (plateau_sum_lower hn hK hb hbr).trans hSq

/-- A version for the geometric block lemma: the right - hand side here is its
finite lower bound for the genuine autoconvolution ratio. -/
theorem lower_le_block_fraction {r b n K : ℕ} (hn : 0 < n) (hK : K ≤ n)
    (hb : 8 * n ^ 3 ≤ b) (hbr : b ≤ r) {eval : ℝ}
    (heval : eval = ((r : ℝ) * b) ^ n * ∑ s ∈ range (K + 1), ((b : ℝ) / r) ^ s) :
    (1 - 1 / (n : ℝ)) * Parameters.factorialRatio (2 * n) (2 * K) *
      Parameters.geomRatio ((b : ℝ) / r) K ≤
      (∑ s ∈ range (K + 1), (s : ℝ) * count n r b s * (height n s) ^ 2) /
        (eval ^ 2 * height n (2 * K)) := by
  exact norm_ratio_lower hn hK hb hbr (congrArg (· ^ 2) heval) (height_pos n (2 * K))
    le_rfl le_rfl

end Autoconvolutions.Estimate

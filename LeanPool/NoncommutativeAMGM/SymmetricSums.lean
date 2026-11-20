/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.ScalarEstimate

/-!
# Elementary symmetric sums

The combinatorial estimate in equation (41), proved by induction on the list of
weights. This avoids using a supremum over subsets in the formal proof.
-/

@[expose] public section

namespace NoncommutativeAMGM

open scoped BigOperators

/-- Elementary symmetric sums, including the empty product in degree zero. -/
noncomputable def elementarySum : List ℝ → ℕ → ℝ
  | [], 0 => 1
  | [], _ + 1 => 0
  | _ :: _, 0 => 1
  | b :: bs, l + 1 => elementarySum bs (l + 1) + b * elementarySum bs l

@[simp] theorem elementarySum_zero (bs : List ℝ) : elementarySum bs 0 = 1 := by
  cases bs <;> rfl

theorem elementarySum_nonneg (bs : List ℝ) (hb : ∀ b ∈ bs, 0 ≤ b) (l : ℕ) :
    0 ≤ elementarySum bs l := by
  induction bs generalizing l with
  | nil => cases l <;> norm_num [elementarySum]
  | cons b bs ih =>
    cases l with
    | zero => simp
    | succ l =>
      rw [elementarySum]
      exact add_nonneg (ih (by aesop) _) (mul_nonneg (hb b (by simp)) (ih (by aesop) _))

/-- This recursive definition equals the usual sum of products over subsets. -/
theorem elementarySum_eq_esymm (bs : List ℝ) (l : ℕ) :
    elementarySum bs l = (bs : Multiset ℝ).esymm l := by
  induction bs generalizing l with
  | nil => cases l <;> simp [elementarySum, Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons b bs ih =>
    cases l with
    | zero => simp
    | succ l =>
      change elementarySum bs (l + 1) + b * elementarySum bs l =
        (b ::ₘ (bs : Multiset ℝ)).esymm (l + 1)
      rw [ih, ih]
      simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add,
        Multiset.sum_add, Multiset.map_map, Function.comp_def, Multiset.prod_cons,
        Multiset.sum_map_mul_left]

/-- If `r` nonnegative weights are at most `B`, their symmetric sums satisfy
`(l+1)S(l+1) ≤ (r-l)B S(l)`, including the zero terms beyond degree `r`. -/
theorem elementarySum_recurrence (bs : List ℝ) (B : ℝ)
    (hb : ∀ b ∈ bs, 0 ≤ b ∧ b ≤ B) (l : ℕ) :
    ((l : ℝ) + 1) * elementarySum bs (l + 1) ≤
      ((bs.length : ℝ) - l) * B * elementarySum bs l := by
  induction bs generalizing l with
  | nil =>
    cases l <;> simp [elementarySum]
  | cons b bs ih =>
    have hb0 : 0 ≤ b := (hb b (by simp)).1
    have hbB : b ≤ B := (hb b (by simp)).2
    have hbs : ∀ a ∈ bs, 0 ≤ a ∧ a ≤ B := by aesop
    cases l with
    | zero =>
      have h := ih hbs 0
      simp only [elementarySum, elementarySum_zero, List.length_cons,
        Nat.cast_add, Nat.cast_one, Nat.cast_zero] at *
      nlinarith
    | succ l =>
      have h1 := ih hbs (l + 1)
      have h0 := ih hbs l
      have hmul := mul_le_mul_of_nonneg_left h0 hb0
      have hbound := mul_le_mul_of_nonneg_right hbB
        (elementarySum_nonneg bs (fun a ha ↦ (hbs a ha).1) (l + 1))
      simp only [elementarySum, List.length_cons, Nat.cast_add, Nat.cast_one] at *
      nlinarith

theorem elementarySum_one (bs : List ℝ) : elementarySum bs 1 = bs.sum := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [elementarySum, ih, add_comm]

/-- The list of `k-1` coefficients `β₁, …, βₖ₋₁` in Section 3.6. -/
noncomputable def betaList (n : ℝ) (k : ℕ) : List ℝ :=
  (List.range (k - 1)).map (fun i ↦ beta n (i + 1))

/-- The actual symmetric sums in equation (33). -/
noncomputable def symmetricBeta (n : ℝ) (k l : ℕ) : ℝ := elementarySum (betaList n k) l

/-- The crude coefficient bound used in equation (41). -/
theorem beta_le_linear (n : ℝ) (hn : 0 < n) (l : ℕ) : beta n l ≤ 4 * l / n := by
  have heq : beta n l = 4 * l / n - 4 * (l : ℝ) ^ 2 / n ^ 2 := by
    unfold beta
    field_simp [hn.ne']
  rw [heq]
  exact sub_le_self _ (by positivity)

theorem betaList_bounds (n : ℝ) (k : ℕ) (hn : 0 < n) (hk : 1 ≤ k) (hkn : (k : ℝ) ≤ n) :
    ∀ b ∈ betaList n k, 0 ≤ b ∧ b ≤ 4 * ((k : ℝ) - 1) / n := by
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  have hiN : i < k - 1 := List.mem_range.mp hi
  have hiR : ((i + 1 : ℕ) : ℝ) ≤ (k : ℝ) - 1 := by
    have h : ((i + 1 : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast (show i + 1 + 1 ≤ k by omega)
    linarith
  constructor
  · exact beta_nonneg (by linarith)
  · calc
      beta n (i + 1) ≤ 4 * (i + 1 : ℕ) / n := beta_le_linear n hn (i + 1)
      _ ≤ _ := by gcongr

theorem symmetricBeta_nonneg (n : ℝ) (k : ℕ) (hn : 0 < n)
    (hk : 1 ≤ k) (hkn : (k : ℝ) ≤ n) (l : ℕ) : 0 ≤ symmetricBeta n k l :=
  elementarySum_nonneg _ (fun b hb ↦ (betaList_bounds n k hn hk hkn b hb).1) l

/-- Equation (41) for the actual elementary symmetric sums of the `β` coefficients. -/
theorem symmetricBeta_recurrence (n : ℝ) (k : ℕ) (hn : 0 < n)
    (hk : 1 ≤ k) (hkn : (k : ℝ) ≤ n) (l : ℕ) :
    symmetricBeta n k (l + 1) ≤
      (4 * ((k : ℝ) - 1) * ((k : ℝ) - 1 - l) / (((l : ℝ) + 1) * n)) *
        symmetricBeta n k l := by
  have h := elementarySum_recurrence (betaList n k) (4 * ((k : ℝ) - 1) / n)
    (betaList_bounds n k hn hk hkn) l
  simp only [betaList, List.length_map, List.length_range, Nat.cast_sub hk, Nat.cast_one] at h
  change ((l : ℝ) + 1) * symmetricBeta n k (l + 1) ≤
    ((k : ℝ) - 1 - l) * (4 * ((k : ℝ) - 1) / n) * symmetricBeta n k l at h
  calc
    _ ≤ (((k : ℝ) - 1 - l) * (4 * ((k : ℝ) - 1) / n) *
        symmetricBeta n k l) / ((l : ℝ) + 1) :=
      (le_div_iff₀ (by positivity)).mpr (by nlinarith [h])
    _ = _ := by
      field_simp [hn.ne', show (l : ℝ) + 1 ≠ 0 by positivity]

theorem symmetricBeta_one (n : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    symmetricBeta n k 1 = ∑ i ∈ Finset.range k, beta n i := by
  have hlist : (betaList n k).sum = ∑ i ∈ Finset.range (k - 1), beta n (i + 1) := by
    unfold betaList
    have hrange : (List.range (k - 1)).toFinset = Finset.range (k - 1) := by
      ext i
      simp
    simpa only [hrange] using (List.sum_toFinset (fun i ↦ beta n (i + 1))
      (show (List.range (k - 1)).Nodup from List.nodup_range)).symm
  rw [symmetricBeta, elementarySum_one, hlist]
  have hshift := Finset.sum_range_succ' (fun i ↦ beta n i) (k - 1)
  rw [Nat.sub_add_cancel hk, beta_zero, add_zero] at hshift
  exact hshift.symm

/-- Section 3.6 for the actual symmetric sums. Only the estimates on `H` from
Section 3.5 remain as hypotheses; no recurrence on symmetric sums is assumed. -/
theorem symmetricBeta_expansion_nonneg (n d : ℝ) (k : ℕ) (hn0 : 0 < n)
    (hk : 1 ≤ k) (hkd : (k : ℝ) ≤ d) (hn : 2 * d ^ 2 ≤ n) (H : ℕ → ℝ)
    (hH : ∀ i, 0 ≤ H i)
    (hfirst : (k : ℝ) * ((k : ℝ) - 1) * H (k - 1) ≤ d ^ 2 * H k)
    (hstep : ∀ l, 1 ≤ l → l + 2 ≤ k →
      H (k - (l + 1)) ≤ ((d - l) ^ 2 / (((k : ℝ) - l - 1) * ((k : ℝ) - l))) *
        H (k - l)) :
    0 ≤ H k + ∑ i ∈ Finset.range (k - 1),
      (-1 : ℝ) ^ (i + 1) * symmetricBeta n k (i + 1) * H (k - (i + 1)) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkn : (k : ℝ) ≤ n := by nlinarith
  have hS := symmetricBeta_nonneg n k hn0 hk hkn
  apply scalar_expansion_nonneg k (symmetricBeta n k) H hS hH
  · apply first_correction_le n d k _ _ _ hn0 hn (hH _) (hH _) _ hfirst
    rw [symmetricBeta_one n k hk]
    exact sum_beta_le n hn0 k
  · intro l hl hlk
    exact correction_term_le n d k l _ _ _ _
      (by exact_mod_cast hl) (by exact_mod_cast hlk) hkd hn
      (hS _) (hS _) (hH _) (symmetricBeta_recurrence n k hn0 hk hkn l) (hstep l hl hlk)

end NoncommutativeAMGM

/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Reduction.AnalyticPredicates

/-! A constant field trivially satisfies the factorial-type analyticity bound
`AnalyticBoundOn` / `LocallyUniformlyAnalyticOn` / `ForceSpatiallyAnalytic` of
`eq:analytic:interior:force` at any positive rate `a`, since every derivative of
positive order vanishes — the base instance the inductive derivative estimates
behind `thm:analytic:interior` (Kahane 1969) specialize to on a field with no
spatial dependence, such as a zero force. -/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



private lemma spatialPartial_const_eq_zero (c : ℝ) (j : Fin 3) (z : ParabolicPoint) :
    spatialPartial (fun _ : ParabolicPoint => c) j z = 0 := by
  unfold spatialPartial
  simp

private lemma spatialPartial_iterate_const (c : ℝ) (j : Fin 3) (m : ℕ) :
    (fun k => spatialPartial k j)^[m] (fun _ : ParabolicPoint => c) =
    if m = 0 then (fun _ : ParabolicPoint => c) else (fun _ : ParabolicPoint => (0 : ℝ)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    rw [ih]
    by_cases hm : m = 0
    · subst hm
      simp only [↓reduceIte, zero_add, one_ne_zero]
      ext z; exact spatialPartial_const_eq_zero c j z
    · have hzero : spatialPartial (fun _ : ParabolicPoint => (0 : ℝ)) j =
        fun _ : ParabolicPoint => (0 : ℝ) := by
        ext z; exact spatialPartial_const_eq_zero (0 : ℝ) j z
      simp [hm, hzero]

theorem multiPartial_const_eq_zero_of_le {c : ℝ} {α : Fin 3 → ℕ} (hα : 1 ≤ α 0 + α 1 + α 2)
    (z : ParabolicPoint) :
    multiPartial (fun _ : ParabolicPoint => c) α z = 0 := by
  unfold multiPartial
  have hsum : 0 < α 0 + α 1 + α 2 :=
    Nat.lt_of_lt_of_le (by norm_num : 0 < 1) hα
  by_cases h2 : α 2 = 0
  · have h2iter : (fun k => spatialPartial k 2)^[α 2] (fun _ : ParabolicPoint => c) =
      fun _ : ParabolicPoint => c := by
      rw [h2]; simp
    rw [h2iter]
    by_cases h1 : α 1 = 0
    · have h1iter : (fun k => spatialPartial k 1)^[α 1] (fun _ : ParabolicPoint => c) =
        fun _ : ParabolicPoint => c := by
        rw [h1]; simp
      rw [h1iter]
      by_cases h0 : α 0 = 0
      · rw [h0, h1, h2] at hsum
        simp at hsum
      · have h0iter : (fun k => spatialPartial k 0)^[α 0] (fun _ : ParabolicPoint => c) =
          fun _ : ParabolicPoint => (0 : ℝ) := by
          rw [spatialPartial_iterate_const c 0 (α 0)]
          simp [h0]
        rw [h0iter]
    · have h1iter : (fun k => spatialPartial k 1)^[α 1] (fun _ : ParabolicPoint => c) =
        fun _ : ParabolicPoint => (0 : ℝ) := by
        rw [spatialPartial_iterate_const c 1 (α 1)]
        simp [h1]
      rw [h1iter]
      by_cases h0 : α 0 = 0
      · rw [h0]; simp
      · have h0iter : (fun k => spatialPartial k 0)^[α 0]
          (fun _ : ParabolicPoint => (0 : ℝ)) = fun _ : ParabolicPoint => (0 : ℝ) := by
          rw [spatialPartial_iterate_const (0 : ℝ) 0 (α 0)]
          simp [h0]
        rw [h0iter]
  · have h2iter : (fun k => spatialPartial k 2)^[α 2] (fun _ : ParabolicPoint => c) =
      fun _ : ParabolicPoint => (0 : ℝ) := by
      rw [spatialPartial_iterate_const c 2 (α 2)]
      simp [h2]
    rw [h2iter]
    have h1iter : (fun k => spatialPartial k 1)^[α 1] (fun _ : ParabolicPoint => (0 : ℝ)) =
        fun _ : ParabolicPoint => (0 : ℝ) := by
      rw [spatialPartial_iterate_const (0 : ℝ) 1 (α 1)]
      by_cases h1' : α 1 = 0
      · rw [h1']; simp
      · simp [h1']
    rw [h1iter]
    have h0iter : (fun k => spatialPartial k 0)^[α 0] (fun _ : ParabolicPoint => (0 : ℝ)) =
        fun _ : ParabolicPoint => (0 : ℝ) := by
      rw [spatialPartial_iterate_const (0 : ℝ) 0 (α 0)]
      by_cases h0' : α 0 = 0
      · rw [h0']; simp
      · simp [h0']
    rw [h0iter]

theorem multiPartial_const_zero_order {c : ℝ} (z : ParabolicPoint) :
    multiPartial (fun _ : ParabolicPoint => c) (fun _ : Fin 3 => 0) z = c := by
  unfold multiPartial
  simp

theorem analyticBoundOn_const {c : Vec3} {M R' a : ℝ} (hM : ∀ i, |c i| ≤ M) (ha : 0 < a)
    {J : Set ℝ} :
    AnalyticBoundOn (fun _ : ParabolicPoint => c) R' J M a := by
  intro α t ht x hx i
  by_cases hsum : α 0 + α 1 + α 2 = 0
  · have ⟨hα01, hα2⟩ := Nat.add_eq_zero_iff.mp hsum
    have ⟨hα0, hα1⟩ := Nat.add_eq_zero_iff.mp hα01
    have hα_eq : α = fun _ => 0 := by
      ext i
      fin_cases i <;> assumption
    rw [hα_eq]
    simp only [add_zero, CharP.cast_eq_zero, neg_zero, Real.rpow_zero, mul_one,
      Nat.factorial_zero, Nat.cast_one, ge_iff_le]
    rw [multiPartial_const_zero_order (c := c i) (x, t)]
    have hMi : |c i| ≤ M := hM i
    simp [hMi]
  · have hsum_pos : 1 ≤ α 0 + α 1 + α 2 :=
      Nat.one_le_of_lt (Nat.pos_of_ne_zero hsum)
    rw [multiPartial_const_eq_zero_of_le hsum_pos (x, t)]
    rw [abs_zero]
    have ha_nonneg : 0 ≤ a := le_of_lt ha
    have hM_nonneg : 0 ≤ M := by
      have h := hM i
      have h_abs := abs_nonneg (c i)
      linarith only [h_abs, h]
    have h_rpow : 0 ≤ a ^ (-((α 0 + α 1 + α 2 : ℕ) : ℝ)) :=
      Real.rpow_nonneg ha_nonneg _
    have h_fact : 0 ≤ (Nat.factorial (α 0 + α 1 + α 2) : ℝ) :=
      Nat.cast_nonneg _
    have h_inner : 0 ≤ M * a ^ (-((α 0 + α 1 + α 2 : ℕ) : ℝ)) :=
      mul_nonneg hM_nonneg h_rpow
    exact mul_nonneg h_inner h_fact

theorem locallyUniformlyAnalyticOn_const {c : Vec3} {M R t₁ t₂ : ℝ} (hM : ∀ i, |c i| ≤ M) :
    LocallyUniformlyAnalyticOn (fun _ : ParabolicPoint => c) R t₁ t₂ := by
  intro R' hR' s₁ s₂ hs₁ hs₂
  refine ⟨M, 1, by norm_num, ?_⟩
  exact analyticBoundOn_const hM (by norm_num : 0 < (1 : ℝ))

theorem forceSpatiallyAnalytic_const {c : Vec3} {M : ℝ} (hM : ∀ i, |c i| ≤ M) :
    ForceSpatiallyAnalytic (fun _ : ParabolicPoint => c) := by
  rw [forceSpatiallyAnalytic_iff_locallyUniformlyAnalyticOn]
  exact locallyUniformlyAnalyticOn_const hM

end CIV

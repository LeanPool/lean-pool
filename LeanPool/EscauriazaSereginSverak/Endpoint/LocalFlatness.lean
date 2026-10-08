/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic

/-!
# Flatness from a zero parabolic neighborhood

This is the elementary flatness estimate used in `lem:flat-from-vanishing`.
-/

public section

open Set
open scoped Topology
open CKN.Foundation.Parabolic


namespace ESS

/-- A bounded field that vanishes on a past neighborhood of its top point has
the corresponding pointwise flatness bounds. -/
theorem flat_from_vanishing
    (R' T' r₀ M : ℝ) (x₀ : Vec3) (w : ParabolicPoint → Vec3)
    (hr₀ : 0 < r₀) (hM : 0 ≤ M)
    (hr₀R' : r₀ ≤ R') (hr₀T' : r₀ ^ 2 ≤ T')
    (hbound : ∀ z ∈ vec3Ball x₀ R' ×ˢ Ico (0 : ℝ) T',
      vec3EuclideanNorm (w z) ≤ M)
    (hzero : ∀ x s, x ∈ vec3Ball x₀ r₀ → 0 < s → s < r₀ ^ 2 →
      (x, s) ∈ vec3Ball x₀ R' ×ˢ Ico (0 : ℝ) T' → w (x, s) = 0) :
    ∀ k : ℕ, ∀ x s, (x, s) ∈ vec3Ball x₀ R' ×ˢ Ioo (0 : ℝ) T' →
      vec3EuclideanNorm (w (x, s)) ≤
        M * r₀⁻¹ ^ k *
          (vec3EuclideanNorm (x - x₀) + Real.sqrt s) ^ k := by
  intro k x s hz
  rcases hz with ⟨hx, hs⟩
  have hspos : 0 < s := hs.1
  have hslt : s < T' := hs.2
  have hdomain : (x, s) ∈ vec3Ball x₀ R' ×ˢ Ico (0 : ℝ) T' :=
    ⟨hx, ⟨le_of_lt hspos, hslt⟩⟩
  have hsize := hbound (x, s) hdomain
  let d := vec3EuclideanNorm (x - x₀) + Real.sqrt s
  have hdnonneg : 0 ≤ d := by
    exact add_nonneg (vec3EuclideanNorm_nonneg _) (Real.sqrt_nonneg _)
  by_cases hdsmall : d < r₀
  · have hxd : vec3EuclideanNorm (x - x₀) < r₀ := by
      dsimp [d] at hdsmall
      exact (le_add_of_nonneg_right (Real.sqrt_nonneg s)).trans_lt hdsmall
    have hsd : Real.sqrt s < r₀ := by
      dsimp [d] at hdsmall
      exact (le_add_of_nonneg_left (vec3EuclideanNorm_nonneg (x - x₀))).trans_lt
        hdsmall
    have hstime : s < r₀ ^ 2 :=
      (Real.sqrt_lt' hr₀).mp hsd
    have hdomainSmall : (x, s) ∈ vec3Ball x₀ R' ×ˢ Ico (0 : ℝ) T' := by
      exact ⟨hxd.trans_le hr₀R', ⟨le_of_lt hspos, lt_of_lt_of_le hstime hr₀T'⟩⟩
    have hvanish := hzero x s hxd hspos hstime hdomainSmall
    rw [hvanish, vec3EuclideanNorm_zero]
    change 0 ≤ M * r₀⁻¹ ^ k * d ^ k
    exact mul_nonneg (mul_nonneg hM (pow_nonneg (inv_nonneg.mpr hr₀.le) k))
      (pow_nonneg hdnonneg k)
  · have hr₀d : r₀ ≤ d := le_of_not_gt hdsmall
    have hratio : 1 ≤ r₀⁻¹ * d := by
      have hdiv : 1 ≤ d / r₀ := (one_le_div hr₀).2 hr₀d
      simpa [div_eq_mul_inv, mul_comm] using hdiv
    have hpow : 1 ≤ (r₀⁻¹ * d) ^ k := one_le_pow₀ hratio
    have hfactor : (r₀⁻¹ * d) ^ k = r₀⁻¹ ^ k * d ^ k := by
      rw [mul_pow]
    calc
      vec3EuclideanNorm (w (x, s)) ≤ M := hsize
      _ = M * 1 := by ring
      _ ≤ M * (r₀⁻¹ * d) ^ k := mul_le_mul_of_nonneg_left hpow hM
      _ = M * r₀⁻¹ ^ k * d ^ k := by rw [hfactor]; ring
      _ = M * r₀⁻¹ ^ k *
          (vec3EuclideanNorm (x - x₀) + Real.sqrt s) ^ k := by rfl

end ESS

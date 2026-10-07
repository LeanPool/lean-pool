/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.RecedingEquation

/-!
# Uniform-on-a-rectangle vanishing of the receding rescaled swirl coefficient

Uniform-on-a-rectangle vanishing of the recentred rescaled swirl coefficient `S_n` of
`eq:aniso:zoom:receding` (the receding-axis analogue of `eq:aniso:zoom:finite:source:b`), as the
recentring ratio `A_n = r_n/λ_n → ∞` (with `λ_n → 0⁺`), from the circulation bound alone —
the uniform-in-`n`, tested-against-a-fixed-rectangle strengthening of the fixed-point limit,
matching Step 3's `|S_n| ≤ C_Γ δ/(A_n + R)` on a
compact set instead of at one point.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem exists_forall_abs_zoomSRec_le_of_isCompact {h rc zc CΓ M lam : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} {K : Set (ℝ × ℝ)} (hM : 0 < M)
    (hKM : ∀ y ∈ K, M ≤ rc / lam + y.1) {Z : ℝ}
    (hΓ : ∀ y ∈ K, |circulation u (zoomPointRec lam h rc zc ((y.1, y.2), Z))| ≤ CΓ) :
    ∀ y ∈ K, |zoomSRec lam h rc zc u ((y.1, y.2), Z)| ≤ CΓ * lam ^ (2 * h) / M := by
  intro y hy
  have hApos : 0 < rc / lam + y.1 := by
    have hM_le : M ≤ rc / lam + y.1 := hKM y hy
    exact hM.trans_le hM_le
  have hbound := abs_zoomSRec_le_of_circulation hlam hApos (hΓ y hy)
  have hCΓ_nonneg : 0 ≤ CΓ := by
    have hpos := hΓ y hy
    have hnonneg : 0 ≤ |circulation u (zoomPointRec lam h rc zc ((y.1, y.2), Z))| := abs_nonneg _
    linarith only [hpos, hnonneg]
  have hnum_nonneg : 0 ≤ CΓ * lam ^ (2 * h) :=
    mul_nonneg hCΓ_nonneg (Real.rpow_nonneg hlam.le _)
  have hM_le : M ≤ rc / lam + y.1 := hKM y hy
  calc
    |zoomSRec lam h rc zc u ((y.1, y.2), Z)| ≤ CΓ * lam ^ (2 * h) / (rc / lam + y.1) := hbound
    _ ≤ CΓ * lam ^ (2 * h) / M :=
      div_le_div_of_nonneg_left hnum_nonneg hM hM_le

theorem tendstoUniformlyOn_zoomSRec_of_tendsto_circulation_bound {h zc CΓ : ℝ}
    (u : ℕ → ParabolicPoint → Vec3) (lamSeq rcSeq : ℕ → ℝ) (hlam : ∀ n, 0 < lamSeq n)
    (hlam0 : Tendsto lamSeq atTop (nhds 0)) {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    {M : ℕ → ℝ} (hMpos : ∀ n, 0 < M n) (hMtop : Tendsto M atTop atTop)
    (hKM : ∀ n, ∀ y ∈ K, M n ≤ rcSeq n / lamSeq n + y.1) {Z : ℝ}
    (hΓ : ∀ n, ∀ y ∈ K,
      |circulation (u n) (zoomPointRec (lamSeq n) h (rcSeq n) zc ((y.1, y.2), Z))| ≤ CΓ)
    (hh : 0 ≤ h) :
    TendstoUniformlyOn (fun n y => zoomSRec (lamSeq n) h (rcSeq n) zc (u n) ((y.1, y.2), Z))
      (fun _ => (0 : ℝ)) atTop K := by
  by_cases hK_empty : K.Nonempty
  · -- K is nonempty: derive CΓ ≥ 0 from the circulation bound
    obtain ⟨y₀, hy₀⟩ := hK_empty
    have hCΓ_nonneg : 0 ≤ CΓ := by
      have hpos := hΓ 0 y₀ hy₀
      have hnonneg : 0 ≤ |circulation (u 0) (zoomPointRec (lamSeq 0) h (rcSeq 0) zc
          ((y₀.1, y₀.2), Z))| := abs_nonneg _
      linarith only [hpos, hnonneg]
    have h2h_nonneg : 0 ≤ 2 * h := by linarith only [hh]
    -- Per-point bound from theorem (1)
    have h_bound (n : ℕ) : ∀ y ∈ K,
        |zoomSRec (lamSeq n) h (rcSeq n) zc (u n) ((y.1, y.2), Z)| ≤ CΓ * lamSeq n ^ (2 * h) / M
          n :=
      fun y hy => exists_forall_abs_zoomSRec_le_of_isCompact (hlam n) (hMpos n) (hKM n)
        (fun y' hy' => hΓ n y' hy') y hy
    -- Show CΓ * lamSeq n ^ (2*h) / M n → 0
    have h_tendsto_div : Tendsto (fun n : ℕ => CΓ * lamSeq n ^ (2 * h) / M n) atTop (𝓝 0) := by
      by_cases hh0 : h = 0
      · -- h = 0: lamSeq n ^ (2*0) = lamSeq n ^ 0 = 1
        subst hh0
        have h_lam_pow : Tendsto (fun n : ℕ => lamSeq n ^ (2 * (0 : ℝ))) atTop (𝓝 ((0 : ℝ) ^ (2
          * (0 : ℝ)))) :=
          hlam0.rpow_const (Or.inr (by norm_num : 0 ≤ (2 * (0 : ℝ))))
        have h_lam_pow_one : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) := tendsto_const_nhds
        have h_lam_pow_simp : Tendsto (fun n : ℕ => lamSeq n ^ (2 * (0 : ℝ))) atTop (𝓝 (1 : ℝ))
          := by
          convert h_lam_pow using 1
          simp [Real.rpow_zero]
        have h_mul : Tendsto (fun n : ℕ => CΓ * lamSeq n ^ (2 * (0 : ℝ))) atTop (𝓝 (CΓ * (1 :
          ℝ))) :=
          h_lam_pow_simp.const_mul CΓ
        have h_inv : Tendsto (fun n : ℕ => (M n)⁻¹) atTop (𝓝 (0 : ℝ)) :=
          tendsto_inv_atTop_zero.comp hMtop
        have h_div : Tendsto (fun n : ℕ => (CΓ * lamSeq n ^ (2 * (0 : ℝ))) * (M n)⁻¹) atTop
            (𝓝 ((CΓ * (1 : ℝ)) * (0 : ℝ))) := h_mul.mul h_inv
        simpa [div_eq_mul_inv, mul_zero, mul_one] using h_div
      · -- h > 0: 2*h > 0, so lamSeq n ^ (2*h) → 0
        have h2h_pos : 0 < 2 * h := by
          by_contra! hle
          have h_eq : 2 * h = 0 := by linarith only [hle, hh]
          have hh0' : h = 0 := by linarith only [h_eq]
          exact hh0 hh0'
        have h_lam_pow : Tendsto (fun n : ℕ => lamSeq n ^ (2 * h)) atTop (𝓝 ((0 : ℝ) ^ (2 * h))) :=
          hlam0.rpow_const (Or.inr h2h_nonneg)
        have h_lam_pow_zero : Tendsto (fun n : ℕ => lamSeq n ^ (2 * h)) atTop (𝓝 (0 : ℝ)) := by
          simpa [Real.zero_rpow (ne_of_gt h2h_pos)] using h_lam_pow
        have h_mul : Tendsto (fun n : ℕ => CΓ * lamSeq n ^ (2 * h)) atTop (𝓝 (CΓ * (0 : ℝ))) :=
          h_lam_pow_zero.const_mul CΓ
        have h_inv : Tendsto (fun n : ℕ => (M n)⁻¹) atTop (𝓝 (0 : ℝ)) :=
          tendsto_inv_atTop_zero.comp hMtop
        have h_div : Tendsto (fun n : ℕ => (CΓ * lamSeq n ^ (2 * h)) * (M n)⁻¹) atTop
            (𝓝 ((CΓ * (0 : ℝ)) * (0 : ℝ))) := h_mul.mul h_inv
        simpa [div_eq_mul_inv, mul_zero] using h_div
    -- Now use the metric characterization of uniform convergence
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have h_event : ∀ᶠ n in atTop, |CΓ * lamSeq n ^ (2 * h) / M n| < ε := by
      have h_abs_tendsto : Tendsto (fun n : ℕ => |CΓ * lamSeq n ^ (2 * h) / M n|) atTop (𝓝 |(0 :
        ℝ)|) :=
        h_tendsto_div.abs
      simp only [abs_zero] at h_abs_tendsto
      exact h_abs_tendsto.eventually (gt_mem_nhds hε)
    filter_upwards [h_event] with n hn y hy
    have hbound := h_bound n y hy
    rw [Real.dist_eq, zero_sub]
    have h_nonneg : 0 ≤ CΓ * lamSeq n ^ (2 * h) / M n :=
      div_nonneg (mul_nonneg hCΓ_nonneg (Real.rpow_nonneg ((hlam n).le) _)) (hMpos n).le
    have h_abs_eq : |CΓ * lamSeq n ^ (2 * h) / M n| = CΓ * lamSeq n ^ (2 * h) / M n :=
      abs_of_nonneg h_nonneg
    rw [h_abs_eq] at hn
    simp only [abs_neg]
    linarith only [hbound, hn]
  · -- K is empty: uniform convergence is vacuously true
    have hK_empty' : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hK_empty
    subst hK_empty'
    refine (Metric.tendstoUniformlyOn_iff (s := (∅ : Set (ℝ × ℝ)))).mpr ?_
    intro ε hε
    refine Filter.Eventually.of_forall (fun n y hy => ?_)
    exfalso
    simp at hy

end CIV

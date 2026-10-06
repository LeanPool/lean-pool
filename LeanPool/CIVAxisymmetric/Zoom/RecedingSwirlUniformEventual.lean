/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.RecedingSwirlUniformVanish

/-!
# Eventual circulation-bound companions for the uniform swirl vanishing

theorem `tendstoUniformlyOn_zoomSRec_of_tendsto_circulation_bound_of_eventual` is the
*eventual* analogue of `tendstoUniformlyOn_zoomSRec_of_tendsto_circulation_bound`; its circulation
hypothesis `hΓ` is only required for sufficiently large `n`, matching the true in-domain
circulation bound `eq:aniso:zoom:circulation` which holds eventually in `n` once `lamSeq n` is
small enough to keep the zoom point inside the domain.

The two pointwise corollaries consume that uniform result: the first specialises it to a
singleton set and extracts a `Tendsto … atTop (nhds 0)` at a single point, which is the
one-point conclusion that the finite-axis and receding-axis contradictions of the proof of
`prop:aniso:small` need.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem tendstoUniformlyOn_zoomSRec_of_tendsto_circulation_bound_of_eventual {h zc CΓ : ℝ}
    (u : ℕ → ParabolicPoint → Vec3) (lamSeq rcSeq : ℕ → ℝ) (hlam : ∀ n, 0 < lamSeq n)
    (hlam0 : Tendsto lamSeq atTop (nhds 0)) {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    {M : ℕ → ℝ} (hMpos : ∀ n, 0 < M n) (hMtop : Tendsto M atTop atTop)
    (hKM : ∀ n, ∀ y ∈ K, M n ≤ rcSeq n / lamSeq n + y.1) {Z : ℝ} (hCΓ : 0 ≤ CΓ)
    (hΓ : ∀ᶠ n in atTop, ∀ y ∈ K,
      |circulation (u n) (zoomPointRec (lamSeq n) h (rcSeq n) zc ((y.1, y.2), Z))| ≤ CΓ)
    (hh : 0 ≤ h) :
    TendstoUniformlyOn (fun n y => zoomSRec (lamSeq n) h (rcSeq n) zc (u n) ((y.1, y.2), Z))
      (fun _ => (0 : ℝ)) atTop K := by
  by_cases hK_empty : K.Nonempty
  · -- K is nonempty: derive the rate of decay and combine with the eventual per-point bound
    have h2h_nonneg : 0 ≤ 2 * h := by linarith only [hh]
    -- Per-point bound from theorem (1) of `RecedingSwirlUniformVanish`, applied eventually
    have h_bound : ∀ᶠ n in atTop, ∀ y ∈ K,
        |zoomSRec (lamSeq n) h (rcSeq n) zc (u n) ((y.1, y.2), Z)| ≤ CΓ * lamSeq n ^ (2 * h) / M
          n :=
      hΓ.mono fun n hn y hy =>
        exists_forall_abs_zoomSRec_le_of_isCompact (hlam n) (hMpos n) (hKM n) hn y hy
    -- Show CΓ * lamSeq n ^ (2*h) / M n → 0
    have h_tendsto_div : Tendsto (fun n : ℕ => CΓ * lamSeq n ^ (2 * h) / M n) atTop (𝓝 0) := by
      by_cases hh0 : h = 0
      · -- h = 0: lamSeq n ^ (2*0) = 1
        subst hh0
        have h_lam_pow : Tendsto (fun n : ℕ => lamSeq n ^ (2 * (0 : ℝ))) atTop (𝓝 ((0 : ℝ) ^ (2
          * (0 : ℝ)))) :=
          hlam0.rpow_const (Or.inr (by norm_num : 0 ≤ (2 * (0 : ℝ))))
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
    filter_upwards [h_event, h_bound] with n hn hbound y hy
    have hbound_y := hbound y hy
    rw [Real.dist_eq, zero_sub]
    have h_nonneg : 0 ≤ CΓ * lamSeq n ^ (2 * h) / M n :=
      div_nonneg (mul_nonneg hCΓ (Real.rpow_nonneg ((hlam n).le) _)) (hMpos n).le
    have h_abs_eq : |CΓ * lamSeq n ^ (2 * h) / M n| = CΓ * lamSeq n ^ (2 * h) / M n :=
      abs_of_nonneg h_nonneg
    rw [h_abs_eq] at hn
    simp only [abs_neg]
    linarith only [hbound_y, hn]
  · -- K is empty: uniform convergence is vacuously true
    have hK_empty' : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hK_empty
    subst hK_empty'
    refine (Metric.tendstoUniformlyOn_iff (s := (∅ : Set (ℝ × ℝ)))).mpr ?_
    intro ε hε
    refine Filter.Eventually.of_forall (fun n y hy => ?_)
    exfalso
    simp at hy

theorem tendsto_zoomSRec_atPoint_of_tendstoUniformlyOn {h : ℝ}
    (u : ℕ → ParabolicPoint → Vec3) (lamSeq rcSeq : ℕ → ℝ) (zc : ℝ)
    {K : Set (ℝ × ℝ)} {Z : ℝ}
    (hunif : TendstoUniformlyOn
      (fun n y => zoomSRec (lamSeq n) h (rcSeq n) zc (u n) ((y.1, y.2), Z))
      (fun _ => (0 : ℝ)) atTop K)
    {y : ℝ × ℝ} (hy : y ∈ K) :
    Tendsto (fun n => zoomSRec (lamSeq n) h (rcSeq n) zc (u n) ((y.1, y.2), Z)) atTop (nhds 0) := by
  exact hunif.tendsto_at hy

theorem tendsto_zoomSRec_atPoint_of_tendsto_circulation_bound_of_eventual {h zc CΓ : ℝ}
    (u : ℕ → ParabolicPoint → Vec3) (lamSeq rcSeq : ℕ → ℝ) (hlam : ∀ n, 0 < lamSeq n)
    (hlam0 : Tendsto lamSeq atTop (nhds 0))
    {M : ℕ → ℝ} (hMpos : ∀ n, 0 < M n) (hMtop : Tendsto M atTop atTop)
    {y : ℝ × ℝ} (hyM : ∀ n, M n ≤ rcSeq n / lamSeq n + y.1) {Z : ℝ} (hCΓ : 0 ≤ CΓ)
    (hΓ : ∀ᶠ n in atTop, |circulation (u n) (zoomPointRec (lamSeq n) h (rcSeq n) zc (y, Z))| ≤ CΓ)
    (hh : 0 ≤ h) :
    Tendsto (fun n => zoomSRec (lamSeq n) h (rcSeq n) zc (u n) ((y.1, y.2), Z)) atTop (nhds 0) := by
  have h_singleton_unif : TendstoUniformlyOn
      (fun n y' => zoomSRec (lamSeq n) h (rcSeq n) zc (u n) ((y'.1, y'.2), Z))
      (fun _ => (0 : ℝ)) atTop ({y} : Set (ℝ × ℝ)) :=
    tendstoUniformlyOn_zoomSRec_of_tendsto_circulation_bound_of_eventual
      u lamSeq rcSeq hlam hlam0 (isCompact_singleton (x := y))
      hMpos hMtop (fun n y' hy' => (Set.mem_singleton_iff.mp hy') ▸ hyM n) hCΓ
      (hΓ.mono fun n hn y' hy' => (Set.mem_singleton_iff.mp hy') ▸ hn) hh
  exact tendsto_zoomSRec_atPoint_of_tendstoUniformlyOn u lamSeq rcSeq zc h_singleton_unif
    (Set.mem_singleton y)

end CIV

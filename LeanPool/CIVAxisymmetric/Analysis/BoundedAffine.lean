/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.MeridionalSmallness
public import LeanPool.CIVAxisymmetric.Statements.IsLocallyBoundedOn
public import LeanPool.CIVAxisymmetric.Statements.IsAdmissibleDrift
public import LeanPool.CIVAxisymmetric.Setting.MeridionalNorm
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Bounded Affine

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- If `|R * c| ≤ M` for all nonnegative `R`, then `c = 0`. -/
theorem eq_zero_of_abs_mul_le_of_nonneg {c M : ℝ} (h : ∀ R : ℝ, 0 ≤ R → |R * c| ≤ M) : c = 0 := by
  have hM_nonneg : 0 ≤ M := by
    have h0 := h 0 (by norm_num)
    simpa [zero_mul] using h0
  by_contra! hc
  have hc_abs_pos : 0 < |c| := abs_pos.mpr hc
  set R := (M + 1) / |c| with hR_def
  have hR_nonneg : 0 ≤ R :=
    div_nonneg (by linarith only [hM_nonneg]) (abs_nonneg _)
  have hRc : |R * c| = M + 1 := by
    calc
      |R * c| = |R| * |c| := abs_mul R c
      _ = R * |c| := by rw [abs_of_nonneg hR_nonneg]
      _ = ((M + 1) / |c|) * |c| := by rw [hR_def]
      _ = M + 1 := by field_simp [hc_abs_pos.ne']
  have h_contra := h R hR_nonneg
  rw [hRc] at h_contra
  linarith only [h_contra]

/-- If `|R * c + d| ≤ M` for all real `R`, then `c = 0`. -/
theorem eq_zero_of_abs_affine_le {c d M : ℝ} (h : ∀ R : ℝ, |R * c + d| ≤ M) : c = 0 := by
  have hM_nonneg : 0 ≤ M := by
    have h0 := h 0
    have hd_abs_nonneg : 0 ≤ |d| := abs_nonneg _
    have hd_le_M : |d| ≤ M := by simpa [zero_mul, zero_add] using h0
    linarith only [hd_abs_nonneg, hd_le_M]
  by_contra! hc
  have hc_abs_pos : 0 < |c| := abs_pos.mpr hc
  set R := (2 * M + |d| + 1) / |c| with hR_def
  have hR_nonneg : 0 ≤ R :=
    div_nonneg (by
      have h2M : 0 ≤ 2 * M := mul_nonneg (by norm_num) hM_nonneg
      linarith only [h2M, abs_nonneg d])
      (abs_nonneg _)
  have h_bound : M < |R * c + d| := by
    have h_triangle : |R * c| - |d| ≤ |R * c + d| := by
      calc
        |R * c| - |d| = |R * c| - |-d| := by simp
        _ ≤ |R * c - (-d)| := abs_sub_abs_le_abs_sub _ _
        _ = |R * c + d| := by ring_nf
    have hRc : |R * c| = 2 * M + |d| + 1 := by
      calc
        |R * c| = |R| * |c| := abs_mul R c
        _ = R * |c| := by rw [abs_of_nonneg hR_nonneg]
        _ = ((2 * M + |d| + 1) / |c|) * |c| := by rw [hR_def]
        _ = 2 * M + |d| + 1 := by field_simp [hc_abs_pos.ne']
    rw [hRc] at h_triangle
    have h_triangle_simp : 2 * M + 1 ≤ |R * c + d| := by linarith only [h_triangle]
    have hM_lt : M < 2 * M + 1 := by linarith only [hM_nonneg]
    linarith only [h_triangle_simp, hM_lt]
  have h_contra := h R
  linarith only [h_bound, h_contra]

/-- If `|a| ≤ b n` for all `n` and `b n → 0`, then `a = 0`. -/
theorem eq_zero_of_forall_abs_le_of_tendsto_zero {a : ℝ} {b : ℕ → ℝ} (hb : Tendsto b atTop (𝓝 0))
    (h : ∀ n, |a| ≤ b n) : a = 0 := by
  have h_abs_nonneg : 0 ≤ |a| := abs_nonneg _
  have h_le_zero : |a| ≤ 0 :=
    le_of_tendsto_of_tendsto (tendsto_const_nhds (x := |a|)) hb
      (Filter.eventually_atTop.mpr ⟨0, fun n _ => h n⟩)
  have h_abs_zero : |a| = 0 := le_antisymm h_le_zero h_abs_nonneg
  exact abs_eq_zero.mp h_abs_zero

/-- If `|c * R + d| ≤ M` for all `R ≥ 0`, then `c = 0`.
The proof is by contradiction: if `c ≠ 0`, pick `R = (M + |d| + 1) / |c|` (with sign
adjusted so `R ≥ 0`) to force `|c * R + d| ≥ M + 1 > M`. -/
theorem eq_zero_of_forall_nonneg_abs_affine_le {c d M : ℝ}
    (h : ∀ R : ℝ, 0 ≤ R → |c * R + d| ≤ M) : c = 0 := by
  have hM_nonneg : 0 ≤ M := by
    have h0 := h 0 (by norm_num)
    have hd_abs_nonneg : 0 ≤ |d| := abs_nonneg _
    have hd_le_M : |d| ≤ M := by simpa [zero_mul] using h0
    linarith only [hd_abs_nonneg, hd_le_M]
  by_contra! hc
  by_cases hc_pos : 0 < c
  · -- Case c > 0: take R = (M + |d| + 1) / c
    set R := (M + |d| + 1) / c with hR_def
    have hR_nonneg : 0 ≤ R :=
      div_nonneg (by linarith only [hM_nonneg, abs_nonneg d]) (by linarith only [hc_pos])
    have hRc : c * R + d = (M + |d| + 1) + d := by
      rw [hR_def]
      field_simp [hc_pos.ne']
    have h_bound : M + 1 ≤ |c * R + d| := by
      rw [hRc]
      have h_abs_M : |M + |d| + 1| = M + |d| + 1 :=
        abs_of_nonneg (by linarith only [hM_nonneg, abs_nonneg d])
      have h_triangle : |M + |d| + 1| - |d| ≤ |(M + |d| + 1) + d| := by
        calc
          |M + |d| + 1| - |d| = |M + |d| + 1| - |-d| := by simp
          _ ≤ |(M + |d| + 1) - (-d)| := abs_sub_abs_le_abs_sub _ _
          _ = |(M + |d| + 1) + d| := by simp
      rw [h_abs_M] at h_triangle
      have h_simp : (M + |d| + 1) - |d| = M + 1 := by ring
      rw [h_simp] at h_triangle
      exact h_triangle
    have h_contra := h R hR_nonneg
    linarith only [h_bound, h_contra]
  · -- Case c < 0: take R = (M + |d| + 1) / (-c)
    have hc_neg : c < 0 := by
      by_contra! hge
      have hc_zero : c = 0 := by linarith only [hc_pos, hge]
      exact hc hc_zero
    set R := (M + |d| + 1) / (-c) with hR_def
    have hR_nonneg : 0 ≤ R :=
      div_nonneg (by linarith only [hM_nonneg, abs_nonneg d]) (by linarith only [hc_neg])
    have hRc : c * R + d = d - (M + |d| + 1) := by
      rw [hR_def]
      field_simp [hc_neg.ne]
      ring_nf
    have h_bound : M + 1 ≤ |c * R + d| := by
      rw [hRc]
      have h_abs_M : |M + |d| + 1| = M + |d| + 1 :=
        abs_of_nonneg (by linarith only [hM_nonneg, abs_nonneg d])
      have h_triangle : |M + |d| + 1| - |d| ≤ |(M + |d| + 1) - d| :=
        abs_sub_abs_le_abs_sub _ _
      have h_eq : |(M + |d| + 1) - d| = |d - (M + |d| + 1)| := by
        rw [← abs_neg, neg_sub]
      rw [h_abs_M, h_eq] at h_triangle
      have h_simp : (M + |d| + 1) - |d| = M + 1 := by ring
      rw [h_simp] at h_triangle
      exact h_triangle
    have h_contra := h R hR_nonneg
    linarith only [h_bound, h_contra]

end CIV

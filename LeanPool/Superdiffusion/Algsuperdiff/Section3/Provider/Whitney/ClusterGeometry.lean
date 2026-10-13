/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Whitney.BadSetDefinitions

/-!
# ClusterGeometry

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# `l.bad.clusters.geometry`: the scale arithmetic of the cluster lemma

**Partial node.**  This module delivers the carrier-free *scale arithmetic* on
which the proof of ABK26's `l.bad.clusters.geometry` rests.

## What is delivered

* `whitneyScaleSeq_add_le` and `whitneyDepth_sub_lt_ten`: the manuscript's
  generation count.  The lift of a layer-`n'` cube to the coarsest scale
  `3^{m-n_min-h_{n_min}}` in the region is a descendant within `(n' + h_{n'}) -
  (n_min + h_{n_min})` generations, and the manuscript needs that number to be
  `< 9` so that `𝓑(□) ⟹ 𝓑^*(□)` (`e.Bext.def` looks at nine generations of
  descendants).  With `b ≤ 1/8` and `n_min ≤ n' ≤ n_min + 3` the count is at
  most `6`.
* `four_mul_three_rpow_whitneyDepth_lt_two_thirds`: the **corrected** gate

  ```
  4 · 3^{b(n+h_n)} · 3^{m-n-h_n}  <  (2/3) · 3^{m-n}    (b ≤ 1/8, k₀ ≥ 3).
  ```

  The manuscript writes `3^{b(n+h_n)}·3^{m-n-h_n} ≤ 3^{m-n}·3^{-(1-b)k₀}` and
  then chooses `k₀` with `3^{-(1-b)k₀} < c`.

## References

* ABK26, `l.bad.clusters.geometry`.
-/

namespace Algsuperdiff.Section3.Provider.Whitney

open HCPolySupport

noncomputable section

/-! ## The generation count of the lift to `𝓑^*` -/

/-- Iterating `e.hn.gap`: the scale separation grows by at most one per layer. -/
theorem whitneyScaleSeq_add_le {b : ℝ} (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (hs k₀ r : ℕ) : ∀ j : ℕ,
      whitneyScaleSeq b hs k₀ (r + j) ≤ whitneyScaleSeq b hs k₀ r + j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      have hstep := whitneyScaleSeq_succ_le hb0 hb hs k₀ (r + j)
      have hidx : r + (j + 1) = (r + j) + 1 := by omega
      rw [hidx]
      omega

/-- **The generation count.**  If two Whitney layers are at most three apart, the
depth gap between them is smaller than ten, i.e. within the generations `0..9`
of the proved `e.Bext.def` (`Finset.range 10`), so a bad layer-`n` cube forces
the extended bad event at the coarser layer-`r` scale. -/
theorem whitneyDepth_sub_lt_ten {b : ℝ} (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (hs k₀ : ℕ) {r n : ℕ} (hrn : r ≤ n) (hnr : n ≤ r + 3) :
    (n + whitneyScaleSeq b hs k₀ n) - (r + whitneyScaleSeq b hs k₀ r) < 10 := by
  have hmono := whitneyScaleSeq_mono (b := b) (by linarith) (by linarith) hs k₀ hrn
  have hgap : whitneyScaleSeq b hs k₀ n ≤ whitneyScaleSeq b hs k₀ r + 3 := by
    have h := whitneyScaleSeq_add_le hb0 hb hs k₀ r (n - r)
    rw [show r + (n - r) = n from by omega] at h
    omega
  omega

/-! ## The layer-exclusion gate -/

/-- The exponent form: `b(n+h_n) - (n+h_n) + n ≤ -2` whenever `b ≤ 1/8` and `k₀ ≥
3`. -/
theorem whitneyLayerExclusionExponent_le {b : ℝ} (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    {hs k₀ : ℕ} (hk₀ : 3 ≤ k₀) (n : ℕ) :
    b * ((n + whitneyScaleSeq b hs k₀ n : ℕ) : ℝ) -
        ((n + whitneyScaleSeq b hs k₀ n : ℕ) : ℝ) + (n : ℝ) ≤ -2 := by
  have hb1 : (0 : ℝ) < 1 - b := by linarith
  have hinv : (1 - b) * (1 - b)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hb1)
  have hlow := le_whitneyScaleSeq_cast b hs k₀ n
  have hk : (3 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hk₀
  have hhs : (0 : ℝ) ≤ (hs : ℝ) := Nat.cast_nonneg hs
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcast : ((n + whitneyScaleSeq b hs k₀ n : ℕ) : ℝ) =
      (n : ℝ) + (whitneyScaleSeq b hs k₀ n : ℝ) := by push_cast; ring
  have h1 : (1 - b) * (b * (1 - b)⁻¹ * (n : ℝ) + (hs : ℝ) + (k₀ : ℝ)) ≤
      (1 - b) * (whitneyScaleSeq b hs k₀ n : ℝ) :=
    mul_le_mul_of_nonneg_left hlow hb1.le
  have h2 : (1 - b) * (b * (1 - b)⁻¹ * (n : ℝ) + (hs : ℝ) + (k₀ : ℝ)) =
      b * (n : ℝ) + (1 - b) * ((hs : ℝ) + (k₀ : ℝ)) := by
    field_simp
    ring
  rw [h2] at h1
  have h3 : (1 - b) * 3 ≤ (1 - b) * ((hs : ℝ) + (k₀ : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) hb1.le
  rw [hcast]
  linarith [h1, h3, hinv, hn]

/-- ```
4 · 3^{b(n+h_n)} · 3^{m-n-h_n}  <  (2/3) · 3^{m-n} .
``` -/
theorem four_mul_three_rpow_whitneyDepth_lt_two_thirds {b : ℝ} (hb0 : 0 < b)
    (hb : b ≤ 1 / 8) {hs k₀ : ℕ} (hk₀ : 3 ≤ k₀) (m : ℤ) (n : ℕ) :
    4 * (3 : ℝ) ^ (b * ((n + whitneyScaleSeq b hs k₀ n : ℕ) : ℝ)) *
        (3 : ℝ) ^ (m - ((n + whitneyScaleSeq b hs k₀ n : ℕ) : ℤ)) <
      (2 / 3 : ℝ) * (3 : ℝ) ^ (m - (n : ℤ)) := by
  set L : ℕ := n + whitneyScaleSeq b hs k₀ n with hL
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hexp := whitneyLayerExclusionExponent_le (hs := hs) hb0 hb hk₀ n
  rw [← hL] at hexp
  -- rewrite both integer powers as real powers
  have hz1 : (3 : ℝ) ^ (m - (L : ℤ)) = (3 : ℝ) ^ (((m - (L : ℤ) : ℤ) : ℝ)) :=
    (Real.rpow_intCast 3 (m - (L : ℤ))).symm
  have hz2 : (3 : ℝ) ^ (m - (n : ℤ)) = (3 : ℝ) ^ (((m - (n : ℤ) : ℤ) : ℝ)) :=
    (Real.rpow_intCast 3 (m - (n : ℤ))).symm
  have hsplit : b * (L : ℝ) + (((m - (L : ℤ) : ℤ) : ℝ)) =
      (((m - (n : ℤ) : ℤ) : ℝ)) + (b * (L : ℝ) - (L : ℝ) + (n : ℝ)) := by
    push_cast
    ring
  rw [hz1, hz2, mul_assoc, ← Real.rpow_add h3, hsplit, Real.rpow_add h3]
  have hpow : (3 : ℝ) ^ (b * (L : ℝ) - (L : ℝ) + (n : ℝ)) ≤ (3 : ℝ) ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hval : (3 : ℝ) ^ (-2 : ℝ) = 1 / 9 := by
    rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) from by norm_num, Real.rpow_intCast]
    norm_num
  rw [hval] at hpow
  have hbase : (0 : ℝ) < (3 : ℝ) ^ (((m - (n : ℤ) : ℤ) : ℝ)) :=
    Real.rpow_pos_of_pos h3 _
  have hnn : (0 : ℝ) ≤ (3 : ℝ) ^ (b * (L : ℝ) - (L : ℝ) + (n : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos h3 _)
  nlinarith [hbase, hpow, hnn,
    mul_nonneg hbase.le (by linarith : (0 : ℝ) ≤
      1 / 9 - (3 : ℝ) ^ (b * (L : ℝ) - (L : ℝ) + (n : ℝ)))]

end

end Algsuperdiff.Section3.Provider.Whitney

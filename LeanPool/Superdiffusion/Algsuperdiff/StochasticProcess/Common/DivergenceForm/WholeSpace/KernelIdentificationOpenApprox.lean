/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ResolventTail
public import LeanPool.MarkovProcess.MarkovProcess.Kernel.ConservativeResolvent

/-!
# KernelIdentificationOpenApprox

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Compactly supported approximation of open-set indicators

This module constructs an increasing sequence of compactly supported continuous
functions converging pointwise to the indicator of a proper open set.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport Set Topology
open scoped ENNReal ZeroAtInfty

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

/-- A compactly supported continuous distance cutoff for an open set. -/
def rawOpenApprox (G : Set (Vec d)) (n : ℕ) (x : Vec d) : ℝ :=
  min 1 (((n : ℝ) + 1) * Metric.infDist x Gᶜ) * cubeBoundaryCutoff n x

omit [NeZero d] in
private theorem continuous_rawOpenApprox (G : Set (Vec d)) (n : ℕ) :
    Continuous (rawOpenApprox G n) := by
  exact (continuous_const.min (continuous_const.mul
    (Metric.continuous_infDist_pt Gᶜ))).mul
      (contDiff_cubeBoundaryCutoff n).continuous

omit [NeZero d] in
private theorem hasCompactSupport_rawOpenApprox (G : Set (Vec d)) (n : ℕ) :
    HasCompactSupport (rawOpenApprox G n) := by
  exact (hasCompactSupport_cubeBoundaryCutoff n).mul_left

/-- The bounded cumulative sum of open-set distance cutoffs. -/
def wholeSpaceOpenApprox (G : Set (Vec d)) (n : ℕ) (x : Vec d) : ℝ :=
  min 1 (∑ k ∈ Finset.range (n + 1), rawOpenApprox G k x)

omit [NeZero d] in
theorem continuous_wholeSpaceOpenApprox (G : Set (Vec d)) (n : ℕ) :
    Continuous (wholeSpaceOpenApprox G n) := by
  apply continuous_const.min
  exact continuous_finsetSum _ fun k _ ↦ continuous_rawOpenApprox G k

omit [NeZero d] in
theorem hasCompactSupport_wholeSpaceOpenApprox (G : Set (Vec d)) (n : ℕ) :
    HasCompactSupport (wholeSpaceOpenApprox G n) := by
  have hsum : HasCompactSupport
      (fun x ↦ ∑ k ∈ Finset.range (n + 1), rawOpenApprox G k x) := by
    classical
    induction Finset.range (n + 1) using Finset.induction_on with
    | empty =>
        simpa only [Finset.sum_empty] using!
          (HasCompactSupport.zero : HasCompactSupport (fun _ : Vec d ↦ (0 : ℝ)))
    | @insert k s hks ih =>
        simpa only [Finset.sum_insert hks] using!
          (hasCompactSupport_rawOpenApprox G k).add ih
  exact hsum.comp_left (by norm_num)

/-- The cumulative open-set cutoff bundled as a function vanishing at infinity. -/
def wholeSpaceOpenApproxC0 (G : Set (Vec d)) (n : ℕ) : C₀(Vec d, ℝ) where
  toFun := wholeSpaceOpenApprox G n
  continuous_toFun := continuous_wholeSpaceOpenApprox G n
  zero_at_infty' := (hasCompactSupport_wholeSpaceOpenApprox G n).is_zero_at_infty

omit [NeZero d] in
private theorem rawOpenApprox_nonneg (G : Set (Vec d)) (n : ℕ) (x : Vec d) :
    0 ≤ rawOpenApprox G n x := by
  apply mul_nonneg
  · exact le_min (by norm_num) (mul_nonneg (by positivity) Metric.infDist_nonneg)
  · exact QuantitativeBallCutoff.canonicalFun_nonneg 0
      (cubeBoundaryCutoffInnerRadius n) (cubeBoundaryCutoffOuterRadius n) x

omit [NeZero d] in
private theorem wholeSpaceOpenApprox_le_one (G : Set (Vec d)) (n : ℕ)
    (x : Vec d) : wholeSpaceOpenApprox G n x ≤ 1 := min_le_left _ _

omit [NeZero d] in
theorem wholeSpaceOpenApprox_nonneg (G : Set (Vec d)) (n : ℕ)
    (x : Vec d) : 0 ≤ wholeSpaceOpenApprox G n x := by
  exact le_min (by norm_num) (Finset.sum_nonneg fun k _ ↦ rawOpenApprox_nonneg G k x)

omit [NeZero d] in
theorem monotone_wholeSpaceOpenApprox (G : Set (Vec d)) (x : Vec d) :
    Monotone fun n ↦ wholeSpaceOpenApprox G n x := by
  apply monotone_nat_of_le_succ
  intro n
  apply min_le_min le_rfl
  have hs : (∑ k ∈ Finset.range (n + 1), rawOpenApprox G k x) ≤
      ∑ k ∈ Finset.range ((n + 1) + 1), rawOpenApprox G k x := by
    calc
      (∑ k ∈ Finset.range (n + 1), rawOpenApprox G k x) ≤
          (∑ k ∈ Finset.range (n + 1), rawOpenApprox G k x) +
            rawOpenApprox G (n + 1) x :=
        le_add_of_nonneg_right (rawOpenApprox_nonneg G (n + 1) x)
      _ = ∑ k ∈ Finset.range ((n + 1) + 1), rawOpenApprox G k x :=
        (Finset.sum_range_succ (fun k ↦ rawOpenApprox G k x) (n + 1)).symm
  simpa only [Nat.add_assoc] using hs

omit [NeZero d] in
private theorem wholeSpaceOpenApprox_eq_zero_of_notMem (G : Set (Vec d))
    {n : ℕ} {x : Vec d} (hx : x ∉ G) : wholeSpaceOpenApprox G n x = 0 := by
  have hraw : ∀ k, rawOpenApprox G k x = 0 := by
    intro k
    have hinf : Metric.infDist x Gᶜ = 0 :=
      Metric.infDist_zero_of_mem (show x ∈ Gᶜ from hx)
    rw [rawOpenApprox, hinf, mul_zero, min_eq_right zero_le_one, zero_mul]
  rw [wholeSpaceOpenApprox]
  simp only [hraw, Finset.sum_const_zero, min_eq_right zero_le_one]

omit [NeZero d] in
private theorem exists_wholeSpaceOpenApprox_eq_one_of_mem (G : Set (Vec d))
    (hG : IsOpen G) (hGne : G ≠ Set.univ) {x : Vec d} (hx : x ∈ G) :
    ∃ n, wholeSpaceOpenApprox G n x = 1 := by
  have hGc : (Gᶜ : Set (Vec d)).Nonempty := Set.nonempty_compl.2 hGne
  have hinf : 0 < Metric.infDist x Gᶜ := by
    rw [← hG.isClosed_compl.notMem_iff_infDist_pos hGc]
    exact fun hxc ↦ hxc hx
  obtain ⟨N, hN⟩ := exists_nat_gt (Metric.infDist x Gᶜ)⁻¹
  have hpow : ∀ᶠ n : ℕ in atTop, 2 * euclideanNorm x + 1 < (3 : ℝ) ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 3 by norm_num)).eventually_gt_atTop _
  obtain ⟨M, hM⟩ := hpow.exists
  let n := max N M
  have hfirstn : min 1 (((n : ℝ) + 1) * Metric.infDist x Gᶜ) = 1 := by
    apply min_eq_left
    have hcast : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (Nat.le_max_left N M)
    have hle : (Metric.infDist x Gᶜ)⁻¹ ≤ (n : ℝ) + 1 := by
      linarith only [hN, hcast]
    rwa [inv_le_iff_one_le_mul₀ hinf] at hle
  have hMn : 2 * euclideanNorm x + 1 < (3 : ℝ) ^ n := by
    exact hM.trans_le (pow_le_pow_right₀ (a := (3 : ℝ)) (by norm_num)
      (Nat.le_max_right N M))
  have hxball : x ∈ euclideanBall 0 (cubeBoundaryCutoffInnerRadius n) := by
    have hr : 0 ≤ cubeBoundaryCutoffInnerRadius n :=
      div_nonneg (pow_nonneg (by norm_num) n) (by norm_num)
    change euclideanSqDist x 0 < cubeBoundaryCutoffInnerRadius n ^ 2
    rw [show euclideanSqDist x 0 = euclideanNorm (x - 0) ^ 2 by
      rw [euclideanNorm_sq]; rfl]
    apply (sq_lt_sq₀ (euclideanNorm_nonneg _) hr).2
    simpa only [sub_zero, cubeBoundaryCutoffInnerRadius] using
      (show euclideanNorm x < (3 : ℝ) ^ n / 2 by linarith only [hMn])
  have hraw : rawOpenApprox G n x = 1 := by
    rw [rawOpenApprox, hfirstn, one_mul, cubeBoundaryCutoff_eq_one hxball]
  refine ⟨n, ?_⟩
  apply le_antisymm (wholeSpaceOpenApprox_le_one G n x)
  rw [wholeSpaceOpenApprox]
  apply le_min le_rfl
  rw [← hraw]
  exact Finset.single_le_sum (fun k _ ↦ rawOpenApprox_nonneg G k x)
    (Finset.mem_range.mpr (Nat.lt_succ_self n))

omit [NeZero d] in
theorem iSup_wholeSpaceOpenApprox (G : Set (Vec d)) (hG : IsOpen G)
    (hGne : G ≠ Set.univ) (x : Vec d) :
    ⨆ n, ENNReal.ofReal (wholeSpaceOpenApprox G n x) =
      G.indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
  by_cases hx : x ∈ G
  · obtain ⟨n, hn⟩ := exists_wholeSpaceOpenApprox_eq_one_of_mem G hG hGne hx
    apply le_antisymm
    · apply iSup_le
      intro k
      rw [Set.indicator_of_mem hx]
      exact ENNReal.ofReal_le_one.mpr (wholeSpaceOpenApprox_le_one G k x)
    · rw [Set.indicator_of_mem hx, ← ENNReal.ofReal_one, ← hn]
      exact le_iSup (fun k ↦ ENNReal.ofReal (wholeSpaceOpenApprox G k x)) n
  · rw [Set.indicator_of_notMem hx]
    simp only [wholeSpaceOpenApprox_eq_zero_of_notMem G hx, ENNReal.ofReal_zero,
      iSup_const]

omit [NeZero d] in
theorem tendsto_wholeSpaceOpenApprox (G : Set (Vec d)) (hG : IsOpen G)
    (hGne : G ≠ Set.univ) (x : Vec d) :
    Tendsto (fun n ↦ wholeSpaceOpenApprox G n x) atTop
      (nhds (G.indicator (fun _ ↦ (1 : ℝ)) x)) := by
  by_cases hx : x ∈ G
  · obtain ⟨n, hn⟩ := exists_wholeSpaceOpenApprox_eq_one_of_mem G hG hGne hx
    rw [Set.indicator_of_mem hx]
    refine tendsto_atTop_of_eventually_const (i₀ := n) fun k hnk ↦ ?_
    apply le_antisymm (wholeSpaceOpenApprox_le_one G k x)
    calc
      1 = wholeSpaceOpenApprox G n x := hn.symm
      _ ≤ wholeSpaceOpenApprox G k x := monotone_wholeSpaceOpenApprox G x hnk
  · rw [Set.indicator_of_notMem hx]
    have hz : ∀ n, wholeSpaceOpenApprox G n x = 0 :=
      fun n ↦ wholeSpaceOpenApprox_eq_zero_of_notMem G hx
    simpa only [hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0))

omit [NeZero d] in
theorem abs_wholeSpaceOpenApprox_le_one (G : Set (Vec d)) (n : ℕ)
    (x : Vec d) : |wholeSpaceOpenApprox G n x| ≤ 1 := by
  rw [abs_of_nonneg (wholeSpaceOpenApprox_nonneg G n x)]
  exact wholeSpaceOpenApprox_le_one G n x

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form

/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Topology.MetricSpace.Pseudo.Real

public import Mathlib.Analysis.Complex.Norm

-- [TABLET NODE: P4909T1OmittedDiskBarrier]

/-!
# P4909T1OmittedDiskBarrier

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4909T1OmittedDiskBarrier (P : Set ℂ) (a : ℂ) (r : ℝ)
    (hr : 0 < r) (ha : a ∉ P)
    (hboundary : Disjoint (frontier P) (Metric.ball a r)) :
    ∀ z ∈ interior P, r < dist z a := by
-- BODY
  have path_cont (z : ℂ) : Continuous (fun t : ℝ => (t : ℂ) * (z - a) + a) := by
    rw [Metric.continuous_iff]
    intro t ε hε
    have hn := norm_nonneg (z - a)
    refine ⟨ε / (‖z - a‖ + 1), div_pos hε (by linarith), ?_⟩
    intro u hu
    have hdiff : (u : ℂ) * (z - a) + a - ((t : ℂ) * (z - a) + a) =
        ((u - t : ℝ) : ℂ) * (z - a) := by push_cast; ring
    rw [dist_eq_norm, hdiff, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hu' : |u - t| < ε / (‖z - a‖ + 1) := by
      simpa only [Real.dist_eq] using hu
    have hprod := (lt_div_iff₀ (by linarith : 0 < ‖z - a‖ + 1)).mp hu'
    nlinarith [abs_nonneg (u - t)]
  have hdisj : Disjoint (interior P) (interior Pᶜ) := by
    rw [Set.disjoint_left]
    intro z hz hc
    exact (interior_subset hc) (interior_subset hz)
  have hcover : Metric.ball a r ⊆ interior P ∪ interior Pᶜ := by
    rw [← compl_frontier_eq_union_interior]
    intro z hz
    exact fun h => Set.disjoint_left.mp hboundary h hz
  have hopen : Disjoint (interior P) (Metric.ball a r) := by
    rw [Set.disjoint_left]
    intro z hz hb
    let γ (t : ℝ) := (t : ℂ) * (z - a) + a
    have hγ : Continuous γ := path_cont z
    have hconn : IsPreconnected (γ '' Set.Icc (0 : ℝ) 1) :=
      isPreconnected_Icc.image γ hγ.continuousOn
    have hsub : γ '' Set.Icc (0 : ℝ) 1 ⊆ Metric.ball a r := by
      rintro w ⟨t, ht, rfl⟩
      change dist (γ t) a < r
      rw [dist_eq_norm]
      dsimp [γ]
      rw [add_sub_cancel_right, Complex.norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg ht.1]
      have hb' : ‖z - a‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hb
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _))
        (by simpa only [one_mul] using hb')
    have ha' : a ∈ γ '' Set.Icc (0 : ℝ) 1 := by
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [γ]⟩
    have hz' : z ∈ γ '' Set.Icc (0 : ℝ) 1 := by
      exact ⟨1, ⟨zero_le_one, le_rfl⟩, by simp [γ]⟩
    rcases hconn.subset_or_subset isOpen_interior isOpen_interior hdisj
      (hsub.trans hcover) with hin | hout
    · exact ha (interior_subset (hin ha'))
    · exact Set.disjoint_left.mp hdisj hz (hout hz')
  have hclosed := hopen.closure_right isOpen_interior
  intro z hz
  apply lt_of_not_ge
  intro hle
  have hzclosure : z ∈ closure (Metric.ball a r) := by
    let γ (t : ℝ) := (t : ℂ) * (z - a) + a
    have hγ : Continuous γ := path_cont z
    have h1 : (1 : ℝ) ∈ closure (Set.Ico (0 : ℝ) 1) := by
      rw [closure_Ico zero_ne_one]
      exact ⟨zero_le_one, le_rfl⟩
    have hmap : Set.MapsTo γ (Set.Ico (0 : ℝ) 1) (Metric.ball a r) := by
      intro t ht
      change dist (γ t) a < r
      rw [dist_eq_norm]
      dsimp [γ]
      rw [add_sub_cancel_right, Complex.norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg ht.1]
      have hn : ‖z - a‖ ≤ r := by simpa only [dist_eq_norm] using hle
      calc
        t * ‖z - a‖ ≤ t * r := mul_le_mul_of_nonneg_left hn ht.1
        _ < r := by nlinarith [hr, ht.2]
    have hlim := hγ.continuousWithinAt.mem_closure h1 hmap
    simpa only [γ, Complex.ofReal_one, one_mul, sub_add_cancel] using hlim
  exact Set.disjoint_left.mp hclosed hz hzclosure

end ApollonianSuperharmonic

end

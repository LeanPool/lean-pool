/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Second-order Taylor estimates along line segments

The coarse remainder constant is sufficient for uniform geodesic residual
estimates. It follows by two applications of the vector-valued mean-value
inequality and does not invoke parameter smoothness of ODE solutions.
-/

@[expose] public section


open Set Filter
open scoped Topology

namespace PlanarMidpoint

/-- A uniform bound on the change in the second derivative controls the
second-order Taylor remainder at time one. -/
theorem second_order_line_remainder {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {x v a : ℝ → V} {M : ℝ} (hM : 0 ≤ M)
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt x (v t) t)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt v (a t) t)
    (ha : ∀ t ∈ Icc (0 : ℝ) 1, ‖a t - a 0‖ ≤ M) :
    ‖x 1 - x 0 - v 0 - (1 / 2 : ℝ) • a 0‖ ≤ M := by
  let vErr : ℝ → V := fun t ↦ v t - t • a 0
  have hvErr (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt vErr (a t - a 0) t := by
    convert (hv t ht).sub ((hasDerivAt_id t).smul_const (a 0)) using 1
    · rfl
    · simp
  have hvBound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖vErr t - vErr 0‖ ≤ M := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun s hs ↦ (hvErr s hs).hasDerivWithinAt)
      (fun s hs ↦ ha s (Ico_subset_Icc_self hs)) t ht
    exact h.trans (by simpa only [sub_zero] using mul_le_of_le_one_right hM ht.2)
  let xErr : ℝ → V := fun t ↦ x t - t • v 0 - (t ^ 2 / 2) • a 0
  have hxErr (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt xErr (vErr t - vErr 0) t := by
    have hp : HasDerivAt (fun s : ℝ ↦ s ^ 2 / 2) t t := by
      convert ((hasDerivAt_id t).pow 2).div_const 2 using 1 <;> simp
    convert ((hx t ht).sub ((hasDerivAt_id t).smul_const (v 0))).sub
      (hp.smul_const (a 0)) using 1
    · rfl
    · dsimp [vErr]
      module
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun s hs ↦ (hxErr s hs).hasDerivWithinAt)
    (fun s hs ↦ hvBound s (Ico_subset_Icc_self hs))
  simpa [xErr, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

/-- A second-order spatial remainder estimate from bounds on the variation of
an actual second Fréchet derivative along the segment. -/
theorem second_order_spatial_remainder {U V : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : U → V} {J : U → U →L[ℝ] V} {H : U → U →L[ℝ] U →L[ℝ] V}
    {S : Set U} {p d : U} {η : ℝ} (hη : 0 ≤ η)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, p + t • d ∈ S)
    (hf : ∀ y ∈ S, HasFDerivAt f (J y) y)
    (hJ : ∀ y ∈ S, HasFDerivAt J (H y) y)
    (hH : ∀ y ∈ S, ‖H y - H p‖ ≤ η) :
    ‖f (p + d) - f p - J p d - (1 / 2 : ℝ) • H p d d‖ ≤ η * ‖d‖ ^ 2 := by
  have hline (t : ℝ) : HasDerivAt (fun s : ℝ ↦ p + s • d) d t := by
    convert (hasDerivAt_const t p).add ((hasDerivAt_id t).smul_const d) using 1
    · rfl
    · simp
  have hfline (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s : ℝ ↦ f (p + s • d)) (J (p + t • d) d) t :=
    (hf _ (hseg t ht)).comp_hasDerivAt t (hline t)
  have hJline (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s : ℝ ↦ J (p + s • d) d) (H (p + t • d) d d) t := by
    have hpath : HasDerivAt (fun s : ℝ ↦ J (p + s • d))
        (H (p + t • d) d) t :=
      (hJ _ (hseg t ht)).comp_hasDerivAt t (hline t)
    simpa only [map_zero, add_zero] using hpath.clm_apply (hasDerivAt_const t d)
  have hvar (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖H (p + t • d) d d - H (p + (0 : ℝ) • d) d d‖ ≤ η * ‖d‖ ^ 2 := by
    simp only [zero_smul, add_zero]
    calc
      ‖H (p + t • d) d d - H p d d‖ = ‖((H (p + t • d) - H p) d) d‖ := by rfl
      _ ≤ ‖(H (p + t • d) - H p) d‖ * ‖d‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖H (p + t • d) - H p‖ * ‖d‖) * ‖d‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ (η * ‖d‖) * ‖d‖ := by
        gcongr
        exact hH _ (hseg t ht)
      _ = η * ‖d‖ ^ 2 := by ring
  have h := second_order_line_remainder (mul_nonneg hη (sq_nonneg ‖d‖))
    hfline hJline hvar
  simpa using h

/-- A `C²` map has a second-order spatial expansion with a uniformly small
quadratic remainder on a sufficiently small ball. -/
theorem exists_second_order_spatial_remainder {U V : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : U → V} {Ω : Set U} {p : U}
    (hΩ : IsOpen Ω) (hp : p ∈ Ω) (hf : ContDiffOn ℝ 2 f Ω)
    {η : ℝ} (hη : 0 < η) :
    ∃ r > (0 : ℝ), Metric.ball p r ⊆ Ω ∧ ∀ d : U, ‖d‖ < r →
      ‖f (p + d) - f p - fderiv ℝ f p d - (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ f) p d d‖ ≤ η * ‖d‖ ^ 2
          := by
  have hJ : ContDiffOn ℝ 1 (fderiv ℝ f) Ω := hf.fderiv_of_isOpen hΩ (by norm_num)
  have hHc : ContinuousAt (fderiv ℝ (fderiv ℝ f)) p :=
    (hJ.continuousOn_fderiv_of_isOpen hΩ (by norm_num)).continuousAt (hΩ.mem_nhds hp)
  have hsmall : ∀ᶠ y in nhds p,
      ‖fderiv ℝ (fderiv ℝ f) y - fderiv ℝ (fderiv ℝ f) p‖ < η := by
    have h : ∀ᶠ y in nhds p, fderiv ℝ (fderiv ℝ f) y ∈
        Metric.ball (fderiv ℝ (fderiv ℝ f) p) η :=
      hHc.eventually (Metric.ball_mem_nhds (fderiv ℝ (fderiv ℝ f) p) hη)
    filter_upwards [h] with y hy
    rw [Metric.mem_ball] at hy
    rw [← dist_eq_norm (fderiv ℝ (fderiv ℝ f) y) (fderiv ℝ (fderiv ℝ f) p)]
    exact hy
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    (hsmall.and (hΩ.mem_nhds hp))
  refine ⟨r, hr, fun y hy ↦ (hball hy).2, ?_⟩
  intro d hd
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : p + t • d ∈ Metric.ball p r := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg d) ht.2).trans_lt hd
  exact second_order_spatial_remainder hη.le hseg
    (fun y hy ↦ ((hf.contDiffAt (hΩ.mem_nhds (hball hy).2)).differentiableAt
      (by norm_num)).hasFDerivAt)
    (fun y hy ↦ ((hJ.contDiffAt (hΩ.mem_nhds (hball hy).2)).differentiableAt
      (by norm_num)).hasFDerivAt)
    (fun y hy ↦ (hball hy).1.le)

end PlanarMidpoint

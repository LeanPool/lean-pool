/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PshRealConvexity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.LocalPshDiscControl
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# Maximum principle on a closed complex disc

The local strong maximum principle already proved from deficit integrals can
be propagated across a connected closed disc.  This upgrades a finite bound
on the boundary circle to the whole disc while using only germwise
plurisubharmonicity.  No global disc-submean theorem is assumed.
-/

@[expose] public section

open Metric Set
open scoped Topology

namespace SGPT.Foundations.Analysis

noncomputable section

/-- A germwise plurisubharmonic function bounded by a finite constant on the
boundary circle is bounded by the same constant on the closed disc. -/
theorem PlurisubharmonicOn.le_const_on_closedBall_of_le_on_sphere
    {u : ℂ → EReal} {Ω : Set ℂ} (hu : PlurisubharmonicOn u Ω)
    {c : ℂ} {R C : ℝ} (hR : 0 < R) (hD : closedBall c R ⊆ Ω)
    (hs : ∀ z ∈ sphere c R, u z ≤ (C : EReal)) :
    ∀ z ∈ closedBall c R, u z ≤ (C : EReal) := by
  intro q hq
  by_contra hqC
  have hCq : (C : EReal) < u q := lt_of_not_ge hqC
  obtain ⟨y, hyD, hmax⟩ :=
    (hu.upperSemicontinuousOn.mono hD).exists_isMaxOn
      ⟨q, hq⟩ (isCompact_closedBall c R)
  have hy_top : u y ≠ ⊤ := (hu y (hD hyD)).ne_top
  have hy_bot : u y ≠ ⊥ := by
    have hy_gt : (C : EReal) < u y := hCq.trans_le (hmax hq)
    intro hy
    rw [hy] at hy_gt
    exact (not_lt_of_ge bot_le) hy_gt
  let B : ℝ := (u y).toReal
  have hyB : u y = (B : EReal) := (EReal.coe_toReal hy_top hy_bot).symm
  have hCB : C < B := by
    rw [← EReal.coe_lt_coe_iff, ← hyB]
    exact hCq.trans_le (hmax hq)
  have hy_ball : y ∈ ball c R := by
    have hyr : dist y c ≤ R := mem_closedBall.mp hyD
    apply mem_ball.mpr
    apply lt_of_le_of_ne hyr
    intro hyr_eq
    have hys : y ∈ sphere c R := mem_sphere.mpr hyr_eq
    have := hs y hys
    rw [hyB, EReal.coe_le_coe_iff] at this
    exact (not_lt_of_ge this) hCB
  let O : Set ℂ := {z | z ∈ ball c R ∧ u z = (B : EReal)}
  have hO : IsOpen O := by
    rw [Metric.isOpen_iff]
    intro z hz
    obtain ⟨W, hW, hzW, hdisc⟩ := hu z (hD (ball_subset_closedBall hz.1))
    have hopen : IsOpen (W ∩ ball c R) := hW.inter isOpen_ball
    have hzopen : z ∈ W ∩ ball c R := ⟨hzW, hz.1⟩
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen z hzopen
    have hBW : ball z δ ⊆ W := fun w hw => (hball hw).1
    have hBbound : ∀ w ∈ ball z δ, u w ≤ (B : EReal) := by
      intro w hw
      exact (hmax (ball_subset_closedBall (hball hw).2)).trans_eq hyB
    have heq := hdisc.eqOn_ball_of_le_of_eq z hBW hBbound hz.2
    refine ⟨δ, hδ, ?_⟩
    intro w hw
    exact ⟨(hball hw).2, heq hw⟩
  have hK : IsCompact (closedBall c R ∩ u ⁻¹' Ici (B : EReal)) :=
    (hu.upperSemicontinuousOn.mono hD).isCompact_inter_preimage_Ici
      (isCompact_closedBall c R) (B : EReal)
  have hOK : O ⊆ closedBall c R ∩ u ⁻¹' Ici (B : EReal) := by
    intro z hz
    exact ⟨ball_subset_closedBall hz.1, by simp [hz.2]⟩
  have hclosure : closure O ∩ closedBall c R ⊆ O := by
    intro z hz
    have hzK := closure_minimal hOK hK.isClosed hz.1
    have hzeq : u z = (B : EReal) := by
      apply le_antisymm
      · exact (hmax hz.2).trans_eq hyB
      · exact hzK.2
    have hzball : z ∈ ball c R := by
      have hzr : dist z c ≤ R := mem_closedBall.mp hz.2
      apply mem_ball.mpr
      apply lt_of_le_of_ne hzr
      intro hzr_eq
      have hzs : z ∈ sphere c R := mem_sphere.mpr hzr_eq
      have hzC := hs z hzs
      rw [hzeq, EReal.coe_le_coe_iff] at hzC
      exact (not_lt_of_ge hzC) hCB
    exact ⟨hzball, hzeq⟩
  have hnonempty : (closedBall c R ∩ O).Nonempty :=
    ⟨y, ball_subset_closedBall hy_ball, hy_ball, hyB⟩
  have hall : closedBall c R ⊆ O :=
    isPreconnected_closedBall.subset_of_closure_inter_subset hO hnonempty hclosure
  let z : ℂ := c + (R : ℂ)
  have hzs : z ∈ sphere c R := by
    simp [z, abs_of_pos hR]
  have hzO := hall (sphere_subset_closedBall hzs)
  exact (not_lt_of_ge (by
    have hzC := hs z hzs
    rw [hzO.2, EReal.coe_le_coe_iff] at hzC
    exact hzC)) hCB

end

end SGPT.Foundations.Analysis

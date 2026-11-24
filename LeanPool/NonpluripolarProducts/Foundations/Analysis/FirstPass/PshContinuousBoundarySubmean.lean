/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.HarmonicDiscPsh
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PshClosedDiscMaximum

/-!
# Continuous boundary majorants for germwise PSH functions

A germwise plurisubharmonic function on a neighborhood of a closed complex
disc lies below the circle average of every continuous real boundary
majorant, provided the majorant can be uniformly approximated on the circle
by global real harmonic functions.  The latter approximation is isolated as
an explicit hypothesis so that the maximum-principle argument is independent
of the Fourier construction.
-/

@[expose] public section

open InnerProductSpace Metric Set MeasureTheory

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

/-- The maximum principle and harmonic mean-value property turn uniform
harmonic approximation of a continuous boundary majorant into a center
submean inequality. -/
theorem PlurisubharmonicOn.le_circleAverage_of_continuous_majorant
    {u : ℂ → EReal} {Ω : Set ℂ} (hu : PlurisubharmonicOn u Ω)
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hD : closedBall c R ⊆ Ω) {g : ℂ → ℝ} (hg : Continuous g)
    (hgu : ∀ z ∈ sphere c R, u z ≤ (g z : EReal))
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ h : ℂ → ℝ, HarmonicOnNhd h univ ∧
        ∀ z ∈ sphere c R, |h z - g z| < ε) :
    u c ≤ ((Real.circleAverage g c R : ℝ) : EReal) := by
  have hcΩ : c ∈ Ω := hD (mem_closedBall_self hR.le)
  have hctop : u c ≠ ⊤ := (hu c hcΩ).ne_top
  by_cases hcbot : u c = ⊥
  · simp [hcbot]
  rw [← EReal.coe_toReal hctop hcbot, EReal.coe_le_coe_iff]
  apply le_of_forall_pos_le_add
  intro δ hδ
  let ε : ℝ := δ / 2
  have hε : 0 < ε := div_pos hδ (by norm_num)
  obtain ⟨h, hh, happ⟩ := happrox ε hε
  have hhΩ : HarmonicOnNhd h Ω := hh.mono (subset_univ Ω)
  have hsub : PlurisubharmonicOn (fun z => u z - (h z : EReal)) Ω :=
    hu.sub_harmonic hhΩ
  have hsphere : ∀ z ∈ sphere c R,
      u z - (h z : EReal) ≤ (ε : EReal) := by
    intro z hz
    have hreal : g z - h z ≤ ε := by
      have := (abs_lt.mp (happ z hz)).1
      linarith
    calc
      u z - (h z : EReal) ≤ (g z : EReal) - (h z : EReal) :=
        EReal.sub_le_sub (hgu z hz) le_rfl
      _ = ((g z - h z : ℝ) : EReal) := by rw [EReal.coe_sub]
      _ ≤ (ε : EReal) := EReal.coe_le_coe_iff.mpr hreal
  have hcenter_sub : u c - (h c : EReal) ≤ (ε : EReal) :=
    hsub.le_const_on_closedBall_of_le_on_sphere hR hD hsphere c
      (mem_closedBall_self hR.le)
  have hcenter : u c ≤ ((h c + ε : ℝ) : EReal) := by
    have hle := (EReal.sub_le_iff_le_add
      (Or.inl (EReal.coe_ne_bot (h c))) (Or.inl (EReal.coe_ne_top (h c)))).mp
      hcenter_sub
    simpa [← EReal.coe_add, add_comm] using hle
  have hhclosed : HarmonicOnNhd h (closedBall c |R|) :=
    hh.mono (subset_univ _)
  have hcircle_h : CircleIntegrable h c R :=
    (hhclosed.continuousOn.mono sphere_subset_closedBall).circleIntegrable'
  have hcircle_g : CircleIntegrable g c R :=
    hg.continuousOn.circleIntegrable'
  have hcircle_const : CircleIntegrable (fun _ : ℂ => ε) c R :=
    circleIntegrable_const ε c R
  have havg : h c ≤ Real.circleAverage g c R + ε := by
    have hmono : Real.circleAverage h c R ≤
        Real.circleAverage (fun z => g z + ε) c R := by
      apply Real.circleAverage_mono hcircle_h (hcircle_g.add hcircle_const)
      intro z hz
      have := (abs_lt.mp (happ z (by simpa [abs_of_pos hR] using hz))).2
      change h z ≤ g z + ε
      linarith
    rw [hhclosed.circleAverage_eq,
      Real.circleAverage_fun_add hcircle_g hcircle_const,
      Real.circleAverage_const] at hmono
    exact hmono
  have hreal_center : (u c).toReal ≤ Real.circleAverage g c R + δ := by
    apply EReal.coe_le_coe_iff.mp
    rw [EReal.coe_toReal hctop hcbot]
    refine hcenter.trans ?_
    apply EReal.coe_le_coe_iff.mpr
    dsimp [ε] at havg ⊢
    linarith
  exact hreal_center

end

end SGPT.Foundations.Analysis.FirstPass

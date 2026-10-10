/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Analysis.Cauchy
public import Mathlib.Tactic.Linarith

/-!
Rectangular action and angle buffers for Cauchy estimates on eroded phase domains.
-/

@[expose] public section

noncomputable section
open scoped NNReal
namespace KamProject.Arnold1963

theorem mem_angleStrip_of_dist_le {n : ℕ} {ρ δ : ℝ≥0} (hδρ : δ ≤ ρ)
    {q q' : ComplexSpace n} (hq : q ∈ angleStrip n (ρ - δ))
    (hd : dist q' q ≤ δ) : q' ∈ angleStrip n ρ := by
  apply (mem_angleStrip_iff _ _).2
  intro j
  have hx := (mem_angleStrip_iff _ _).1 hq j
  rw [NNReal.coe_sub hδρ] at hx
  have hv : |(q' j - q j).im| ≤ (δ : ℝ) :=
    (Complex.abs_im_le_norm _).trans ((norm_le_pi_norm (q' - q) j).trans
      (by simpa [dist_eq_norm] using hd))
  have heq : (q' j).im = (q' j - q j).im + (q j).im := by simp
  rw [heq]
  exact (abs_add_le _ _).trans (by linarith)

theorem phaseDomain_rectangular_buffer {n : ℕ} {G : Set (ComplexSpace n)}
    {ρ β δ : ℝ≥0} (hδρ : δ ≤ ρ) {p q : ComplexSpace n}
    (hx : (p, q) ∈ phaseDomain (erosion G β) (ρ - δ)) :
    Metric.closedBall p β ×ˢ Metric.closedBall q δ ⊆ phaseDomain G ρ := by
  intro y hy
  exact ⟨hx.1 hy.1, mem_angleStrip_of_dist_le hδρ hx.2 hy.2⟩

theorem phaseDomain_shrink_subset_erosion {n : ℕ} (G : Set (ComplexSpace n))
    {ρ r : ℝ≥0} (hrρ : r ≤ ρ) :
    phaseDomain (erosion G r) (ρ - r) ⊆ erosion (phaseDomain G ρ) r := by
  intro x hx y hy
  have hnorm : max ‖y.1 - x.1‖ ‖y.2 - x.2‖ ≤ (r : ℝ) := by
    simpa [Metric.mem_closedBall, dist_eq_norm, phase_norm_eq] using hy
  have hp : ‖y.1 - x.1‖ ≤ (r : ℝ) := (le_max_left _ _).trans hnorm
  have hq : ‖y.2 - x.2‖ ≤ (r : ℝ) := (le_max_right _ _).trans hnorm
  refine ⟨hx.1 (by simpa [Metric.mem_closedBall, dist_eq_norm] using hp), ?_⟩
  apply (mem_angleStrip_iff _ _).2
  intro j
  have hxq := (mem_angleStrip_iff _ _).1 hx.2 j
  rw [NNReal.coe_sub hrρ] at hxq
  have hd : |(y.2 j - x.2 j).im| ≤ (r : ℝ) :=
    (Complex.abs_im_le_norm _).trans ((norm_le_pi_norm (y.2 - x.2) j).trans hq)
  have heq : (y.2 j).im = (y.2 j - x.2 j).im + (x.2 j).im := by simp
  rw [heq]
  exact (abs_add_le _ _).trans (by linarith)

theorem AnalyticPhaseFunction.norm_vectorField_le_on_shrink {n : ℕ}
    {G : Set (ComplexSpace n)} {ρ r : ℝ≥0} (f : AnalyticPhaseFunction n G ρ)
    (hr : 0 < r) (hrρ : r ≤ ρ) {x : ComplexPhaseSpace n}
    (hx : x ∈ phaseDomain (erosion G r) (ρ - r)) :
    ‖hamiltonianVectorField f.toFun x‖ ≤ f.uniformNorm / r :=
  f.norm_vectorField_le_div hr (phaseDomain_shrink_subset_erosion G hrρ hx)

theorem AnalyticPhaseFunction.norm_pGradient_le_rectangular {n : ℕ}
    {G : Set (ComplexSpace n)} {ρ β : ℝ≥0} (f : AnalyticPhaseFunction n G ρ)
    (hβ : 0 < β) {p q : ComplexSpace n}
    (hp : p ∈ erosion G β) (hq : q ∈ angleStrip n ρ) :
    ‖pGradient f.toFun (p, q)‖ ≤ f.uniformNorm / β := by
  let g : ComplexSpace n → ℂ := fun p => f.toFun (p, q)
  have hg : AnalyticOnNhd ℂ g G := by
    intro p hp
    exact (f.analytic (p, q) ⟨hp, hq⟩).comp (f := fun x : ComplexSpace n => (x, q))
      (analyticAt_id.prod analyticAt_const)
  have hb : NormBoundOn g G f.uniformNorm :=
    ⟨(f.norm_le_iff.mp le_rfl).nonneg,
      fun p hp => (f.norm_le_iff.mp le_rfl).norm_le ⟨hp, hq⟩⟩
  have hd := (f.hasFDerivAt (x := (p, q)) ⟨erosion_subset G β hp, hq⟩).comp p
    ((hasFDerivAt_id (𝕜 := ℂ) p).prodMk (hasFDerivAt_const q p))
  apply (complex_norm_le_iff _ (div_nonneg hb.nonneg β.coe_nonneg)).2
  intro j
  have h := norm_fderiv_apply_le_div_of_mem_erosion (f := g) (x := p) hβ hg hb hp
    (show ‖Pi.single j (1 : ℂ)‖ ≤ 1 by rw [Pi.norm_single]; norm_num)
  change ‖fderiv ℂ g p (Pi.single j 1)‖ ≤ _ at h
  rw [show fderiv ℂ g p = _ from hd.fderiv] at h
  exact h

theorem AnalyticPhaseFunction.norm_qGradient_le_rectangular {n : ℕ}
    {G : Set (ComplexSpace n)} {ρ δ : ℝ≥0} (f : AnalyticPhaseFunction n G ρ)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) {p q : ComplexSpace n}
    (hp : p ∈ G) (hq : q ∈ angleStrip n (ρ - δ)) :
    ‖qGradient f.toFun (p, q)‖ ≤ f.uniformNorm / δ := by
  let g : ComplexSpace n → ℂ := fun q => f.toFun (p, q)
  have hg : AnalyticOnNhd ℂ g (angleStrip n ρ) := by
    intro q hq
    exact (f.analytic (p, q) ⟨hp, hq⟩).comp (f := fun x : ComplexSpace n => (p, x))
      (analyticAt_const.prod analyticAt_id)
  have hb : NormBoundOn g (angleStrip n ρ) f.uniformNorm :=
    ⟨(f.norm_le_iff.mp le_rfl).nonneg,
      fun q hq => (f.norm_le_iff.mp le_rfl).norm_le ⟨hp, hq⟩⟩
  have hq' : q ∈ erosion (angleStrip n ρ) δ :=
    fun _ hx => mem_angleStrip_of_dist_le hδρ hq hx
  have hd := (f.hasFDerivAt (x := (p, q)) ⟨hp, erosion_subset _ _ hq'⟩).comp q
    ((hasFDerivAt_const p q).prodMk (hasFDerivAt_id (𝕜 := ℂ) q))
  apply (complex_norm_le_iff _ (div_nonneg hb.nonneg δ.coe_nonneg)).2
  intro j
  have h := norm_fderiv_apply_le_div_of_mem_erosion (f := g) (x := q) hδ hg hb hq'
    (show ‖Pi.single j (1 : ℂ)‖ ≤ 1 by rw [Pi.norm_single]; norm_num)
  change ‖fderiv ℂ g q (Pi.single j 1)‖ ≤ _ at h
  rw [show fderiv ℂ g q = _ from hd.fderiv] at h
  exact h

end KamProject.Arnold1963

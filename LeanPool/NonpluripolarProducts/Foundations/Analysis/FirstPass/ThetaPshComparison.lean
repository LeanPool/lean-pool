/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.LocalPotentialIndependence
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ManifoldPluripolar
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PlurisubharmonicAE
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.RooftopEnvelope
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ERealChordUSC
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.GlobalPotentialTransforms

/-!
# Quasi-everywhere comparison of theta-PSH functions

A theta-PSH function lying quasi-everywhere below another one lies below it
everywhere. In a chart both functions become PSH after adding one common
smooth local potential, pluripolar sets are Haar-null, and almost-everywhere
comparison of a PSH function with an upper semicontinuous one is pointwise.
-/

@[expose] public section

open Set MeasureTheory

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Quasi-everywhere comparison of theta-PSH functions is pointwise. -/
theorem ThetaPlurisubharmonic.le_of_quasiEverywhere_le {θ : SmoothRealForm n M 2}
    {u v : M → EReal} (hu : ThetaPlurisubharmonic θ u) (hv : ThetaPlurisubharmonic θ v)
    (huv : QuasiEverywhere (n := n) (fun x => u x ≤ v x)) : u ≤ v := by
  intro x
  let e : ComplexChart n M := complexChartAt x
  have hx : e.val x ∈ e.val.target := e.val.map_source (mem_chart_source _ x)
  obtain ⟨W₁, ρ, hzW₁, hρ, hpu⟩ := hu e (e.val x) hx
  obtain ⟨W₂, σ, hzW₂, hσ, hpv⟩ := hv e (e.val x) hx
  let V := W₁ ∩ W₂
  have hV : IsOpen V := hρ.1.inter hσ.1
  have hρV := hρ.mono hV inter_subset_left
  have hσV := hσ.mono hV inter_subset_right
  have hpuV : PlurisubharmonicOn (fun y => chartFunction u e y + (σ y : EReal)) V :=
    (smoothLocalPotential_psh_iff θ e V ρ σ hρV hσV (chartFunction u e)).1
      (hpu.mono inter_subset_left)
  have hpvV := hpv.mono (inter_subset_right (s := W₁))
  have hae : ∀ᵐ y ∂(Measure.addHaar : Measure (ComplexModel n)).restrict V,
      chartFunction u e y + (σ y : EReal) ≤ chartFunction v e y + (σ y : EReal) := by
    have hVt : V ⊆ e.val.target := inter_subset_left.trans hρ.2.1
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hVt
      (huv.ae_in_chart e Measure.addHaar)] with y hy
    exact add_le_add_left hy _
  have hle := hpuV.le_of_ae_le hV hpvV.upperSemicontinuousOn Measure.addHaar hae
    (e.val x) ⟨hzW₁, hzW₂⟩
  have hcancel := add_le_add_left hle (((0 - σ (e.val x) : ℝ)) : EReal)
  rw [corrected_add_sub, corrected_add_sub, EReal.coe_zero, add_zero, add_zero] at hcancel
  simpa [chartFunction, e, e.val.left_inv (mem_chart_source _ x)] using hcancel

/-- The rooftop envelope of `min u (v + C)` lies below both theta-PSH obstacles.
No regularity of the envelope itself is used. -/
theorem rooftopEnvelope_min_add_const_le_obstacles {θ : SmoothRealForm n M 2}
    {u v : M → EReal} (hu : ThetaPlurisubharmonic θ u) (hv : ThetaPlurisubharmonic θ v)
    (C : ℝ) :
    rooftopEnvelope θ (fun x => min (u x) (v x + (C : EReal))) ≤ u ∧
      rooftopEnvelope θ (fun x => min (u x) (v x + (C : EReal))) ≤
        fun x => v x + (C : EReal) := by
  have hvC : ThetaPlurisubharmonic θ (fun x => v x + (C : EReal)) := by
    simpa [sub_eq_add_neg] using GlobalPotentialTransforms.thetaPlurisubharmonic_sub_const hv (-C)
  have hbound : ∀ g : M → EReal, ThetaPlurisubharmonic θ g →
      (∀ x, min (u x) (v x + (C : EReal)) ≤ g x) →
      rooftopEnvelope θ (fun x => min (u x) (v x + (C : EReal))) ≤ g := by
    intro g hg hmin
    refine (rooftopEnvelope_le_iff
      (ManifoldQuasiPlurisubharmonic.upperSemicontinuous hg.quasiPlurisubharmonic)).2 ?_
    intro ψ hψ hψle
    exact hψ.1.le_of_quasiEverywhere_le hg (hψle.mono fun x hx => hx.trans (hmin x))
  exact ⟨hbound u hu fun x => min_le_left _ _, hbound _ hvC fun x => min_le_right _ _⟩

end

end SGPT.Foundations.Analysis.FirstPass

/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.CircleDeficitMajorants
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ContinuousUscMajorants
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.HarmonicCircleApproximation
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PshContinuousBoundarySubmean
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.LocalPshDiscControl
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PlurisubharmonicPullback

/-!
# From PSH germs to the full affine-disc criterion

This file assembles the germwise closed-disc maximum principle, continuous
majorants of upper-semicontinuous boundary data, monotone convergence of
nonnegative deficits, and affine pullback.  The only remaining input is the
explicit uniform approximation of continuous circle data by global real
harmonic functions; it is named as a proposition so that the analytic
assembly remains independent of its Fourier construction.
-/

@[expose] public section

open InnerProductSpace Metric Set
open scoped ENNReal

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

/-- The precise harmonic approximation input required by the local-to-global
disc theorem. -/
def HasGlobalHarmonicCircleApproximation : Prop :=
  ∀ (c : ℂ) {R : ℝ}, R ≠ 0 → ∀ (g : ℂ → ℝ), Continuous g →
    ∀ ε : ℝ, 0 < ε →
      ∃ h : ℂ → ℝ, HarmonicOnNhd h univ ∧
        ∀ z ∈ sphere c |R|, |h z - g z| < ε

/-- On one complex line, germwise PSH plus global harmonic circle
approximation gives the exact extended-real deficit submean inequality on
every contained closed disc. -/
theorem PlurisubharmonicOn.circleSubmean_of_closedBall_subset_of_harmonicApproximation
    (hHA : HasGlobalHarmonicCircleApproximation)
    {u : ℂ → EReal} {Ω : Set ℂ} (hu : PlurisubharmonicOn u Ω)
    {c : ℂ} {R C : ℝ} (hR : 0 < R) (hD : closedBall c R ⊆ Ω)
    (hC : ∀ z ∈ closedBall c R, u z ≤ (C : EReal)) :
    circleDeficit u c 1 R C ≤
      ENNReal.ofReal (2 * Real.pi) * ((C : EReal) - u c).toENNReal := by
  let K : Set ℂ := sphere c R
  have hK : IsCompact K := isCompact_sphere c R
  have hKne : K.Nonempty := by
    let z : ℂ := c + (R : ℂ)
    exact ⟨z, by simp [K, z, abs_of_pos hR]⟩
  have hKΩ : K ⊆ Ω := by
    intro z hz
    exact hD (sphere_subset_closedBall hz)
  have husc : UpperSemicontinuousOn u K :=
    hu.upperSemicontinuousOn.mono hKΩ
  have htop : ∀ z ∈ K, u z ≠ ⊤ := fun z hz => (hu z (hKΩ hz)).ne_top
  have hCK : ∀ z ∈ K, u z ≤ (C : EReal) :=
    fun z hz => hC z (sphere_subset_closedBall hz)
  let g : ℕ → ℂ → ℝ := fun n => uscSupConvolution K u C n
  have hg : ∀ n, Continuous (g n) := fun n =>
    continuous_uscSupConvolution hKne htop hCK n
  have hgu : ∀ n z, z ∈ K → u z ≤ (g n z : EReal) := fun n z hz =>
    le_coe_uscSupConvolution hKne htop hCK n hz
  have hgC : ∀ n z, g n z ≤ C := fun n z =>
    uscSupConvolution_le hKne htop hCK n z
  have hganti : ∀ z, Antitone fun n => g n z := fun z =>
    uscSupConvolution_antitone hKne htop hCK z
  have hginf : ∀ z, z ∈ K → (⨅ n : ℕ, (g n z : EReal)) = u z :=
    fun z hz => iInf_coe_uscSupConvolution hKne husc htop hCK hz
  have hcenter : ∀ n, u c ≤ ((Real.circleAverage (g n) c R : ℝ) : EReal) := by
    intro n
    apply PlurisubharmonicOn.le_circleAverage_of_continuous_majorant
      hu hR hD (hg n)
    · intro z hz
      exact hgu n z hz
    · intro ε hε
      simpa [abs_of_pos hR] using hHA c hR.ne' (g n) (hg n) ε hε
  apply circleSubmean_of_continuous_antitone_majorants c g hg
  · intro n z _
    exact hgC n z
  · intro t m n hmn
    apply EReal.coe_le_coe_iff.mpr
    exact hganti (c + circleMap 0 R t) hmn
  · intro t
    have hz : c + circleMap 0 R t ∈ K := by
      simpa [K, circleMap] using circleMap_mem_sphere c hR.le t
    exact hginf _ hz
  · exact hcenter

/-- Conditional local-to-global theorem in an arbitrary complex normed
space.  No openness of `U` is needed because `PlurisubharmonicOn` already
stores ambient germs at all of its points. -/
theorem PlurisubharmonicOn.discPshOn_of_harmonicApproximation
    (hHA : HasGlobalHarmonicCircleApproximation)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u : E → EReal} {U : Set E} (hu : PlurisubharmonicOn u U) :
    DiscPshOn u U := by
  refine ⟨fun x hx => (hu x hx).ne_top, hu.upperSemicontinuousOn, ?_⟩
  intro x v r hr hD C hC
  let L : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight v
  let Ω : Set ℂ := (fun z => x + L z) ⁻¹' U
  let w : ℂ → EReal := fun z => u (x + L z)
  have hw : PlurisubharmonicOn w Ω := hu.comp_affine L x
  have hclosed : closedBall 0 r ⊆ Ω := by
    intro z hz
    apply hD
    exact ⟨z, hz, by simp [L]⟩
  have hwC : ∀ z ∈ closedBall 0 r, w z ≤ (C : EReal) := by
    intro z hz
    apply hC
    exact ⟨z, hz, by simp [L]⟩
  have hsub :=
    PlurisubharmonicOn.circleSubmean_of_closedBall_subset_of_harmonicApproximation
      hHA hw hr hclosed hwC
  change circleDeficit (fun z => u (x + L z)) 0 1 r C ≤
    ENNReal.ofReal (2 * Real.pi) *
      ((C : EReal) - u (x + L 0)).toENNReal at hsub
  rw [circleDeficit_comp_affine u L x] at hsub
  simpa [L] using hsub

/-- Fourier density on the additive circle supplies the harmonic
approximation input used above, for either sign of the nonzero radius. -/
theorem hasGlobalHarmonicCircleApproximation :
    HasGlobalHarmonicCircleApproximation := by
  intro c R hR g hg ε hε
  simpa using exists_global_harmonic_uniformApproxOn_sphere c
    (abs_pos.mpr hR) hg.continuousOn hε

/-- Germwise plurisubharmonicity implies the full affine-disc criterion on
an arbitrary domain.  Together with the existing reverse implication on
open domains, this supplies the local-to-global bridge needed by the PSH
supremum theorem. -/
theorem PlurisubharmonicOn.discPshOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u : E → EReal} {U : Set E} (hu : PlurisubharmonicOn u U) :
    DiscPshOn u U :=
  SGPT.Foundations.Analysis.FirstPass.PlurisubharmonicOn.discPshOn_of_harmonicApproximation
    hasGlobalHarmonicCircleApproximation hu

end

end SGPT.Foundations.Analysis.FirstPass

namespace SGPT.Foundations.Analysis

/-- Public local-to-global bridge from ambient PSH germs to the complete
affine-disc criterion. -/
theorem PlurisubharmonicOn.discPshOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u : E → EReal} {U : Set E} (hu : PlurisubharmonicOn u U) :
    DiscPshOn u U :=
  FirstPass.PlurisubharmonicOn.discPshOn hu

end SGPT.Foundations.Analysis

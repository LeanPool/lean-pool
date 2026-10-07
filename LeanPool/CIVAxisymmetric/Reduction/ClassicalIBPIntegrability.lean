/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder

/-!
The space-time-agnostic integration-by-parts core that the weak-divergence, weak-momentum,
and local-energy-inequality clauses of `CKN.IsSuitableWeakSolution` all need to move a spatial or
temporal derivative from a classical (`ContDiffOn`, not globally `ContDiff`) field onto a smooth
compactly-supported test function.
-/

public section

open MeasureTheory MeasureTheory.Measure Set
open CKN.Foundation.Parabolic

noncomputable section
namespace CIV



theorem integrableOn_mul_of_continuousOn_of_tsupport_subset
    {E : Type} [NormedAddCommGroup E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [T2Space E]
    {μ : Measure E} [IsAddHaarMeasure μ]
    {S K : Set E} {g ρ : E → ℝ}
    (hK : IsCompact K) (hKS : K ⊆ S)
    (hg : ContinuousOn g S) (hρ : Continuous ρ) (hsupp : tsupport ρ ⊆ K) :
    Integrable (fun x => g x * ρ x) μ := by
  have h_cont : ContinuousOn (fun x => g x * ρ x) K :=
    (hg.mono hKS).mul hρ.continuousOn
  have h_intOn : IntegrableOn (fun x => g x * ρ x) K μ :=
    h_cont.integrableOn_of_subset_isCompact hK hK.measurableSet Subset.rfl
      (hK.measure_ne_top)
  refine h_intOn.integrable_of_forall_notMem_eq_zero ?_
  intro x hx
  have hx' : x ∉ tsupport ρ := by
    intro hx_tsupp
    apply hx
    exact hsupp hx_tsupp
  have hρx : ρ x = 0 := image_eq_zero_of_notMem_tsupport hx'
  simp [hρx]

theorem integrable_mul_fderiv_of_continuousOn
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [T2Space E]
    {μ : Measure E} [IsAddHaarMeasure μ]
    {S K : Set E} {g ψ : E → ℝ} {v : E}
    (hK : IsCompact K) (hKS : K ⊆ S)
    (hg : ContinuousOn g S) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hsupp : tsupport ψ ⊆ K) :
    Integrable (fun x => g x * fderiv ℝ ψ x v) μ := by
  have _ := hψc
  have h_cont_fderiv : Continuous (fun x => fderiv ℝ ψ x v) :=
    (hψ.continuous_fderiv_apply (by simp)).comp
      (Continuous.prodMk continuous_id continuous_const)
  have hsupp_fderiv : tsupport (fun x => fderiv ℝ ψ x v) ⊆ K := by
    calc
      tsupport (fun x => fderiv ℝ ψ x v) ⊆ tsupport ψ := tsupport_fderiv_apply_subset ℝ v
      _ ⊆ K := hsupp
  exact integrableOn_mul_of_continuousOn_of_tsupport_subset
    hK hKS hg h_cont_fderiv hsupp_fderiv

theorem integral_mul_fderiv_eq_neg_fderiv_mul_of_continuousOn
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [OpensMeasurableSpace E] [T2Space E] [FiniteDimensional ℝ E]
    {μ : Measure E} [IsAddHaarMeasure μ]
    {S K : Set E} {h ψ : E → ℝ} {v : E}
    (hSopen : IsOpen S) (hK : IsCompact K) (hKS : K ⊆ S)
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h S)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (hsupp : tsupport ψ ⊆ K) :
    ∫ x, h x * fderiv ℝ ψ x v ∂μ = - ∫ x, fderiv ℝ h x v * ψ x ∂μ := by
  have h_cont_fderiv_h : ContinuousOn (fun x => fderiv ℝ h x v) S := by
    have h_map : ContinuousOn (fderiv ℝ h) S :=
      hh.continuousOn_fderiv_of_isOpen hSopen (by simp)
    intro x hx
    exact ContinuousWithinAt.clm_apply (h_map x hx) (continuous_const.continuousWithinAt)
  have hdf_h : ∀ x ∈ tsupport ψ, DifferentiableAt ℝ h x := by
    intro x hx
    have hxS : x ∈ S := hKS (hsupp hx)
    have h_diffOn : DifferentiableOn ℝ h S := hh.differentiableOn (by simp)
    exact h_diffOn.differentiableAt (hSopen.mem_nhds hxS)
  have hdf_ψ : ∀ x ∈ tsupport h, DifferentiableAt ℝ ψ x := by
    intro _ _
    exact hψ.differentiable (by simp) |>.differentiableAt
  have hf'g : Integrable (fun x => fderiv ℝ h x v * ψ x) μ :=
    integrableOn_mul_of_continuousOn_of_tsupport_subset
      hK hKS h_cont_fderiv_h hψ.continuous hsupp
  have hfg' : Integrable (fun x => h x * fderiv ℝ ψ x v) μ :=
    integrable_mul_fderiv_of_continuousOn
      hK hKS hh.continuousOn hψ hψc hsupp
  have hfg : Integrable (fun x => h x * ψ x) μ :=
    integrableOn_mul_of_continuousOn_of_tsupport_subset
      hK hKS hh.continuousOn hψ.continuous hsupp
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hf'g hfg' hfg hdf_h hdf_ψ

end CIV

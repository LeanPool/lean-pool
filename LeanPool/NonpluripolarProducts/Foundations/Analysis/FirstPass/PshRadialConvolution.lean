/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PshRadialRegularization
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PlurisubharmonicAE
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PlurisubharmonicLimits
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PshDiscLocalGlobal
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Radial convolution regularization of locally bounded PSH functions

The finite-dimensional bump instance used by the general mollifier API records
central symmetry but does not expose radiality.  We therefore isolate the
classical radial-kernel construction as explicit data: smooth nonnegative
normalized kernels, shrinking support, scalar-unitary invariance, localized
convolution monotonicity, and almost-everywhere convergence.

For any such concrete system, almost-everywhere convergence upgrades to
pointwise convergence without another assumption.  The decreasing
extended-real infimum is PSH, and almost-everywhere comparison with the
original upper-semicontinuous PSH representative gives equality at every
point.  Construction of the system itself is kept outside `FirstPass` until
the circle-mean/Fubini argument has been fully formalized.
-/

@[expose] public section

noncomputable section

open Set Metric Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.FirstPass.MongeAmpere

variable {n : ℕ}

/-- Almost-everywhere convergence of a decreasing real-valued PSH sequence
upgrades to pointwise `EReal` convergence to the given PSH representative.
The representative may have genuine `⊥` poles.  This is the
order/representative part of radial regularization and is independent of the
construction of the kernels. -/
theorem tendsto_everywhere_ereal_of_ae_of_antitone_psh
    {U : Opens (ComplexModel n)} {u : ComplexModel n → EReal}
    {f : ℕ → ComplexModel n → ℝ}
    (hu : PlurisubharmonicOn u U)
    (hf : ∀ j, PlurisubharmonicOn (fun z ↦ (f j z : EReal)) U)
    (hanti : ∀ z ∈ U, Antitone (fun j ↦ f j z))
    (hae : ∀ᵐ z ∂volume.restrict (U : Set (ComplexModel n)),
      Tendsto (fun j ↦ (f j z : EReal)) atTop (𝓝 (u z))) :
    ∀ z ∈ U, Tendsto (fun j ↦ (f j z : EReal)) atTop (𝓝 (u z)) := by
  let g : ComplexModel n → EReal := fun z ↦ ⨅ j, (f j z : EReal)
  have hantiE (z : ComplexModel n) (hz : z ∈ U) :
      Antitone (fun j ↦ (f j z : EReal)) := by
    intro a b hab
    exact EReal.coe_le_coe_iff.mpr (hanti z hz hab)
  have hgpsh : PlurisubharmonicOn g U := by
    apply DiscPshOn.plurisubharmonicOn_iInf_of_antitone U.isOpen
    · intro j
      exact (hf j).discPshOn
    · exact hantiE
  have hgae : ∀ᵐ z ∂volume.restrict (U : Set (ComplexModel n)),
      g z = u z := by
    filter_upwards [hae, ae_restrict_mem U.isOpen.measurableSet] with z hzlim hzU
    exact tendsto_nhds_unique (tendsto_atTop_iInf (hantiE z hzU)) hzlim
  have hgu : EqOn g u U :=
    hgpsh.eqOn_of_ae_eq hu U.isOpen volume hgae
  intro z hz
  rw [← hgu hz]
  exact tendsto_atTop_iInf (hantiE z hz)

/-- Real-valued specialization of
`tendsto_everywhere_ereal_of_ae_of_antitone_psh`. -/
theorem tendsto_everywhere_of_ae_of_antitone_psh
    {U : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    {f : ℕ → ComplexModel n → ℝ}
    (hu : PlurisubharmonicOn (fun z ↦ (u z : EReal)) U)
    (hf : ∀ j, PlurisubharmonicOn (fun z ↦ (f j z : EReal)) U)
    (hanti : ∀ z ∈ U, Antitone (fun j ↦ f j z))
    (hae : ∀ᵐ z ∂volume.restrict (U : Set (ComplexModel n)),
      Tendsto (fun j ↦ f j z) atTop (𝓝 (u z))) :
    ∀ z ∈ U, Tendsto (fun j ↦ f j z) atTop (𝓝 (u z)) := by
  have haeE : ∀ᵐ z ∂volume.restrict (U : Set (ComplexModel n)),
      Tendsto (fun j ↦ (f j z : EReal)) atTop (𝓝 (u z : EReal)) := by
    filter_upwards [hae] with z hzlim
    exact EReal.tendsto_coe.mpr hzlim
  intro z hz
  apply EReal.tendsto_coe.mp
  exact tendsto_everywhere_ereal_of_ae_of_antitone_psh hu hf hanti haeE z hz

end SGPT.Foundations.Analysis.FirstPass.MongeAmpere

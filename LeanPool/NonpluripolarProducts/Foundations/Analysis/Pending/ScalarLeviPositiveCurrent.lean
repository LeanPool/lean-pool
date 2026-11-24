/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.DistributionRegularizationFinal
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorContinuity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorCollar

/-!
# A scalar positive-Levi distribution produces a full positive local current

The top current uses canonical complex-oriented density and actual scalar distributions.
Its local positive differential will be obtained from the produced smooth PSH regularization,
with positivity tested on arbitrary variable strongly-positive compact tests.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.ScalarLeviPositiveCurrent

open FirstPass StronglyPositiveForms LocalProductCurrents LocalBedfordTaylorProducts
  LocalBedfordTaylorSmooth LocalBedfordTaylorContinuity LocalBedfordTaylorCollar

variable {n : ℕ} {U : Opens (ComplexModel n)}

/-- The genuine canonically oriented top current associated to a scalar distribution. -/
def scalarTopCurrent (T : 𝓓'(U, ℝ)) : LocalProductCurrent n U n :=
  LinearMap.smulRight (TopDegreeDensity.topDensityLM n ∘ₗ (formSpan n n).subtype) T

theorem scalarTopCurrent_apply (T : 𝓓'(U, ℝ)) (γ : formSpan n n) (φ : 𝓓(U, ℝ)) :
    scalarTopCurrent T γ φ = TopDegreeDensity.topDensity (γ : RealForm n (2 * n)) * T φ := by
  rfl

/-- Smooth regular distributions agree with the actual coefficient-measure multiplication. -/
theorem scalarTopCurrent_regularDistribution_eq_mulBorel
    {f : ComplexModel n → ℝ} (hf : ContDiff ℝ ∞ f) :
    scalarTopCurrent (regularDistribution volume f
      (hf.continuous.locallyIntegrable.locallyIntegrableOn U)) =
      mulBorel (oneCurrent U) ((U : Set (ComplexModel n)).indicator f) := by
  have hb : IsLocallyBoundedOn f U := fun K hK _ => by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuous.continuousOn
    exact ⟨C, fun x hx => by simpa [Real.norm_eq_abs] using hC x hx⟩
  rw [mulBorel_congr isPositive_oneCurrent
    (measurable_indicator_of_continuousOn hf.continuous.continuousOn)
    (isLocallyBoundedOn_indicator_of_continuousOn hf.continuous.continuousOn)
    hf.continuous.measurable hb (fun x hx => Set.indicator_of_mem hx f)]
  ext γ φ
  rw [scalarTopCurrent_apply, regularDistribution_apply,
    mulBorel_apply isPositive_oneCurrent hf.continuous.measurable hb,
    ← IsPositive.apply_smoothMulTest isPositive_oneCurrent U.isOpen
      hf.contDiffOn γ φ φ.tsupport_subset,
    oneCurrent_apply]
  simp only [smoothMulTest_apply]

/-- Scalar weak convergence gives actual current weak convergence. -/
theorem weakTendsto_scalarTopCurrent {T : ℕ → 𝓓'(U, ℝ)} {T₀ : 𝓓'(U, ℝ)}
    (h : ∀ φ : 𝓓(U, ℝ), Tendsto (fun j => T j φ) atTop (𝓝 (T₀ φ))) :
    WeakTendsto (fun j => scalarTopCurrent (T j)) (scalarTopCurrent T₀) := by
  intro γ φ
  simp only [scalarTopCurrent_apply]
  exact (h φ).const_mul _

/-- Natural scalar Levi positivity internally produces a full positive local differential. -/
theorem exists_local_isPositive_ddc_scalarTopCurrent
    {m : ℕ} {Ω : Opens (ComplexModel (m + 1))} {T : 𝓓'(Ω, ℝ)}
    (hT : HasNonnegativeDistributionalLevi T)
    (x : ComplexModel (m + 1)) (hx : x ∈ Ω) :
    ∃ (V : Opens (ComplexModel (m + 1))) (hVΩ : V ≤ Ω),
      x ∈ V ∧ IsPositive (ddc (scalarTopCurrent (restrictDistribution T hVΩ))) := by
  obtain ⟨V, hVΩ, f, hxV, hf⟩ :=
    exists_local_decreasing_psh_regularization volume hT x hx
  let Tf : ℕ → 𝓓'(V, ℝ) := fun j => regularDistribution volume (f j)
    ((hf.1 j).continuous.locallyIntegrable.locallyIntegrableOn V)
  have hweak : WeakTendsto (fun j => scalarTopCurrent (Tf j))
      (scalarTopCurrent (restrictDistribution T hVΩ)) := by
    apply weakTendsto_scalarTopCurrent
    intro φ
    simpa only [Tf, regularDistribution_apply] using hf.2.2.2 φ
  have hpositive : ∀ j, IsPositive (ddc (scalarTopCurrent (Tf j))) := by
    intro j
    rw [show scalarTopCurrent (Tf j) =
      mulBorel (oneCurrent V) ((V : Set (ComplexModel (m + 1))).indicator (f j)) from
      scalarTopCurrent_regularDistribution_eq_mulBorel (hf.1 j)]
    change IsPositive (ddcMul (oneCurrent V) (f j))
    rw [ddcMul_eq_ddcWedge isPositive_oneCurrent
      (isClosedAny_oneCurrent (n := m + 1)) (hf.1 j).contDiffOn]
    apply isPositive_ddcWedge isPositive_oneCurrent
    intro z hz v
    exact FirstPass.leviForm_nonneg_of_contDiffOn_plurisubharmonicOn
      (hf.1 j).contDiffOn ((hf.2.1 j).plurisubharmonicOn V.isOpen) hz v
  exact ⟨V, hVΩ, hxV, isPositive_of_weakTendsto hpositive (weakTendsto_ddc hweak)⟩

end SGPT.Foundations.Analysis.Pending.ScalarLeviPositiveCurrent

/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Calculus
public import LeanPool.KLS.FunctionalInequalities.Energy.SmoothGradient.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Density of the smooth-gradient realization

Compactly supported `C∞` real functions are dense in finite-exponent `L²` on a
finite-dimensional Borel space. Their gradients are continuous and compactly supported, hence
their squared gradient norms are integrable. This packages Mathlib's approximation theorem into
the exact `PreEnergy.DenseRealization` interface used by sequential relaxation.

Here `C∞` is represented by `ContDiff ℝ ∞`. No analytic (`ContDiff ℝ ⊤`) regularity
is imposed.
-/

@[expose] public section

noncomputable section

open InnerProductSpace MeasureTheory
open scoped ContDiff

namespace FunctionalInequalities.Energy.SmoothGradient

open FunctionalInequalities.Analysis.BakryEmery (continuous_gradient_of_contDiff)

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]

omit [SecondCountableTopology E] [FiniteDimensional ℝ E] in
private theorem gradientSq_integrable_of_hasCompactSupport {μ : Measure E}
    [IsFiniteMeasureOnCompacts μ] {f : E → ℝ}
    (hf_compact : HasCompactSupport f) (hf_smooth : ContDiff ℝ ∞ f) :
    Integrable (fun x ↦ ‖gradient f x‖ ^ 2) μ := by
  have hfderiv_compact : HasCompactSupport (fderiv ℝ f) :=
    hf_compact.fderiv ℝ
  have hgradient_compact : HasCompactSupport (gradient f) := by
    change HasCompactSupport ((toDual ℝ E).symm ∘ fderiv ℝ f)
    exact hfderiv_compact.comp_left (map_zero _)
  have hsq_compact :
      HasCompactSupport ((fun z : E ↦ ‖z‖ ^ 2) ∘ gradient f) :=
    hgradient_compact.comp_left (g := fun z : E ↦ ‖z‖ ^ 2) (by simp)
  change HasCompactSupport (fun x ↦ ‖gradient f x‖ ^ 2) at hsq_compact
  exact ((continuous_gradient_of_contDiff hf_smooth (by simp)).norm.pow 2)
    |>.integrable_of_hasCompactSupport hsq_compact

/-- The concrete smooth-gradient tests have dense realization in real `L²(μ)`. -/
theorem preEnergy_denseRealization (μ : ProbabilityMeasure E) :
    (preEnergy μ).DenseRealization := by
  apply (Lp.dense_hasCompactSupport_contDiff (μ := (μ : Measure E))
    (F := ℝ) (p := (2 : ENNReal)) (by simp)).mono
  rintro f ⟨g, hfg, hg_compact, hg_smooth⟩
  have hg_memLp : MemLp g 2 (μ : Measure E) :=
    (Lp.memLp f).ae_eq hfg
  let test : Test μ :=
    { toFun := g
      contDiff := hg_smooth
      memLp_two := hg_memLp
      gradient_sq_integrable :=
        gradientSq_integrable_of_hasCompactSupport hg_compact hg_smooth }
  refine ⟨test, ?_⟩
  change test.toL2 = f
  rw [Lp.ext_iff]
  exact test.toL2_coeFn.trans hfg.symm

end FunctionalInequalities.Energy.SmoothGradient

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedMain
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedRegular
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedIBPGlobal
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedBochnerMain
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedCutoffs

/-! # Parallel gradient of first eigenfunctions (Workstream A, unconditional) -/

@[expose] public section

open Bundle MeasureTheory
open scoped Manifold ContDiff

namespace CutCur

section Final

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M]

/-- Every smooth `L²` eigenfunction of `-𝓛` with eigenvalue `ρ` under `CD(ρ,∞)` has parallel
gradient (hypotheses of `riemannian_gaussian_splitting`; `hgap` is not needed). -/
theorem manifold_eigenfunction_parallel_gradient {V : M → ℝ} (hV : MSmooth F V)
    {μ : Measure M} [IsProbabilityMeasure μ] (hμ : IsWeightedVolume F μ V) {ρ : ℝ} (hρ : 0 < ρ)
    (hCD : CD F ρ V) (_hgap : mSpectralGap F μ = ρ) {f : M → ℝ}
    (hf : IsMEigenfunction F μ V ρ f) (x : M) :
    CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F f) x = 0 :=
  manifold_eigenfunction_parallel_gradient_of_inputs F hV hμ hρ.le
    (weightedIBP_of_isWeightedVolume F hV hμ) (weightedRegular V hV)
    (weightedBochnerIneq_of_CD F hV hCD) (weightedCutoffs_of_complete F) hf x

end Final

end CutCur

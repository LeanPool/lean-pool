/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.SmoothRegularLevelManifold

/-! # The genuine smooth hypersurface of a nonzero parallel gradient -/

@[expose] public section
open Bundle Set
open scoped Manifold ContDiff Topology

namespace CutoffRigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [BoundarylessManifold I M] [CompleteSpace M] [PreconnectedSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

omit [CompleteSpace M] [IsRiemannianManifold I M] in
/-- The actual nonzero parallel gradient gives a genuinely regular scalar
differential at every point. -/
theorem parallelGradient_differential_ne_zero
    {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
    (hpX : ∀ x, CovariantDerivative.leviCivitaConnection I M X x = 0)
    {f : M → ℝ} (hgrad : ∀ x v, mvfderiv I f x v = inner ℝ (X x) v)
    (x₀ : M) (hne : X x₀ ≠ 0) (x : M) : mvfderiv I f x (X x) ≠ 0 := by
  rw [hgrad, real_inner_self_eq_norm_sq]
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr
    (parallelField_ne_zero_everywhere hX hpX x₀ hne x))

/-- The zero level of the actual source potential, with its actual IFT atlas. -/
@[instance_reducible] noncomputable def parallelGradientLevelChartedSpace
    {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
    (hpX : ∀ x, CovariantDerivative.leviCivitaConnection I M X x = 0)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hgrad : ∀ x v, mvfderiv I f x v = inner ℝ (X x) v)
    (x₀ : M) (hne : X x₀ ≠ 0) :
    ChartedSpace (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))) {y : M // f y = 0} :=
  smoothRegularLevelChartedSpace hf X (parallelGradient_differential_ne_zero hX hpX hgrad x₀ hne)

omit [CompleteSpace M] [IsRiemannianManifold I M] in
/-- The zero level in the paper's flow splitting is a genuine `C²`
codimension-one manifold, constructed from the original assumptions. -/
theorem isManifold_parallelGradientLevel
    {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
    (hpX : ∀ x, CovariantDerivative.leviCivitaConnection I M X x = 0)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hgrad : ∀ x v, mvfderiv I f x v = inner ℝ (X x) v)
    (x₀ : M) (hne : X x₀ ≠ 0) :
    letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))) 2
      {y : M // f y = 0} :=
  isManifold_smoothRegularLevel hf X (parallelGradient_differential_ne_zero hX hpX hgrad x₀ hne)

omit [CompleteSpace M] [IsRiemannianManifold I M] in
/-- The actual level inclusion is `C²`. -/
theorem contMDiff_parallelGradientLevel_inclusion
    {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
    (hpX : ∀ x, CovariantDerivative.leviCivitaConnection I M X x = 0)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hgrad : ∀ x v, mvfderiv I f x v = inner ℝ (X x) v)
    (x₀ : M) (hne : X x₀ ≠ 0) :
    letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))) I 2
      (Subtype.val : {y : M // f y = 0} → M) :=
  contMDiff_smoothRegularLevel_inclusion hf X
    (parallelGradient_differential_ne_zero hX hpX hgrad x₀ hne)

omit [CompleteSpace M] [IsRiemannianManifold I M] in
/-- Its actual tangent map is injective. -/
theorem injective_mfderiv_parallelGradientLevel_inclusion
    {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
    (hpX : ∀ x, CovariantDerivative.leviCivitaConnection I M X x = 0)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hgrad : ∀ x v, mvfderiv I f x v = inner ℝ (X x) v)
    (x₀ : M) (hne : X x₀ ≠ 0) :
    letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
    ∀ x : {y : M // f y = 0}, Function.Injective
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))) I
        (Subtype.val : {y : M // f y = 0} → M) x) :=
  injective_mfderiv_smoothRegularLevel_inclusion hf X
    (parallelGradient_differential_ne_zero hX hpX hgrad x₀ hne)

end CutoffRigidity

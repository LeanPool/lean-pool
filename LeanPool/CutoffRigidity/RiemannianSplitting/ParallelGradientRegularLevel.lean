/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianParallelProductTopology
public import LeanPool.CutoffRigidity.RiemannianSplitting.ParallelFlowIsometry
public import Mathlib.Topology.Connected.Basic

/-! # Genuine regularity and topology of the parallel-gradient zero level
Nonzero parallelism forces the actual gradient to remain nonzero. The actual
potential differential is consequently surjective everywhere. The actual zero
level is closed and complete and inherits connectedness from the proved product
homeomorphism; no submanifold or metric-product conclusion is assumed here.
-/

@[expose] public section
open Bundle Set
open scoped Manifold ContDiff Topology

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] [BoundarylessManifold I M] [CompleteSpace M] [PreconnectedSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

omit [CompleteSpace M] [IsRiemannianManifold I M] in
/-- A nonzero parallel field is nonzero at every point of the connected
manifold, by the proved constancy of its actual Riemannian norm. -/
theorem parallelField_ne_zero_everywhere
    {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
    (hpX : ∀ x, CovariantDerivative.leviCivitaConnection I M X x = 0)
    (x₀ : M) (hne : X x₀ ≠ 0) (x : M) : X x ≠ 0 := by
  intro hx
  have hn := norm_parallel_eq_of_preconnected hX hpX x x₀
  rw [hx, norm_zero] at hn
  exact (norm_ne_zero_iff.mpr hne) hn.symm

omit [CompleteSpace M] [IsRiemannianManifold I M] in
/-- The actual scalar differential of an actual nonzero parallel-gradient
potential is surjective at every point, so every level is regular. -/
theorem surjective_mvfderiv_parallelGradient
    {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
    (hpX : ∀ x, CovariantDerivative.leviCivitaConnection I M X x = 0)
    {f : M → ℝ} (hgrad : ∀ x v, mvfderiv I f x v = inner ℝ (X x) v)
    (x₀ : M) (hne : X x₀ ≠ 0) (x : M) : Function.Surjective (mvfderiv I f x) := by
  have hpos : 0 < ‖X x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr
    (parallelField_ne_zero_everywhere hX hpX x₀ hne x))
  intro a
  refine ⟨(a / ‖X x‖ ^ 2) • X x, ?_⟩
  rw [hgrad, inner_smul_right, real_inner_self_eq_norm_sq]
  have hn : ‖X x‖ ≠ 0 := fun heq => by
    rw [heq, zero_pow (by norm_num)] at hpos
    exact (lt_irrefl 0) hpos
  field_simp [hn]

omit [CompleteSpace M] [IsRiemannianManifold I M] in
/-- Surjectivity also holds for the actual manifold derivative, with its
actual tangent-space codomain. -/
theorem surjective_mfderiv_parallelGradient
    {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
    (hpX : ∀ x, CovariantDerivative.leviCivitaConnection I M X x = 0)
    {f : M → ℝ} (hgrad : ∀ x v, mvfderiv I f x v = inner ℝ (X x) v)
    (x₀ : M) (hne : X x₀ ≠ 0) (x : M) : Function.Surjective (mfderiv I 𝓘(ℝ, ℝ) f x) := by
  intro a
  obtain ⟨v, hv⟩ := surjective_mvfderiv_parallelGradient hX hpX hgrad x₀ hne x
    ((NormedSpace.fromTangentSpace (f x)) a)
  refine ⟨v, (NormedSpace.fromTangentSpace (f x)).injective ?_⟩
  convert! hv using 1

omit [IsContMDiffRiemannianBundle I 1 E fun x : M ↦ TangentSpace I x]
  [FiniteDimensional ℝ E]
  [IsManifold I 2 M]
  [BoundarylessManifold I M]
  [PreconnectedSpace M]
  [RiemannianBundle fun x : M ↦ TangentSpace I x]
  [IsRiemannianManifold I M] in
/-- The actual zero level is a complete subspace for the original ambient
Riemannian distance, with completeness derived from closedness. -/
theorem completeSpace_parallelGradient_zeroLevel {f : M → ℝ}
    (hf : MDifferentiable I 𝓘(ℝ, ℝ) f) : CompleteSpace {x : M // f x = 0} :=
  (isClosed_eq hf.continuous continuous_const).isComplete.completeSpace_coe

omit [PreconnectedSpace M] in
/-- The actual zero level is connected: the proved actual product
homeomorphism gives a genuine continuous surjective projection onto it. -/
theorem connectedSpace_parallelGradient_zeroLevel [ConnectedSpace M]
    {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
    (hpX : ∀ x, CovariantDerivative.leviCivitaConnection I M X x = 0)
    {f : M → ℝ} (hf : MDifferentiable I 𝓘(ℝ, ℝ) f)
    (hgrad : ∀ x v, mvfderiv I f x v = inner ℝ (X x) v)
    (x₀ : M) (hne : X x₀ ≠ 0) : ConnectedSpace {x : M // f x = 0} := by
  let e := unitParallelGradientLevelHomeomorph hX hpX hf hgrad x₀ hne
  let q : M → {x : M // f x = 0} := fun x ↦ (e.symm x).2
  have hq : Continuous q := continuous_snd.comp e.symm.continuous
  have hsurj : Function.Surjective q := by
    intro z
    refine ⟨e (0, z), ?_⟩
    change (e.symm (e (0, z))).2 = z
    rw [e.symm_apply_apply]
  exact hsurj.connectedSpace hq

end CutoffRigidity

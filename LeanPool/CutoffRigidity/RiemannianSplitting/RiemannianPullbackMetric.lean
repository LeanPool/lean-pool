/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.ParallelGradientLevelManifold
public import Mathlib.Analysis.LocallyConvex.Bounded

/-! # Actual Riemannian metric induced by an immersion
The positive-definite pullback metric is constructed from the actual injective
manifold derivative. No induced metric or isometric immersion is an input.
-/

@[expose] public section
open Bundle Set
open scoped Manifold ContDiff Topology

namespace CutoffRigidity

/-- The unit sublevel of the actual pullback quadratic form is bounded.
This supplies the topology compatibility required of an actual Riemannian metric. -/
theorem isVonNBounded_pullback_inner_unit
    {P Q : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]
    (D : P →L[ℝ] Q) (hD : Function.Injective D) :
    Bornology.IsVonNBounded ℝ {v : P | inner ℝ (D v) (D v) < 1} := by
  obtain ⟨K, _, hK⟩ := D.toLinearMap.injective_iff_antilipschitz.mp hD
  apply NormedSpace.isVonNBounded_of_isBounded ℝ
  apply (hK.isBounded_preimage (Metric.isBounded_ball (x := (0 : Q)) (r := 1))).subset
  intro v hv
  simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right]
  change ‖D v‖ < 1
  change inner ℝ (D v) (D v) < 1 at hv
  rw [real_inner_self_eq_norm_sq] at hv
  nlinarith [norm_nonneg (D v)]

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J 2 N]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The actual positive-definite metric induced by an actual immersion.
Temporary model norms are used only to prove topology compatibility; the
resulting Riemannian metric is the actual pullback of the original metric. -/
noncomputable def immersionPullbackRiemannianMetric (f : N → M)
    (hinj : ∀ x, Function.Injective (mfderiv J I f x)) :
    RiemannianMetric (fun x : N ↦ TangentSpace J x) := by
  letI : (x : N) → NormedAddCommGroup (TangentSpace J x) :=
    fun _ ↦ inferInstanceAs (NormedAddCommGroup F)
  letI : (x : N) → NormedSpace ℝ (TangentSpace J x) :=
    fun _ ↦ inferInstanceAs (NormedSpace ℝ F)
  refine
    { inner := fun x ↦ (ContinuousLinearMap.precomp ℝ (mfderiv J I f x)).comp
        ((innerSL ℝ (E := TangentSpace I (f x))).comp (mfderiv J I f x))
      symm := ?_
      pos := ?_
      continuousAt := ?_
      isVonNBounded := ?_ }
  · intro x v w
    change inner ℝ ((mfderiv J I f x) v) ((mfderiv J I f x) w) =
      inner ℝ ((mfderiv J I f x) w) ((mfderiv J I f x) v)
    exact real_inner_comm _ _
  · intro x v hv
    change 0 < inner ℝ ((mfderiv J I f x) v) ((mfderiv J I f x) v)
    apply real_inner_self_pos.mpr
    intro heq
    exact hv ((hinj x) (heq.trans (map_zero _).symm))
  · intro x
    change ContinuousAt (fun v ↦ inner ℝ ((mfderiv J I f x) v)
      ((mfderiv J I f x) v)) 0
    exact ((mfderiv J I f x).continuous.inner (mfderiv J I f x).continuous).continuousAt
  · intro x
    exact isVonNBounded_pullback_inner_unit (mfderiv J I f x) (hinj x)

omit [IsManifold I 2 M] [IsManifold J 2 N] in
/-- The constructed fiber pairing is exactly the original metric applied to
the actual differential of the immersion. -/
theorem immersionPullbackRiemannianMetric_inner (f : N → M)
    (hinj : ∀ x, Function.Injective (mfderiv J I f x)) (x : N)
    (v w : TangentSpace J x) :
    (immersionPullbackRiemannianMetric f hinj).inner x v w =
      inner ℝ ((mfderiv J I f x) v) ((mfderiv J I f x) w) := rfl

/-- The actual bundle metric induced by the immersion. -/
@[instance_reducible] noncomputable def immersionPullbackRiemannianBundle (f : N → M)
    (hinj : ∀ x, Function.Injective (mfderiv J I f x)) :
    RiemannianBundle (fun x : N ↦ TangentSpace J x) :=
  ⟨immersionPullbackRiemannianMetric f hinj⟩

omit [IsManifold I 2 M] [IsManifold J 2 N] in
/-- The actual induced fiber norm makes the actual immersion differential
norm-preserving; this is a conclusion of the constructed metric. -/
theorem norm_mfderiv_immersionPullback (f : N → M)
    (hinj : ∀ x, Function.Injective (mfderiv J I f x)) :
    letI := immersionPullbackRiemannianBundle f hinj
    ∀ (x : N) (v : TangentSpace J x), ‖(mfderiv J I f x) v‖ = ‖v‖ := by
  let := immersionPullbackRiemannianBundle f hinj
  intro x v
  have hi : inner ℝ ((mfderiv J I f x) v) ((mfderiv J I f x) v) = inner ℝ v v := rfl
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hi
  nlinarith [norm_nonneg ((mfderiv J I f x) v), norm_nonneg v]

end CutoffRigidity

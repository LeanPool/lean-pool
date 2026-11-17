/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Graph.Jacobian
public import LeanPool.KLS.FunctionalInequalities.Analysis.Vector.JacobianContinuity

/-! # Graphs of vector-valued maps

The `C¹` infrastructure for the graph of a
**`K`-valued** map, `dim K = m`, which is what a codimension-`m` fibre looks like.  The
codimension-one case lives in `Analysis/Graph/Area.lean`; this module mirrors its second and third
phases — the graph map, its retraction, injectivity, derivative, image measurability and linear
approximation — with a vector-valued slope.

Two things are easier here than in codimension one.  The retraction `graphProj ι = ιᵀ` is already
available and is an **explicit** left inverse of the graph map, which is exactly what the general
area-formula route lacks.  And the linear area formula for the graph model is immediate from
Mathlib's `LinearMap.hausdorffMeasure_image` together with `normDet_graphMapLinear`, so the shear
argument the codimension-one file needed is not repeated.

This module supplies the graph-map infrastructure. The two-sided estimates and area formula
are in `Analysis/Vector/Graph/{Sandwich,Area}.lean`, and the weighted change of variables is in
`Analysis/Vector/Graph/Integral.lean`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace FunctionalInequalities.Analysis

section Defs

variable {H K V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The graph of a `K`-valued map inside `V`: `y ↦ ι y + κ (γ y)`.  Its derivative is
`graphMapLinear ι κ (fderiv ℝ γ y)`. -/
def vectorGraphMap (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V) (γ : H → K) : H → V :=
  fun y => ι y + κ (γ y)

@[simp] theorem vectorGraphMap_apply (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V) (γ : H → K) (y : H) :
    vectorGraphMap ι κ γ y = ι y + κ (γ y) := rfl

end Defs

section Projection

variable {H K V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The retraction kills the second factor. -/
theorem graphProj_apply_of_perp (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) (z : K) :
    graphProj ι (κ z) = 0 := by
  refine ext_inner_right ℝ fun w => ?_
  rw [graphProj, ContinuousLinearMap.adjoint_inner_left, inner_zero_left, real_inner_comm]
  exact hperp w z

/-- **The explicit left inverse.**  The parameter retraction recovers the parameter from a point of
the graph; this is what the general area-formula route has to construct by hand. -/
theorem graphProj_vectorGraphMap (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) (γ : H → K) (y : H) :
    graphProj ι (vectorGraphMap ι κ γ y) = y := by
  rw [vectorGraphMap, map_add, graphProj_ι, graphProj_apply_of_perp ι κ hperp, add_zero]

/-- A graph map is injective, with no hypothesis on the slope. -/
theorem vectorGraphMap_injective (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) (γ : H → K) :
    Function.Injective (vectorGraphMap ι κ γ) := by
  intro y y' h
  have hy := graphProj_vectorGraphMap ι κ hperp γ y
  rw [h, graphProj_vectorGraphMap ι κ hperp γ y'] at hy
  exact hy.symm

end Projection

section Calculus

variable {H K V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem continuous_vectorGraphMap (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V) {γ : H → K}
    (hγ : Continuous γ) : Continuous (vectorGraphMap ι κ γ) :=
  ι.continuous.add (κ.continuous.comp hγ)

/-- **The derivative of a graph map is the linear graph map of the derivative.** -/
theorem hasFDerivAt_vectorGraphMap (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V) {γ : H → K} {y : H}
    (hγ : DifferentiableAt ℝ γ y) :
    HasFDerivAt (vectorGraphMap ι κ γ) (graphMapLinear ι κ (fderiv ℝ γ y)) y := by
  have h1 : HasFDerivAt (fun y : H => ι y) ι.toContinuousLinearMap y :=
    ι.toContinuousLinearMap.hasFDerivAt
  have h2 : HasFDerivAt (fun y : H => κ (γ y))
      (κ.toContinuousLinearMap ∘L fderiv ℝ γ y) y :=
    κ.toContinuousLinearMap.hasFDerivAt.comp y hγ.hasFDerivAt
  exact h1.add h2

/-- **Linear approximation.**  On a ball where the derivative varies by at most `ε`, the graph map
is `ε`-close to the linear graph map of the derivative at the centre.  The estimate is cleaner than
in codimension one: the second factor is an isometry, so its norm disappears. -/
theorem approximatesLinearOn_vectorGraphMap (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    {γ : H → K} (hγ : ContDiff ℝ 1 γ) {y₀ : H} {r : ℝ} {ε : ℝ≥0}
    (hball : ∀ z ∈ Metric.ball y₀ r, ‖fderiv ℝ γ z - fderiv ℝ γ y₀‖ ≤ (ε : ℝ))
    {t : Set H} (hts : t ⊆ Metric.ball y₀ r) :
    ApproximatesLinearOn (vectorGraphMap ι κ γ) (graphMapLinear ι κ (fderiv ℝ γ y₀)) t ε := by
  set A : H →L[ℝ] K := fderiv ℝ γ y₀ with hA
  set h : H → K := fun z => γ z - A z with hh
  have hγd : Differentiable ℝ γ := hγ.differentiable one_ne_zero
  have hhd : ∀ x : H, DifferentiableAt ℝ h x := fun x => (hγd x).sub A.differentiableAt
  have hfd : ∀ x : H, fderiv ℝ h x = fderiv ℝ γ x - A := by
    intro x
    have h3 : HasFDerivAt h (fderiv ℝ γ x - A) x := (hγd x).hasFDerivAt.sub A.hasFDerivAt
    exact h3.fderiv
  have hbound : ∀ x ∈ Metric.ball y₀ r, ‖fderiv ℝ h x‖ ≤ (ε : ℝ) := by
    intro x hx
    rw [hfd x]
    exact hball x hx
  intro y hy y' hy'
  have hsub : vectorGraphMap ι κ γ y - vectorGraphMap ι κ γ y'
      - graphMapLinear ι κ A (y - y') = κ (h y - h y') := by
    simp only [vectorGraphMap_apply, graphMapLinear_apply, hh, map_sub]
    abel
  rw [hsub, κ.norm_map]
  exact (convex_ball y₀ r).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => hhd x) hbound (hts hy') (hts hy)

end Calculus

section Measure

variable {H K V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [MeasurableSpace H] [BorelSpace H] [FiniteDimensional ℝ K] [MeasurableSpace V]
  [BorelSpace V] in
theorem image_vectorGraphMap_eq (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) (γ : H → K) (E : Set H) :
    vectorGraphMap ι κ γ '' E
      = {x : V | vectorGraphMap ι κ γ (graphProj ι x) = x} ∩ (graphProj ι) ⁻¹' E := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, ?_⟩
    · change vectorGraphMap ι κ γ (graphProj ι (vectorGraphMap ι κ γ y)) = vectorGraphMap ι κ γ y
      rw [graphProj_vectorGraphMap ι κ hperp γ y]
    · simp only [Set.mem_preimage, graphProj_vectorGraphMap ι κ hperp γ y]
      exact hy
  · rintro ⟨hx1, hx2⟩
    exact ⟨graphProj ι x, hx2, hx1⟩

omit [FiniteDimensional ℝ K] in
/-- The image of a measurable set under a continuous graph map is measurable: the graph is a closed
condition and the parameter set is pulled back by the retraction. -/
theorem measurableSet_image_vectorGraphMap (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) {γ : H → K} (hγ : Continuous γ)
    {E : Set H} (hE : MeasurableSet E) :
    MeasurableSet (vectorGraphMap ι κ γ '' E) := by
  rw [image_vectorGraphMap_eq ι κ hperp γ E]
  refine MeasurableSet.inter ?_ (hE.preimage (graphProj ι).continuous.measurable)
  exact (isClosed_eq
    ((continuous_vectorGraphMap ι κ hγ).comp (graphProj ι).continuous) continuous_id).measurableSet

/--
**The linear case of vector-valued graph area.**  No shear argument is needed: this is Mathlib's
linear area formula
combined with the volume factor computed in `Analysis/Graph/Jacobian.lean`. -/
theorem hausdorffMeasure_image_graphMapLinear (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) (A : H →L[ℝ] K) (s : Set H) :
    μH[(Module.finrank ℝ H : ℝ)] (graphMapLinear ι κ A '' s) =
      ENNReal.ofReal
          (Real.sqrt
            (LinearMap.det
              (LinearMap.id + LinearMap.adjoint (A : H →ₗ[ℝ] K) ∘ₗ (A : H →ₗ[ℝ] K)))) *
        μH[(Module.finrank ℝ H : ℝ)] s := by
  rw [← normDet_graphMapLinear ι κ hperp A]
  exact LinearMap.hausdorffMeasure_image ((graphMapLinear ι κ A : H →ₗ[ℝ] V)) s

omit [MeasurableSpace V] [BorelSpace V] in
/-- The volume factor along a `C¹` slope is measurable, from `continuous_normDet`. -/
theorem measurable_vectorGraphJacobian (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V) (γ : H → K) :
    Measurable (fun y : H =>
      LinearMap.normDet ((graphMapLinear ι κ (fderiv ℝ γ y) : H →ₗ[ℝ] V))) := by
  have hcont : Continuous (fun A : H →L[ℝ] K =>
      LinearMap.normDet ((graphMapLinear ι κ A : H →ₗ[ℝ] V))) := by
    refine continuous_normDet.comp ?_
    exact continuous_const.add ((ContinuousLinearMap.compL ℝ H K V
      κ.toContinuousLinearMap).continuous)
  exact hcont.measurable.comp (measurable_fderiv ℝ γ)

end Measure

end FunctionalInequalities.Analysis

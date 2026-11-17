/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Graph.Area
public import LeanPool.KLS.FunctionalInequalities.Analysis.Vector.Jacobian

/-! # The graph Jacobian in arbitrary codimension

Step two of the codimension-`m` coarea program, linear layer.

The area formula already proved in `Analysis/Graph/Area.lean` is **codimension one**: its graph
map is `y ↦ ι y + g y • e` for a *real-valued* `g`, with linear model `graphLinear ι e a` and
volume factor `graphJacobian a = √(1 + ‖a‖²)`.  The fibres of a map into an `m`-dimensional target
have codimension `m`, so the program needs the graph of a `K`-valued slope with `dim K = m`.

This module supplies that linear model.  For isometric embeddings `ι`, `κ` with orthogonal ranges
and a slope `A : H →L[ℝ] K`, the graph map is `y ↦ ι y + κ (A y)`, and its volume factor is

`√det (1 + Aᵀ A)`,

a determinant on the **parameter** space `H`.  The codimension-one case is recovered exactly:
`normDet (graphLinear ι e a) = graphJacobian a`, which also identifies the repository's existing
codimension-one Jacobian with Mathlib's general `normDet`, so the two frameworks agree.

Everything below concerns linear maps. Nonlinear vector-graph area and weighted parametrization
are supplied separately by `Analysis/Vector/Graph/{Area,Integral}.lean`. A general
parametrized-image area formula is outside the statements of this linear module.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace FunctionalInequalities.Analysis

variable {H K V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace H] [BorelSpace H] [MeasurableSpace V] [BorelSpace V]

/-- The linear graph map of a slope `A : H →L[ℝ] K`, embedded in `V` along two isometries with
orthogonal ranges: `y ↦ ι y + κ (A y)`.  For `K = ℝ` this is `graphLinear`. -/
def graphMapLinear (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V) (A : H →L[ℝ] K) : H →L[ℝ] V :=
  ι.toContinuousLinearMap + κ.toContinuousLinearMap ∘L A

omit [FiniteDimensional ℝ H] [FiniteDimensional ℝ K] [FiniteDimensional ℝ V]
  [MeasurableSpace H] [BorelSpace H] [MeasurableSpace V] [BorelSpace V] in
@[simp] theorem graphMapLinear_apply (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V) (A : H →L[ℝ] K) (y : H) :
    graphMapLinear ι κ A y = ι y + κ (A y) := rfl

section GraphJacobian

omit [MeasurableSpace H] [BorelSpace H] [MeasurableSpace V] [BorelSpace V]
/-- The Gram operator of a graph map is `1 + Aᵀ A` on the parameter space: the two isometries
contribute the identity and the cross terms vanish because their ranges are orthogonal. -/
theorem adjoint_comp_graphMapLinear (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) (A : H →L[ℝ] K) :
    LinearMap.adjoint ((graphMapLinear ι κ A : H →ₗ[ℝ] V)) ∘ₗ (graphMapLinear ι κ A : H →ₗ[ℝ] V)
      = LinearMap.id + LinearMap.adjoint (A : H →ₗ[ℝ] K) ∘ₗ (A : H →ₗ[ℝ] K) := by
  ext x
  refine ext_inner_right ℝ fun y => ?_
  have hcross : ⟪ι x, κ (A y)⟫ = (0 : ℝ) := hperp x (A y)
  have hcross' : ⟪κ (A x), ι y⟫ = (0 : ℝ) := by
    rw [real_inner_comm]; exact hperp y (A x)
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
  simp only [ContinuousLinearMap.coe_coe, graphMapLinear_apply, LinearMap.add_apply,
    LinearMap.id_apply, inner_add_left, inner_add_right, hcross, hcross',
    ι.inner_map_map, κ.inner_map_map, LinearMap.comp_apply, LinearMap.adjoint_inner_left]
  ring

/-- **The graph volume factor, squared.**  No square root and no positivity argument is needed for
this form. -/
theorem normDet_graphMapLinear_sq (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) (A : H →L[ℝ] K) :
    LinearMap.normDet ((graphMapLinear ι κ A : H →ₗ[ℝ] V)) ^ 2
      = LinearMap.det (LinearMap.id + LinearMap.adjoint (A : H →ₗ[ℝ] K) ∘ₗ (A : H →ₗ[ℝ] K)) := by
  have h := LinearMap.normDet_sq ((graphMapLinear ι κ A : H →ₗ[ℝ] V))
  rw [adjoint_comp_graphMapLinear ι κ hperp A] at h
  exact_mod_cast h

/-- **The graph volume factor in arbitrary codimension**: `√det (1 + Aᵀ A)`, a determinant on the
parameter space `H`, independent of the ambient embedding. -/
theorem normDet_graphMapLinear (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) (A : H →L[ℝ] K) :
    LinearMap.normDet ((graphMapLinear ι κ A : H →ₗ[ℝ] V))
      = Real.sqrt (LinearMap.det
          (LinearMap.id + LinearMap.adjoint (A : H →ₗ[ℝ] K) ∘ₗ (A : H →ₗ[ℝ] K))) := by
  rw [← normDet_graphMapLinear_sq ι κ hperp A,
    Real.sqrt_sq (LinearMap.normDet_nonneg _)]

end GraphJacobian

/-! ### The codimension-one case agrees with the existing area formula -/

omit [FiniteDimensional ℝ V] in
/-- **The repository's codimension-one graph Jacobian is Mathlib's `normDet`.**  Both the already
proved linear codimension-one area formula and Mathlib's linear area formula describe the volume
factor of the same map, so the two factors coincide; the volume factor of a linear map is unique
because some set has positive finite measure.  This identifies the two frameworks, so the proved
codimension-one area formula is the `m = 1` case of the general one. -/
theorem normDet_graphLinear (ι : H →ₗᵢ[ℝ] V) {e : V} (he : ‖e‖ = 1)
    (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ)) (a : H) :
    LinearMap.normDet ((graphLinear ι e a : H →ₗ[ℝ] V)) = graphJacobian a := by
  set s : Set H := Metric.closedBall 0 1 with hs
  have hmpos : μH[(Module.finrank ℝ H : ℝ)] s ≠ 0 := by
    rw [hausdorffMeasure_finrank_eq_smul_volume H, Measure.smul_apply, smul_eq_mul]
    have hball : (0 : ℝ≥0∞) < volume (Metric.closedBall (0 : H) 1) :=
      lt_of_lt_of_le
        (Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.2 one_pos))
        (measure_mono Metric.ball_subset_closedBall)
    refine mul_ne_zero ?_ hball.ne'
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have : 0 < KLS.unitBallVolume (Module.finrank ℝ H) := by
      unfold KLS.unitBallVolume; positivity
    positivity
  have hmtop : μH[(Module.finrank ℝ H : ℝ)] s ≠ ⊤ := by
    rw [hausdorffMeasure_finrank_eq_smul_volume H, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne
  have hrepo := hausdorffMeasure_image_graphLinear ι he hperp a s
  have hmath := LinearMap.hausdorffMeasure_image ((graphLinear ι e a : H →ₗ[ℝ] V)) s
  rw [show (⇑(graphLinear ι e a : H →ₗ[ℝ] V)) = ⇑(graphLinear ι e a) from rfl, hrepo] at hmath
  have hofReal := (ENNReal.mul_left_inj hmpos hmtop).mp hmath.symm
  exact (ENNReal.ofReal_eq_ofReal_iff (LinearMap.normDet_nonneg _)
    (graphJacobian_nonneg a)).mp hofReal

end FunctionalInequalities.Analysis

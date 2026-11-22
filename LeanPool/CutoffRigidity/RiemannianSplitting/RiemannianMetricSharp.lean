/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianDifferentialOperators
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianChartMetric

/-! # Genuine inverse metric in a fixed coordinate space

Positive definiteness proves invertibility of the actual metric map into the
dual. Smoothness of inversion then supplies the coordinate musical inverse.
This is the analytic ingredient needed to derive gradient regularity from
regularity of the metric and scalar function.
-/
public section
namespace CutoffRigidity
open Bundle
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A positive-definite actual continuous bilinear form identifies the space
with its genuine continuous dual. No inverse metric is supplied as data. -/
theorem metricMap_isInvertible
    (G : E →L[ℝ] StrongDual ℝ E)
    (hG : ∀ v : E, v ≠ 0 → 0 < G v v) : G.IsInvertible := by
  have hinj : Function.Injective G := by
    intro v w hvw
    have hz : G (v-w)=0 := by rw [map_sub,hvw,sub_self]
    have hv : v-w=0 := by
      by_contra hn
      have hp := hG (v-w) hn
      rw [hz,zero_apply] at hp
      exact (lt_irrefl 0) hp
    exact sub_eq_zero.mp hv
  have hdim : Module.finrank ℝ E=Module.finrank ℝ (StrongDual ℝ E) :=
    (InnerProductSpace.toDual ℝ E).toLinearEquiv.finrank_eq
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  let L := (LinearEquiv.ofBijective G.toLinearMap ⟨hinj,hsurj⟩).toContinuousLinearEquiv
  refine ⟨L,?_⟩
  rfl

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A C¹ positive metric has a genuinely C¹ inverse near the point; this
uses inversion of continuous linear maps and actual positivity. -/
theorem contDiffAt_metricSharp
    {G : F → E →L[ℝ] StrongDual ℝ E} {x : F} {n : ℕ∞ω}
    (hG : ContDiffAt ℝ n G x)
    (hpos : ∀ v : E, v ≠ 0 → 0 < G x v v) :
    ContDiffAt ℝ n (fun y => (G y).inverse) x := by
  exact (metricMap_isInvertible (G x) hpos).contDiffAt_map_inverse.comp x hG

open scoped Manifold
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M => TangentSpace I x)]

omit [IsContMDiffRiemannianBundle I 1 E fun x : M ↦ TangentSpace I x]
  [BoundarylessManifold I M] in
/-- The actual metric of the manifold, expressed in its actual tangent chart,
has an invertible dual map at the chart center. -/
theorem chartMetric_isInvertible (x : M) :
    (chartMetric (I := I) x (extChartAt I x x)).IsInvertible := by
  apply metricMap_isInvertible
  intro v hv
  rw [chartMetric_center_apply,chartFrame_self]
  exact real_inner_self_pos.mpr hv

/-- Actual C¹ inverse metric coefficients, with their regularity and
invertibility both derived from the genuine Riemannian structure. -/
theorem contDiffAt_chartMetric_inverse (x : M) :
    ContDiffAt ℝ 1 (fun z => (chartMetric (I := I) x z).inverse) (extChartAt I x x) := by
  exact (chartMetric_isInvertible (I := I) x).contDiffAt_map_inverse.comp _
    (contDiffAt_chartMetric (I := I) x)

end CutoffRigidity

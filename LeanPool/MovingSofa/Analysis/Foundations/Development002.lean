/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.ForMathlib.BoundedVariation.Foundations.Development001
public import LeanPool.MovingSofa.ForMathlib.Convex.Foundations.Development001
public import LeanPool.MovingSofa.ForMathlib.Geometry.Foundations.Development001
public import LeanPool.MovingSofa.ForMathlib.MeasureTheory.Foundations.Development001

public import LeanPool.MovingSofa.ForMathlib.MeasureTheory.Foundations.Development002

public import LeanPool.MovingSofa.ForMathlib.Order.Foundations.Development001
public import LeanPool.MovingSofa.ForMathlib.Topology.Foundations.Development001
public import LeanPool.MovingSofa.Geometry.Foundations.Development001



public import Mathlib.Analysis.BoundedVariation
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.VectorMeasure.IntegrationByParts
public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.Maps.Proper.Basic
/-!
# Moving sofa: related mathematical developments

* `Analysis.BoundedVariation`.
* `Analysis.MeasureProducts`.
* `Analysis.Stieltjes.Integral`.
* `Analysis.Stieltjes.AbsoluteContinuity`.
* `Analysis.Stieltjes.Calculus`.
* `Analysis.Stieltjes.DensityIntegration`.
* `Analysis.Stieltjes.Linearity`.
* `Analysis.Stieltjes.InnerProduct`.
* `Analysis.Stieltjes.Smooth`.
* `Analysis.Stieltjes.Frame`.
* `Analysis.Stieltjes.Transport`.
* `Analysis.Stieltjes.Continuous`.
* `Analysis.Stieltjes.Affine`.
* `Analysis.Stieltjes.RiemannSums`.
* `Analysis.Stieltjes.Shift`.
* `Analysis.SurfaceMeasure.Basic`.
* `Analysis.SurfaceMeasure.ExteriorNormal`.
* `Analysis.SurfaceMeasure.GraphDefinitions`.
* `Analysis.SurfaceMeasure.Regularity`.
* `Analysis.SurfaceMeasure.Segment`.
* `Analysis.SurfaceMeasure.SegmentFaces`.
* `Analysis.SurfaceMeasure.SegmentGraph`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Bounded Variation
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- Bounded variation for a real function on its actual closed-interval domain. -/
def IsIntervalBoundedVariation (a b : ℝ) (f : Set.Icc a b → ℝ) : Prop :=
  BoundedVariationOn f Set.univ

private theorem intervalBV_add {a b : ℝ} {f g : Set.Icc a b → ℝ}
    (hf : IsIntervalBoundedVariation a b f) (hg : IsIntervalBoundedVariation a b g) :
    IsIntervalBoundedVariation a b (f + g) := by
  refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩) ?_
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) :=
      Finset.sum_le_sum fun _ _ ↦ edist_add_add_le _ _ _ _
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (eVariationOn.sum_le hu hus) (eVariationOn.sum_le hu hus)

/-- The submodule of continuous planar interval functions with coordinatewise finite variation. -/
def continuousBVSubmodule (a b : ℝ) : Submodule ℝ (Set.Icc a b → Point) where
  carrier := {f | Continuous f ∧
    ∀ i : Fin 2, IsIntervalBoundedVariation a b (fun t ↦ f t i)}
  zero_mem' := by
    refine ⟨continuous_const, fun i ↦ ?_⟩
    simp [IsIntervalBoundedVariation, BoundedVariationOn, eVariationOn]
  add_mem' := by
    intro f g hf hg
    exact ⟨hf.1.add hg.1, fun i ↦ intervalBV_add (hf.2 i) (hg.2 i)⟩
  smul_mem' := by
    intro c f hf
    refine ⟨continuous_const.smul hf.1, fun i ↦ ?_⟩
    exact (ContinuousLinearMap.lsmul ℝ ℝ c).lipschitzWith.comp_boundedVariationOn (hf.2 i)

/-- The real vector space of continuous planar BV paths on a closed interval. -/
abbrev ContinuousBVPaths (a b : ℝ) : Type := continuousBVSubmodule a b

/-- A continuous planar BV path has finite vector variation on its whole domain. -/
theorem ContinuousBVPaths.boundedVariationOn {a b : ℝ} (x : ContinuousBVPaths a b) :
    BoundedVariationOn x.val Set.univ := by
  have hdist (p q : Point) : edist p q ≤ edist (p 0) (q 0) + edist (p 1) (q 1) := by
    have hnorm (z : Point) : ‖z‖ ≤ |z 0| + |z 1| := by
      nlinarith [Point.norm_sq_eq z, sq_abs (z 0), sq_abs (z 1), abs_nonneg (z 0),
        abs_nonneg (z 1), norm_nonneg z, mul_nonneg (abs_nonneg (z 0)) (abs_nonneg (z 1))]
    simp only [edist_dist, dist_eq_norm, Real.norm_eq_abs]
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (by simpa using hnorm (p - q))
  refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨x.property.2 0, x.property.2 1⟩) ?_
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        (edist (x.val (u (i + 1)) 0) (x.val (u i) 0) +
          edist (x.val (u (i + 1)) 1) (x.val (u i) 1)) :=
      Finset.sum_le_sum fun _ _ ↦ hdist _ _
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (eVariationOn.sum_le (f := fun t ↦ x.val t 0) (n := n) hu hus)
      (eVariationOn.sum_le (f := fun t ↦ x.val t 1) (n := n) hu hus)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Measure Products
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- Multiply a signed measure by a real density using the continuous multiplication map. -/
def functionMeasureMul {X : Type*} [MeasurableSpace X]
    (f : X → ℝ) (μ : SignedMeasure X) : SignedMeasure X :=
  μ.withDensity f (ContinuousLinearMap.mul ℝ ℝ)

/-- Multiply one signed measure by each of two scalar densities. -/
def pairFunctionMeasureMul {X : Type*} [MeasurableSpace X]
    (f : (X → ℝ) × (X → ℝ)) (μ : SignedMeasure X) :
    SignedMeasure X × SignedMeasure X :=
  (functionMeasureMul f.1 μ, functionMeasureMul f.2 μ)

/-- Multiply both components of a signed-measure pair by one scalar density. -/
def functionPairMeasureMul {X : Type*} [MeasurableSpace X]
    (f : X → ℝ) (μ : SignedMeasure X × SignedMeasure X) :
    SignedMeasure X × SignedMeasure X :=
  (functionMeasureMul f μ.1, functionMeasureMul f μ.2)

/-- The sum of the coordinatewise density products of a function pair and measure pair. -/
def functionMeasureDot {X : Type*} [MeasurableSpace X]
    (f : (X → ℝ) × (X → ℝ)) (μ : SignedMeasure X × SignedMeasure X) :
    SignedMeasure X :=
  functionMeasureMul f.1 μ.1 + functionMeasureMul f.2 μ.2

/-- The oriented planar determinant `p₀ q₁ - p₁ q₀`. -/
def planeCrossProduct (p q : Point) : ℝ :=
  p 0 * q 1 - p 1 * q 0

/-- The signed-measure determinant of a function pair and a measure pair. -/
def functionMeasureCross {X : Type*} [MeasurableSpace X]
    (f : (X → ℝ) × (X → ℝ)) (μ : SignedMeasure X × SignedMeasure X) :
    SignedMeasure X :=
  functionMeasureMul f.1 μ.2 - functionMeasureMul f.2 μ.1

/-- Bundle the scalar, vector and dot-product operations on signed measures. -/
def functionMeasureProducts (X : Type*) [MeasurableSpace X] :
    ((X → ℝ) → SignedMeasure X → SignedMeasure X) ×
    (((X → ℝ) × (X → ℝ)) → SignedMeasure X → SignedMeasure X × SignedMeasure X) ×
    ((X → ℝ) → (SignedMeasure X × SignedMeasure X) → SignedMeasure X × SignedMeasure X) ×
    (((X → ℝ) × (X → ℝ)) → (SignedMeasure X × SignedMeasure X) → SignedMeasure X) :=
  (functionMeasureMul, pairFunctionMeasureMul, functionPairMeasureMul, functionMeasureDot)

/-- Bundle the planar determinant and its signed-measure counterpart. -/
def planeCrossProducts (X : Type*) [MeasurableSpace X] :
    (Point → Point → ℝ) ×
    (((X → ℝ) × (X → ℝ)) → (SignedMeasure X × SignedMeasure X) → SignedMeasure X) :=
  (planeCrossProduct, functionMeasureCross)

/-! ### The oriented planar determinant

Basic algebra of `planeCrossProduct`, the transitivity of the order it induces on the closed
first quadrant, and the two shapes of level set used when a planar region is fanned into
triangles over a base point.
-/

@[simp] theorem planeCrossProduct_self (p : Point) : planeCrossProduct p p = 0 := by
  simp only [planeCrossProduct]
  ring

@[simp] theorem planeCrossProduct_zero_left (p : Point) : planeCrossProduct 0 p = 0 := by
  simp [planeCrossProduct]

@[simp] theorem planeCrossProduct_zero_right (p : Point) : planeCrossProduct p 0 = 0 := by
  simp [planeCrossProduct]

/-- The oriented determinant is antisymmetric. -/
theorem planeCrossProduct_swap (p q : Point) :
    planeCrossProduct p q = -planeCrossProduct q p := by
  simp only [planeCrossProduct]
  ring

/-- The oriented determinant is the inner product against the quarter turn of its first
argument. -/
theorem planeCrossProduct_eq_inner (p q : Point) :
    planeCrossProduct p q = inner ℝ q !₂[-p 1, p 0] := by
  simp [planeCrossProduct, PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- In the closed first quadrant the oriented determinant order is transitive: if `v` is
nonzero and both `u × v` and `v × w` are nonnegative, then so is `u × w`. -/
theorem planeCrossProduct_nonneg_trans {u v w : Point} (hv : v ≠ 0)
    (hu0 : 0 ≤ u 0) (hu1 : 0 ≤ u 1) (hv0 : 0 ≤ v 0) (hv1 : 0 ≤ v 1)
    (hw0 : 0 ≤ w 0) (hw1 : 0 ≤ w 1)
    (huv : 0 ≤ planeCrossProduct u v) (hvw : 0 ≤ planeCrossProduct v w) :
    0 ≤ planeCrossProduct u w := by
  have hvpos : 0 < v 0 ^ 2 + v 1 ^ 2 := by
    rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ v 0 ^ 2 + v 1 ^ 2) with h | h
    · refine absurd ?_ hv
      have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
      have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
      ext i
      fin_cases i
      · simpa using h0
      · simpa using h1
    · exact h
  have hid : planeCrossProduct u w * (v 0 ^ 2 + v 1 ^ 2)
      = (w 0 * v 0 + w 1 * v 1) * planeCrossProduct u v
        + planeCrossProduct v w * (u 0 * v 0 + u 1 * v 1) := by
    simp only [planeCrossProduct]
    ring
  nlinarith [mul_nonneg (add_nonneg (mul_nonneg hw0 hv0) (mul_nonneg hw1 hv1)) huv,
    mul_nonneg hvw (add_nonneg (mul_nonneg hu0 hv0) (mul_nonneg hu1 hv1))]

/-- The closed angular sector between two rays through a base point is convex. -/
theorem convex_setOf_planeCrossProduct_fan (u v L : Point) :
    Convex ℝ {x : Point | 0 ≤ planeCrossProduct u (x - L) ∧
      0 ≤ planeCrossProduct (x - L) v} := by
  intro x hx y hy a b ha hb hab
  obtain rfl : b = 1 - a := by linarith
  simp only [Set.mem_ofPred_eq, planeCrossProduct, PiLp.sub_apply, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul] at hx hy ⊢
  constructor
  · nlinarith [mul_nonneg ha hx.1, mul_nonneg hb hy.1]
  · nlinarith [mul_nonneg ha hx.2, mul_nonneg hb hy.2]

/-- The line through a base point in a nonzero direction carries no planar area. -/
theorem volume_setOf_planeCrossProduct_sub_eq_zero {w : Point} (hw : w ≠ 0) (L : Point) :
    volume {x : Point | planeCrossProduct w (x - L) = 0} = 0 := by
  have hrot : (!₂[-w 1, w 0] : Point) ≠ 0 := by
    intro h
    refine hw ?_
    have h0 : w 0 = 0 := by simpa using congrArg (fun v : Point ↦ v 1) h
    have h1 : w 1 = 0 := by simpa using congrArg (fun v : Point ↦ v 0) h
    ext i
    fin_cases i
    · simpa using h0
    · simpa using h1
  have hset : {x : Point | planeCrossProduct w (x - L) = 0}
      = {x : Point | inner ℝ x (!₂[-w 1, w 0] : Point) =
          inner ℝ L (!₂[-w 1, w 0] : Point)} := by
    ext x
    simp only [Set.mem_ofPred_eq, planeCrossProduct_eq_inner, inner_sub_left, sub_eq_zero]
  rw [hset]
  exact volume.addHaar_setOf_real_inner_eq hrot _

/-- The planar cross product is the frame determinant at every angle. -/
theorem planeCrossProduct_eq_inner_frame (a b : Point) (t : ℝ) :
    planeCrossProduct a b =
      inner ℝ a (normalVector (t : Real.Angle)) * inner ℝ b (tangentVector (t : Real.Angle)) -
        inner ℝ a (tangentVector (t : Real.Angle)) *
          inner ℝ b (normalVector (t : Real.Angle)) := by
  simp only [planeCrossProduct, normalVector, tangentVector, frame, PiLp.inner_apply,
    Fin.sum_univ_two, Real.Angle.cos_coe, Real.Angle.sin_coe, RCLike.inner_apply,
    conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (a.ofLp 1 * b.ofLp 0 - a.ofLp 0 * b.ofLp 1) * (Real.sin_sq_add_cos_sq t)

/-- The oriented determinant of a point against the frame tangent is its normal coordinate. -/
theorem planeCrossProduct_tangentVector (p : Point) (t : Real.Angle) :
    planeCrossProduct p (tangentVector t) = inner ℝ p (normalVector t) := by
  simp [planeCrossProduct, normalVector, tangentVector, frame, PiLp.inner_apply,
    Fin.sum_univ_two]
  ring

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Stieltjes / Integral
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- A right-continuous real BV function on its actual closed-interval domain. -/
structure RightContinuousIntervalBV (a b : ℝ) where
  /-- The real-valued function on the closed parameter interval. -/
  toFun : Set.Icc a b → ℝ
  boundedVariation : IsIntervalBoundedVariation a b toFun
  right_continuous : ∀ t, ContinuousWithinAt toFun (Set.Ici t) t

/-- A right-continuous interval-BV function is determined by its underlying function. -/
theorem RightContinuousIntervalBV.toFun_injective {a b : ℝ} :
    Function.Injective (@RightContinuousIntervalBV.toFun a b) := by
  rintro ⟨f, hf, hfr⟩ ⟨g, hg, hgr⟩ hfg
  cases hfg
  rfl

/-- A right-continuous interval-BV function on a nonempty interval is bounded, by its value at
the left endpoint plus the total variation. -/
theorem RightContinuousIntervalBV.exists_norm_bound {a b : ℝ} (hab : a ≤ b)
    (f : RightContinuousIntervalBV a b) : ∃ C : ℝ, ∀ t, ‖f.toFun t‖ ≤ C := by
  refine ⟨‖f.toFun ⟨a, le_rfl, hab⟩‖ + (eVariationOn f.toFun Set.univ).toReal, fun t ↦ ?_⟩
  calc ‖f.toFun t‖
      ≤ ‖f.toFun ⟨a, le_rfl, hab⟩‖ + ‖f.toFun t - f.toFun ⟨a, le_rfl, hab⟩‖ :=
        norm_le_norm_add_norm_sub' _ _
    _ ≤ _ := by
        gcongr
        simpa [dist_eq_norm_sub] using
          f.boundedVariation.dist_le (Set.mem_univ t) (Set.mem_univ ⟨a, le_rfl, hab⟩)

/-- The finite signed Stieltjes measure on the interval, with zero initial atom. -/
def intervalStieltjesMeasure {a b : ℝ} (f : RightContinuousIntervalBV a b) :
    SignedMeasure (Set.Icc a b) :=
  f.boundedVariation.vectorMeasure

/-- The Stieltjes integral, used for bounded measurable integrands and Borel subsets. -/
def intervalStieltjesIntegral {a b : ℝ} (f : RightContinuousIntervalBV a b)
    (g : Set.Icc a b → ℝ) (X : Set (Set.Icc a b)) : ℝ :=
  ∫ᵛ t in X, g t ∂[ContinuousLinearMap.mul ℝ ℝ; intervalStieltjesMeasure f]

/-- Over the whole parameter interval, the interval Stieltjes integral is the unrestricted
vector-measure integral. -/
theorem intervalStieltjesIntegral_univ {a b : ℝ} (f : RightContinuousIntervalBV a b)
    (g : Set.Icc a b → ℝ) :
    intervalStieltjesIntegral f g Set.univ =
      VectorMeasure.integral (intervalStieltjesMeasure f) g (ContinuousLinearMap.mul ℝ ℝ) := by
  simp only [intervalStieltjesIntegral, VectorMeasure.restrict_univ]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Stieltjes / Absolute Continuity
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace MovingSofa

/-- Extend an interval function to the real line by zero outside its domain. -/
def stieltjesScalarExtension {a b : ℝ} (f : RightContinuousIntervalBV a b)
    (t : ℝ) : ℝ := by
  classical
  exact if h : t ∈ Set.Icc a b then f.toFun ⟨t, h⟩ else 0

/-- An integrable density represents the interval Stieltjes measure on measurable sets. -/
def HasIntervalStieltjesDensity {a b : ℝ} (f : RightContinuousIntervalBV a b)
    (r : ℝ → ℝ) : Prop :=
  Integrable r (volume.restrict (Set.Icc a b)) ∧
    ∀ E : Set ℝ, MeasurableSet E →
      intervalStieltjesMeasure f {t | (t : ℝ) ∈ E} =
        ∫ t in E, r t ∂volume.restrict (Set.Icc a b)

theorem intervalStieltjesMeasure_Ioc {a b : ℝ}
    (f : RightContinuousIntervalBV a b) (c d : Set.Icc a b) (hcd : c ≤ d) :
    intervalStieltjesMeasure f (Set.Ioc c d) = f.toFun d - f.toFun c := by
  rw [intervalStieltjesMeasure, f.boundedVariation.vectorMeasure_Ioc hcd]
  rw [f.right_continuous d |>.rightLim_eq, f.right_continuous c |>.rightLim_eq]

private theorem stieltjesScalarExtension_eq_add_integral {a b : ℝ} (hab : a ≤ b)
    (f : RightContinuousIntervalBV a b) (r : ℝ → ℝ)
    (hr : HasIntervalStieltjesDensity f r) (t : Set.Icc a b) :
    stieltjesScalarExtension f (t : ℝ) =
      f.toFun ⟨a, le_rfl, hab⟩ + ∫ x in a..(t : ℝ), r x := by
  have hinc := hr.2 (Ioc a (t : ℝ)) measurableSet_Ioc
  have hset : {x : Icc a b | (x : ℝ) ∈ Ioc a (t : ℝ)} =
      Ioc (⟨a, le_rfl, hab⟩ : Icc a b) t := rfl
  rw [hset, intervalStieltjesMeasure_Ioc f _ _ t.property.1] at hinc
  have hmeasure :
      (volume.restrict (Set.Icc a b)).restrict (Set.Ioc a (t : ℝ)) =
        volume.restrict (Set.Ioc a (t : ℝ)) := by
    exact Measure.restrict_restrict_of_subset
      (fun x hx ↦ ⟨hx.1.le, hx.2.trans t.property.2⟩)
  have hrestrict :
      (∫ x in Set.Ioc a (t : ℝ), r x ∂volume.restrict (Set.Icc a b)) =
        ∫ x in Set.Ioc a (t : ℝ), r x := by
    rw [hmeasure]
  rw [stieltjesScalarExtension]
  simp only [dite_eq_left t.2]
  change f.toFun t = _
  rw [intervalIntegral.integral_of_le t.2.1]
  have hinc' := hinc.trans hrestrict
  linarith

private theorem absolutelyContinuousOnInterval_of_stieltjesDensity {a b : ℝ} (hab : a ≤ b)
    (f : RightContinuousIntervalBV a b) (r : ℝ → ℝ)
    (hr : HasIntervalStieltjesDensity f r) :
    AbsolutelyContinuousOnInterval (stieltjesScalarExtension f) a b := by
  have hri : IntervalIntegrable r volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hr.1
  have hp := hri.absolutelyContinuousOnInterval_intervalIntegral
    (c := a) (by simp [hab])
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ f.toFun ⟨a, le_rfl, hab⟩) a b :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  have hs := hc.add hp
  apply hs.congr
  intro x hx
  have hx' : x ∈ Set.Icc a b := by
    simpa [Set.uIcc_of_le hab] using hx
  have hprim := stieltjesScalarExtension_eq_add_integral hab f r hr ⟨x, hx'⟩
  simpa [stieltjesScalarExtension, hx'] using hprim.symm

private theorem ae_hasDerivAt_of_stieltjesDensity {a b : ℝ} (hab : a ≤ b)
    (f : RightContinuousIntervalBV a b) (r : ℝ → ℝ)
    (hr : HasIntervalStieltjesDensity f r) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      HasDerivAt (stieltjesScalarExtension f) (r t) t := by
  have hri : IntervalIntegrable r volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hr.1
  have hder := IntervalIntegrable.ae_hasDerivAt_integral hri
  refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
  filter_upwards [hder] with x hx hxo
  have hxu : x ∈ Set.uIcc a b := by
    simpa [Set.uIcc_of_le hab] using ⟨hxo.1.le, hxo.2.le⟩
  have hd := hx hxu a (by simp [hab])
  have hd' := hd.const_add (f.toFun ⟨a, le_rfl, hab⟩)
  apply hd'.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hxo] with y hyo
  have hycc : y ∈ Set.Icc a b := ⟨hyo.1.le, hyo.2.le⟩
  have hprim := stieltjesScalarExtension_eq_add_integral hab f r hr ⟨y, hycc⟩
  simpa [stieltjesScalarExtension, hycc] using hprim

private theorem intervalStieltjes_hasDensity_deriv {a b : ℝ} (hab : a ≤ b)
    (f : RightContinuousIntervalBV a b)
    (hf : AbsolutelyContinuousOnInterval (stieltjesScalarExtension f) a b) :
    HasIntervalStieltjesDensity f (deriv (stieltjesScalarExtension f)) := by
  let g := stieltjesScalarExtension f
  have hr : IntegrableOn (deriv g) (Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hf.intervalIntegrable_deriv
  have hsub : Continuous f.toFun := by
    have h := (continuousOn_iff_continuous_domRestrict).mp
      (show ContinuousOn g (Icc a b) by simpa only [uIcc_of_le hab] using hf.continuousOn)
    convert h using 1
    funext x
    simp [g, stieltjesScalarExtension, x.property]
  have hri : Integrable (fun x : Icc a b ↦ deriv g x)
      (volume.comap (Subtype.val : Icc a b → ℝ)) :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Icc).mp hr
  have hmeasure : intervalStieltjesMeasure f =
      (volume.comap (Subtype.val : Icc a b → ℝ)).withDensityᵥ
        (fun x : Icc a b ↦ deriv g x) := by
    apply f.boundedVariation.vectorMeasure_eq_withDensity_of_integral_Icc hsub hri
    intro c d hcd
    have hinc := (hf.mono (show uIcc (c : ℝ) (d : ℝ) ⊆ uIcc a b by
      rw [uIcc_of_le (show (c : ℝ) ≤ d from hcd), uIcc_of_le hab]
      exact Icc_subset_Icc c.property.1 d.property.2)).integral_deriv_eq_sub
    have hset : Icc c d = {x : Icc a b | (x : ℝ) ∈ Icc (c : ℝ) (d : ℝ)} := rfl
    rw [hset, integral_subtype_preimage measurableSet_Icc measurableSet_Icc]
    rw [Measure.restrict_restrict_of_subset (Icc_subset_Icc c.property.1 d.property.2),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hcd, hinc]
    simp [stieltjesScalarExtension, c.property, d.property]
  refine ⟨hr, ?_⟩
  intro E hE
  have hpre : MeasurableSet {t : Icc a b | (t : ℝ) ∈ E} :=
    hE.preimage measurable_subtype_coe
  rw [hmeasure, withDensityᵥ_apply hri hpre,
    integral_subtype_preimage measurableSet_Icc hE]

theorem intervalStieltjes_absoluteContinuity (a b : ℝ) (hab : a ≤ b)
    (f : RightContinuousIntervalBV a b) :
    (AbsolutelyContinuousOnInterval (stieltjesScalarExtension f) a b ↔
      ∃ r : ℝ → ℝ, HasIntervalStieltjesDensity f r) ∧
    (∀ r : ℝ → ℝ, HasIntervalStieltjesDensity f r →
      ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        HasDerivAt (stieltjesScalarExtension f) (r t) t) := by
  refine ⟨⟨?_, ?_⟩, fun r hr ↦ ae_hasDerivAt_of_stieltjesDensity hab f r hr⟩
  · intro hf
    exact ⟨deriv (stieltjesScalarExtension f), intervalStieltjes_hasDensity_deriv hab f hf⟩
  · rintro ⟨r, hr⟩
    exact absolutelyContinuousOnInterval_of_stieltjesDensity hab f r hr

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Stieltjes / Calculus
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace MovingSofa

theorem intervalStieltjes_integration_by_parts (a b : ℝ) (hab : a ≤ b)
    (f g : RightContinuousIntervalBV a b) :
    ∃ left : Set.Icc a b → ℝ,
      (∀ t : Set.Icc a b, a < (t : ℝ) →
        Tendsto f.toFun (nhdsWithin t (Set.Iio t)) (𝓝 (left t))) ∧
      intervalStieltjesIntegral f g.toFun {t | a < (t : ℝ)} +
        intervalStieltjesIntegral g left {t | a < (t : ℝ)} =
      f.toFun ⟨b, hab, le_rfl⟩ * g.toFun ⟨b, hab, le_rfl⟩ -
        f.toFun ⟨a, le_rfl, hab⟩ * g.toFun ⟨a, le_rfl, hab⟩ := by
  let a' : Set.Icc a b := ⟨a, le_rfl, hab⟩
  let b' : Set.Icc a b := ⟨b, hab, le_rfl⟩
  refine ⟨Function.leftLim f.toFun, fun t _ ↦ f.boundedVariation.tendsto_leftLim t, ?_⟩
  have hfa (t : Set.Icc a b) : Function.rightLim f.toFun t = f.toFun t :=
    (f.right_continuous t).rightLim_eq
  have hga (t : Set.Icc a b) : Function.rightLim g.toFun t = g.toFun t :=
    (g.right_continuous t).rightLim_eq
  have hparts := BoundedVariationOn.setIntegral_Ioc_leftLim_vectorMeasure_eq_sub
    (B := ContinuousLinearMap.mul ℝ ℝ) f.boundedVariation g.boundedVariation (show a' ≤ b' by
      exact hab)
  have hset : {t : Set.Icc a b | a < (t : ℝ)} = Set.Ioc a' b' := by
    ext t
    constructor
    · intro ht
      exact ⟨ht, t.property.2⟩
    · exact fun ht ↦ ht.1
  have hmulflip : (ContinuousLinearMap.mul ℝ ℝ).flip = ContinuousLinearMap.mul ℝ ℝ := by
    ext
    simp
  rw [hmulflip] at hparts
  rw [hset]
  unfold intervalStieltjesIntegral intervalStieltjesMeasure
  change (∫ᵛ t in Set.Ioc a' b', g.toFun t
      ∂[ContinuousLinearMap.mul ℝ ℝ; f.boundedVariation.vectorMeasure]) +
    (∫ᵛ t in Set.Ioc a' b', Function.leftLim f.toFun t
      ∂[ContinuousLinearMap.mul ℝ ℝ; g.boundedVariation.vectorMeasure]) = _
  rw [hparts]
  simp only [hfa, hga]
  change _ + (f.toFun b' * g.toFun b' - f.toFun a' * g.toFun a' - _) = _
  dsimp [a', b']
  ring

/-- Stieltjes integration by parts on the open interval `(a, b)`: no endpoint atom is included
at `b`, and none is introduced at `a`. The left limit in the first integrand accounts for
simultaneous jumps. -/
theorem intervalStieltjes_integration_by_parts_Ioo (a b : ℝ) (hab : a < b)
    (f g : RightContinuousIntervalBV a b) :
    intervalStieltjesIntegral g (Function.leftLim f.toFun)
        {t | a < (t : ℝ) ∧ (t : ℝ) < b} +
      intervalStieltjesIntegral f g.toFun {t | a < (t : ℝ) ∧ (t : ℝ) < b} =
      Function.leftLim f.toFun ⟨b, hab.le, le_rfl⟩ *
          Function.leftLim g.toFun ⟨b, hab.le, le_rfl⟩ -
        f.toFun ⟨a, le_rfl, hab.le⟩ * g.toFun ⟨a, le_rfl, hab.le⟩ := by
  have hfa (t : Set.Icc a b) : Function.rightLim f.toFun t = f.toFun t :=
    (f.right_continuous t).rightLim_eq
  have hga (t : Set.Icc a b) : Function.rightLim g.toFun t = g.toFun t :=
    (g.right_continuous t).rightLim_eq
  have hparts := BoundedVariationOn.setIntegral_Ioo_leftLim_vectorMeasure_eq_sub
    (B := ContinuousLinearMap.mul ℝ ℝ) f.boundedVariation g.boundedVariation
    (show (⟨a, le_rfl, hab.le⟩ : Set.Icc a b) < ⟨b, hab.le, le_rfl⟩ from hab)
  have hset : {t : Set.Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b} =
      Set.Ioo (⟨a, le_rfl, hab.le⟩ : Set.Icc a b) ⟨b, hab.le, le_rfl⟩ := by
    ext t
    exact ⟨fun ht ↦ ⟨ht.1, ht.2⟩, fun ht ↦ ⟨ht.1, ht.2⟩⟩
  have hmulflip : (ContinuousLinearMap.mul ℝ ℝ).flip = ContinuousLinearMap.mul ℝ ℝ := by
    ext
    simp
  rw [hmulflip] at hparts
  rw [hset]
  unfold intervalStieltjesIntegral intervalStieltjesMeasure
  rw [hparts]
  simp only [hfa, hga, ContinuousLinearMap.mul_apply']
  ring

theorem intervalStieltjes_product (a b : ℝ)
    (f g : RightContinuousIntervalBV a b)
    (hcont : Continuous f.toFun ∨ Continuous g.toFun) :
    ∃ h : RightContinuousIntervalBV a b,
      (∀ t, h.toFun t = f.toFun t * g.toFun t) ∧
      ∀ E : Set (Set.Icc a b), MeasurableSet E →
        intervalStieltjesMeasure h E =
          intervalStieltjesIntegral f g.toFun E + intervalStieltjesIntegral g f.toFun E := by
  let h : RightContinuousIntervalBV a b :=
    ⟨fun t ↦ f.toFun t * g.toFun t,
      f.boundedVariation.bilinear_comp g.boundedVariation (ContinuousLinearMap.mul ℝ ℝ),
      fun t ↦ (f.right_continuous t).mul (g.right_continuous t)⟩
  refine ⟨h, fun _ ↦ rfl, fun E _ ↦ ?_⟩
  have hflip : (ContinuousLinearMap.mul ℝ ℝ).flip = ContinuousLinearMap.mul ℝ ℝ := by
    ext
    simp
  have hfr : Function.rightLim f.toFun = f.toFun :=
    funext fun t ↦ (f.right_continuous t).rightLim_eq
  have hgr : Function.rightLim g.toFun = g.toFun :=
    funext fun t ↦ (g.right_continuous t).rightLim_eq
  rcases hcont with hf | hg
  · have hfl : Function.leftLim f.toFun = f.toFun :=
      funext fun t ↦ hf.continuousAt.continuousWithinAt.leftLim_eq
    have hp := f.boundedVariation.setIntegral_leftLim_vectorMeasure_eq_sub
      (B := ContinuousLinearMap.mul ℝ ℝ) g.boundedVariation (s := E)
    rw [hflip, hfl, hgr] at hp
    change _ = _ + _
    unfold intervalStieltjesIntegral intervalStieltjesMeasure
    change (f.boundedVariation.bilinear_comp g.boundedVariation
      (ContinuousLinearMap.mul ℝ ℝ)).vectorMeasure E = _
    linarith
  · have hgl : Function.leftLim g.toFun = g.toFun :=
      funext fun t ↦ hg.continuousAt.continuousWithinAt.leftLim_eq
    have hp := f.boundedVariation.setIntegral_rightLim_vectorMeasure_eq_sub
      (B := ContinuousLinearMap.mul ℝ ℝ) g.boundedVariation (s := E)
    rw [hflip, hfr, hgl] at hp
    unfold intervalStieltjesIntegral intervalStieltjesMeasure
    change (f.boundedVariation.bilinear_comp g.boundedVariation
      (ContinuousLinearMap.mul ℝ ℝ)).vectorMeasure E = _
    linarith

/-- The integrated Stieltjes product rule: a bounded measurable weight distributes over the
Lebesgue–Stieltjes measure of a product one factor of which is continuous. -/
theorem intervalStieltjesIntegral_product_of_bounded {a b : ℝ} (hab : a ≤ b)
    (f g h : RightContinuousIntervalBV a b) (hgc : Continuous g.toFun)
    (hh : ∀ t, h.toFun t = f.toFun t * g.toFun t)
    (φ : Set.Icc a b → ℝ) (hφ : Measurable φ) (C : ℝ) (hφb : ∀ t, ‖φ t‖ ≤ C)
    (E : Set (Set.Icc a b)) (hE : MeasurableSet E) :
    intervalStieltjesIntegral h φ E =
      intervalStieltjesIntegral f (fun t ↦ φ t * g.toFun t) E +
        intervalStieltjesIntegral g (fun t ↦ φ t * f.toFun t) E := by
  obtain ⟨h', hh', hh'm⟩ := intervalStieltjes_product a b f g (Or.inr hgc)
  have hheq : h = h' :=
    RightContinuousIntervalBV.toFun_injective (funext fun t ↦ (hh t).trans (hh' t).symm)
  obtain ⟨Cf, hCf⟩ := f.exists_norm_bound hab
  obtain ⟨Cg, hCg⟩ := g.exists_norm_bound hab
  have hfm : Measurable f.toFun := f.boundedVariation.measurable
  have hgm : Measurable g.toFun := g.boundedVariation.measurable
  -- both Stieltjes measures are absolutely continuous over the sum of their total variations
  set ρ : Measure (Set.Icc a b) := (intervalStieltjesMeasure f).totalVariation +
    (intervalStieltjesMeasure g).totalVariation with hρ
  have _ : IsFiniteMeasure ρ := by rw [hρ]; infer_instance
  have hac : ∀ μ : SignedMeasure (Set.Icc a b), μ.totalVariation ≤ ρ →
      μ ≪ᵥ ρ.toENNRealVectorMeasure := fun μ hle ↦ by
    rw [SignedMeasure.absolutelyContinuous_ennreal_iff,
      VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure]
    exact Measure.absolutelyContinuous_of_le hle
  have hacf := hac (intervalStieltjesMeasure f) (by rw [hρ]; exact Measure.le_add_right le_rfl)
  have hacg := hac (intervalStieltjesMeasure g) (by rw [hρ]; exact Measure.le_add_left le_rfl)
  set rf : Set.Icc a b → ℝ := (intervalStieltjesMeasure f).rnDeriv ρ with hrf
  set rg : Set.Icc a b → ℝ := (intervalStieltjesMeasure g).rnDeriv ρ with hrg
  have hrfi : Integrable rf ρ := SignedMeasure.integrable_rnDeriv _ ρ
  have hrgi : Integrable rg ρ := SignedMeasure.integrable_rnDeriv _ ρ
  have hμf : ρ.withDensityᵥ rf = intervalStieltjesMeasure f :=
    SignedMeasure.withDensityᵥ_rnDeriv_eq _ ρ hacf
  have hμg : ρ.withDensityᵥ rg = intervalStieltjesMeasure g :=
    SignedMeasure.withDensityᵥ_rnDeriv_eq _ ρ hacg
  have hgrf : Integrable (fun x ↦ g.toFun x * rf x) ρ :=
    hrfi.bdd_mul hgm.aestronglyMeasurable (Filter.Eventually.of_forall hCg)
  have hfrg : Integrable (fun x ↦ f.toFun x * rg x) ρ :=
    hrgi.bdd_mul hfm.aestronglyMeasurable (Filter.Eventually.of_forall hCf)
  have hsumi : Integrable (fun x ↦ g.toFun x * rf x + f.toFun x * rg x) ρ := hgrf.add hfrg
  have hφg : Measurable fun t ↦ φ t * g.toFun t := hφ.mul hgm
  have hφf : Measurable fun t ↦ φ t * f.toFun t := hφ.mul hfm
  -- the product measure is the density of the two-term Radon–Nikodym sum
  have hsum : intervalStieltjesMeasure h =
      ρ.withDensityᵥ (fun x ↦ g.toFun x * rf x + f.toFun x * rg x) := by
    rw [hheq]
    ext S hS
    rw [withDensityᵥ_apply hsumi hS, hh'm S hS]
    have h1 : intervalStieltjesIntegral f g.toFun S = ∫ x in S, g.toFun x * rf x ∂ρ := by
      rw [intervalStieltjesIntegral, ← hμf,
        VectorMeasure.setIntegral_withDensity_mul_of_bounded hrfi
          hgm.aestronglyMeasurable Cg hCg S hS]
    have h2 : intervalStieltjesIntegral g f.toFun S = ∫ x in S, f.toFun x * rg x ∂ρ := by
      rw [intervalStieltjesIntegral, ← hμg,
        VectorMeasure.setIntegral_withDensity_mul_of_bounded hrgi
          hfm.aestronglyMeasurable Cf hCf S hS]
    rw [h1, h2, integral_add hgrf.integrableOn hfrg.integrableOn]
  have hb1 : ∀ x, ‖φ x * g.toFun x‖ ≤ C * Cg := fun x ↦ by
    rw [norm_mul]
    exact mul_le_mul (hφb x) (hCg x) (norm_nonneg _) ((norm_nonneg _).trans (hφb x))
  have hb2 : ∀ x, ‖φ x * f.toFun x‖ ≤ C * Cf := fun x ↦ by
    rw [norm_mul]
    exact mul_le_mul (hφb x) (hCf x) (norm_nonneg _) ((norm_nonneg _).trans (hφb x))
  have hi1 : Integrable (fun x ↦ φ x * g.toFun x * rf x) ρ :=
    hrfi.bdd_mul hφg.aestronglyMeasurable (Filter.Eventually.of_forall hb1)
  have hi2 : Integrable (fun x ↦ φ x * f.toFun x * rg x) ρ :=
    hrgi.bdd_mul hφf.aestronglyMeasurable (Filter.Eventually.of_forall hb2)
  rw [show intervalStieltjesIntegral h φ E =
      ∫ x in E, φ x * (g.toFun x * rf x + f.toFun x * rg x) ∂ρ by
    rw [intervalStieltjesIntegral, hsum,
      VectorMeasure.setIntegral_withDensity_mul_of_bounded hsumi
        hφ.aestronglyMeasurable C hφb E hE],
    show intervalStieltjesIntegral f (fun t ↦ φ t * g.toFun t) E =
      ∫ x in E, φ x * g.toFun x * rf x ∂ρ by
    rw [intervalStieltjesIntegral, ← hμf,
      VectorMeasure.setIntegral_withDensity_mul_of_bounded hrfi
        hφg.aestronglyMeasurable (C * Cg) hb1 E hE],
    show intervalStieltjesIntegral g (fun t ↦ φ t * f.toFun t) E =
      ∫ x in E, φ x * f.toFun x * rg x ∂ρ by
    rw [intervalStieltjesIntegral, ← hμg,
      VectorMeasure.setIntegral_withDensity_mul_of_bounded hrgi
        hφf.aestronglyMeasurable (C * Cf) hb2 E hE],
    ← integral_add hi1.integrableOn hi2.integrableOn]
  exact setIntegral_congr_fun hE fun x _ ↦ by ring

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Stieltjes / Density Integration
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MovingSofa

/-- A continuous integrand against an interval Stieltjes measure with an ordinary density is
the corresponding weighted Lebesgue integral on the interval subtype. -/
theorem intervalStieltjesIntegral_eq_integral_mul_of_density
    {a b : ℝ} (F : RightContinuousIntervalBV a b) {r : ℝ → ℝ}
    (hr : HasIntervalStieltjesDensity F r) {q : Icc a b → ℝ} (hq : Continuous q)
    (E : Set (Icc a b)) (hE : MeasurableSet E) :
    intervalStieltjesIntegral F q E =
      ∫ t in E, q t * r t ∂volume.comap (Subtype.val : Icc a b → ℝ) := by
  have hri : Integrable (fun t : Icc a b ↦ r t)
      (volume.comap (Subtype.val : Icc a b → ℝ)) :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Icc).mp hr.1
  have hmeasure : intervalStieltjesMeasure F =
      (volume.comap (Subtype.val : Icc a b → ℝ)).withDensityᵥ
        (fun t : Icc a b ↦ r t) := by
    ext S hS
    have himage : MeasurableSet ((Subtype.val : Icc a b → ℝ) '' S) :=
      (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image' hS
    have hpre : {t : Icc a b | (t : ℝ) ∈ (Subtype.val : Icc a b → ℝ) '' S} = S :=
      Set.preimage_image_eq S Subtype.val_injective
    rw [withDensityᵥ_apply hri hS, ← hpre,
      integral_subtype_preimage measurableSet_Icc himage]
    exact hr.2 _ himage
  let _ : IsFiniteMeasure (volume.comap (Subtype.val : Icc a b → ℝ)) :=
    ⟨by
      rw [comap_subtype_coe_apply measurableSet_Icc]
      simp only [image_univ, Subtype.range_val]
      exact measure_Icc_lt_top⟩
  unfold intervalStieltjesIntegral
  rw [hmeasure]
  exact VectorMeasure.setIntegral_withDensity_mul hri hq E hE

/-- The density formula also applies to a bounded-variation integrand on a nonempty compact
interval. -/
theorem intervalStieltjesIntegral_eq_integral_mul_of_density_bv
    {a b : ℝ} (hab : a ≤ b) (F : RightContinuousIntervalBV a b) {r : ℝ → ℝ}
    (hr : HasIntervalStieltjesDensity F r) {q : Icc a b → ℝ}
    (hq : BoundedVariationOn q univ) (E : Set (Icc a b)) (hE : MeasurableSet E) :
    intervalStieltjesIntegral F q E =
      ∫ t in E, q t * r t ∂volume.comap (Subtype.val : Icc a b → ℝ) := by
  have hri : Integrable (fun t : Icc a b ↦ r t)
      (volume.comap (Subtype.val : Icc a b → ℝ)) :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Icc).mp hr.1
  have hmeasure : intervalStieltjesMeasure F =
      (volume.comap (Subtype.val : Icc a b → ℝ)).withDensityᵥ
        (fun t : Icc a b ↦ r t) := by
    ext S hS
    have himage : MeasurableSet ((Subtype.val : Icc a b → ℝ) '' S) :=
      (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image' hS
    have hpre : {t : Icc a b | (t : ℝ) ∈ (Subtype.val : Icc a b → ℝ) '' S} = S :=
      Set.preimage_image_eq S Subtype.val_injective
    rw [withDensityᵥ_apply hri hS, ← hpre,
      integral_subtype_preimage measurableSet_Icc himage]
    exact hr.2 _ himage
  let _ : IsFiniteMeasure (volume.comap (Subtype.val : Icc a b → ℝ)) :=
    ⟨by
      rw [comap_subtype_coe_apply measurableSet_Icc]
      simp only [image_univ, Subtype.range_val]
      exact measure_Icc_lt_top⟩
  let t₀ : Icc a b := ⟨a, le_rfl, hab⟩
  let C := ‖q t₀‖ + (eVariationOn q univ).toReal
  have hq_bound : ∀ t, ‖q t‖ ≤ C := by
    intro t
    calc
      ‖q t‖ ≤ ‖q t₀‖ + ‖q t - q t₀‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ ‖q t₀‖ + (eVariationOn q univ).toReal := by
        gcongr
        simpa [dist_eq_norm_sub] using hq.dist_le (mem_univ t) (mem_univ t₀)
      _ = C := rfl
  unfold intervalStieltjesIntegral
  rw [hmeasure]
  exact VectorMeasure.setIntegral_withDensity_mul_of_bounded hri
    hq.stronglyMeasurable.aestronglyMeasurable C hq_bound E hE

/-- A real function agreeing with a BV representative is integrable on its interval. -/
theorem RightContinuousIntervalBV.integrableOn_Icc_of_eq
    {a b : ℝ} (f : RightContinuousIntervalBV a b) (q : ℝ → ℝ)
    (hq : ∀ t : Icc a b, q t = f.toFun t) : IntegrableOn q (Icc a b) := by
  have hfinite : IsFiniteMeasure (volume.comap (Subtype.val : Icc a b → ℝ)) :=
    ⟨by
      rw [comap_subtype_coe_apply measurableSet_Icc]
      simp only [image_univ, Subtype.range_val]
      exact measure_Icc_lt_top⟩
  let _ := hfinite
  rw [IntegrableOn, ← map_comap_subtype_coe measurableSet_Icc,
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).integrable_map_iff
      (μ := volume.comap (Subtype.val : Icc a b → ℝ))]
  convert f.boundedVariation.integrable
      (μ := volume.comap (Subtype.val : Icc a b → ℝ)) using 1
  funext t
  exact hq t

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Stieltjes / Linearity
-/

@[expose] public section

noncomputable section

open scoped Topology

namespace MovingSofa

theorem intervalStieltjes_linear_combination (a b : ℝ)
    (f g : RightContinuousIntervalBV a b) (r s : ℝ) :
    ∃ h : RightContinuousIntervalBV a b,
      (∀ t, h.toFun t = r * f.toFun t + s * g.toFun t) ∧
      intervalStieltjesMeasure h =
        r • intervalStieltjesMeasure f + s • intervalStieltjesMeasure g := by
  let hfun : Set.Icc a b → ℝ := fun t ↦ r * f.toFun t + s * g.toFun t
  have hBV : IsIntervalBoundedVariation a b hfun := by
    have hfr := (ContinuousLinearMap.lsmul ℝ ℝ r).lipschitzWith.comp_boundedVariationOn
      f.boundedVariation
    have hgr := (ContinuousLinearMap.lsmul ℝ ℝ s).lipschitzWith.comp_boundedVariationOn
      g.boundedVariation
    exact BoundedVariationOn.add hfr hgr
  change BoundedVariationOn hfun Set.univ at hBV
  let h : RightContinuousIntervalBV a b :=
    { toFun := hfun
      boundedVariation := hBV
      right_continuous := fun t ↦ by
        exact (f.right_continuous t).const_mul r |>.add ((g.right_continuous t).const_mul s) }
  refine ⟨h, ?_, ?_⟩
  · intro t
    rfl
  · apply MeasureTheory.VectorMeasure.ext_of_Icc
    intro x y hxy
    have hbv : BoundedVariationOn h.toFun Set.univ := h.boundedVariation
    have hleft (z : Set.Icc a b) :
        Function.leftLim h.toFun z =
          r * Function.leftLim f.toFun z + s * Function.leftLim g.toFun z := by
      rcases Filter.eq_or_neBot (𝓝[<] z) with hz | hz
      · simp [leftLim_eq_of_eq_bot _ hz, h, hfun]
      · exact tendsto_nhds_unique (hbv.tendsto_leftLim z)
          ((f.boundedVariation.tendsto_leftLim z).const_smul r |>.add
            ((g.boundedVariation.tendsto_leftLim z).const_smul s))
    have hfxy : Function.rightLim f.toFun y = f.toFun y :=
      (f.right_continuous y).rightLim_eq
    have gfxy : Function.rightLim g.toFun y = g.toFun y :=
      (g.right_continuous y).rightLim_eq
    have hxy' : Function.rightLim h.toFun y = h.toFun y :=
      (h.right_continuous y).rightLim_eq
    simp only [smul_apply, add_apply]
    rw [show intervalStieltjesMeasure h (Set.Icc x y) =
        Function.rightLim h.toFun y - Function.leftLim h.toFun x by
          exact BoundedVariationOn.vectorMeasure_Icc hbv hxy]
    rw [show intervalStieltjesMeasure f (Set.Icc x y) =
        Function.rightLim f.toFun y - Function.leftLim f.toFun x by
          exact BoundedVariationOn.vectorMeasure_Icc f.boundedVariation hxy]
    rw [show intervalStieltjesMeasure g (Set.Icc x y) =
        Function.rightLim g.toFun y - Function.leftLim g.toFun x by
          exact BoundedVariationOn.vectorMeasure_Icc g.boundedVariation hxy]
    rw [hleft x]
    rw [hxy', hfxy, gfxy]
    simp [h, hfun, sub_eq_add_neg]
    ring

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Stieltjes / Inner Product
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MovingSofa

/-- Componentwise product rule for the Euclidean pairing of two planar interval-BV functions,
when the second function is continuous. -/
theorem intervalStieltjes_inner_fin_two {a b : ℝ}
    (f g : Fin 2 → RightContinuousIntervalBV a b)
    (hg : ∀ i, Continuous (g i).toFun) :
    ∃ h : RightContinuousIntervalBV a b,
      (∀ t, h.toFun t = ∑ i, (f i).toFun t * (g i).toFun t) ∧
      ∀ E : Set (Icc a b), MeasurableSet E →
        intervalStieltjesMeasure h E =
          ∑ i, (intervalStieltjesIntegral (f i) (g i).toFun E +
            intervalStieltjesIntegral (g i) (f i).toFun E) := by
  obtain ⟨p0, hp0, hp0m⟩ := intervalStieltjes_product a b (f 0) (g 0) (Or.inr (hg 0))
  obtain ⟨p1, hp1, hp1m⟩ := intervalStieltjes_product a b (f 1) (g 1) (Or.inr (hg 1))
  obtain ⟨h, hh, hhm⟩ := intervalStieltjes_linear_combination a b p0 p1 1 1
  refine ⟨h, ?_, ?_⟩
  · intro t
    rw [hh, hp0, hp1, Fin.sum_univ_two]
    ring
  · intro E hE
    rw [show intervalStieltjesMeasure h E =
        intervalStieltjesMeasure p0 E + intervalStieltjesMeasure p1 E by
      rw [hhm]
      simp]
    rw [hp0m E hE, hp1m E hE, Fin.sum_univ_two]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Stieltjes / Smooth
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MovingSofa

/-- A continuously differentiable real function restricted to a compact interval, together with
its Stieltjes density. -/
theorem exists_intervalBV_of_hasDerivAt {a b : ℝ} (hab : a ≤ b)
    (φ φ' : ℝ → ℝ) (hderiv : ∀ t, HasDerivAt φ (φ' t) t) (hφ' : Continuous φ') :
    ∃ F : RightContinuousIntervalBV a b,
      (∀ t, F.toFun t = φ t) ∧ HasIntervalStieltjesDensity F φ' := by
  have hdiff : Differentiable ℝ φ := fun t ↦ (hderiv t).differentiableAt
  have hcontDiff : ContDiff ℝ 1 φ := by
    rw [contDiff_one_iff_deriv]
    refine ⟨hdiff, ?_⟩
    convert hφ' using 1
    funext t
    exact (hderiv t).deriv
  have hBVreal : BoundedVariationOn φ (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      (hcontDiff.contDiffOn.absolutelyContinuousOnInterval (a := a) (b := b)).boundedVariationOn
  let ι : Icc a b → ℝ := (↑)
  have hBV : BoundedVariationOn (φ ∘ ι) Set.univ :=
    ne_top_of_le_ne_top hBVreal
      (eVariationOn.comp_le_of_monotoneOn φ ι
        (fun _ _ _ _ h ↦ h) (fun t _ ↦ t.property))
  let F : RightContinuousIntervalBV a b :=
    { toFun := φ ∘ ι
      boundedVariation := hBV
      right_continuous := fun t ↦
        (hderiv (t : ℝ)).continuousAt.comp_continuousWithinAt
          continuous_subtype_val.continuousWithinAt }
  have hφ'int : Integrable φ' (volume.restrict (Icc a b)) :=
    hφ'.continuousOn.integrableOn_compact isCompact_Icc
  have hsubtype : Integrable (fun t : Icc a b ↦ φ' t)
      (volume.comap (Subtype.val : Icc a b → ℝ)) :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Icc).mp hφ'int
  have hmeasure : intervalStieltjesMeasure F =
      (volume.comap (Subtype.val : Icc a b → ℝ)).withDensityᵥ
        (fun t : Icc a b ↦ φ' t) := by
    apply F.boundedVariation.vectorMeasure_eq_withDensity_of_integral_Icc
    · exact (continuous_iff_continuousAt.2 fun t ↦ (hderiv t).continuousAt).comp
        continuous_subtype_val
    · exact hsubtype
    · intro c d hcd
      have hftc : ∫ x in (c : ℝ)..(d : ℝ), φ' x = φ d - φ c :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x _ ↦ hderiv x) (hφ'.intervalIntegrable (c : ℝ) (d : ℝ))
      have hset : Icc c d = {x : Icc a b | (x : ℝ) ∈ Icc (c : ℝ) (d : ℝ)} := rfl
      rw [hset, integral_subtype_preimage measurableSet_Icc measurableSet_Icc,
        Measure.restrict_restrict_of_subset
          (Icc_subset_Icc c.property.1 d.property.2)]
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hcd, hftc]
      simp [F, ι]
  refine ⟨F, fun _ ↦ rfl, hφ'int, ?_⟩
  intro E hE
  have hpre : MeasurableSet {t : Icc a b | (t : ℝ) ∈ E} :=
    hE.preimage measurable_subtype_coe
  rw [hmeasure, withDensityᵥ_apply hsubtype hpre,
    integral_subtype_preimage measurableSet_Icc hE]

/-- A right-continuous interval bounded-variation function that agrees on its interval with an
absolutely continuous function differentiable on the open interval has that derivative as its
Stieltjes density. Unlike `exists_intervalBV_of_hasDerivAt` this identifies the density of a
*given* bounded-variation function, and asks for differentiability only in the interior. -/
theorem hasIntervalStieltjesDensity_of_hasDerivAt {a b : ℝ} (hab : a ≤ b)
    (F : RightContinuousIntervalBV a b) (φ φ' : ℝ → ℝ)
    (hF : ∀ t : Icc a b, F.toFun t = φ t)
    (hac : AbsolutelyContinuousOnInterval φ a b)
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt φ (φ' t) t)
    (hint : IntegrableOn φ' (Icc a b)) :
    HasIntervalStieltjesDensity F φ' := by
  have hext : ∀ t ∈ Icc a b, stieltjesScalarExtension F t = φ t := by
    intro t ht
    rw [stieltjesScalarExtension, dite_eq_left ht]
    exact hF ⟨t, ht⟩
  have hac' : AbsolutelyContinuousOnInterval (stieltjesScalarExtension F) a b :=
    hac.congr fun t ht ↦ (hext t (by simpa only [uIcc_of_le hab] using ht)).symm
  obtain ⟨ρ, hρ⟩ := (intervalStieltjes_absoluteContinuity a b hab F).1.1 hac'
  have hIoo : ρ =ᵐ[volume.restrict (Ioo a b)] φ' := by
    filter_upwards [(intervalStieltjes_absoluteContinuity a b hab F).2 ρ hρ,
      ae_restrict_mem measurableSet_Ioo] with t ht htmem
    refine ht.unique ((hderiv t htmem).congr_of_eventuallyEq ?_)
    filter_upwards [isOpen_Ioo.mem_nhds htmem] with u hu
    exact hext u (Ioo_subset_Icc_self hu)
  have hIcc : ρ =ᵐ[volume.restrict (Icc a b)] φ' := by
    rwa [Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume))] at hIoo
  refine ⟨hint, fun E hE ↦ ?_⟩
  rw [hρ.2 E hE]
  exact integral_congr_ae (hIcc.filter_mono (ae_mono Measure.restrict_le_self))

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Stieltjes / Frame
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MovingSofa

/-- A coordinate of the rotating normal frame is a continuous interval-BV function whose
Stieltjes density is the corresponding tangent coordinate. -/
theorem exists_normalVector_coordinate_intervalBV {a b : ℝ} (hab : a ≤ b) (i : Fin 2) :
    ∃ F : RightContinuousIntervalBV a b,
      (∀ t, F.toFun t = normalVector (((t : ℝ) : Real.Angle)) i) ∧
      HasIntervalStieltjesDensity F
        (fun t ↦ tangentVector ((t : ℝ) : Real.Angle) i) := by
  refine exists_intervalBV_of_hasDerivAt hab
    (fun t : ℝ ↦ normalVector (t : Real.Angle) i)
    (fun t : ℝ ↦ tangentVector (t : Real.Angle) i) ?_ ?_
  · intro t
    fin_cases i
    · change HasDerivAt Real.cos (-Real.sin t) t
      exact Real.hasDerivAt_cos t
    · change HasDerivAt Real.sin (Real.cos t) t
      exact Real.hasDerivAt_sin t
  · fin_cases i
    · change Continuous (fun t : ℝ ↦ -Real.sin t)
      fun_prop
    · change Continuous Real.cos
      fun_prop

/-- A coordinate of the rotating tangent frame is a continuous interval-BV function whose
Stieltjes density is the negative normal coordinate. -/
theorem exists_tangentVector_coordinate_intervalBV {a b : ℝ} (hab : a ≤ b) (i : Fin 2) :
    ∃ F : RightContinuousIntervalBV a b,
      (∀ t, F.toFun t = tangentVector (((t : ℝ) : Real.Angle)) i) ∧
      HasIntervalStieltjesDensity F
        (fun t ↦ -normalVector ((t : ℝ) : Real.Angle) i) := by
  refine exists_intervalBV_of_hasDerivAt hab
    (fun t : ℝ ↦ tangentVector (t : Real.Angle) i)
    (fun t : ℝ ↦ -normalVector (t : Real.Angle) i) ?_ ?_
  · intro t
    fin_cases i
    · change HasDerivAt (fun t : ℝ ↦ -Real.sin t) (-Real.cos t) t
      convert (Real.hasDerivAt_sin t).neg using 1
    · change HasDerivAt Real.cos (-Real.sin t) t
      exact Real.hasDerivAt_cos t
  · fin_cases i
    · change Continuous (fun t : ℝ ↦ -Real.cos t)
      fun_prop
    · change Continuous (fun t : ℝ ↦ -Real.sin t)
      fun_prop

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Stieltjes / Transport
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Function

namespace MovingSofa

/-- Continuous monotone surjective reparametrization preserves the Stieltjes integral. -/
theorem intervalStieltjesIntegral_comp_monotone_surjective
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (F : RightContinuousIntervalBV a b)
    (hFc : Continuous F.toFun) (g : Set.Icc a b → ℝ) (hgc : Continuous g)
    (φ : Set.Icc c d → Set.Icc a b) (hφc : Continuous φ) (hφ : Monotone φ)
    (hφs : Function.Surjective φ) :
    intervalStieltjesIntegral F g Set.univ =
      intervalStieltjesIntegral
        { toFun := F.toFun ∘ φ
          boundedVariation := BoundedVariationOn.comp_monotone_surjective_Icc
            hab F.boundedVariation hφ hφs
          right_continuous := fun _ ↦
            (hFc.comp hφc).continuousAt.continuousWithinAt }
        (g ∘ φ) Set.univ := by
  let Fφ : RightContinuousIntervalBV c d :=
    { toFun := F.toFun ∘ φ
      boundedVariation := BoundedVariationOn.comp_monotone_surjective_Icc
        hab F.boundedVariation hφ hφs
      right_continuous := fun _ ↦
        (hFc.comp hφc).continuousAt.continuousWithinAt }
  have hmap : (intervalStieltjesMeasure Fφ).map φ = intervalStieltjesMeasure F :=
    BoundedVariationOn.vectorMeasure_map_comp_monotone_surjective_Icc
      hab hcd F.boundedVariation hFc hφc hφ hφs
  let _ : IsFiniteMeasure (intervalStieltjesMeasure Fφ).variation := by
    change IsFiniteMeasure Fφ.boundedVariation.vectorMeasure.variation
    exact BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure Fφ.boundedVariation
  have hgint : (intervalStieltjesMeasure Fφ).Integrable (g ∘ φ) :=
    (hgc.comp hφc).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))
  have hgm : AEStronglyMeasurable g
      ((intervalStieltjesMeasure Fφ).variation.map φ) :=
    hgc.aestronglyMeasurable
  unfold intervalStieltjesIntegral
  simp only [VectorMeasure.restrict_univ]
  rw [← hmap, MeasureTheory.VectorMeasure.integral_map hφc.measurable hgm hgint]
  rfl

/-- Restricting a continuous Stieltjes integral agrees with integration on the subinterval. -/
theorem intervalStieltjesIntegral_Ioc_eq_inclusion
    {a b : ℝ} (F : RightContinuousIntervalBV a b) (hFc : Continuous F.toFun)
    (g : Set.Icc a b → ℝ) (hgc : Continuous g) (l u : Set.Icc a b) (hlu : l ≤ u) :
    let ι : Set.Icc (l : ℝ) u → Set.Icc a b := fun x ↦
      ⟨x, le_trans l.property.1 x.property.1, le_trans x.property.2 u.property.2⟩
    let hfr : BoundedVariationOn (F.toFun ∘ ι) Set.univ :=
      ne_top_of_le_ne_top F.boundedVariation (eVariationOn.comp_le_of_monotoneOn F.toFun ι
        (fun _ _ _ _ h ↦ h) (mapsTo_univ ι _))
    intervalStieltjesIntegral F g (Ioc l u) =
      intervalStieltjesIntegral
        { toFun := F.toFun ∘ ι
          boundedVariation := hfr
          right_continuous := fun _ ↦
            (hFc.comp (continuous_subtype_val.subtype_mk _)).continuousAt.continuousWithinAt }
        (g ∘ ι) Set.univ := by
  dsimp only
  let ι : Set.Icc (l : ℝ) u → Set.Icc a b := fun x ↦
    ⟨x, le_trans l.property.1 x.property.1, le_trans x.property.2 u.property.2⟩
  let hfr : BoundedVariationOn (F.toFun ∘ ι) Set.univ :=
    ne_top_of_le_ne_top F.boundedVariation (eVariationOn.comp_le_of_monotoneOn F.toFun ι
      (fun _ _ _ _ h ↦ h) (mapsTo_univ ι _))
  let Fr : RightContinuousIntervalBV (l : ℝ) u :=
    { toFun := F.toFun ∘ ι
      boundedVariation := hfr
      right_continuous := fun _ ↦
        (hFc.comp (continuous_subtype_val.subtype_mk _)).continuousAt.continuousWithinAt }
  have hmap : (intervalStieltjesMeasure Fr).map ι =
      (intervalStieltjesMeasure F).restrict (Ioc l u) :=
    BoundedVariationOn.vectorMeasure_map_Icc_inclusion F.boundedVariation hFc l u hlu
  let _ : IsFiniteMeasure (intervalStieltjesMeasure Fr).variation := by
    change IsFiniteMeasure hfr.vectorMeasure.variation
    exact BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure hfr
  have hgint : (intervalStieltjesMeasure Fr).Integrable (g ∘ ι) :=
    (hgc.comp (continuous_subtype_val.subtype_mk _)).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))
  have hgm : AEStronglyMeasurable g
      ((intervalStieltjesMeasure Fr).variation.map ι) :=
    hgc.aestronglyMeasurable
  unfold intervalStieltjesIntegral
  simp only [VectorMeasure.restrict_univ]
  rw [← hmap, MeasureTheory.VectorMeasure.integral_map
    (continuous_subtype_val.subtype_mk _).measurable hgm hgint]
  rfl

/-- A continuous Stieltjes integral splits over a finite monotone partition. -/
theorem intervalStieltjesIntegral_eq_sum_Ioc
    {a b : ℝ} (F : RightContinuousIntervalBV a b) (hFc : Continuous F.toFun)
    (g : Set.Icc a b → ℝ) (hgc : Continuous g) {n : ℕ}
    (cuts : Fin (n + 1) → Set.Icc a b) (hcuts : Monotone cuts)
    (hzero : (cuts 0 : ℝ) = a) (hlast : (cuts (Fin.last n) : ℝ) = b) :
    intervalStieltjesIntegral F g Set.univ =
      ∑ i : Fin n, intervalStieltjesIntegral F g (Ioc (cuts i.castSucc) (cuts i.succ)) := by
  have hab : a ≤ b := by
    calc
      a = cuts 0 := hzero.symm
      _ ≤ cuts (Fin.last n) := hcuts (Fin.zero_le _)
      _ = b := hlast
  let _ : Fact (a ≤ b) := ⟨hab⟩
  let _ : IsFiniteMeasure (intervalStieltjesMeasure F).variation := by
    exact BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure F.boundedVariation
  unfold intervalStieltjesIntegral
  have hmeas (i : Fin n) : MeasurableSet (Ioc (cuts i.castSucc) (cuts i.succ)) :=
    measurableSet_Ioc
  have hall : (intervalStieltjesMeasure F).Integrable g :=
    hgc.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))
  have hint (i : Fin n) :
      (intervalStieltjesMeasure F).IntegrableOn g (Ioc (cuts i.castSucc) (cuts i.succ)) :=
    hall.integrableOn
  have hpair : Set.Pairwise ((Finset.univ : Finset (Fin n)) : Set (Fin n))
      (Disjoint on fun i ↦ Ioc (cuts i.castSucc) (cuts i.succ)) := by
    intro i _ j _ hij
    change Disjoint (Ioc (cuts i.castSucc) (cuts i.succ))
      (Ioc (cuts j.castSucc) (cuts j.succ))
    rw [Set.disjoint_left]
    intro x hxi hxj
    rcases lt_or_gt_of_ne hij with hij' | hji'
    · have hij_fin : i.succ ≤ j.castSucc := by
        simpa using Nat.succ_le_of_lt hij'
      exact (not_lt_of_ge (le_trans hxi.2 (hcuts hij_fin))) hxj.1
    · have hji_fin : j.succ ≤ i.castSucc := by
        simpa using Nat.succ_le_of_lt hji'
      exact (not_lt_of_ge (le_trans hxj.2 (hcuts hji_fin))) hxi.1
  rw [← MeasureTheory.VectorMeasure.setIntegral_biUnion_finset Finset.univ
    (fun i _ ↦ hmeas i) hpair (fun i _ ↦ hint i)]
  have hunion :
      (⋃ i : Fin n, Ioc (cuts i.castSucc) (cuts i.succ)) = Set.univ \ {cuts 0} := by
    rw [hcuts.iUnion_Ioc_fin]
    ext x
    simp only [mem_Ioc, mem_sdiff, mem_univ, true_and, mem_singleton_iff]
    constructor
    · rintro ⟨hx0, _⟩ hxe
      exact hx0.ne' hxe
    · intro hxe
      exact ⟨lt_of_le_of_ne (by
        change (cuts 0 : ℝ) ≤ (x : ℝ)
        simpa [hzero] using x.property.1) (fun hx ↦ hxe hx.symm),
        by
          change (x : ℝ) ≤ (cuts (Fin.last n) : ℝ)
          simpa [hlast] using x.property.2⟩
  simp only [Finset.mem_univ, iUnion_true]
  rw [hunion]
  rw [MeasureTheory.VectorMeasure.setIntegral_sdiff (s := Set.univ) (t := {cuts 0})
    MeasurableSet.univ (measurableSet_singleton _) hall.integrableOn (subset_univ _)]
  rw [MeasureTheory.VectorMeasure.integral_singleton]
  have hz : intervalStieltjesMeasure F {cuts 0} = 0 :=
    BoundedVariationOn.vectorMeasure_singleton_eq_zero_of_continuous F.boundedVariation hFc _
  rw [hz]
  simp

/-- Reversing both continuous integrand and BV integrator negates their Stieltjes integral. -/
theorem intervalStieltjesIntegral_comp_reverse
    {a b : ℝ} (hab : a ≤ b) (F : RightContinuousIntervalBV a b)
    (hFc : Continuous F.toFun) (g : Set.Icc a b → ℝ) (hgc : Continuous g) :
    let r := Set.Icc.reverse hab
    let hfr := BoundedVariationOn.comp_antitone_surjective_Icc hab F.boundedVariation
      (Set.Icc.antitone_reverse hab) (Set.Icc.surjective_reverse hab)
    intervalStieltjesIntegral
        { toFun := F.toFun ∘ r
          boundedVariation := hfr
          right_continuous := fun _ ↦
            (hFc.comp (Set.Icc.continuous_reverse hab)).continuousAt.continuousWithinAt }
        (g ∘ r) Set.univ =
      -intervalStieltjesIntegral F g Set.univ := by
  dsimp only
  let r := Set.Icc.reverse hab
  let hfr := BoundedVariationOn.comp_antitone_surjective_Icc hab F.boundedVariation
    (Set.Icc.antitone_reverse hab) (Set.Icc.surjective_reverse hab)
  let Fr : RightContinuousIntervalBV a b :=
    { toFun := F.toFun ∘ r
      boundedVariation := hfr
      right_continuous := fun _ ↦
        (hFc.comp (Set.Icc.continuous_reverse hab)).continuousAt.continuousWithinAt }
  have hmap : (intervalStieltjesMeasure Fr).map r = -intervalStieltjesMeasure F :=
    BoundedVariationOn.vectorMeasure_map_reverse_Icc hab F.boundedVariation hFc
  let _ : IsFiniteMeasure (intervalStieltjesMeasure Fr).variation := by
    change IsFiniteMeasure hfr.vectorMeasure.variation
    exact BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure hfr
  have hgint : (intervalStieltjesMeasure Fr).Integrable (g ∘ r) :=
    (hgc.comp (Set.Icc.continuous_reverse hab)).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))
  have hgm : AEStronglyMeasurable g
      ((intervalStieltjesMeasure Fr).variation.map r) :=
    hgc.aestronglyMeasurable
  unfold intervalStieltjesIntegral
  simp only [MeasureTheory.VectorMeasure.restrict_univ]
  rw [← MeasureTheory.VectorMeasure.integral_neg_vectorMeasure, ← hmap,
    MeasureTheory.VectorMeasure.integral_map
      (Set.Icc.continuous_reverse hab).measurable hgm hgint]
  rfl

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Stieltjes / Continuous
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace MovingSofa

/-- A continuous function is integrable against a BV Stieltjes measure on a compact interval. -/
theorem RightContinuousIntervalBV.integrable_of_continuous {a b : ℝ} (F :
  RightContinuousIntervalBV a b)
    {g : Set.Icc a b → ℝ} (hg : Continuous g) : (intervalStieltjesMeasure F).Integrable g := by
  let _ : IsFiniteMeasure (intervalStieltjesMeasure F).variation :=
    BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure F.boundedVariation
  exact hg.integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))

private theorem intervalStieltjesIntegral_univ_eq_Ioc_of_continuous
    {a b : ℝ} (hab : a ≤ b) (F : RightContinuousIntervalBV a b)
    (hF : Continuous F.toFun) (g : Set.Icc a b → ℝ) (hg : Continuous g) :
    intervalStieltjesIntegral F g Set.univ =
      intervalStieltjesIntegral F g {t | a < (t : ℝ)} := by
  let a' : Set.Icc a b := ⟨a, le_rfl, hab⟩
  let b' : Set.Icc a b := ⟨b, hab, le_rfl⟩
  let cuts : Fin 2 → Set.Icc a b := Fin.cases a' (fun _ ↦ b')
  have hcuts : Monotone cuts := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Std.le_refl,
      Nat.reduceAdd, Fin.cases_zero, cuts, a', b',
      Fin.mk_one, zero_le, nonpos_iff_eq_zero, one_ne_zero] at hij ⊢
    exact hab
  have hparts := intervalStieltjesIntegral_eq_sum_Ioc F hF g hg cuts hcuts rfl rfl
  have hset : Set.Ioc a' b' = {t : Set.Icc a b | a < (t : ℝ)} := by
    ext t
    simp only [Set.mem_Ioc, Set.mem_ofPred_eq]
    constructor
    · exact fun ht ↦ ht.1
    · exact fun ht ↦ ⟨ht, t.property.2⟩
  dsimp [cuts] at hparts
  simpa [Fin.sum_univ_succ, hset] using hparts

/-- For a continuous driver and a continuous integrand, the closed-interval Stieltjes integral
agrees with the open-interval one: neither endpoint carries an atom. -/
theorem intervalStieltjesIntegral_univ_eq_Ioo_of_continuous {a b : ℝ} (hab : a ≤ b)
    (F : RightContinuousIntervalBV a b) (hF : Continuous F.toFun)
    (g : Set.Icc a b → ℝ) (hg : Continuous g) :
    intervalStieltjesIntegral F g Set.univ =
      intervalStieltjesIntegral F g (Set.Ioo ⟨a, le_rfl, hab⟩ ⟨b, hab, le_rfl⟩) := by
  set a' : Set.Icc a b := ⟨a, le_rfl, hab⟩
  set b' : Set.Icc a b := ⟨b, hab, le_rfl⟩
  have hdiff : (Set.univ : Set (Set.Icc a b)) \ Set.Ioo a' b' ⊆ {a'} ∪ {b'} := by
    intro t ht
    rcases lt_or_ge a' t with hlt | hle
    · exact Or.inr (le_antisymm t.property.2 (not_lt.mp fun h ↦ ht.2 ⟨hlt, h⟩))
    · exact Or.inl (le_antisymm hle t.property.1)
  have hzero : intervalStieltjesIntegral F g
      ((Set.univ : Set (Set.Icc a b)) \ Set.Ioo a' b') = 0 := by
    refine VectorMeasure.setIntegral_of_variation_apply_eq_zero _ (measure_mono_null hdiff ?_)
    refine measure_union_null ?_ ?_ <;>
      · rw [intervalStieltjesMeasure, F.boundedVariation.variation_vectorMeasure_singleton,
          hF.continuousAt.continuousWithinAt.rightLim_eq,
          hF.continuousAt.continuousWithinAt.leftLim_eq]
        simp
  have hsplit := VectorMeasure.setIntegral_inter_add_sdiff
    (μ := intervalStieltjesMeasure F) (B := ContinuousLinearMap.mul ℝ ℝ) (f := g)
    (s := (Set.univ : Set (Set.Icc a b))) (t := Set.Ioo a' b')
    MeasurableSet.univ measurableSet_Ioo (F.integrable_of_continuous hg).integrableOn
  rw [Set.univ_inter] at hsplit
  change intervalStieltjesIntegral F g (Set.Ioo a' b') +
    intervalStieltjesIntegral F g ((Set.univ : Set (Set.Icc a b)) \ Set.Ioo a' b') =
    intervalStieltjesIntegral F g Set.univ at hsplit
  rw [hzero, add_zero] at hsplit
  exact hsplit.symm

/-- Integration by parts for continuous BV functions on the full compact interval. -/
theorem intervalStieltjes_integration_by_parts_of_continuous
    (a b : ℝ) (hab : a ≤ b) (F G : RightContinuousIntervalBV a b)
    (hF : Continuous F.toFun) (hG : Continuous G.toFun) :
    intervalStieltjesIntegral F G.toFun Set.univ +
        intervalStieltjesIntegral G F.toFun Set.univ =
      F.toFun ⟨b, hab, le_rfl⟩ * G.toFun ⟨b, hab, le_rfl⟩ -
        F.toFun ⟨a, le_rfl, hab⟩ * G.toFun ⟨a, le_rfl, hab⟩ := by
  obtain ⟨left, hleft, hparts⟩ := intervalStieltjes_integration_by_parts a b hab F G
  have hleft_eq : Set.EqOn left F.toFun {t | a < (t : ℝ)} := by
    intro t ht
    change a < (t : ℝ) at ht
    have hnonempty : (Set.Iio t).Nonempty := by
      let s : Set.Icc a b := ⟨(a + (t : ℝ)) / 2, by constructor <;> linarith [t.property.2]⟩
      exact ⟨s, by change (a + (t : ℝ)) / 2 < (t : ℝ); linarith⟩
    have hne : (nhdsWithin t (Set.Iio t)).NeBot :=
      nhdsWithin_Iio_neBot' hnonempty le_rfl
    let _ : (nhdsWithin t (Set.Iio t)).NeBot := hne
    have hcont : Filter.Tendsto F.toFun (nhdsWithin t (Set.Iio t))
        (nhds (F.toFun t)) := hF.continuousAt.continuousWithinAt
    exact tendsto_nhds_unique (hleft t ht) hcont
  have hintegrand : intervalStieltjesIntegral G left {t | a < (t : ℝ)} =
      intervalStieltjesIntegral G F.toFun {t | a < (t : ℝ)} := by
    unfold intervalStieltjesIntegral
    exact MeasureTheory.VectorMeasure.setIntegral_congr_fun hleft_eq
  rw [intervalStieltjesIntegral_univ_eq_Ioc_of_continuous hab F hF G.toFun hG,
    intervalStieltjesIntegral_univ_eq_Ioc_of_continuous hab G hG F.toFun hF,
    ← hintegrand]
  exact hparts

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Stieltjes / Affine
-/

@[expose] public section

noncomputable section

namespace MovingSofa

open MeasureTheory Set

private def unitIntervalIdentity : RightContinuousIntervalBV 0 1 where
  toFun t := t
  boundedVariation := by
    apply ((show Monotone ((↑) : Set.Icc (0 : ℝ) 1 → ℝ) from fun _ _ h ↦ h).monotoneOn
      Set.univ).boundedVariationOn (C := 1)
    intro t _
    rw [abs_of_nonneg t.property.1]
    exact t.property.2
  right_continuous t := continuous_subtype_val.continuousAt.continuousWithinAt

private theorem continuous_unitIntervalIdentity :
    Continuous unitIntervalIdentity.toFun :=
  continuous_subtype_val

/-- A continuous BV driver carries total Stieltjes mass equal to its increment. -/
theorem intervalStieltjesMeasure_univ_of_continuous {a b : ℝ} (hab : a ≤ b)
    (Q : RightContinuousIntervalBV a b) (hQ : Continuous Q.toFun) :
    intervalStieltjesMeasure Q univ =
      Q.toFun ⟨b, hab, le_rfl⟩ - Q.toFun ⟨a, le_rfl, hab⟩ := by
  have hu : (univ : Set (Icc a b)) = Icc ⟨a, le_rfl, hab⟩ ⟨b, hab, le_rfl⟩ := by
    ext x
    simp only [mem_univ, mem_Icc, true_iff]
    exact x.property
  unfold intervalStieltjesMeasure
  rw [hu, Q.boundedVariation.vectorMeasure_Icc (show
      (⟨a, le_rfl, hab⟩ : Icc a b) ≤ ⟨b, hab, le_rfl⟩ from hab),
    hQ.continuousAt.continuousWithinAt.rightLim_eq,
    hQ.continuousAt.continuousWithinAt.leftLim_eq]

/-- An affine function of a continuous BV driver has that driver's Stieltjes measure, scaled by
the affine map's slope. -/
theorem intervalStieltjesMeasure_affine {a b : ℝ}
    (Q F : RightContinuousIntervalBV a b) (hQ : Continuous Q.toFun) (u v : ℝ)
    (hF : ∀ t, F.toFun t = u + v * Q.toFun t) :
    intervalStieltjesMeasure F = v • intervalStieltjesMeasure Q := by
  have hFc : Continuous F.toFun := by
    rw [show F.toFun = fun t ↦ u + v * Q.toFun t from funext hF]
    exact continuous_const.add (continuous_const.mul hQ)
  apply VectorMeasure.ext_of_Icc
  intro x y hxy
  simp only [smul_apply]
  unfold intervalStieltjesMeasure
  rw [F.boundedVariation.vectorMeasure_Icc hxy, Q.boundedVariation.vectorMeasure_Icc hxy,
    hFc.continuousAt.continuousWithinAt.rightLim_eq,
    hFc.continuousAt.continuousWithinAt.leftLim_eq,
    hQ.continuousAt.continuousWithinAt.rightLim_eq,
    hQ.continuousAt.continuousWithinAt.leftLim_eq, hF x, hF y]
  ring

/-- Shifting a continuous BV driver and its integrand by constants shifts the interval Stieltjes
integral over the whole parameter interval by the integrand's shift times the driver's increment;
the driver's own shift has no effect. -/
theorem intervalStieltjesIntegral_add_const {a b : ℝ} (hab : a ≤ b)
    (F G : RightContinuousIntervalBV a b) (hF : Continuous F.toFun) (c : ℝ)
    (hFG : ∀ t, G.toFun t = F.toFun t + c) (g : Icc a b → ℝ) (hg : Continuous g) (d : ℝ) :
    intervalStieltjesIntegral G (fun t ↦ g t + d) univ =
      intervalStieltjesIntegral F g univ +
        d * (F.toFun ⟨b, hab, le_rfl⟩ - F.toFun ⟨a, le_rfl, hab⟩) := by
  let _ : IsFiniteMeasure (intervalStieltjesMeasure F).variation :=
    BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure F.boundedVariation
  have hmeas : intervalStieltjesMeasure G = intervalStieltjesMeasure F := by
    rw [intervalStieltjesMeasure_affine F G hF c 1 fun t ↦ by rw [hFG t]; ring, one_smul]
  have hsum : (fun t ↦ g t + d) = g + fun _ ↦ d := rfl
  rw [intervalStieltjesIntegral_univ, intervalStieltjesIntegral_univ, hmeas, hsum,
    VectorMeasure.integral_add (F.integrable_of_continuous hg)
      (F.integrable_of_continuous continuous_const),
    VectorMeasure.integral_const, ← intervalStieltjesMeasure_univ_of_continuous hab F hF]
  simp

/-- The signed cross integral of two affine functions of one continuous BV driver. -/
theorem intervalStieltjesIntegral_affine_driver_cross {a b : ℝ} (hab : a ≤ b)
    (Q F G : RightContinuousIntervalBV a b) (hQ : Continuous Q.toFun)
    (u v w z : ℝ) (hF : ∀ t, F.toFun t = u + v * Q.toFun t)
    (hG : ∀ t, G.toFun t = w + z * Q.toFun t) :
    intervalStieltjesIntegral G F.toFun univ - intervalStieltjesIntegral F G.toFun univ =
      (u * z - w * v) * (Q.toFun ⟨b, hab, le_rfl⟩ - Q.toFun ⟨a, le_rfl, hab⟩) := by
  let _ : IsFiniteMeasure (intervalStieltjesMeasure Q).variation :=
    BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure Q.boundedVariation
  have hFm := intervalStieltjesMeasure_affine Q F hQ u v hF
  have hGm := intervalStieltjesMeasure_affine Q G hQ w z hG
  have hi (H : RightContinuousIntervalBV a b) (c d : ℝ)
      (hH : ∀ t, H.toFun t = c + d * Q.toFun t) :
      intervalStieltjesIntegral Q H.toFun univ =
        c * (Q.toFun ⟨b, hab, le_rfl⟩ - Q.toFun ⟨a, le_rfl, hab⟩) +
          d * intervalStieltjesIntegral Q Q.toFun univ := by
    have heq : H.toFun = (fun _ ↦ c) + d • Q.toFun := by
      funext t
      exact hH t
    have hc := Q.integrable_of_continuous (g := fun _ ↦ c) continuous_const
    have hd := Q.integrable_of_continuous (g := d • Q.toFun) (continuous_const.smul hQ)
    unfold intervalStieltjesIntegral
    simp only [VectorMeasure.restrict_univ, heq]
    rw [VectorMeasure.integral_add hc hd, VectorMeasure.integral_smul,
      VectorMeasure.integral_const, intervalStieltjesMeasure_univ_of_continuous hab Q hQ]
    simp
  have hFI := hi F u v hF
  have hGI := hi G w z hG
  unfold intervalStieltjesIntegral at hFI hGI ⊢
  simp only [VectorMeasure.restrict_univ] at hFI hGI ⊢
  rw [hFm, hGm, VectorMeasure.integral_smul_vectorMeasure,
    VectorMeasure.integral_smul_vectorMeasure, hFI, hGI]
  ring

theorem intervalStieltjesIntegral_affine_cross
    (F G : RightContinuousIntervalBV 0 1) (a b c d : ℝ)
    (hF : ∀ t, F.toFun t = a + b * (t : ℝ))
    (hG : ∀ t, G.toFun t = c + d * (t : ℝ)) :
    intervalStieltjesIntegral G F.toFun Set.univ -
        intervalStieltjesIntegral F G.toFun Set.univ = a * d - c * b := by
  simpa only [unitIntervalIdentity, sub_zero, mul_one] using
    intervalStieltjesIntegral_affine_driver_cross (by norm_num : (0 : ℝ) ≤ 1)
      unitIntervalIdentity F G continuous_unitIntervalIdentity a b c d hF hG

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Riemann-Stieltjes sums for continuous integrands

Left-endpoint sums over finite monotone partitions converge to the interval Stieltjes
integral of a continuous integrand against a continuous BV integrator, uniformly in the
mesh of the partition.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace MovingSofa

/-- Two Stieltjes integrals differ by at most the uniform distance of their integrands
times the total variation of the integrator. -/
theorem intervalStieltjesIntegral_sub_le_of_abs_sub_le
    {a b : ℝ} (F : RightContinuousIntervalBV a b) {g h : Set.Icc a b → ℝ}
    (hg : (intervalStieltjesMeasure F).Integrable g)
    (hh : (intervalStieltjesMeasure F).Integrable h)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbound : ∀ᵐ t ∂(intervalStieltjesMeasure F).variation, |g t - h t| ≤ ε) :
    |intervalStieltjesIntegral F g univ - intervalStieltjesIntegral F h univ| ≤
      ε * (intervalStieltjesMeasure F).variation.real univ := by
  let _ : IsFiniteMeasure (intervalStieltjesMeasure F).variation :=
    BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure F.boundedVariation
  unfold intervalStieltjesIntegral
  simp only [VectorMeasure.restrict_univ]
  rw [← VectorMeasure.integral_sub hg hh, ← Real.norm_eq_abs]
  have h := VectorMeasure.norm_integral_le_of_norm_le_const
    (B := ContinuousLinearMap.mul ℝ ℝ) (by simpa only [Real.norm_eq_abs] using hbound)
  refine h.trans ?_
  calc
    ε * ‖ContinuousLinearMap.mul ℝ ℝ‖ * (intervalStieltjesMeasure F).variation.real univ ≤
        ε * 1 * (intervalStieltjesMeasure F).variation.real univ := by
      gcongr
      exact ContinuousLinearMap.opNorm_mul_le ℝ ℝ
    _ = _ := by ring

private theorem intervalStieltjesIntegral_sum_indicator_Ioc
    {a b : ℝ} (F : RightContinuousIntervalBV a b) {ι : Type*}
    (s : Finset ι) (l u : ι → Set.Icc a b) (c : ι → ℝ)
    (hlu : ∀ i ∈ s, l i ≤ u i) :
    intervalStieltjesIntegral F
        (fun t ↦ ∑ i ∈ s, (Ioc (l i) (u i)).indicator (fun _ ↦ c i) t) univ =
      ∑ i ∈ s, c i * (F.toFun (u i) - F.toFun (l i)) := by
  classical
  let _ : IsFiniteMeasure (intervalStieltjesMeasure F).variation :=
    BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure F.boundedVariation
  unfold intervalStieltjesIntegral
  rw [VectorMeasure.restrict_univ, VectorMeasure.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [VectorMeasure.integral_indicator_const _ measurableSet_Ioc]
    change c i * F.boundedVariation.vectorMeasure (Ioc (l i) (u i)) = _
    rw [F.boundedVariation.vectorMeasure_Ioc (hlu i hi),
      (F.right_continuous (u i)).rightLim_eq, (F.right_continuous (l i)).rightLim_eq]
  · intro i _
    exact (MeasureTheory.integrable_const (c i)).indicator measurableSet_Ioc

/-- The error in a left-endpoint Stieltjes sum is controlled by the cell oscillation of the
integrand times the total variation of the integrator. -/
theorem intervalStieltjesIntegral_sub_sum_le_of_oscillation
    {a b : ℝ} (F : RightContinuousIntervalBV a b) (hF : Continuous F.toFun)
    {g : Set.Icc a b → ℝ} (hg : Continuous g) {n : ℕ}
    (cuts : Fin (n + 1) → Set.Icc a b) (hcuts : Monotone cuts)
    (hzero : (cuts 0 : ℝ) = a) (hlast : (cuts (Fin.last n) : ℝ) = b)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hosc : ∀ (i : Fin n) t, t ∈ Ioc (cuts i.castSucc) (cuts i.succ) →
      |g t - g (cuts i.castSucc)| ≤ ε) :
    |intervalStieltjesIntegral F g univ -
        ∑ i : Fin n, g (cuts i.castSucc) *
          (F.toFun (cuts i.succ) - F.toFun (cuts i.castSucc))| ≤
      ε * (intervalStieltjesMeasure F).variation.real univ := by
  classical
  let _ : IsFiniteMeasure (intervalStieltjesMeasure F).variation :=
    BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure F.boundedVariation
  let step : Set.Icc a b → ℝ := fun t ↦ ∑ i : Fin n,
    (Ioc (cuts i.castSucc) (cuts i.succ)).indicator (fun _ ↦ g (cuts i.castSucc)) t
  have hstep : (intervalStieltjesMeasure F).Integrable step := by
    apply MeasureTheory.integrable_finsetSum
    intro i _
    exact (MeasureTheory.integrable_const _).indicator measurableSet_Ioc
  have heval : intervalStieltjesIntegral F step univ =
      ∑ i : Fin n, g (cuts i.castSucc) *
        (F.toFun (cuts i.succ) - F.toFun (cuts i.castSucc)) :=
    intervalStieltjesIntegral_sum_indicator_Ioc (ι := Fin n) F Finset.univ
      (fun i ↦ cuts i.castSucc) (fun i ↦ cuts i.succ)
      (fun i ↦ g (cuts i.castSucc)) (fun i _ ↦ hcuts (Fin.castSucc_le_succ i))
  rw [← heval]
  apply intervalStieltjesIntegral_sub_le_of_abs_sub_le F
    (F.integrable_of_continuous hg) hstep hε
  have hatom : (intervalStieltjesMeasure F).variation {cuts 0} = 0 := by
    rw [VectorMeasure.variation_apply_singleton]
    have hz : intervalStieltjesMeasure F {cuts 0} = 0 :=
      BoundedVariationOn.vectorMeasure_singleton_eq_zero_of_continuous
        F.boundedVariation hF _
    simp [hz]
  have hae : ∀ᵐ t ∂(intervalStieltjesMeasure F).variation, t ≠ cuts 0 := by
    rw [ae_iff]
    have hset : {x : Set.Icc a b | ¬x ≠ cuts 0} = {cuts 0} := by
      ext x
      simp
    rw [hset]
    exact hatom
  filter_upwards [hae] with t ht
  have htcell : t ∈ ⋃ i : Fin n, Ioc (cuts i.castSucc) (cuts i.succ) := by
    rw [hcuts.iUnion_Ioc_fin]
    refine ⟨lt_of_le_of_ne ?_ (Ne.symm ht), ?_⟩
    · change (cuts 0 : ℝ) ≤ (t : ℝ)
      simpa [hzero] using t.property.1
    · change (t : ℝ) ≤ (cuts (Fin.last n) : ℝ)
      simpa [hlast] using t.property.2
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp htcell
  have hvalue : step t = g (cuts i.castSucc) := by
    dsimp [step]
    rw [Finset.sum_eq_single i]
    · exact Set.indicator_of_mem hi _
    · intro j _ hji
      apply Set.indicator_of_notMem
      intro hj
      rcases lt_or_gt_of_ne hji with hji | hij
      · have hji' : j.succ ≤ i.castSucc := by simpa using Nat.succ_le_of_lt hji
        exact (not_lt_of_ge (hj.2.trans (hcuts hji'))) hi.1
      · have hij' : i.succ ≤ j.castSucc := by simpa using Nat.succ_le_of_lt hij
        exact (not_lt_of_ge (hi.2.trans (hcuts hij'))) hj.1
    · simp
  rw [hvalue]
  exact hosc i t hi

/-- Sufficiently fine partitions approximate a continuous Stieltjes integrand uniformly. -/
theorem exists_mesh_bound_intervalStieltjesIntegral_sub_sum
    {a b : ℝ} (F : RightContinuousIntervalBV a b) (hF : Continuous F.toFun)
    {g : Set.Icc a b → ℝ} (hg : Continuous g) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {n : ℕ} (cuts : Fin (n + 1) → Set.Icc a b),
      Monotone cuts → (cuts 0 : ℝ) = a → (cuts (Fin.last n) : ℝ) = b →
      (∀ i : Fin n, (cuts i.succ : ℝ) - (cuts i.castSucc : ℝ) < δ) →
      |intervalStieltjesIntegral F g univ -
          ∑ i : Fin n, g (cuts i.castSucc) *
            (F.toFun (cuts i.succ) - F.toFun (cuts i.castSucc))| ≤
        ε * (intervalStieltjesMeasure F).variation.real univ := by
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hg) ε hε
  refine ⟨δ, hδ, fun cuts hcuts hzero hlast hmesh ↦ ?_⟩
  apply intervalStieltjesIntegral_sub_sum_le_of_oscillation F hF hg cuts hcuts hzero hlast
    hε.le
  intro i t ht
  have hdist : dist t (cuts i.castSucc) < δ := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg
      (sub_nonneg.mpr (show (cuts i.castSucc : ℝ) ≤ (t : ℝ) from ht.1.le))]
    exact (sub_le_sub_right (show (t : ℝ) ≤ (cuts i.succ : ℝ) from ht.2) _).trans_lt
      (hmesh i)
  simpa only [Real.dist_eq] using (hmod hdist).le

/-- Left-endpoint Stieltjes sums converge along any family of partitions whose mesh
tends to zero. -/
theorem tendsto_stieltjesSum_of_mesh_tendsto_zero
    {a b : ℝ} (F : RightContinuousIntervalBV a b) (hF : Continuous F.toFun)
    {g : Set.Icc a b → ℝ} (hg : Continuous g) (N : ℕ → ℕ)
    (cuts : ∀ k, Fin (N k + 1) → Set.Icc a b)
    (hcuts : ∀ k, Monotone (cuts k))
    (hzero : ∀ k, (cuts k 0 : ℝ) = a)
    (hlast : ∀ k, (cuts k (Fin.last (N k)) : ℝ) = b)
    (hmesh : ∀ δ > 0, ∀ᶠ k in Filter.atTop, ∀ i : Fin (N k),
      (cuts k i.succ : ℝ) - (cuts k i.castSucc : ℝ) < δ) :
    Filter.Tendsto (fun k ↦ ∑ i : Fin (N k), g (cuts k i.castSucc) *
      (F.toFun (cuts k i.succ) - F.toFun (cuts k i.castSucc)))
      Filter.atTop (nhds (intervalStieltjesIntegral F g univ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set V := (intervalStieltjesMeasure F).variation.real univ with hVdef
  have hV : 0 ≤ V := measureReal_nonneg
  have hpos : 0 < ε / (V + 1) := div_pos hε (by positivity)
  obtain ⟨δ, hδ, happrox⟩ :=
    exists_mesh_bound_intervalStieltjesIntegral_sub_sum F hF hg hpos
  filter_upwards [hmesh δ hδ] with k hk
  have hbound := happrox (cuts k) (hcuts k) (hzero k) (hlast k) hk
  rw [Real.dist_eq, abs_sub_comm]
  apply hbound.trans_lt
  have hcancel : ε / (V + 1) * (V + 1) = ε :=
    div_mul_cancel₀ ε (by positivity)
  change ε / (V + 1) * V < ε
  nlinarith

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Stieltjes / Shift
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MovingSofa

/-- Translate a continuous interval-BV representative and its Stieltjes measure. -/
theorem exists_intervalBV_shift_add {a b c : ℝ} (hab : a ≤ b)
    (f : RightContinuousIntervalBV (a + c) (b + c)) (hfc : Continuous f.toFun) :
    ∃ g : RightContinuousIntervalBV a b,
      (∀ t, g.toFun t = f.toFun
        ⟨(t : ℝ) + c, by constructor <;> linarith [t.property.1, t.property.2]⟩) ∧
      ∀ E : Set (Icc a b), MeasurableSet E →
        intervalStieltjesMeasure g E = intervalStieltjesMeasure f
          ((fun t : Icc a b ↦
            ⟨(t : ℝ) + c, by constructor <;> linarith [t.property.1, t.property.2]⟩) '' E) := by
  let φ : Icc a b → Icc (a + c) (b + c) := fun t ↦
    ⟨(t : ℝ) + c, by constructor <;> linarith [t.property.1, t.property.2]⟩
  let ψ : Icc (a + c) (b + c) → Icc a b := fun t ↦
    ⟨(t : ℝ) - c, by constructor <;> linarith [t.property.1, t.property.2]⟩
  have hφc : Continuous φ := (continuous_subtype_val.add_const c).subtype_mk _
  have hψc : Continuous ψ := (continuous_subtype_val.sub continuous_const).subtype_mk _
  have hφm : Monotone φ := fun x y hxy ↦ by
    change (x : ℝ) + c ≤ (y : ℝ) + c
    linarith [show (x : ℝ) ≤ (y : ℝ) from hxy]
  have hφs : Function.Surjective φ := by
    intro y
    refine ⟨ψ y, ?_⟩
    apply Subtype.ext
    simp [φ, ψ]
  have hφi : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    simpa [φ] using congrArg Subtype.val hxy
  let e : Icc a b ≃ₜ Icc (a + c) (b + c) :=
    { toFun := φ
      invFun := ψ
      left_inv := fun x ↦ by apply Subtype.ext; simp [φ, ψ]
      right_inv := fun x ↦ by apply Subtype.ext; simp [φ, ψ]
      continuous_toFun := hφc
      continuous_invFun := hψc }
  let hgbv := BoundedVariationOn.comp_monotone_surjective_Icc
    (by linarith : a + c ≤ b + c)
    f.boundedVariation hφm hφs
  let g : RightContinuousIntervalBV a b :=
    { toFun := f.toFun ∘ φ
      boundedVariation := hgbv
      right_continuous := fun t ↦
        (hfc.comp hφc).continuousAt.continuousWithinAt }
  refine ⟨g, fun _ ↦ rfl, ?_⟩
  intro E hE
  have hmap := BoundedVariationOn.vectorMeasure_map_comp_monotone_surjective_Icc
    (by linarith : a + c ≤ b + c) hab f.boundedVariation hfc hφc hφm hφs
  have hφE : MeasurableSet (φ '' E) := e.measurableEmbedding.measurableSet_image' hE
  change hgbv.vectorMeasure E = f.boundedVariation.vectorMeasure (φ '' E)
  rw [← hmap, VectorMeasure.map_apply _ hφc.measurable hφE,
    hφi.preimage_image]

/-- Specialize interval translation to an interval starting at zero. -/
theorem exists_intervalBV_shift_from_zero {b c : ℝ} (hb : 0 ≤ b)
    (f : RightContinuousIntervalBV (0 + c) (b + c)) (hfc : Continuous f.toFun) :
    ∃ g : RightContinuousIntervalBV 0 b,
      (∀ t, g.toFun t = f.toFun
        ⟨(t : ℝ) + c, by constructor <;> linarith [t.property.1, t.property.2]⟩) ∧
      ∀ E : Set (Icc 0 b), MeasurableSet E →
        intervalStieltjesMeasure g E = intervalStieltjesMeasure f
          ((fun t : Icc 0 b ↦
            ⟨(t : ℝ) + c, by constructor <;> linarith [t.property.1, t.property.2]⟩) '' E) := by
  exact exists_intervalBV_shift_add (a := 0) (b := b) (c := c) hb f hfc

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Basic
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace MovingSofa

instance angleMeasurableSpace : MeasurableSpace Real.Angle := borel Real.Angle

instance angleBorelSpace : BorelSpace Real.Angle := ⟨rfl⟩

/-- An exterior normal direction at a point of a convex body. -/
def IsExteriorNormal (K : ConvexBody Point) (p : Point) (a : Real.Angle) : Prop :=
  ∀ q ∈ (K : Set Point), inner ℝ (q - p) (normalVector a) ≤ 0

/-- Boundary points with exactly one exterior unit normal. -/
def regularBoundary (K : ConvexBody Point) : Set Point :=
  {p | p ∈ frontier (K : Set Point) ∧ ∃! a, IsExteriorNormal K p a}

/-- The unique exterior normal at regular points, extended by zero elsewhere. -/
def exteriorNormalAngle (K : ConvexBody Point) (p : Point) : Real.Angle := by
  classical
  exact if h : ∃! a, IsExteriorNormal K p a then h.exists.choose else 0

/-- A nontrivial segment presentation and a perpendicular angular direction. -/
def IsSegmentPresentation (K : ConvexBody Point) (d : Point × Point × Real.Angle) : Prop :=
  d.1 ≠ d.2.1 ∧ (K : Set Point) = segment ℝ d.1 d.2.1 ∧
    inner ℝ (d.2.1 - d.1) (normalVector d.2.2) = 0

/-- Surface measure in angular coordinates, including point and segment bodies. -/
def surfaceAreaMeasure (K : ConvexBody Point) : Measure Real.Angle := by
  classical
  exact if (K : Set Point).Subsingleton then 0
  else if h : ∃ d, IsSegmentPresentation K d then
    let d := h.choose
    ENNReal.ofReal (dist d.1 d.2.1) •
      (Measure.dirac d.2.2 + Measure.dirac (d.2.2 + ((Real.pi : ℝ) : Real.Angle)))
  else
    Measure.map (exteriorNormalAngle K)
      ((Measure.hausdorffMeasure 1).restrict (regularBoundary K))

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Exterior Normal
-/

@[expose] public section

noncomputable section

namespace MovingSofa

open Set

/-- Every frontier point of a convex body with nonempty interior admits an exterior unit normal. -/
theorem exists_isExteriorNormal_of_mem_frontier
    (K : ConvexBody Point) (hK : (interior (K : Set Point)).Nonempty)
    {p : Point} (hp : p ∈ frontier (K : Set Point)) :
    ∃ a, IsExteriorNormal K p a := by
  have hpnot : p ∉ interior (K : Set Point) := by
    have hpK : p ∈ K := by
      change p ∈ (K : Set Point)
      rw [← K.isClosed.closure_eq]
      exact frontier_subset_closure hp
    exact (mem_frontier_iff_notMem_interior hpK).mp hp
  obtain ⟨f, hf⟩ := geometric_hahn_banach_point_open K.convex.interior isOpen_interior hpnot
  let fc : Point →L[ℝ] ℝ := f.toContinuousLinearMap
  have hfne : fc ≠ 0 := by
    obtain ⟨q, hq⟩ := hK
    intro hzero
    have h := hf q hq
    have hfp : fc p = 0 := by rw [hzero]; rfl
    have hfq : fc q = 0 := by rw [hzero]; rfl
    change fc p < fc q at h
    linarith
  let w : Point := -(InnerProductSpace.toDual ℝ Point).symm fc
  have hw : w ≠ 0 := by
    intro hzero
    apply hfne
    apply (InnerProductSpace.toDual ℝ Point).symm.injective
    simpa using neg_eq_zero.mp hzero
  obtain ⟨a, ha⟩ := exists_angle_normalVector_eq (u := ‖w‖⁻¹ • w) (by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)])
  refine ⟨a, ?_⟩
  rw [IsExteriorNormal, ha]
  intro q hq
  have hclosed : IsClosed {q : Point | fc p ≤ fc q} :=
    isClosed_le continuous_const fc.continuous
  have hinterior : interior (K : Set Point) ⊆ {q : Point | fc p ≤ fc q} :=
    fun q hq ↦ (hf q hq).le
  have hsubset : (K : Set Point) ⊆ {q : Point | fc p ≤ fc q} := by
    rw [← K.isClosed.closure_eq,
      ← K.convex.closure_interior_eq_closure_of_nonempty_interior hK]
    exact closure_minimal hinterior hclosed
  have hfpq := hsubset hq
  rw [inner_smul_right, inner_neg_right, real_inner_comm,
    InnerProductSpace.toDual_symm_apply]
  dsimp only [fc] at hfpq ⊢
  rw [map_sub]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg w))
    (neg_nonpos.mpr (sub_nonneg.mpr hfpq))

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Graph Definitions
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- Project the convex body horizontally after translating and changing orthonormal frame. -/
def horizontalProjection (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) : Set ℝ :=
  (fun p : Point ↦ e (p - o) 0) '' (K : Set Point)

/-- The infimum and supremum of the body’s horizontal projection in the chosen frame. -/
def horizontalBounds (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) : ℝ × ℝ :=
  (sInf (horizontalProjection K o e), sSup (horizontalProjection K o e))

/-- The supremum of the body’s vertical section at a given horizontal coordinate. -/
def upperGraphHeight (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) (x : ℝ) : ℝ :=
  sSup {y : ℝ | o + e.symm !₂[x, y] ∈ (K : Set Point)}

/-- The argument of a planar vector, viewed as an angle modulo a full turn. -/
def vectorNormalAngle (p : Point) : Real.Angle :=
  (Complex.arg ⟨p 0, p 1⟩ : ℝ)

/-- The normal vector associated to a nonzero planar vector is its normalization. -/
theorem normalVector_vectorNormalAngle {p : Point} (hp : p ≠ 0) :
    normalVector (vectorNormalAngle p) = ‖p‖⁻¹ • p := by
  let z : ℂ := ⟨p 0, p 1⟩
  have hz : z ≠ 0 := by
    intro hz
    apply hp
    ext i
    fin_cases i
    · exact congrArg Complex.re hz
    · exact congrArg Complex.im hz
  have hnorm : ‖z‖ = ‖p‖ := by
    rw [Complex.norm_def, EuclideanSpace.norm_eq]
    congr 1
    simp only [z, Complex.normSq_apply, Fin.sum_univ_two]
    simp [Real.norm_eq_abs, pow_two]
  ext i
  fin_cases i
  · simpa [vectorNormalAngle, normalVector, frame, z, hnorm, div_eq_inv_mul] using
      Complex.cos_arg hz
  · simpa [vectorNormalAngle, normalVector, frame, z, hnorm, div_eq_inv_mul] using
      Complex.sin_arg z

/-- Weight the upper graph by its normal direction and arc-length Jacobian. -/
def upperGraphSurfaceIntegrand (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ) (x : ℝ) : ℝ :=
  ψ (vectorNormalAngle (e.symm !₂[-deriv (upperGraphHeight K o e) x, 1])) *
    Real.sqrt (1 + (deriv (upperGraphHeight K o e) x) ^ 2)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Regularity
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace MovingSofa

instance angleCompactSpace : CompactSpace Real.Angle :=
  AddCircle.homeomorphCircle'.symm.compactSpace

/-- The unit normal depends continuously on its angle. -/
theorem continuous_normalVector_angle :
    Continuous normalVector := by
  let c : Real.Angle → (i : Fin 2) → ℝ := fun t i ↦
    Fin.cases t.cos (fun _ ↦ t.sin) i
  have hc : Continuous c := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact Real.Angle.continuous_cos
    · exact Real.Angle.continuous_sin
  have heq : normalVector = (fun t ↦ WithLp.toLp 2 (c t)) := by
    funext t
    ext i
    fin_cases i <;> rfl
  rw [heq]
  exact (PiLp.continuous_toLp (2 : ENNReal) (fun _ : Fin 2 ↦ ℝ)).comp hc

private theorem isClosed_isExteriorNormal (K : ConvexBody Point) :
    IsClosed {z : Point × Real.Angle | IsExteriorNormal K z.1 z.2} := by
  change IsClosed {z : Point × Real.Angle |
    ∀ q ∈ (K : Set Point), inner ℝ (q - z.1) (normalVector z.2) ≤ 0}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro q
  apply isClosed_iInter
  intro _
  apply isClosed_le
  · exact (continuous_const.sub continuous_fst).inner
      (continuous_normalVector_angle.comp continuous_snd)
  · exact continuous_const

private def normalGraph (K : ConvexBody Point) : Set (Point × Real.Angle) :=
  {z | z.1 ∈ frontier (K : Set Point) ∧ IsExteriorNormal K z.1 z.2}

private theorem isCompact_normalGraph (K : ConvexBody Point) :
    IsCompact (normalGraph K) := by
  have hfront : IsCompact (frontier (K : Set Point)) := by
    apply K.isCompact.of_isClosed_subset isClosed_frontier
    simpa only [K.isClosed.closure_eq] using
      (frontier_subset_closure : frontier (K : Set Point) ⊆ closure (K : Set Point))
  have hclosed : IsClosed (normalGraph K) := by
    exact (isClosed_frontier.preimage continuous_fst).inter (isClosed_isExteriorNormal K)
  apply (hfront.prod isCompact_univ).of_isClosed_subset
  · exact hclosed
  · rintro ⟨p, a⟩ ⟨hp, _⟩
    exact ⟨hp, Set.mem_univ a⟩

private def normalDomain (K : ConvexBody Point) : Set Point :=
  Prod.fst '' normalGraph K

private theorem isCompact_normalDomain (K : ConvexBody Point) :
    IsCompact (normalDomain K) :=
  (isCompact_normalGraph K).image continuous_fst

private def separatedNormalPairs (K : ConvexBody Point) (n : ℕ) :
    Set (Point × (Real.Angle × Real.Angle)) :=
  {z | z.1 ∈ frontier (K : Set Point) ∧
    IsExteriorNormal K z.1 z.2.1 ∧ IsExteriorNormal K z.1 z.2.2 ∧
      (1 : ℝ) / (n + 1) ≤ dist z.2.1 z.2.2}

private theorem isCompact_separatedNormalPairs (K : ConvexBody Point) (n : ℕ) :
    IsCompact (separatedNormalPairs K n) := by
  have hfront : IsCompact (frontier (K : Set Point)) := by
    apply K.isCompact.of_isClosed_subset isClosed_frontier
    simpa only [K.isClosed.closure_eq] using
      (frontier_subset_closure : frontier (K : Set Point) ⊆ closure (K : Set Point))
  have hrel₁ : IsClosed {z : Point × (Real.Angle × Real.Angle) |
      IsExteriorNormal K z.1 z.2.1} :=
    (isClosed_isExteriorNormal K).preimage
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have hrel₂ : IsClosed {z : Point × (Real.Angle × Real.Angle) |
      IsExteriorNormal K z.1 z.2.2} :=
    (isClosed_isExteriorNormal K).preimage
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  have hsep : IsClosed {z : Point × (Real.Angle × Real.Angle) |
      (1 : ℝ) / (n + 1) ≤ dist z.2.1 z.2.2} := by
    exact isClosed_le continuous_const
      ((continuous_fst.comp continuous_snd).dist (continuous_snd.comp continuous_snd))
  have hfclosed : IsClosed {z : Point × (Real.Angle × Real.Angle) |
      z.1 ∈ frontier (K : Set Point)} :=
    isClosed_frontier.preimage continuous_fst
  have hclosed : IsClosed (separatedNormalPairs K n) := by
    have h := ((hfclosed.inter hrel₁).inter hrel₂).inter hsep
    simpa only [separatedNormalPairs, Set.inter_def, Set.mem_ofPred_eq, and_assoc] using h
  apply (hfront.prod (isCompact_univ.prod isCompact_univ)).of_isClosed_subset hclosed
  rintro ⟨p, a, b⟩ ⟨hp, _⟩
  exact ⟨hp, Set.mem_univ _, Set.mem_univ _⟩

private def separatedNormalPoints (K : ConvexBody Point) (n : ℕ) : Set Point :=
  Prod.fst '' separatedNormalPairs K n

private theorem isCompact_separatedNormalPoints (K : ConvexBody Point) (n : ℕ) :
    IsCompact (separatedNormalPoints K n) :=
  (isCompact_separatedNormalPairs K n).image continuous_fst

private theorem regularBoundary_eq_normalDomain_sdiff_iUnion (K : ConvexBody Point) :
    regularBoundary K = normalDomain K \ ⋃ n, separatedNormalPoints K n := by
  ext p
  constructor
  · rintro ⟨hp, a, ha, hua⟩
    refine ⟨⟨(p, a), ⟨hp, ha⟩, rfl⟩, ?_⟩
    intro hnonunique
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hnonunique
    obtain ⟨⟨q, b, c⟩, ⟨_, hb, hc, hdist⟩, rfl⟩ := hn
    rw [hua b hb, hua c hc, dist_self] at hdist
    have hpos : 0 < (1 : ℝ) / (n + 1) := by positivity
    linarith
  · rintro ⟨hdom, hnot⟩
    obtain ⟨⟨q, a⟩, ⟨hp, ha⟩, hqp⟩ := hdom
    change q = p at hqp
    subst q
    refine ⟨hp, a, ha, ?_⟩
    intro b hb
    by_contra hba
    have hdpos : 0 < dist a b := dist_pos.mpr (Ne.symm hba)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hdpos
    apply hnot
    apply Set.mem_iUnion.mpr
    refine ⟨n, ⟨(p, (a, b)), ?_, rfl⟩⟩
    exact ⟨hp, ha, hb, hn.le⟩

/-- Points with a unique exterior normal form a Borel set. -/
theorem measurableSet_regularBoundary (K : ConvexBody Point) :
    MeasurableSet (regularBoundary K) := by
  rw [regularBoundary_eq_normalDomain_sdiff_iUnion]
  exact (isCompact_normalDomain K).measurableSet.diff
    (MeasurableSet.iUnion fun n ↦ (isCompact_separatedNormalPoints K n).measurableSet)

/-- The exterior normal varies continuously on the regular boundary. -/
theorem continuousOn_exteriorNormalAngle_regularBoundary (K : ConvexBody Point) :
    ContinuousOn (exteriorNormalAngle K) (regularBoundary K) := by
  have hnormal (p : Point) (hp : p ∈ regularBoundary K) :
      IsExteriorNormal K p (exteriorNormalAngle K p) := by
    rcases hp.2 with ⟨a, ha, hua⟩
    dsimp only [exteriorNormalAngle]
    split
    · rename_i h
      exact h.exists.choose_spec
    · rename_i h
      exact (h ⟨a, ha, hua⟩).elim
  have hunique (p : Point) (hp : p ∈ regularBoundary K) (a : Real.Angle)
      (ha : IsExteriorNormal K p a) : a = exteriorNormalAngle K p := by
    rcases hp.2 with ⟨b, hb, hub⟩
    exact (hub a ha).trans (hub _ (hnormal p hp)).symm
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_of_isClosed_graph
  have hgraph : Function.graph ((regularBoundary K).domRestrict (exteriorNormalAngle K)) =
      {z : (regularBoundary K) × Real.Angle | IsExteriorNormal K z.1 z.2} := by
    ext z
    constructor
    · intro hz
      change exteriorNormalAngle K z.1 = z.2 at hz
      change IsExteriorNormal K z.1 z.2
      rw [← hz]
      exact hnormal z.1 z.1.2
    · intro hz
      change exteriorNormalAngle K z.1 = z.2
      exact (hunique z.1 z.1.2 z.2 hz).symm
  rw [hgraph]
  exact (isClosed_isExteriorNormal K).preimage
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

/-- The exterior normal is measurable for any measure restricted to the regular boundary. -/
theorem aemeasurable_exteriorNormalAngle_restrict_regularBoundary
    (K : ConvexBody Point) (μ : Measure Point) :
    AEMeasurable (exteriorNormalAngle K) (μ.restrict (regularBoundary K)) :=
  aemeasurable_restrict_of_measurable_subtype (measurableSet_regularBoundary K)
    (continuousOn_exteriorNormalAngle_regularBoundary K).domRestrict.measurable

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Segment
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- Two angular unit normals perpendicular to a nonzero planar vector are equal or antipodal. -/
theorem normalVector_eq_or_eq_add_pi_of_orthogonal
    {v : Point} (hv : v ≠ 0) {s t : Real.Angle}
    (hvs : inner ℝ v (normalVector s) = 0)
    (hvt : inner ℝ v (normalVector t) = 0) : s = t ∨ s = t + (Real.pi : Real.Angle) := by
  let o : Orientation ℝ Point (Fin 2) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  have hnorm (a : Real.Angle) : ‖normalVector a‖ = 1 := by
    induction a using Real.Angle.induction_on with
    | _ a =>
      rw [EuclideanSpace.norm_eq]
      simp [normalVector, frame, Fin.sum_univ_two]
  rcases EuclideanGeometry.eq_or_eq_neg_of_unit_orthogonal o hv (hnorm s) (hnorm t) hvs hvt with
    h | h
  · left
    induction s using Real.Angle.induction_on with
    | _ s =>
      induction t using Real.Angle.induction_on with
      | _ t =>
        apply Real.Angle.cos_sin_inj
        · exact congrFun (congrArg WithLp.ofLp h) 0
        · exact congrFun (congrArg WithLp.ofLp h) 1
  · right
    induction s using Real.Angle.induction_on with
    | _ s =>
      induction t using Real.Angle.induction_on with
      | _ t =>
        apply Real.Angle.cos_sin_inj
        · have h0 := congrFun (congrArg WithLp.ofLp h) 0
          simpa [normalVector, frame, Real.cos_add_pi] using h0
        · have h1 := congrFun (congrArg WithLp.ofLp h) 1
          simpa [normalVector, frame, Real.sin_add_pi] using h1

private theorem dirac_add_antipode_eq_of_orthogonal
    {v : Point} (hv : v ≠ 0) {s t : Real.Angle}
    (hvs : inner ℝ v (normalVector s) = 0)
    (hvt : inner ℝ v (normalVector t) = 0) :
    Measure.dirac s + Measure.dirac (s + (Real.pi : Real.Angle)) =
      Measure.dirac t + Measure.dirac (t + (Real.pi : Real.Angle)) := by
  rcases normalVector_eq_or_eq_add_pi_of_orthogonal hv hvs hvt with h | h
  · rw [h]
  · rw [h]
    have hpi : (t + (Real.pi : Real.Angle)) + (Real.pi : Real.Angle) = t := by
      rw [add_assoc, Real.Angle.coe_pi_add_coe_pi, add_zero]
    rw [hpi, add_comm]

/-- The atomic segment measure is independent of its segment presentation. -/
theorem segmentPresentation_measure_eq (K : ConvexBody Point)
    {d c : Point × Point × Real.Angle}
    (hd : IsSegmentPresentation K d) (hc : IsSegmentPresentation K c) :
    ENNReal.ofReal (dist d.1 d.2.1) •
        (Measure.dirac d.2.2 + Measure.dirac (d.2.2 + (Real.pi : Real.Angle))) =
      ENNReal.ofReal (dist c.1 c.2.1) •
        (Measure.dirac c.2.2 + Measure.dirac (c.2.2 + (Real.pi : Real.Angle))) := by
  have hseg : segment ℝ d.1 d.2.1 = segment ℝ c.1 c.2.1 := hd.2.1.symm.trans hc.2.1
  have hlen : dist d.1 d.2.1 = dist c.1 c.2.1 := EuclideanGeometry.dist_eq_of_segment_eq hseg
  have hcn : inner ℝ (d.2.1 - d.1) (normalVector c.2.2) = 0 :=
    EuclideanGeometry.inner_direction_eq_zero_of_segment_eq hseg hc.2.2
  rw [hlen, dirac_add_antipode_eq_of_orthogonal (sub_ne_zero.mpr hd.1.symm) hd.2.2 hcn]

/-- A singleton convex body has zero surface measure. -/
theorem surfaceAreaMeasure_eq_zero_of_subsingleton (K : ConvexBody Point)
    (hK : (K : Set Point).Subsingleton) :
    surfaceAreaMeasure K = 0 := by
  simp [surfaceAreaMeasure, hK]

private theorem surfaceAreaMeasure_eq_chosenSegment (K : ConvexBody Point)
    (hK : ¬(K : Set Point).Subsingleton) (hseg : ∃ d, IsSegmentPresentation K d) :
    surfaceAreaMeasure K =
      ENNReal.ofReal (dist hseg.choose.1 hseg.choose.2.1) •
        (Measure.dirac hseg.choose.2.2 +
          Measure.dirac (hseg.choose.2.2 + ((Real.pi : ℝ) : Real.Angle))) := by
  simp [surfaceAreaMeasure, hK, hseg]

/-- A nondegenerate segment presentation makes the represented convex body nonsingleton. -/
theorem not_subsingleton_of_isSegmentPresentation (K : ConvexBody Point)
    {d : Point × Point × Real.Angle} (hd : IsSegmentPresentation K d) :
    ¬(K : Set Point).Subsingleton := by
  intro hK
  apply hd.1
  apply hK
  · rw [hd.2.1]
    exact left_mem_segment ℝ _ _
  · rw [hd.2.1]
    exact right_mem_segment ℝ _ _

/-- The surface measure of a segment is its length times the two normal atoms. -/
theorem surfaceAreaMeasure_eq_segmentPresentation (K : ConvexBody Point)
    (d : Point × Point × Real.Angle) (hd : IsSegmentPresentation K d) :
    surfaceAreaMeasure K = ENNReal.ofReal (dist d.1 d.2.1) •
      (Measure.dirac d.2.2 + Measure.dirac (d.2.2 + (Real.pi : Real.Angle))) := by
  let hseg : ∃ c, IsSegmentPresentation K c := ⟨d, hd⟩
  rw [surfaceAreaMeasure_eq_chosenSegment K
    (not_subsingleton_of_isSegmentPresentation K hd) hseg]
  exact segmentPresentation_measure_eq K hseg.choose_spec hd

/-- The surface area measure of a singleton convex body is finite. -/
theorem isFiniteMeasure_surfaceAreaMeasure_of_subsingleton (K : ConvexBody Point)
    (hK : (K : Set Point).Subsingleton) :
    IsFiniteMeasure (surfaceAreaMeasure K) := by
  rw [surfaceAreaMeasure_eq_zero_of_subsingleton K hK]
  infer_instance

/-- The surface area measure of a convex body with a segment presentation is finite. -/
theorem isFiniteMeasure_surfaceAreaMeasure_of_segmentPresentation (K : ConvexBody Point)
    {d : Point × Point × Real.Angle} (hd : IsSegmentPresentation K d) :
    IsFiniteMeasure (surfaceAreaMeasure K) := by
  rw [surfaceAreaMeasure_eq_segmentPresentation K d hd]
  exact (Measure.dirac d.2.2 +
    Measure.dirac (d.2.2 + ((Real.pi : ℝ) : Real.Angle))).smul_finite
      ENNReal.ofReal_ne_top

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Segment Faces
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace MovingSofa

private theorem not_both_mem_short_angleArc {E : Set Real.Angle} {a b : ℝ}
    (hab : a ≤ b) (hshort : b < a + Real.pi)
    (hE : E ⊆ (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Icc a b)
    (t : Real.Angle) : ¬(t ∈ E ∧ t + (Real.pi : Real.Angle) ∈ E) := by
  rintro ⟨ht, htpi⟩
  obtain ⟨s, hs, hst⟩ := hE ht
  obtain ⟨u, hu, hut⟩ := hE htpi
  have hang : (u : Real.Angle) = ((s + Real.pi : ℝ) : Real.Angle) := by
    calc
      (u : Real.Angle) = t + (Real.pi : Real.Angle) := hut
      _ = (s : Real.Angle) + (Real.pi : Real.Angle) := by rw [← hst]
      _ = ((s + Real.pi : ℝ) : Real.Angle) := Real.Angle.coe_add _ _ |>.symm
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hang
  have hlow : -(2 * Real.pi) < u - (s + Real.pi) := by
    linarith [hs.1, hs.2, hu.1, hu.2]
  have hupp : u - (s + Real.pi) < 0 := by
    linarith [hs.1, hs.2, hu.1, hu.2]
  rw [hk] at hlow hupp
  have hkneg : (k : ℝ) < 0 := by nlinarith [Real.pi_pos]
  have hkgt : (-1 : ℝ) < k := by nlinarith [Real.pi_pos]
  rw [← Int.cast_zero] at hkneg
  have hcast_neg_one : (((-1 : ℤ) : ℝ)) = -1 := by norm_num
  rw [← hcast_neg_one] at hkgt
  have hkneg' : k < 0 := Int.cast_lt.mp hkneg
  have hkgt' : (-1 : ℤ) < k := Int.cast_lt.mp hkgt
  omega

/-- A normal perpendicular to a segment exposes the whole segment. -/
theorem exposedEdge_eq_segment_of_orthogonal (K : ConvexBody Point)
    (d : Point × Point × Real.Angle) (hd : IsSegmentPresentation K d)
    (t : Real.Angle) (ht : inner ℝ (d.2.1 - d.1) (normalVector t) = 0) :
    exposedEdge K t = (K : Set Point) := by
  have hfst : d.1 ∈ K := by
    change d.1 ∈ (K : Set Point)
    rw [hd.2.1]
    exact left_mem_segment ℝ _ _
  have hconst : ∀ p ∈ (K : Set Point),
      inner ℝ p (normalVector t) = inner ℝ d.1 (normalVector t) := by
    intro p hp
    rw [hd.2.1, segment_eq_image'] at hp
    obtain ⟨u, hu, rfl⟩ := hp
    rw [inner_add_left, inner_smul_left, ht, mul_zero, add_zero]
  have hsupport : supportValue K t = inner ℝ d.1 (normalVector t) := by
    apply le_antisymm
    · apply csSup_le (K.nonempty.image _)
      rintro _ ⟨p, hp, rfl⟩
      exact (hconst p hp).le
    · exact inner_le_supportValue K hfst t
  ext p
  constructor
  · exact fun hp ↦ hp.1
  · intro hp
    refine ⟨hp, ?_⟩
    change inner ℝ p (normalVector t) = supportValue K t
    rw [hconst p hp, hsupport]

private theorem exposedEdge_subset_endpoints_of_not_orthogonal (K : ConvexBody Point)
    (d : Point × Point × Real.Angle) (hd : IsSegmentPresentation K d)
    (t : Real.Angle) (ht : inner ℝ (d.2.1 - d.1) (normalVector t) ≠ 0) :
    exposedEdge K t ⊆ {d.1, d.2.1} := by
  have hfst : d.1 ∈ K := by
    change d.1 ∈ (K : Set Point)
    rw [hd.2.1]
    exact left_mem_segment ℝ _ _
  have hsnd : d.2.1 ∈ K := by
    change d.2.1 ∈ (K : Set Point)
    rw [hd.2.1]
    exact right_mem_segment ℝ _ _
  intro p hp
  have hpK : p ∈ segment ℝ d.1 d.2.1 := by
    rw [← hd.2.1]
    exact hp.1
  rw [segment_eq_image'] at hpK
  obtain ⟨u, hu, rfl⟩ := hpK
  have hx := inner_le_supportValue K hfst t
  have hy := inner_le_supportValue K hsnd t
  rw [← hp.2] at hx hy
  simp only [inner_add_left, inner_smul_left] at hx hy
  let c := inner ℝ (d.2.1 - d.1) (normalVector t)
  change inner ℝ d.1 (normalVector t) ≤
    inner ℝ d.1 (normalVector t) + u * c at hx
  change inner ℝ d.2.1 (normalVector t) ≤
    inner ℝ d.1 (normalVector t) + u * c at hy
  have hdiff : inner ℝ d.2.1 (normalVector t) =
      inner ℝ d.1 (normalVector t) + c := by
    dsimp only [c]
    rw [inner_sub_left]
    ring
  rw [hdiff] at hy
  have hc : c ≠ 0 := ht
  rcases lt_or_gt_of_ne hc with hcneg | hcpos
  · have hu0 : u = 0 := by
      apply le_antisymm _ hu.1
      by_contra hnot
      have hupos : 0 < u := lt_of_not_ge hnot
      nlinarith
    simp [hu0]
  · have hu1 : u = 1 := by
      apply le_antisymm hu.2
      by_contra hnot
      have hult : u < 1 := lt_of_not_ge hnot
      nlinarith
    simp [hu1]

/-- The face-union formula for a segment on an angular arc shorter than a half-turn. -/
theorem surfaceAreaMeasure_face_union_of_segmentPresentation
    (K : ConvexBody Point) (d : Point × Point × Real.Angle)
    (hd : IsSegmentPresentation K d) (E : Set Real.Angle) (hE : MeasurableSet E)
    {a b : ℝ} (hab : a ≤ b) (hshort : b < a + Real.pi)
    (hsubset : E ⊆ (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Icc a b) :
    surfaceAreaMeasure K E =
      Measure.hausdorffMeasure 1 (⋃ t ∈ E, exposedEdge K t) := by
  have hnotboth := not_both_mem_short_angleArc hab hshort hsubset d.2.2
  have hnormalPi :
      normalVector (d.2.2 + (Real.pi : Real.Angle)) = -normalVector d.2.2 := by
    induction d.2.2 using Real.Angle.induction_on with
    | _ t => simpa only [← Real.Angle.coe_add] using normalVector_add_pi t
  have hpiorth :
      inner ℝ (d.2.1 - d.1)
        (normalVector (d.2.2 + (Real.pi : Real.Angle))) = 0 := by
    rw [hnormalPi, inner_neg_right, hd.2.2, neg_zero]
  by_cases hn : d.2.2 ∈ E
  · have hnpi : d.2.2 + (Real.pi : Real.Angle) ∉ E := fun hnpi ↦ hnotboth ⟨hn, hnpi⟩
    have hunion : (⋃ t ∈ E, exposedEdge K t) = (K : Set Point) := by
      apply Set.Subset.antisymm
      · intro p hp
        obtain ⟨t, ht, hpt⟩ := Set.mem_iUnion₂.mp hp
        exact hpt.1
      · intro p hp
        exact Set.mem_iUnion₂.mpr ⟨d.2.2, hn, by
          rw [exposedEdge_eq_segment_of_orthogonal K d hd d.2.2 hd.2.2]
          exact hp⟩
    rw [surfaceAreaMeasure_eq_segmentPresentation K d hd, hunion, hd.2.1]
    simp [hE, hn, hnpi, edist_dist]
  · by_cases hnpi : d.2.2 + (Real.pi : Real.Angle) ∈ E
    · have hunion : (⋃ t ∈ E, exposedEdge K t) = (K : Set Point) := by
        apply Set.Subset.antisymm
        · intro p hp
          obtain ⟨t, ht, hpt⟩ := Set.mem_iUnion₂.mp hp
          exact hpt.1
        · intro p hp
          exact Set.mem_iUnion₂.mpr ⟨d.2.2 + (Real.pi : Real.Angle), hnpi, by
            rw [exposedEdge_eq_segment_of_orthogonal K d hd _ hpiorth]
            exact hp⟩
      rw [surfaceAreaMeasure_eq_segmentPresentation K d hd, hunion, hd.2.1]
      simp [hE, hn, hnpi, edist_dist]
    · have hunion : (⋃ t ∈ E, exposedEdge K t) ⊆ {d.1, d.2.1} := by
        intro p hp
        obtain ⟨t, ht, hpt⟩ := Set.mem_iUnion₂.mp hp
        have htorth : inner ℝ (d.2.1 - d.1) (normalVector t) ≠ 0 := by
          intro hortho
          rcases normalVector_eq_or_eq_add_pi_of_orthogonal
              (sub_ne_zero.mpr hd.1.symm) hortho hd.2.2 with h | h
          · exact hn (h ▸ ht)
          · exact hnpi (h ▸ ht)
        exact exposedEdge_subset_endpoints_of_not_orthogonal K d hd t htorth hpt
      rw [surfaceAreaMeasure_eq_segmentPresentation K d hd]
      have hzero : Measure.hausdorffMeasure 1 (⋃ t ∈ E, exposedEdge K t) = 0 := by
        let _ := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
        exact measure_mono_null hunion
          ((Set.finite_singleton d.2.1).insert d.1 |>.measure_zero _)
      rw [hzero]
      simp [hE, hn, hnpi]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Segment Graph
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- A singleton convex body has equal horizontal projection bounds. -/
theorem horizontalBounds_eq_of_subsingleton (K : ConvexBody Point)
    (hK : (K : Set Point).Subsingleton) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) :
    (horizontalBounds K o e).1 = (horizontalBounds K o e).2 := by
  obtain ⟨p, hp⟩ := K.nonempty
  have hset : (K : Set Point) = {p} :=
    Set.eq_singleton_iff_unique_mem.mpr ⟨hp, fun x hx ↦ hK hx hp⟩
  simp [horizontalBounds, horizontalProjection, hset]

/-- Every surface-area integral of a singleton convex body vanishes. -/
theorem surfaceAreaMeasure_integral_eq_zero_of_subsingleton (K : ConvexBody Point)
    (hK : (K : Set Point).Subsingleton) (ψ : Real.Angle → ℝ) :
    (∫ t, ψ t ∂surfaceAreaMeasure K) = 0 := by
  rw [surfaceAreaMeasure_eq_zero_of_subsingleton K hK]
  simp

private theorem horizontalProjection_segment (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {a b : Point}
    (hK : (K : Set Point) = segment ℝ a b) :
    horizontalProjection K o e = Set.uIcc (e (a - o) 0) (e (b - o) 0) := by
  rw [horizontalProjection, hK, segment_eq_image']
  calc
    (fun p : Point ↦ e (p - o) 0) ''
        ((fun t : ℝ ↦ a + t • (b - a)) '' Set.Icc 0 1) =
        (fun t : ℝ ↦ e (a - o) 0 + t * (e (b - o) 0 - e (a - o) 0)) ''
          Set.Icc 0 1 := by
      rw [Set.image_image]
      congr 1
      funext t
      simp only [map_sub, map_add, map_smul, PiLp.add_apply,
        PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    _ = segment ℝ (e (a - o) 0) (e (b - o) 0) :=
      (segment_eq_image' ℝ (e (a - o) 0) (e (b - o) 0)).symm
    _ = Set.uIcc (e (a - o) 0) (e (b - o) 0) := segment_eq_uIcc _ _

private theorem horizontalBounds_segment (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {a b : Point}
    (hK : (K : Set Point) = segment ℝ a b) :
    horizontalBounds K o e =
      (min (e (a - o) 0) (e (b - o) 0), max (e (a - o) 0) (e (b - o) 0)) := by
  rw [horizontalBounds, horizontalProjection_segment K o e hK]
  simp [Set.uIcc, csInf_Icc, csSup_Icc]

private theorem coordinate_normal_second_eq_zero_of_horizontalBounds_eq
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    (d : Point × Point × Real.Angle) (hd : IsSegmentPresentation K d)
    (hbounds : (horizontalBounds K o e).1 = (horizontalBounds K o e).2) :
    e (normalVector d.2.2) 1 = 0 := by
  have hb := horizontalBounds_segment K o e hd.2.1
  rw [hb] at hbounds
  dsimp only at hbounds
  have hx : e (d.1 - o) 0 = e (d.2.1 - o) 0 := by
    have hle₁ := min_le_left (e (d.1 - o) 0) (e (d.2.1 - o) 0)
    have hle₂ := min_le_right (e (d.1 - o) 0) (e (d.2.1 - o) 0)
    have hge₁ := le_max_left (e (d.1 - o) 0) (e (d.2.1 - o) 0)
    have hge₂ := le_max_right (e (d.1 - o) 0) (e (d.2.1 - o) 0)
    linarith
  have hdir0 : e (d.2.1 - d.1) 0 = 0 := by
    simp only [map_sub, PiLp.sub_apply] at hx ⊢
    linarith
  have hdir_ne : e (d.2.1 - d.1) 1 ≠ 0 := by
    intro h
    have hz : d.2.1 - d.1 = 0 := e.injective (by
      simp only [map_zero]
      ext i
      fin_cases i
      · exact hdir0
      · exact h)
    exact hd.1.symm (sub_eq_zero.mp hz)
  have hinner : inner ℝ (e (d.2.1 - d.1)) (e (normalVector d.2.2)) = 0 := by
    rw [e.inner_map_map]
    exact hd.2.2
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two,
    hdir0, mul_zero, zero_add] at hinner
  exact (mul_eq_zero.mp hinner).resolve_right hdir_ne

/-- A segment with zero horizontal width contributes zero against weights supported on
normals with positive vertical coordinate. -/
theorem segment_integral_eq_zero_of_horizontalBounds_eq
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    (ψ : Real.Angle → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hsupport : ∀ t, e (normalVector t) 1 < ε → ψ t = 0)
    (d : Point × Point × Real.Angle) (hd : IsSegmentPresentation K d)
    (hbounds : (horizontalBounds K o e).1 = (horizontalBounds K o e).2) :
    (∫ t, ψ t ∂surfaceAreaMeasure K) = 0 := by
  have hn := coordinate_normal_second_eq_zero_of_horizontalBounds_eq K o e d hd hbounds
  have hψn : ψ d.2.2 = 0 := hsupport d.2.2 (by linarith)
  have hnpi : e (normalVector (d.2.2 + (Real.pi : Real.Angle))) 1 = 0 := by
    have hv : normalVector (d.2.2 + (Real.pi : Real.Angle)) = -normalVector d.2.2 := by
      induction d.2.2 using Real.Angle.induction_on with
      | _ t => simpa only [← Real.Angle.coe_add] using normalVector_add_pi t
    rw [hv, map_neg, PiLp.neg_apply, hn, neg_zero]
  have hψnpi : ψ (d.2.2 + (Real.pi : Real.Angle)) = 0 :=
    hsupport _ (by rw [hnpi]; exact hε)
  rw [surfaceAreaMeasure_eq_segmentPresentation K d hd]
  rw [MeasureTheory.integral_smul_measure]
  rw [MeasureTheory.integral_add_measure (MeasureTheory.integrable_dirac (by finiteness))
    (MeasureTheory.integrable_dirac (by finiteness))]
  simp [hψn, hψnpi]

private theorem upperGraphHeight_segment_of_lt (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {a b : Point}
    (hK : (K : Set Point) = segment ℝ a b)
    (hab : e (a - o) 0 < e (b - o) 0) {x : ℝ}
    (hx : x ∈ Set.Icc (e (a - o) 0) (e (b - o) 0)) :
    upperGraphHeight K o e x = e (a - o) 1 +
      ((x - e (a - o) 0) / (e (b - o) 0 - e (a - o) 0)) *
        (e (b - o) 1 - e (a - o) 1) := by
  let t := (x - e (a - o) 0) / (e (b - o) 0 - e (a - o) 0)
  let y := e (a - o) 1 + t * (e (b - o) 1 - e (a - o) 1)
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hab.le)
    · exact (div_le_one (sub_pos.mpr hab)).mpr (by linarith [hx.2])
  have hfiber : {z : ℝ | o + e.symm !₂[x, z] ∈ (K : Set Point)} = {y} := by
    ext z
    rw [Set.mem_ofPred_eq, hK, segment_eq_image', Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨r, hr, heq⟩
      have heq' := congrArg (fun p : Point ↦ e (p - o)) heq
      have heq0 := congrFun (congrArg WithLp.ofLp heq') 0
      have heq1 := congrFun (congrArg WithLp.ofLp heq') 1
      have hrt : r = t := by
        dsimp [t]
        simp only [map_sub, map_add, map_smul, LinearIsometryEquiv.apply_symm_apply,
          PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, Matrix.cons_val_zero,
          smul_eq_mul] at heq0
        simp at heq0
        apply (eq_div_iff (sub_ne_zero.mpr hab.ne')).mpr
        simp only [map_sub, PiLp.sub_apply]
        linarith
      dsimp [y]
      rw [← hrt]
      simp only [map_sub, map_add, map_smul, LinearIsometryEquiv.apply_symm_apply,
          PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, Matrix.cons_val_one,
          smul_eq_mul] at heq1
      simp at heq1
      simp only [map_sub, PiLp.sub_apply]
      linarith
    · intro hzy
      subst z
      refine ⟨t, ht, ?_⟩
      apply e.injective
      ext i
      fin_cases i
      · have hdx : e b 0 - e a 0 ≠ 0 := by
          simp only [map_sub, PiLp.sub_apply] at hab
          linarith
        simp only [map_add, map_sub, LinearIsometryEquiv.apply_symm_apply, map_smul,
          PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
        simp
        dsimp [t]
        simp only [map_sub, PiLp.sub_apply]
        field_simp [hdx]
        ring
      · simp only [map_add, map_sub, LinearIsometryEquiv.apply_symm_apply, map_smul,
          PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
        simp
        dsimp [y]
        simp only [map_sub, PiLp.sub_apply]
        ring
  rw [upperGraphHeight, hfiber, csSup_singleton]

private theorem deriv_upperGraphHeight_segment_of_lt (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {a b : Point}
    (hK : (K : Set Point) = segment ℝ a b)
    (hab : e (a - o) 0 < e (b - o) 0) {x : ℝ}
    (hx : x ∈ Set.Ioo (e (a - o) 0) (e (b - o) 0)) :
    deriv (upperGraphHeight K o e) x =
      (e (b - o) 1 - e (a - o) 1) / (e (b - o) 0 - e (a - o) 0) := by
  let g : ℝ → ℝ := fun y ↦ e (a - o) 1 +
    ((y - e (a - o) 0) / (e (b - o) 0 - e (a - o) 0)) *
      (e (b - o) 1 - e (a - o) 1)
  have hg : HasDerivAt g
      ((e (b - o) 1 - e (a - o) 1) / (e (b - o) 0 - e (a - o) 0)) x := by
    dsimp [g]
    have hsub : HasDerivAt (fun y : ℝ ↦ y - e (a - o) 0) 1 x :=
      (hasDerivAt_id x).sub_const _
    have hdiv := HasDerivAt.div_const hsub (e (b - o) 0 - e (a - o) 0)
    have hmul := HasDerivAt.mul_const hdiv (e (b - o) 1 - e (a - o) 1)
    convert hmul.const_add (e (a - o) 1) using 1
    all_goals ring
  have heq : upperGraphHeight K o e =ᶠ[nhds x] g := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact upperGraphHeight_segment_of_lt K o e hK hab ⟨hy.1.le, hy.2.le⟩
  exact (hg.congr_of_eventuallyEq heq).deriv

private theorem segment_graph_normal (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) {a b : Point}
    (hab : e (a - o) 0 < e (b - o) 0) :
    let m := (e (b - o) 1 - e (a - o) 1) / (e (b - o) 0 - e (a - o) 0)
    let q := e.symm !₂[-m, 1]
    q ≠ 0 ∧ inner ℝ (b - a) q = 0 ∧
      e (normalVector (vectorNormalAngle q)) 1 = ‖q‖⁻¹ ∧
      dist a b = (e (b - o) 0 - e (a - o) 0) * ‖q‖ := by
  dsimp only
  let m := (e (b - o) 1 - e (a - o) 1) / (e (b - o) 0 - e (a - o) 0)
  let q := e.symm !₂[-m, 1]
  have hq : q ≠ 0 := by
    intro h
    have h1 := congrFun (congrArg WithLp.ofLp (congrArg e h)) 1
    simp [q] at h1
  have hdx : 0 < e (b - o) 0 - e (a - o) 0 := sub_pos.mpr hab
  have hden : e b 0 - e a 0 ≠ 0 := by
    simp only [map_sub, PiLp.sub_apply] at hab
    linarith
  have horth : inner ℝ (b - a) q = 0 := by
    rw [← e.inner_map_map]
    simp only [q, m, LinearIsometryEquiv.apply_symm_apply, PiLp.inner_apply,
      RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, map_sub, PiLp.sub_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp [hden]
    ring
  have hup : e (normalVector (vectorNormalAngle q)) 1 = ‖q‖⁻¹ := by
    rw [normalVector_vectorNormalAngle hq, map_smul, PiLp.smul_apply]
    simp [q]
  have hlen : dist a b = (e (b - o) 0 - e (a - o) 0) * ‖q‖ := by
    rw [dist_eq_norm, ← e.norm_map]
    have hv : e (b - a) = (e (b - o) 0 - e (a - o) 0) • !₂[1, m] := by
      ext i
      fin_cases i
      · simp [m]
      · simp [m]
        field_simp [hden]
    rw [show a - b = -(b - a) by module, map_neg, norm_neg, hv, norm_smul,
      Real.norm_eq_abs, abs_of_pos hdx]
    congr 1
    rw [← e.norm_map q, LinearIsometryEquiv.apply_symm_apply]
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp [m, Real.norm_eq_abs, pow_two]
    ring
  exact ⟨hq, horth, hup, hlen⟩

private theorem segment_graph_integrand_ae (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ) {a b : Point}
    (hK : (K : Set Point) = segment ℝ a b)
    (hab : e (a - o) 0 < e (b - o) 0) :
    let m := (e (b - o) 1 - e (a - o) 1) / (e (b - o) 0 - e (a - o) 0)
    let q := e.symm !₂[-m, 1]
    upperGraphSurfaceIntegrand K o e ψ =ᵐ[
        volume.restrict (Set.Icc (e (a - o) 0) (e (b - o) 0))]
      fun _ ↦ ψ (vectorNormalAngle q) * ‖q‖ := by
  dsimp only
  let m := (e (b - o) 1 - e (a - o) 1) / (e (b - o) 0 - e (a - o) 0)
  let q := e.symm !₂[-m, 1]
  have hnormq : Real.sqrt (1 + m ^ 2) = ‖q‖ := by
    rw [← e.norm_map q, LinearIsometryEquiv.apply_symm_apply, EuclideanSpace.norm_eq]
    congr 1
    simp [Fin.sum_univ_two, Real.norm_eq_abs, pow_two]
    ring
  rw [← restrict_Ioo_eq_restrict_Icc]
  refine ae_restrict_of_forall_mem measurableSet_Ioo fun x hx ↦ ?_
  rw [upperGraphSurfaceIntegrand,
    deriv_upperGraphHeight_segment_of_lt K o e hK hab hx]
  change ψ (vectorNormalAngle q) * Real.sqrt (1 + m ^ 2) = _
  rw [hnormq]

private theorem integrable_segment_graph (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ) {a b : Point}
    (hK : (K : Set Point) = segment ℝ a b)
    (hab : e (a - o) 0 < e (b - o) 0) :
    Integrable (upperGraphSurfaceIntegrand K o e ψ)
      (volume.restrict (Set.Icc (e (a - o) 0) (e (b - o) 0))) := by
  have hae := segment_graph_integrand_ae K o e ψ hK hab
  have hc : Integrable (fun _ : ℝ ↦ ψ (vectorNormalAngle
      (e.symm !₂[-((e (b - o) 1 - e (a - o) 1) /
        (e (b - o) 0 - e (a - o) 0)), 1])) *
      ‖e.symm !₂[-((e (b - o) 1 - e (a - o) 1) /
        (e (b - o) 0 - e (a - o) 0)), 1]‖)
      (volume.restrict (Set.Icc (e (a - o) 0) (e (b - o) 0))) := integrable_const _
  exact hc.congr hae.symm

private theorem segment_graph_integral (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ) {a b : Point}
    (hK : (K : Set Point) = segment ℝ a b)
    (hab : e (a - o) 0 < e (b - o) 0) {ε : ℝ} (hε : 0 < ε)
    (hsupport : ∀ t, e (normalVector t) 1 < ε → ψ t = 0) :
    (∫ t, ψ t ∂surfaceAreaMeasure K) =
      ∫ x in Set.Icc (e (a - o) 0) (e (b - o) 0),
        upperGraphSurfaceIntegrand K o e ψ x := by
  let m := (e (b - o) 1 - e (a - o) 1) / (e (b - o) 0 - e (a - o) 0)
  let q := e.symm !₂[-m, 1]
  let t := vectorNormalAngle q
  obtain ⟨hq, horth, hup, hlen⟩ := segment_graph_normal o e hab
  have hd : IsSegmentPresentation K (a, b, t) := by
    refine ⟨?_, hK, ?_⟩
    · intro heq
      have := hab
      simp only at heq
      rw [heq] at this
      exact this.false
    · dsimp [t]
      rw [normalVector_vectorNormalAngle hq, inner_smul_right, horth, mul_zero]
  have hqnorm : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have hdowncoord : e (normalVector (t + (Real.pi : Real.Angle))) 1 = -‖q‖⁻¹ := by
    have hv : normalVector (t + (Real.pi : Real.Angle)) = -normalVector t := by
      induction t using Real.Angle.induction_on with
      | _ t => simpa only [← Real.Angle.coe_add] using normalVector_add_pi t
    rw [hv, map_neg, PiLp.neg_apply]
    exact congrArg Neg.neg hup
  have hdown : ψ (t + (Real.pi : Real.Angle)) = 0 :=
    hsupport _ (by
      rw [hdowncoord]
      have hinv : 0 < ‖q‖⁻¹ := inv_pos.mpr hqnorm
      linarith)
  have hlhs : (∫ u, ψ u ∂surfaceAreaMeasure K) = dist a b * ψ t := by
    rw [surfaceAreaMeasure_eq_segmentPresentation K (a, b, t) hd]
    rw [MeasureTheory.integral_smul_measure]
    rw [MeasureTheory.integral_add_measure (MeasureTheory.integrable_dirac (by finiteness))
      (MeasureTheory.integrable_dirac (by finiteness))]
    simp [hdown, ENNReal.toReal_ofReal (dist_nonneg : 0 ≤ dist a b)]
  rw [hlhs, hlen]
  have hae := segment_graph_integrand_ae K o e ψ hK hab
  rw [integral_congr_ae hae]
  have hdx : 0 ≤ e (b - o) 0 - e (a - o) 0 := sub_nonneg.mpr hab.le
  have hdx' : 0 ≤ e b 0 - e a 0 := by
    simp only [map_sub, PiLp.sub_apply] at hdx
    linarith
  simp only [Fin.isValue, map_sub, PiLp.sub_apply, sub_sub_sub_cancel_right, norm_map,
    integral_const, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter,
    Real.volume_real_Icc, smul_eq_mul, t, q, m]
  rw [max_eq_left hdx']
  ring

/-- The surface-area integral of a nonvertical segment agrees with its upper
graph integral. -/
theorem segment_graph_formula (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hsupport : ∀ t, e (normalVector t) 1 < ε → ψ t = 0)
    (d : Point × Point × Real.Angle) (hd : IsSegmentPresentation K d)
    (hbounds : (horizontalBounds K o e).1 < (horizontalBounds K o e).2) :
    Integrable (upperGraphSurfaceIntegrand K o e ψ)
        (volume.restrict (Set.Icc (horizontalBounds K o e).1
          (horizontalBounds K o e).2)) ∧
      (∫ t, ψ t ∂surfaceAreaMeasure K) =
        ∫ x in Set.Icc (horizontalBounds K o e).1 (horizontalBounds K o e).2,
          upperGraphSurfaceIntegrand K o e ψ x := by
  rw [horizontalBounds_segment K o e hd.2.1] at hbounds ⊢
  dsimp only at hbounds ⊢
  have hne : e (d.1 - o) 0 ≠ e (d.2.1 - o) 0 := by
    intro heq
    simp only [map_sub, PiLp.sub_apply] at heq hbounds
    rw [heq, min_self, max_self] at hbounds
    exact hbounds.false
  rcases lt_or_gt_of_ne hne with hab | hba
  · rw [min_eq_left hab.le, max_eq_right hab.le] at hbounds ⊢
    exact ⟨integrable_segment_graph K o e ψ hd.2.1 hbounds,
      segment_graph_integral K o e ψ hd.2.1 hbounds hε hsupport⟩
  · rw [min_eq_right hba.le, max_eq_left hba.le] at hbounds ⊢
    have hK' : (K : Set Point) = segment ℝ d.2.1 d.1 := by
      rw [segment_symm]
      exact hd.2.1
    exact ⟨integrable_segment_graph K o e ψ hK' hbounds,
      segment_graph_integral K o e ψ hK' hbounds hε hsupport⟩

/-- A nonsingleton planar convex body with empty interior has a segment presentation. -/
theorem exists_segmentPresentation_of_interior_empty (K : ConvexBody Point)
    (hsub : ¬(K : Set Point).Subsingleton) (hint : interior (K : Set Point) = ∅) :
    ∃ d, IsSegmentPresentation K d := by
  obtain ⟨a, b, hab, hK⟩ := K.exists_eq_segment_of_interior_empty hsub hint
  let orient : Orientation ℝ Point (Fin 2) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  let _ : Fact (Module.finrank ℝ Point = 2) := ⟨by simp [Point]⟩
  let n := ‖b - a‖⁻¹ • orient.rotation (Real.pi / 2 : ℝ) (b - a)
  have hvnorm : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm)
  have hn : ‖n‖ = 1 := by
    rw [norm_smul, (orient.rotation (Real.pi / 2 : ℝ)).norm_map]
    simp [hvnorm.ne']
  obtain ⟨t, ht⟩ := exists_angle_normalVector_eq hn
  refine ⟨(a, b, t), hab, hK, ?_⟩
  rw [ht]
  exact orient.inner_smul_rotation_pi_div_two_right (b - a) ‖b - a‖⁻¹

end MovingSofa

end

end

end

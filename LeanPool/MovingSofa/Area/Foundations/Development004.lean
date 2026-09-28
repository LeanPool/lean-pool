/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Area.Foundations.Development001
public import LeanPool.MovingSofa.Convex.Foundations.Development004

public import LeanPool.MovingSofa.Convex.Foundations.Development001
/-!
# Moving sofa: related mathematical developments

* `Area.Mamikon.Basic`.
* `Area.Variation`.
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
# Area / Mamikon / Basic
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The signed area between the convex boundary arc and a path on its supporting lines. -/
def mamikonFunctional (K : ConvexBody Point) (a b : ℝ)
    (hab : a < b) (_hba : b < a + Real.pi) (z : ContinuousBVPaths a b)
    (_hz : ∀ t : Set.Icc a b,
      z.val t ∈ (supportingLineHalfPlane K (t.val : Real.Angle)).1) : ℝ :=
  segmentArea (edgeVertices K (a : Real.Angle)).1
      (z.val ⟨a, le_rfl, hab.le⟩) +
    curveAreaFunctional z +
    segmentArea (z.val ⟨b, hab.le, le_rfl⟩)
      (edgeVertices K (b : Real.Angle)).2 -
    convexArcArea K a b

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
# Area / Variation
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped unitInterval

namespace MovingSofa

/-- Coordinatewise convex combination of two pairs of planar points. -/
def pointPairCombination (t : I) (x y : Point × Point) : Point × Point :=
  ((1 - (t : ℝ)) • x.1 + (t : ℝ) • y.1,
    (1 - (t : ℝ)) • x.2 + (t : ℝ) • y.2)

theorem segmentArea_variation :
    IsQuadraticFunctional pointPairCombination (fun x ↦ segmentArea x.1 x.2) ∧
    ∀ p q p' q' : Point,
      convexDirectionalDerivative pointPairCombination (fun x ↦ segmentArea x.1 x.2)
        (p, q) (p', q') =
      (planeCrossProduct (p' + q') (q - p) - 2 * planeCrossProduct p q) / 2 +
        (segmentArea q q' - segmentArea p p') := by
  let h : (Point × Point) → (Point × Point) → ℝ := fun x y ↦
    (planeCrossProduct x.1 y.2 + planeCrossProduct y.1 x.2) / 4
  have hh : IsConvexBilinear pointPairCombination pointPairCombination realCombination h := by
    constructor <;> intro x t y z <;>
      simp [h, pointPairCombination, realCombination, planeCrossProduct] <;> ring
  have hf (x : Point × Point) : segmentArea x.1 x.2 = h x x := by
    simp only [h, segmentArea]
    ring
  refine ⟨⟨h, hh, hf⟩, ?_⟩
  intro p q p' q'
  rw [(quadratic_directional_derivative pointPairCombination _ h hh hf).2.1]
  simp [h, segmentArea, planeCrossProduct]
  ring

/-- The pointwise convex combination of two continuous BV paths. -/
def bvPathCombination {a b : ℝ} (t : I) (x y : ContinuousBVPaths a b) :
    ContinuousBVPaths a b :=
  (1 - (t : ℝ)) • x + (t : ℝ) • y

private theorem coordinate_measure_smul_add_smul {a b : ℝ} (hab : a ≤ b) (r s : ℝ)
    (x y : ContinuousBVPaths a b) (i : Fin 2) :
    intervalStieltjesMeasure (continuousBVCoordinate (r • x + s • y) i) =
      r • intervalStieltjesMeasure (continuousBVCoordinate x i) +
        s • intervalStieltjesMeasure (continuousBVCoordinate y i) := by
  obtain ⟨F, hF, hμ⟩ := intervalStieltjes_linear_combination a b
    (continuousBVCoordinate x i) (continuousBVCoordinate y i) r s
  rw [← hμ]
  refine congrArg _ (RightContinuousIntervalBV.toFun_injective (funext fun u ↦ ?_))
  simpa [continuousBVCoordinate] using (hF u).symm

private def coordinateIntegral {a b : ℝ} (x y : ContinuousBVPaths a b) (i j : Fin 2) : ℝ :=
  intervalStieltjesIntegral (continuousBVCoordinate y j) (fun t ↦ x.val t i) univ

private theorem coordinateIntegral_smul_add_smul_right {a b : ℝ} (hab : a ≤ b) (r s : ℝ)
    (x y z : ContinuousBVPaths a b) (i j : Fin 2) :
    coordinateIntegral x (r • y + s • z) i j =
      r * coordinateIntegral x y i j + s * coordinateIntegral x z i j := by
  have hi (w : ContinuousBVPaths a b) :
      (intervalStieltjesMeasure (continuousBVCoordinate w j)).Integrable (fun s ↦ x.val s i) :=
    RightContinuousIntervalBV.integrable_of_continuous _
      ((PiLp.continuous_apply 2 _ i).comp x.property.1)
  unfold coordinateIntegral intervalStieltjesIntegral
  simp only [VectorMeasure.restrict_univ]
  rw [coordinate_measure_smul_add_smul hab, VectorMeasure.integral_add_vectorMeasure
    ((hi y).smul_vectorMeasure _) ((hi z).smul_vectorMeasure _)]
  simp only [VectorMeasure.integral_smul_vectorMeasure, smul_eq_mul]

private theorem coordinateIntegral_smul_add_smul_left {a b : ℝ} (r s : ℝ)
    (x y z : ContinuousBVPaths a b) (i j : Fin 2) :
    coordinateIntegral (r • x + s • y) z i j =
      r * coordinateIntegral x z i j + s * coordinateIntegral y z i j := by
  have hi (w : ContinuousBVPaths a b) :
      (intervalStieltjesMeasure (continuousBVCoordinate z j)).Integrable (fun s ↦ w.val s i) :=
    RightContinuousIntervalBV.integrable_of_continuous _
      ((PiLp.continuous_apply 2 _ i).comp w.property.1)
  unfold coordinateIntegral intervalStieltjesIntegral
  simp only [VectorMeasure.restrict_univ]
  change (∫ᵛ u, r • x.val u i + s • y.val u i
    ∂[ContinuousLinearMap.mul ℝ ℝ; intervalStieltjesMeasure (continuousBVCoordinate z j)]) = _
  have hadd := VectorMeasure.integral_fun_add (B := ContinuousLinearMap.mul ℝ ℝ)
    ((hi x).smul r) ((hi y).smul s)
  simp only [Pi.smul_apply, VectorMeasure.integral_fun_smul] at hadd
  simpa only [smul_eq_mul] using hadd

private theorem coordinateIntegral_combination_right {a b : ℝ} (hab : a ≤ b)
    (t : I) (x y z : ContinuousBVPaths a b) (i j : Fin 2) :
    coordinateIntegral x (bvPathCombination t y z) i j =
      (1 - (t : ℝ)) * coordinateIntegral x y i j + (t : ℝ) * coordinateIntegral x z i j :=
  coordinateIntegral_smul_add_smul_right hab _ _ x y z i j

private theorem coordinateIntegral_combination_left {a b : ℝ}
    (t : I) (x y z : ContinuousBVPaths a b) (i j : Fin 2) :
    coordinateIntegral (bvPathCombination t x y) z i j =
      (1 - (t : ℝ)) * coordinateIntegral x z i j + (t : ℝ) * coordinateIntegral y z i j :=
  coordinateIntegral_smul_add_smul_left _ _ x y z i j

private theorem coordinateIntegral_difference {a b : ℝ} (x y : ContinuousBVPaths a b)
    (i j : Fin 2) :
    intervalStieltjesIntegral (continuousBVCoordinate x j) (fun t ↦ y.val t i - x.val t i) univ =
      coordinateIntegral y x i j - coordinateIntegral x x i j := by
  unfold coordinateIntegral intervalStieltjesIntegral
  simp only [VectorMeasure.restrict_univ]
  exact VectorMeasure.integral_fun_sub
    (RightContinuousIntervalBV.integrable_of_continuous _
      ((PiLp.continuous_apply 2 _ i).comp y.property.1))
    (RightContinuousIntervalBV.integrable_of_continuous _
      ((PiLp.continuous_apply 2 _ i).comp x.property.1))

private theorem curveArea_quadratic_derivative (a b : ℝ) (hab : a ≤ b) :
    IsQuadraticFunctional bvPathCombination (@curveAreaFunctional a b) ∧
    ∀ x y : ContinuousBVPaths a b,
      convexDirectionalDerivative bvPathCombination curveAreaFunctional x y =
        (coordinateIntegral x y 0 1 - coordinateIntegral x y 1 0 +
          (coordinateIntegral y x 0 1 - coordinateIntegral y x 1 0) -
          2 * (coordinateIntegral x x 0 1 - coordinateIntegral x x 1 0)) / 2 := by
  let h : ContinuousBVPaths a b → ContinuousBVPaths a b → ℝ := fun x y ↦
    (coordinateIntegral x y 0 1 - coordinateIntegral x y 1 0) / 2
  have hh : IsConvexBilinear bvPathCombination bvPathCombination realCombination h := by
    constructor
    · intro x t y z
      dsimp only [h]
      rw [coordinateIntegral_combination_right hab, coordinateIntegral_combination_right hab]
      simp only [realCombination]
      ring
    · intro x t y z
      dsimp only [h]
      rw [coordinateIntegral_combination_left, coordinateIntegral_combination_left]
      simp only [realCombination]
      ring
  have hf (x : ContinuousBVPaths a b) : curveAreaFunctional x = h x x := rfl
  refine ⟨⟨h, hh, hf⟩, ?_⟩
  intro x y
  rw [(quadratic_directional_derivative bvPathCombination _ h hh hf).2.1]
  dsimp only [h]
  ring

theorem curveArea_variation (a b : ℝ) (hab : a ≤ b) :
    IsQuadraticFunctional bvPathCombination (@curveAreaFunctional a b) ∧
    ∀ x y : ContinuousBVPaths a b,
      convexDirectionalDerivative bvPathCombination curveAreaFunctional x y =
      intervalStieltjesIntegral (continuousBVCoordinate x 1)
          (fun t ↦ y.val t 0 - x.val t 0) Set.univ -
        intervalStieltjesIntegral (continuousBVCoordinate x 0)
          (fun t ↦ y.val t 1 - x.val t 1) Set.univ +
        (segmentArea (x.val ⟨b, hab, le_rfl⟩) (y.val ⟨b, hab, le_rfl⟩) -
          segmentArea (x.val ⟨a, le_rfl, hab⟩) (y.val ⟨a, le_rfl, hab⟩)) := by
  obtain ⟨hq, hd⟩ := curveArea_quadratic_derivative a b hab
  refine ⟨hq, ?_⟩
  intro x y
  have hc (w : ContinuousBVPaths a b) (i : Fin 2) :
      Continuous (continuousBVCoordinate w i).toFun :=
    (PiLp.continuous_apply 2 _ i).comp w.property.1
  have h01 := intervalStieltjes_integration_by_parts_of_continuous a b hab
    (continuousBVCoordinate x 0) (continuousBVCoordinate y 1) (hc x 0) (hc y 1)
  have h10 := intervalStieltjes_integration_by_parts_of_continuous a b hab
    (continuousBVCoordinate x 1) (continuousBVCoordinate y 0) (hc x 1) (hc y 0)
  change coordinateIntegral y x 1 0 + coordinateIntegral x y 0 1 = _ at h01
  change coordinateIntegral y x 0 1 + coordinateIntegral x y 1 0 = _ at h10
  rw [hd, coordinateIntegral_difference, coordinateIntegral_difference]
  simp only [continuousBVCoordinate] at h01 h10
  simp only [segmentArea, planeCrossProduct]
  linarith

private theorem curveAreaFunctional_eq_coordinateIntegral {a b : ℝ}
    (x : ContinuousBVPaths a b) :
    curveAreaFunctional x = (coordinateIntegral x x 0 1 - coordinateIntegral x x 1 0) / 2 := rfl

/-- Translating a continuous BV path by another one adds the translating path's own signed area
and the two mixed cross integrals. -/
private theorem curveAreaFunctional_add {a b : ℝ} (hab : a ≤ b)
    (x c : ContinuousBVPaths a b) :
    curveAreaFunctional (x + c) = curveAreaFunctional x + curveAreaFunctional c +
      (coordinateIntegral x c 0 1 - coordinateIntegral x c 1 0 +
        (coordinateIntegral c x 0 1 - coordinateIntegral c x 1 0)) / 2 := by
  have hone : x + c = (1 : ℝ) • x + (1 : ℝ) • c := by rw [one_smul, one_smul]
  simp only [curveAreaFunctional_eq_coordinateIntegral, hone,
    coordinateIntegral_smul_add_smul_left, coordinateIntegral_smul_add_smul_right hab]
  ring

/-- Translating a continuous BV path by a fixed one changes its signed area by a convex-linear
functional of the path: the two mixed Stieltjes cross integrals are separately linear and the
translating path's own area is constant. -/
theorem curveArea_translation_convexLinear {a b : ℝ} (hab : a ≤ b)
    (c : ContinuousBVPaths a b) :
    IsConvexLinear bvPathCombination realCombination
      (fun x ↦ curveAreaFunctional (x + c) - curveAreaFunctional x) := by
  intro t x y
  show curveAreaFunctional ((1 - (t : ℝ)) • x + (t : ℝ) • y + c) -
      curveAreaFunctional ((1 - (t : ℝ)) • x + (t : ℝ) • y) =
    realCombination t (curveAreaFunctional (x + c) - curveAreaFunctional x)
      (curveAreaFunctional (y + c) - curveAreaFunctional y)
  rw [curveAreaFunctional_add hab ((1 - (t : ℝ)) • x + (t : ℝ) • y) c,
    curveAreaFunctional_add hab x c, curveAreaFunctional_add hab y c, realCombination]
  simp only [coordinateIntegral_smul_add_smul_left, coordinateIntegral_smul_add_smul_right hab]
  ring

theorem convexArcArea_variation (a b : ℝ) (hab : a < b) (hba : b < a + Real.pi) :
    IsQuadraticFunctional convexBodyCombination (fun K ↦ convexArcArea K a b) ∧
    ∀ K L : ConvexBody Point,
      convexDirectionalDerivative convexBodyCombination (fun M ↦ convexArcArea M a b) K L =
      (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        (supportValue L t - supportValue K t) ∂surfaceAreaMeasure K) +
        (segmentArea (edgeVertices K (b : Real.Angle)).2 (edgeVertices L (b : Real.Angle)).2 -
          segmentArea (edgeVertices K (a : Real.Angle)).1 (edgeVertices L (a : Real.Angle)).1) := by
  obtain ⟨hbil0, F, hFtoFun, hFcross, hFarea⟩ := convexArc_bilinear_computation a b hab hba
  let E := (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b
  let B : ConvexBody Point → ConvexBody Point → ℝ := fun K L ↦
    (1 / 2 : ℝ) * ∫ t in E, supportValue K t ∂surfaceAreaMeasure L
  have hbil : IsConvexBilinear convexBodyCombination convexBodyCombination realCombination B :=
    hbil0
  have hfB : ∀ K : ConvexBody Point, convexArcArea K a b = B K K := fun K ↦
    (hFarea K).trans ((hFcross K K).1).symm
  refine ⟨⟨B, hbil, hfB⟩, ?_⟩
  intro K L
  have hcont (M : ConvexBody Point) : Continuous fun u : Real.Angle ↦ supportValue M u :=
    (compactSet_support_continuity M M M.nonempty M.isCompact M.nonempty M.isCompact).2.2.1
  have hint (M N : ConvexBody Point) :
      Integrable (fun u : Real.Angle ↦ supportValue M u) (surfaceAreaMeasure N) := by
    let _ : IsFiniteMeasure (surfaceAreaMeasure N) := (surfaceAreaMeasure_face_union N).1
    exact (hcont M).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
  have hsub : (∫ t in E, (supportValue L t - supportValue K t) ∂surfaceAreaMeasure K) =
      2 * B L K - 2 * B K K := by
    rw [integral_sub (hint L K).restrict (hint K K).restrict]
    simp only [B, E]
    ring
  have hanti : B K L - B L K =
      segmentArea (edgeVertices K (b : Real.Angle)).2 (edgeVertices L (b : Real.Angle)).2 -
        segmentArea (edgeVertices K (a : Real.Angle)).1 (edgeVertices L (a : Real.Angle)).1 := by
    have h1 : B K L = openIntervalCrossIntegral (F L)
        (fun t : Set.Icc a b ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).2) := (hFcross K L).2
    have h2 : B L K = openIntervalCrossIntegral (F K)
        (fun t : Set.Icc a b ↦ (edgeVertices L ((t : ℝ) : Real.Angle)).1) := (hFcross L K).1
    rw [h1, h2]
    exact openIntervalCrossIntegral_antisymm hab K L (F K) (F L) (hFtoFun K) (hFtoFun L)
  rw [(quadratic_directional_derivative convexBodyCombination
    (fun M ↦ convexArcArea M a b) B hbil hfB).2.1 K L, hsub]
  linarith

end MovingSofa

end

end

end

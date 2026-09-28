/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Infrastructure.Analysis.Foundations.Development002
public import LeanPool.MovingSofa.Infrastructure.Geometry.Foundations.Development002
public import LeanPool.MovingSofa.Cap.Foundations.Development002
public import LeanPool.MovingSofa.Infrastructure.Curves.Foundations.Development001
public import LeanPool.MovingSofa.Infrastructure.MathlibExtensions.Foundations.Development001

public import LeanPool.MovingSofa.Geometry.Foundations.Development003
public import LeanPool.MovingSofa.Gerver.Foundations.Development002
/-!
# Moving sofa: related mathematical developments

* `Cap.Tail.Arcs`.
* `Cap.Tail.Space`.
* `Cap.CornerMeasure`.
* `Cap.CornerPaths`.
* `Cap.Tail.Canonical`.
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
# Cap / Tail / Arcs
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- A planar carrier set equipped with ordered start and end points. -/
structure DirectedArcData where
  /-- The set traced by the directed arc. -/
  carrier : Set Point
  /-- The starting point of the arc. -/
  startPoint : Point
  /-- The ending point of the arc. -/
  endPoint : Point

/-- The directed convex boundary arcs used for the right and left tail bodies. -/
def rightLeftTailArcs (B D : ConvexBody Point) : DirectedArcData × DirectedArcData :=
  (⟨convexBoundaryArc B (Real.pi + paperGerverConstants.2.1) (3 * Real.pi / 2),
    (edgeVertices B ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)).1,
    (edgeVertices B ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2⟩,
   ⟨convexBoundaryArc D (3 * Real.pi / 2) (3 * Real.pi / 2 + paperGerverConstants.2.2),
    (edgeVertices D ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1,
    (edgeVertices D ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)).2⟩)

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
# Cap / Tail / Space
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace MovingSofa

/-- The real-angle inner-corner path of a cap. -/
def capInnerCorner (K : RightAngleCapSpace) (t : ℝ) : Point :=
  (rotatingHallwayParts (K.1 : Set Point) (t : Real.Angle)).innerCorner

/-- The two surface densities on the upper half-circle, with the top atom excluded. -/
def HasCapDensities (K : RightAngleCapSpace) (r s : ℝ → ℝ≥0) : Prop :=
  Measurable r ∧ Measurable s ∧
    (surfaceAreaMeasure K.1).restrict
        ((fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ico 0 (Real.pi / 2)) =
      Measure.map (fun t : ℝ ↦ (t : Real.Angle))
        ((volume.restrict (Set.Ico 0 (Real.pi / 2))).withDensity (fun t ↦ (r t : ℝ≥0∞))) ∧
    (surfaceAreaMeasure K.1).restrict
        ((fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ioc (Real.pi / 2) Real.pi) =
      Measure.map (fun t : ℝ ↦ ((t + Real.pi / 2 : ℝ) : Real.Angle))
        ((volume.restrict (Set.Ioc 0 (Real.pi / 2))).withDensity (fun t ↦ (s t : ℝ≥0∞)))

/-- The density, corner regularity and strict interior signs of the injectivity condition. -/
def SatisfiesInjectivityCondition (K : RightAngleCapSpace) : Prop :=
  (∃ r s : ℝ → ℝ≥0, HasCapDensities K r s ∧
    ∀ r' s', HasCapDensities K r' s' →
      (r =ᵐ[volume.restrict (Set.Icc 0 (Real.pi / 2))] r') ∧
      (s =ᵐ[volume.restrict (Set.Icc 0 (Real.pi / 2))] s')) ∧
    ContDiffOn ℝ 1 (capInnerCorner K) (Set.Icc 0 (Real.pi / 2)) ∧
    ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      inner ℝ (derivWithin (capInnerCorner K) (Set.Icc 0 (Real.pi / 2)) t)
        (normalVector (t : Real.Angle)) < 0 ∧
      0 < inner ℝ (derivWithin (capInnerCorner K) (Set.Icc 0 (Real.pi / 2)) t)
        (tangentVector (t : Real.Angle))

/-- Right-angle caps satisfying injectivity and the cap-area threshold. -/
def SpecialCapSpace :=
  {K : RightAngleCapSpace // SatisfiesInjectivityCondition K ∧
    (11 : ℝ) / 5 ≤ ClassicalResults.area (K.1 : Set Point)}

/-- A special cap and two convex tails satisfying the support constraints. -/
structure CapTailSpace where
  /-- The special cap forming the central component of the triple. -/
  cap : SpecialCapSpace
  rightBody : ConvexBody Point
  leftBody : ConvexBody Point
  right_subset : (rightBody : Set Point) ⊆ (cap.1.1 : Set Point)
  left_subset : (leftBody : Set Point) ⊆ (cap.1.1 : Set Point)
  right_bound : ∀ t ∈ Set.Icc paperGerverConstants.2.1 (Real.pi / 2),
    supportValue cap.1.1 (t : Real.Angle) +
      supportValue rightBody ((Real.pi + t : ℝ) : Real.Angle) ≤ 1
  right_eq : ∀ t ∈ ({paperGerverConstants.2.1, Real.pi / 2} : Set ℝ),
    supportValue cap.1.1 (t : Real.Angle) +
      supportValue rightBody ((Real.pi + t : ℝ) : Real.Angle) = 1
  left_bound : ∀ t ∈ Set.Icc (0 : ℝ) paperGerverConstants.2.2,
    supportValue cap.1.1 ((Real.pi / 2 + t : ℝ) : Real.Angle) +
      supportValue leftBody ((3 * Real.pi / 2 + t : ℝ) : Real.Angle) ≤ 1
  left_eq : ∀ t ∈ ({0, paperGerverConstants.2.2} : Set ℝ),
    supportValue cap.1.1 ((Real.pi / 2 + t : ℝ) : Real.Angle) +
      supportValue leftBody ((3 * Real.pi / 2 + t : ℝ) : Real.Angle) = 1

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
# Cap / Corner Measure
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- The normal and tangent components of the inner-corner path derivative. -/
def capVelocityCoefficients (K : SpecialCapSpace) (t : ℝ) : ℝ × ℝ :=
  (inner ℝ (derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) t)
      (normalVector (t : Real.Angle)),
    inner ℝ (derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) t)
      (tangentVector (t : Real.Angle)))

/-- The density formed by joining the two signed corner-velocity components over `[0, π]`. -/
def capCornerDensity (K : SpecialCapSpace) (s : ℝ) : ℝ :=
  if 0 < s ∧ s ≤ Real.pi / 2 then (capVelocityCoefficients K s).2
  else if Real.pi / 2 < s ∧ s ≤ Real.pi then
    -(capVelocityCoefficients K (s - Real.pi / 2)).1
  else 0

/-- The measure on the real angle interval defined by the nonnegative corner density. -/
def capCornerMeasure (K : SpecialCapSpace) : Measure ℝ :=
  (volume.restrict (Set.Icc 0 Real.pi)).withDensity
    (fun s ↦ ENNReal.ofReal (capCornerDensity K s))

/-- Push the corner-density measure to angles modulo a full turn. -/
def capCornerAngleMeasure (K : SpecialCapSpace) : Measure Real.Angle :=
  Measure.map (fun s : ℝ ↦ (s : Real.Angle)) (capCornerMeasure K)

/-- Bundle the corner density and its real and angular measures. -/
def capCornerMeasureData (K : SpecialCapSpace) :
    (ℝ → ℝ) × Measure ℝ × Measure Real.Angle :=
  (capCornerDensity K, capCornerMeasure K, capCornerAngleMeasure K)

/-- The corner measure of a special cap reads its density on the angular image of every
measurable subset of `[0, π]`. -/
theorem capCornerAngleMeasure_angleImage_eq_setLIntegral (K : SpecialCapSpace) {T : Set ℝ}
    (hT : MeasurableSet T) (hT' : T ⊆ Set.Icc 0 Real.pi) :
    capCornerAngleMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' T) =
      ∫⁻ s in T, ENNReal.ofReal (capCornerDensity K s) := by
  have hturn : Real.pi ≤ -1 + 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hsub : Set.Icc (0 : ℝ) Real.pi ⊆ Set.Ioc (-1 : ℝ) Real.pi :=
    fun x hx ↦ ⟨by linarith [hx.1], hx.2⟩
  show Measure.map (fun s : ℝ ↦ (s : Real.Angle))
      ((volume.restrict (Set.Icc 0 Real.pi)).withDensity
        (fun s ↦ ENNReal.ofReal (capCornerDensity K s)))
      ((fun s : ℝ ↦ (s : Real.Angle)) '' T) = _
  exact Real.Angle.map_coe_withDensity_image_eq_setLIntegral hturn hsub hT hT'

/-! ### Regularity and signs of the corner density

The injectivity condition makes the inner corner continuously differentiable on the closed
quarter turn, so both frame coefficients of its velocity are continuous there; the strict interior
signs then extend to the two endpoints by continuity.  The corner density is the sum of the two
branches extended by zero, whence its measurability and its bound. -/

/-- The inner-corner velocity of a special cap is continuous on the cap domain. -/
theorem continuousOn_derivWithin_capInnerCorner (K : SpecialCapSpace) :
    ContinuousOn (derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)))
      (Set.Icc 0 (Real.pi / 2)) :=
  K.property.1.2.1.continuousOn_derivWithin
    (uniqueDiffOn_Icc (by positivity : (0 : ℝ) < Real.pi / 2)) le_rfl

/-- Both frame components of the inner-corner velocity are continuous on the cap domain. -/
theorem continuousOn_capVelocityCoefficients (K : SpecialCapSpace) :
    ContinuousOn (fun s ↦ (capVelocityCoefficients K s).1) (Set.Icc 0 (Real.pi / 2)) ∧
      ContinuousOn (fun s ↦ (capVelocityCoefficients K s).2) (Set.Icc 0 (Real.pi / 2)) :=
  ⟨(continuousOn_derivWithin_capInnerCorner K).inner
      continuous_normalVector_real.continuousOn,
    (continuousOn_derivWithin_capInnerCorner K).inner
      lipschitzWith_tangentVector_real.continuous.continuousOn⟩

/-- The corner density is bounded, being continuous on the two compact halves of the cap domain
and zero outside. -/
theorem exists_bound_capCornerDensity (K : SpecialCapSpace) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, capCornerDensity K s ≤ C := by
  obtain ⟨hα, hβ⟩ := continuousOn_capVelocityCoefficients K
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hα
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hβ
  refine ⟨max (max C₁ C₂) 0, le_max_right _ _, fun s ↦ ?_⟩
  rw [capCornerDensity]
  split_ifs with h1 h2
  · exact le_max_of_le_left (le_max_of_le_right
      ((le_abs_self _).trans (hC₂ s ⟨h1.1.le, h1.2⟩)))
  · refine le_max_of_le_left (le_max_of_le_left ?_)
    have h := neg_le_abs (capVelocityCoefficients K (s - Real.pi / 2)).1
    exact h.trans (hC₁ _ ⟨by linarith [h2.1], by linarith [h2.2]⟩)
  · exact le_max_right _ _

/-! ### Finiteness and atomlessness of the corner measure -/

instance isFiniteMeasure_capCornerMeasure (K : SpecialCapSpace) :
    IsFiniteMeasure (capCornerMeasure K) := by
  obtain ⟨C, -, hC⟩ := exists_bound_capCornerDensity K
  refine ⟨?_⟩
  rw [capCornerMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc ∫⁻ s, ENNReal.ofReal (capCornerDensity K s) ∂volume.restrict (Set.Icc 0 Real.pi)
      ≤ ∫⁻ _, ENNReal.ofReal C ∂volume.restrict (Set.Icc 0 Real.pi) :=
        lintegral_mono fun s ↦ ENNReal.ofReal_le_ofReal (hC s)
    _ < ⊤ := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

instance isFiniteMeasure_capCornerAngleMeasure (K : SpecialCapSpace) :
    IsFiniteMeasure (capCornerAngleMeasure K) := by
  rw [capCornerAngleMeasure]
  exact Measure.isFiniteMeasure_map _ _

instance nullSingletonClass_capCornerAngleMeasure (K : SpecialCapSpace) :
    NullSingletonClass (capCornerAngleMeasure K) := by
  refine ⟨fun x ↦ ?_⟩
  rw [capCornerAngleMeasure,
    Measure.map_apply Real.Angle.continuous_coe.measurable (measurableSet_singleton x),
    capCornerMeasure]
  exact ((withDensity_absolutelyContinuous _ _).trans
    Measure.restrict_le_self.absolutelyContinuous)
    ((Real.Angle.countable_preimage_coe_singleton x).measure_zero volume)

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
# Cap / Corner Paths
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The inner-corner path restricted and bundled as a continuous BV path. -/
def capCornerBV (K : SpecialCapSpace) {a b : ℝ}
    (h : Set.Icc a b ⊆ Set.Icc 0 (Real.pi / 2)) : ContinuousBVPaths a b :=
  continuousBVOfContDiffOn (capInnerCorner K.val) (K.property.1.2.1.mono h)

/-- The corner BV path between the two reflected Gerver switching angles. -/
def capMiddleBV (K : SpecialCapSpace) :
    ContinuousBVPaths paperGerverConstants.2.1 paperGerverConstants.2.2 :=
  capCornerBV K (by
    have hφ : 0 ≤ GerversSofa.φ := GerversSofa.ABφθSpec.existsUnique.choose_spec.1.1
    intro t ht
    change GerversSofa.φ ≤ t ∧ t ≤ Real.pi / 2 - GerversSofa.φ at ht
    exact ⟨le_trans hφ ht.1, by linarith [ht.2]⟩)

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
# Cap / Tail / Canonical
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The closed half-planes above the right and left inner supporting walls. -/
def innerWallUpperHalfPlanes (K : RightAngleCapSpace) (t : ℝ) : Set Point × Set Point :=
  (normalHalfPlane (t : Real.Angle) (supportValue K.1 (t : Real.Angle) - 1) true false,
    normalHalfPlane ((t + Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue K.1 ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) true false)

/-- The right and left canonical tail sets, before bundling their convex-body proofs. -/
def canonicalTailSets (K : SpecialCapSpace) : Set Point × Set Point :=
  ((K.1.1 : Set Point) ∩
      ⋂ t ∈ Set.Icc paperGerverConstants.2.1 (Real.pi / 2),
        (innerWallUpperHalfPlanes K.1 t).1,
    (K.1.1 : Set Point) ∩
      ⋂ t ∈ Set.Icc (0 : ℝ) paperGerverConstants.2.2,
        (innerWallUpperHalfPlanes K.1 t).2)

end MovingSofa

end

end

end

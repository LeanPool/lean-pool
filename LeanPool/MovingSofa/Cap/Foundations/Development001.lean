/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Classical.Foundations.Development001
public import LeanPool.MovingSofa.Geometry.Foundations.Development001
public import Mathlib.Tactic.Linarith
/-!
# Moving sofa: related mathematical developments

* `Cap.Basic`.
* `Cap.AngleDomain`.
* `Cap.Area`.
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
# Cap / Basic
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The two real intervals of upper cap normals. -/
def capUpperAngles (ω : ℝ) : Set ℝ :=
  Set.Icc 0 ω ∪ Set.Icc (Real.pi / 2) (ω + Real.pi / 2)

/-- The normal directions of the two lower strip boundaries. -/
def capLowerNormals (ω : ℝ) : Set Real.Angle :=
  {((ω + Real.pi : ℝ) : Real.Angle), ((3 * Real.pi / 2 : ℝ) : Real.Angle)}

/-- A set represented by closed lower half-planes with allowed normal directions. -/
def HasHalfPlaneRepresentation (s : Set Point) (normals : Set Real.Angle) : Prop :=
  ∃ constraints : Set (Real.Angle × ℝ),
    (∀ c ∈ constraints, c.1 ∈ normals) ∧
      s = ⋂ c ∈ constraints, normalHalfPlane c.1 c.2 false false

/-- The normalized cap conditions, including its nonzero rotation-angle domain. -/
def IsCap (ω : ℝ) (K : ConvexBody Point) : Prop :=
  0 < ω ∧ ω ≤ Real.pi / 2 ∧
    supportValue K (ω : Real.Angle) = 1 ∧
    supportValue K ((Real.pi / 2 : ℝ) : Real.Angle) = 1 ∧
    supportValue K ((ω + Real.pi : ℝ) : Real.Angle) = 0 ∧
    supportValue K ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 ∧
    HasHalfPlaneRepresentation K
      (((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles ω) ∪ capLowerNormals ω)

/-- The space of caps at a fixed rotation angle. -/
def CapSpace (ω : ℝ) := {K : ConvexBody Point // IsCap ω K}

/-- A nonempty finite set of angles strictly between zero and its rotation angle. -/
structure AngleSet where
  /-- The terminal rotation angle of the polygonal approximation. -/
  angle : ℝ
  angle_pos : 0 < angle
  angle_le : angle ≤ Real.pi / 2
  /-- The finite nonempty set of interior wall directions. -/
  directions : Finset ℝ
  nonempty : directions.Nonempty
  interior : ∀ t ∈ directions, t ∈ Set.Ioo 0 angle

/-- The finite upper-normal domain associated with an angle set. -/
def angleDomain (Θ : AngleSet) : Set ℝ :=
  (Θ.directions : Set ℝ) ∪
    ((fun t ↦ t + Real.pi / 2) '' (Θ.directions : Set ℝ)) ∪
    {Θ.angle, Real.pi / 2}

/-- Polygon caps whose upper normals belong to the specified angle domain. -/
def PolygonCapSpace (Θ : AngleSet) :=
  {K : CapSpace Θ.angle // HasHalfPlaneRepresentation (K.1 : Set Point)
    (((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle)}

/-- The fan above both lower strip boundaries. -/
def capFan (ω : ℝ) : Set Point :=
  normalHalfPlane (ω : Real.Angle) 0 true false ∩
    normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false

/-- The fan of a rotation angle is convex. -/
theorem convex_capFan (ω : ℝ) : Convex ℝ (capFan ω) :=
  (convex_normalHalfPlane _ _ _).inter (convex_normalHalfPlane _ _ _)

/-- The open inward quadrant of the supporting hallway, in support coordinates. -/
def innerQuadrant (s : Set Point) (t : ℝ) : Set Point :=
  normalHalfPlane (t : Real.Angle) (supportValue s (t : Real.Angle) - 1) false true ∩
    normalHalfPlane ((t + Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) false true

/-- The open inward quadrant of a supporting hallway is convex. -/
theorem convex_innerQuadrant (s : Set Point) (t : ℝ) : Convex ℝ (innerQuadrant s t) :=
  (convex_normalHalfPlane_open _ _ _).inter (convex_normalHalfPlane_open _ _ _)

/-- The niche is the union of inward quadrants clipped by the fan. -/
def capNiche {ω : ℝ} (K : CapSpace ω) : Set Point :=
  capFan ω ∩ ⋃ t ∈ Set.Ioo 0 ω, innerQuadrant (K.1 : Set Point) t

/-- The finite-angle niche uses the same fan clipping as the continuous niche. -/
def polygonNiche (Θ : AngleSet) (K : CapSpace Θ.angle) : Set Point :=
  capFan Θ.angle ∩ ⋃ t ∈ Θ.directions, innerQuadrant (K.1 : Set Point) t

/-- Avoiding an inward quadrant means lying above one of its two inner walls. -/
theorem notMem_innerQuadrant_iff (S : Set Point) (u : ℝ) (p : Point) :
    p ∉ innerQuadrant S u ↔
      p ∈ normalHalfPlane (u : Real.Angle) (supportValue S (u : Real.Angle) - 1) true false ∨
        p ∈ normalHalfPlane ((u + Real.pi / 2 : ℝ) : Real.Angle)
          (supportValue S ((u + Real.pi / 2 : ℝ) : Real.Angle) - 1) true false := by
  have h1 : (p ∈ innerQuadrant S u) ↔
      (inner ℝ p (normalVector (u : Real.Angle)) < supportValue S (u : Real.Angle) - 1 ∧
        inner ℝ p (normalVector ((u + Real.pi / 2 : ℝ) : Real.Angle)) <
          supportValue S ((u + Real.pi / 2 : ℝ) : Real.Angle) - 1) := Iff.rfl
  have h2 : (p ∈ normalHalfPlane (u : Real.Angle)
      (supportValue S (u : Real.Angle) - 1) true false) ↔
      (supportValue S (u : Real.Angle) - 1 ≤ inner ℝ p (normalVector (u : Real.Angle))) := Iff.rfl
  have h3 : (p ∈ normalHalfPlane ((u + Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue S ((u + Real.pi / 2 : ℝ) : Real.Angle) - 1) true false) ↔
      (supportValue S ((u + Real.pi / 2 : ℝ) : Real.Angle) - 1 ≤
        inner ℝ p (normalVector ((u + Real.pi / 2 : ℝ) : Real.Angle))) := Iff.rfl
  rw [h1, h2, h3, not_and_or, not_lt, not_lt]

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
# Cap / Angle Domain
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- Every upper normal of an angle set has strictly positive sine. -/
lemma angleDomain_subset_Ioo (Θ : AngleSet) : angleDomain Θ ⊆ Set.Ioo 0 Real.pi := by
  intro t ht
  rcases ht with (ht | ⟨s, hs, rfl⟩) | ht
  · have h := Θ.interior t ht
    constructor <;> linarith [h.1, h.2, Θ.angle_le, Real.pi_pos]
  · have h := Θ.interior s hs
    constructor <;> linarith [h.1, h.2, Θ.angle_le, Real.pi_pos]
  · rcases ht with rfl | ht
    · constructor <;> linarith [Θ.angle_pos, Θ.angle_le, Real.pi_pos]
    · have ht : t = Real.pi / 2 := ht
      rw [ht]
      constructor <;> linarith [Real.pi_pos]

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
# Cap / Area
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- Cap area minus niche area, with real Lebesgue area as in the classical interface. -/
def capAreaFunctional {ω : ℝ} (K : CapSpace ω) : ℝ :=
  ClassicalResults.area (K.1 : Set Point) - ClassicalResults.area (capNiche K)

/-- The cap space at a right angle. -/
abbrev RightAngleCapSpace := CapSpace (Real.pi / 2)

/-- The sofa area functional on the right-angle cap space. -/
def rightAngleAreaFunctional (K : RightAngleCapSpace) : ℝ := capAreaFunctional K

end MovingSofa

end

end

end

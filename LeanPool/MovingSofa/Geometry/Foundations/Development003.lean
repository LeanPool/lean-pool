/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Canonical.Foundations.Development001
public import LeanPool.MovingSofa.Infrastructure.Geometry.Foundations.Development002
public import LeanPool.MovingSofa.Infrastructure.Geometry.Foundations.Development003
public import LeanPool.MovingSofa.Infrastructure.MathlibExtensions.Foundations.Development001


public import Mathlib.Analysis.Convex.Segment
/-!
# Moving sofa: related mathematical developments

* `Geometry.Hallway`.
* `Geometry.HallwayParts`.
* `Geometry.HallwayPartsProperties`.
* `Geometry.HallwayRay`.
* `Geometry.HallwaySupport`.
* `Geometry.Parallelogram`.
* `Geometry.ParallelogramGap`.
* `Geometry.PathHalfPlaneCap`.
* `Geometry.Reflection`.
* `Geometry.SupportingHallway`.
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
# Geometry / Hallway
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- Counterclockwise rotation about the origin. -/
def rotationMap (t : Real.Angle) (p : Point) : Point :=
  (EuclideanGeometry.o.rotation t) p

/-- The horizontal, vertical and rotated vertical strips. -/
def strips (ω : ℝ) : Set Point × Set Point × Set Point :=
  let H : Set Point := {p | 0 ≤ p 1 ∧ p 1 ≤ 1}
  let V : Set Point := {p | 0 ≤ p 0 ∧ p 0 ≤ 1}
  (H, V, rotationMap (ω : Real.Angle) '' V)

/-- The intersection of strips and its two distinguished points. -/
def stripParallelogram (ω : ℝ) : Set Point × Point × Point :=
  ((strips ω).1 ∩ (strips ω).2.2, 0, !₂[Real.tan (Real.pi / 4 - ω / 2), 1])

/-- Corners, walls, rays and quadrants of a hallway. -/
structure HallwayParts where
  /-- The inner reentrant corner of the hallway. -/
  innerCorner : Point
  /-- The outer corner opposite the inner corner. -/
  outerCorner : Point
  /-- The outer wall corresponding to the fixed hallway’s line `x = 1`. -/
  a : Set Point
  /-- The inner wall corresponding to the fixed hallway’s line `x = 0`. -/
  b : Set Point
  /-- The outer wall corresponding to the fixed hallway’s line `y = 1`. -/
  c : Set Point
  /-- The inner wall corresponding to the fixed hallway’s line `y = 0`. -/
  d : Set Point
  /-- The ray on the inner B wall extending away from the corner. -/
  bRay : Set Point
  /-- The ray on the inner D wall extending away from the corner. -/
  dRay : Set Point
  /-- The closed quadrant cut out by the two outer walls. -/
  outerQuadrant : Set Point
  /-- The open forbidden quadrant behind the inner corner. -/
  innerQuadrant : Set Point

/-- The named parts of the fixed hallway. -/
def hallwayParts : HallwayParts where
  innerCorner := 0
  outerCorner := !₂[1, 1]
  a := {p | p 0 = 1}
  b := {p | p 0 = 0}
  c := {p | p 1 = 1}
  d := {p | p 1 = 0}
  bRay := {p | p 0 = 0 ∧ p 1 ≤ 0}
  dRay := {p | p 0 ≤ 0 ∧ p 1 = 0}
  outerQuadrant := {p | p 0 ≤ 1 ∧ p 1 ≤ 1}
  innerQuadrant := {p | p 0 < 0 ∧ p 1 < 0}

/-- Rotation followed by the support-determined translation. -/
def supportingPlacement (s : Set Point) (t : Real.Angle) (p : Point) : Point :=
  rotationMap t p + (supportValue s t - 1) • normalVector t +
    (supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) • tangentVector t

/-- The supporting hallway of a nonempty compact set. -/
def supportingHallway (s : Set Point) (t : Real.Angle) : Set Point :=
  supportingPlacement s t '' hallway

/-- The images of all named hallway parts under its supporting placement. -/
def rotatingHallwayParts (s : Set Point) (t : Real.Angle) : HallwayParts where
  innerCorner := supportingPlacement s t hallwayParts.innerCorner
  outerCorner := supportingPlacement s t hallwayParts.outerCorner
  a := supportingPlacement s t '' hallwayParts.a
  b := supportingPlacement s t '' hallwayParts.b
  c := supportingPlacement s t '' hallwayParts.c
  d := supportingPlacement s t '' hallwayParts.d
  bRay := supportingPlacement s t '' hallwayParts.bRay
  dRay := supportingPlacement s t '' hallwayParts.dRay
  outerQuadrant := supportingPlacement s t '' hallwayParts.outerQuadrant
  innerQuadrant := supportingPlacement s t '' hallwayParts.innerQuadrant

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
# Geometry / Hallway Parts
-/

@[expose] public section

noncomputable section

namespace MovingSofa

theorem rightAngleRotation_apply (p : Point) :
    EuclideanGeometry.o.rightAngleRotation p = !₂[-p 1, p 0] := by
  apply (ext_inner_left (𝕜 := ℝ))
  intro y
  rw [Orientation.inner_rightAngleRotation_right, Orientation.areaForm_to_volumeForm,
    EuclideanGeometry.o.volumeForm_robust (EuclideanSpace.basisFun (Fin 2) ℝ) rfl,
    Module.Basis.det_apply]
  simp [Matrix.det_fin_two, Module.Basis.toMatrix, PiLp.inner_apply]
  ring

theorem inner_rotationMap_normalVector (p : Point) (t : Real.Angle) :
    inner ℝ (rotationMap t p) (normalVector t) = p 0 := by
  rw [rotationMap, Orientation.rotation_apply, rightAngleRotation_apply]
  simp [normalVector, frame, PiLp.inner_apply]
  linear_combination p 0 * Real.Angle.cos_sq_add_sin_sq t

theorem inner_rotationMap_tangentVector (p : Point) (t : Real.Angle) :
    inner ℝ (rotationMap t p) (tangentVector t) = p 1 := by
  rw [rotationMap, Orientation.rotation_apply, rightAngleRotation_apply]
  simp [tangentVector, frame, PiLp.inner_apply]
  linear_combination p 1 * Real.Angle.cos_sq_add_sin_sq t

theorem normalVector_add_pi_div_two (t : Real.Angle) :
    normalVector (t + ((Real.pi / 2 : ℝ) : Real.Angle)) = tangentVector t := by
  simp [normalVector, tangentVector, frame, Real.Angle.cos_add_pi_div_two,
    Real.Angle.sin_add_pi_div_two]

/-- Rotating a real normal direction by a right angle gives the tangent direction. -/
theorem normalVector_add_pi_div_two_real (t : ℝ) :
    normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle) = tangentVector (t : Real.Angle) := by
  rw [Real.Angle.coe_add, normalVector_add_pi_div_two]

theorem inner_supportingPlacement_normalVector (s : Set Point) (t : Real.Angle)
    (p : Point) :
    inner ℝ (supportingPlacement s t p) (normalVector t) =
      p 0 + supportValue s t - 1 := by
  simp only [supportingPlacement, inner_add_left, real_inner_smul_left,
    inner_rotationMap_normalVector]
  simp [normalVector, tangentVector, frame, PiLp.inner_apply,
    PiLp.norm_sq_eq_of_L2, Real.Angle.cos_sq_add_sin_sq]
  ring

theorem inner_supportingPlacement_tangentVector (s : Set Point) (t : Real.Angle)
    (p : Point) :
    inner ℝ (supportingPlacement s t p) (tangentVector t) =
      p 1 + supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1 := by
  simp only [supportingPlacement, inner_add_left, real_inner_smul_left,
    inner_rotationMap_tangentVector]
  simp [normalVector, tangentVector, frame, PiLp.inner_apply,
    PiLp.norm_sq_eq_of_L2, Real.Angle.cos_sq_add_sin_sq, add_comm]
  ring

theorem hallway_eq_outerQuadrant_sdiff_innerQuadrant :
    hallway = hallwayParts.outerQuadrant \ hallwayParts.innerQuadrant := by
  ext p
  constructor
  · rintro (⟨a, b, h, rfl⟩ | ⟨a, b, h, rfl⟩)
    · change (a ≤ 1 ∧ b ≤ 1) ∧ ¬(a < 0 ∧ b < 0)
      exact ⟨⟨h.1, h.2.2⟩, fun hn ↦ (not_lt_of_ge h.2.1) hn.2⟩
    · change (a ≤ 1 ∧ b ≤ 1) ∧ ¬(a < 0 ∧ b < 0)
      exact ⟨⟨h.2.1, h.2.2⟩, fun hn ↦ (not_lt_of_ge h.1) hn.1⟩
  · intro hp
    change (p 0 ≤ 1 ∧ p 1 ≤ 1) ∧ ¬(p 0 < 0 ∧ p 1 < 0) at hp
    have heq : (!₂[p 0, p 1] : Point) = p := by
      ext i
      fin_cases i <;> rfl
    by_cases h : 0 ≤ p 0
    · exact Or.inr ⟨p 0, p 1, ⟨h, hp.1.1, hp.1.2⟩, heq⟩
    · exact Or.inl ⟨p 0, p 1,
        ⟨hp.1.1, le_of_not_gt (fun hy ↦ hp.2 ⟨lt_of_not_ge h, hy⟩), hp.1.2⟩, heq⟩

/-- The first coordinate of a rotated point. -/
theorem rotationMap_apply_zero (θ : Real.Angle) (x : Point) :
    rotationMap θ x 0 = θ.cos * x 0 - θ.sin * x 1 := by
  rw [rotationMap, Orientation.rotation_apply, rightAngleRotation_apply]
  simp
  ring

/-- The second coordinate of a rotated point. -/
theorem rotationMap_apply_one (θ : Real.Angle) (x : Point) :
    rotationMap θ x 1 = θ.sin * x 0 + θ.cos * x 1 := by
  rw [rotationMap, Orientation.rotation_apply, rightAngleRotation_apply]
  simp
  ring

/-- Coordinate bounds for a point of the horizontal side of the hallway. -/
theorem mem_horizontalHallway_coordinates {p : Point} (hp : p ∈ horizontalHallway) :
    p 0 ≤ 1 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1 := by
  obtain ⟨x, y, h, rfl⟩ := hp
  simpa using h

/-- Coordinate bounds for a point of the vertical side of the hallway. -/
theorem mem_verticalHallway_coordinates {p : Point} (hp : p ∈ verticalHallway) :
    0 ≤ p 0 ∧ p 0 ≤ 1 ∧ p 1 ≤ 1 := by
  obtain ⟨x, y, h, rfl⟩ := hp
  simpa using h

/-- A point lies in the hallway exactly when it lies in the outer quadrant and is not
strictly inside the inner one. -/
theorem mem_hallway_iff (q : Point) : q ∈ hallway ↔
    (q 0 ≤ 1 ∧ q 1 ≤ 1) ∧ (0 ≤ q 0 ∨ 0 ≤ q 1) := by
  constructor
  · rintro (⟨a, b, h, rfl⟩ | ⟨a, b, h, rfl⟩)
    · exact ⟨⟨h.1, h.2.2⟩, Or.inr h.2.1⟩
    · exact ⟨⟨h.2.1, h.2.2⟩, Or.inl h.1⟩
  · rintro ⟨⟨hx, hy⟩, h⟩
    have heq : (!₂[q 0, q 1] : Point) = q := by
      ext i
      fin_cases i <;> rfl
    rcases h with hx0 | hy0
    · exact Or.inr ⟨q 0, q 1, ⟨hx0, hx, hy⟩, heq⟩
    · exact Or.inl ⟨q 0, q 1, ⟨hx, hy0, hy⟩, heq⟩

/-- Coordinate bounds place a point in the horizontal side of the hallway. -/
theorem mem_horizontalHallway_of_coordinates (p : Point)
    (hx : p 0 ≤ 1) (hy : p 1 ∈ Set.Icc (0 : ℝ) 1) : p ∈ horizontalHallway := by
  refine ⟨p 0, p 1, ⟨hx, hy⟩, ?_⟩
  ext i
  fin_cases i <;> rfl

/-- Coordinate bounds place a point in the vertical side of the hallway. -/
theorem mem_verticalHallway_of_coordinates (p : Point)
    (hx : p 0 ∈ Set.Icc (0 : ℝ) 1) (hy : p 1 ≤ 1) : p ∈ verticalHallway := by
  refine ⟨p 0, p 1, ⟨hx.1, hx.2, hy⟩, ?_⟩
  ext i
  fin_cases i <;> rfl

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
# Geometry / Hallway Parts Properties
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- A supporting hallway lies in its outer quadrant. -/
theorem supportingHallway_subset_outerQuadrant (s : Set Point) (t : Real.Angle) :
    supportingHallway s t ⊆ (rotatingHallwayParts s t).outerQuadrant := by
  change supportingPlacement s t '' hallway ⊆
    supportingPlacement s t '' hallwayParts.outerQuadrant
  apply Set.image_mono
  rw [hallway_eq_outerQuadrant_sdiff_innerQuadrant]
  exact Set.sdiff_subset

theorem rotatingHallwayParts_formulas (s : Set Point) (t : Real.Angle) :
    supportingHallway s t = (rotatingHallwayParts s t).outerQuadrant \ (rotatingHallwayParts s
      t).innerQuadrant ∧
    (rotatingHallwayParts s t).innerCorner = (supportValue s t - 1) • normalVector t +
      (supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) • tangentVector t ∧
    (rotatingHallwayParts s t).outerCorner = supportValue s t • normalVector t + supportValue s (t
      + ((Real.pi / 2 : ℝ) : Real.Angle)) • tangentVector t ∧
    (rotatingHallwayParts s t).a = normalLine t (supportValue s t) ∧
    (rotatingHallwayParts s t).b = normalLine t (supportValue s t - 1) ∧
    (rotatingHallwayParts s t).c = normalLine (t + ((Real.pi / 2 : ℝ) : Real.Angle)) (supportValue
      s (t + ((Real.pi / 2 : ℝ) : Real.Angle))) ∧
    (rotatingHallwayParts s t).d = normalLine (t + ((Real.pi / 2 : ℝ) : Real.Angle)) (supportValue
      s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) ∧
    (rotatingHallwayParts s t).outerQuadrant =
      normalHalfPlane t (supportValue s t) false false ∩
        normalHalfPlane (t + ((Real.pi / 2 : ℝ) : Real.Angle)) (supportValue s (t + ((Real.pi / 2
          : ℝ) : Real.Angle))) false false ∧
    (rotatingHallwayParts s t).innerQuadrant =
      normalHalfPlane t (supportValue s t - 1) false true ∩
        normalHalfPlane (t + ((Real.pi / 2 : ℝ) : Real.Angle)) (supportValue s (t + ((Real.pi / 2
          : ℝ) : Real.Angle)) - 1) false true := by
  have hinj : Function.Injective (supportingPlacement s t) := by
    intro p q h
    apply (EuclideanGeometry.o.rotation t).injective
    simpa only [supportingPlacement, rotationMap, add_left_inj] using h
  have hsurj : Function.Surjective (supportingPlacement s t) := by
    intro q
    obtain ⟨p, hp⟩ := (EuclideanGeometry.o.rotation t).surjective
      (q - (supportValue s t - 1) • normalVector t -
        (supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) • tangentVector t)
    refine ⟨p, ?_⟩
    simp only [supportingPlacement, rotationMap, hp]
    abel
  have himage (A B : Set Point)
      (h : ∀ p, p ∈ A ↔ supportingPlacement s t p ∈ B) :
      supportingPlacement s t '' A = B := by
    apply (Set.preimage_eq_preimage hsurj).mp
    rw [Set.preimage_image_eq A hinj]
    exact Set.ext h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (Set.preimage_eq_preimage hsurj).mp
    change supportingPlacement s t ⁻¹' (supportingPlacement s t '' hallway) =
      supportingPlacement s t ⁻¹' (supportingPlacement s t '' hallwayParts.outerQuadrant \
        supportingPlacement s t '' hallwayParts.innerQuadrant)
    rw [Set.preimage_sdiff, Set.preimage_image_eq _ hinj,
      Set.preimage_image_eq _ hinj, Set.preimage_image_eq _ hinj]
    exact hallway_eq_outerQuadrant_sdiff_innerQuadrant
  · simp [rotatingHallwayParts, supportingPlacement, hallwayParts, rotationMap]
  · simp only [rotatingHallwayParts, supportingPlacement, hallwayParts,
      rotationMap, Orientation.rotation_apply, rightAngleRotation_apply]
    ext i
    fin_cases i <;> simp [normalVector, tangentVector, frame] <;> ring
  · apply himage
    intro p
    change p 0 = 1 ↔ inner ℝ (supportingPlacement s t p) (normalVector t) = _
    rw [inner_supportingPlacement_normalVector]
    constructor <;> intro h <;> linarith
  · apply himage
    intro p
    change p 0 = 0 ↔ inner ℝ (supportingPlacement s t p) (normalVector t) = _
    rw [inner_supportingPlacement_normalVector]
    constructor <;> intro h <;> linarith
  · apply himage
    intro p
    change p 1 = 1 ↔ inner ℝ (supportingPlacement s t p)
      (normalVector (t + ((Real.pi / 2 : ℝ) : Real.Angle))) = _
    rw [normalVector_add_pi_div_two, inner_supportingPlacement_tangentVector]
    constructor <;> intro h <;> linarith
  · apply himage
    intro p
    change p 1 = 0 ↔ inner ℝ (supportingPlacement s t p)
      (normalVector (t + ((Real.pi / 2 : ℝ) : Real.Angle))) = _
    rw [normalVector_add_pi_div_two, inner_supportingPlacement_tangentVector]
    constructor <;> intro h <;> linarith
  · apply himage
    intro p
    change (p 0 ≤ 1 ∧ p 1 ≤ 1) ↔
      (inner ℝ (supportingPlacement s t p) (normalVector t) ≤ _) ∧
      (inner ℝ (supportingPlacement s t p)
        (normalVector (t + ((Real.pi / 2 : ℝ) : Real.Angle))) ≤ _)
    rw [normalVector_add_pi_div_two, inner_supportingPlacement_normalVector,
      inner_supportingPlacement_tangentVector]
    constructor <;> rintro ⟨h₀, h₁⟩ <;> constructor <;> linarith
  · apply himage
    intro p
    change (p 0 < 0 ∧ p 1 < 0) ↔
      (inner ℝ (supportingPlacement s t p) (normalVector t) < _) ∧
      (inner ℝ (supportingPlacement s t p)
        (normalVector (t + ((Real.pi / 2 : ℝ) : Real.Angle))) < _)
    rw [normalVector_add_pi_div_two, inner_supportingPlacement_normalVector,
      inner_supportingPlacement_tangentVector]
    constructor <;> rintro ⟨h₀, h₁⟩ <;> constructor <;> linarith

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
# Geometry / Hallway Ray
-/

@[expose] public section

noncomputable section

open Set MeasureTheory

namespace MovingSofa

/-- Coordinate description of the downward ray of a supporting hallway. -/
theorem mem_rotatingHallwayParts_bRay_iff (s : Set Point) (t : Real.Angle) (p : Point) :
    p ∈ (rotatingHallwayParts s t).bRay ↔
      inner ℝ p (normalVector t) = supportValue s t - 1 ∧
      inner ℝ p (tangentVector t) ≤
        supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1 := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    change q 0 = 0 ∧ q 1 ≤ 0 at hq
    rw [inner_supportingPlacement_normalVector, inner_supportingPlacement_tangentVector]
    exact ⟨by linarith [hq.1], by linarith [hq.2]⟩
  · intro hp
    obtain ⟨q, rfl⟩ := (show Function.Surjective (supportingPlacement s t) by
      intro p
      obtain ⟨q, hq⟩ := (EuclideanGeometry.o.rotation t).surjective
        (p - (supportValue s t - 1) • normalVector t -
          (supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) • tangentVector t)
      refine ⟨q, ?_⟩
      simp only [supportingPlacement, rotationMap, hq]
      abel) p
    rw [inner_supportingPlacement_normalVector, inner_supportingPlacement_tangentVector] at hp
    change supportingPlacement s t q ∈ supportingPlacement s t '' hallwayParts.bRay
    refine ⟨q, ?_, rfl⟩
    change q 0 = 0 ∧ q 1 ≤ 0
    exact ⟨by linarith [hp.1], by linarith [hp.2]⟩

/-- Coordinate description of the leftward ray of a supporting hallway. -/
theorem mem_rotatingHallwayParts_dRay_iff (s : Set Point) (t : Real.Angle) (p : Point) :
    p ∈ (rotatingHallwayParts s t).dRay ↔
      inner ℝ p (normalVector t) ≤ supportValue s t - 1 ∧
      inner ℝ p (tangentVector t) =
        supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1 := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    change q 0 ≤ 0 ∧ q 1 = 0 at hq
    rw [inner_supportingPlacement_normalVector, inner_supportingPlacement_tangentVector]
    exact ⟨by linarith [hq.1], by linarith [hq.2]⟩
  · intro hp
    obtain ⟨q, rfl⟩ := (show Function.Surjective (supportingPlacement s t) by
      intro p
      obtain ⟨q, hq⟩ := (EuclideanGeometry.o.rotation t).surjective
        (p - (supportValue s t - 1) • normalVector t -
          (supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) • tangentVector t)
      refine ⟨q, ?_⟩
      simp only [supportingPlacement, rotationMap, hq]
      abel) p
    rw [inner_supportingPlacement_normalVector, inner_supportingPlacement_tangentVector] at hp
    change supportingPlacement s t q ∈ supportingPlacement s t '' hallwayParts.dRay
    refine ⟨q, ?_, rfl⟩
    change q 0 ≤ 0 ∧ q 1 = 0
    exact ⟨by linarith [hp.1], by linarith [hp.2]⟩

/-- The part of a supporting hallway ray above a transverse line has the expected length. -/
theorem hausdorffMeasure_bRay_inter_normalHalfPlane (s : Set Point) (t u h : ℝ)
    (htrans : 0 < inner ℝ (tangentVector (t : Real.Angle))
      (normalVector (u : Real.Angle))) :
    Measure.hausdorffMeasure 1
        ((rotatingHallwayParts s (t : Real.Angle)).bRay ∩
          normalHalfPlane (u : Real.Angle) h true false) =
      ENNReal.ofReal (max 0
        ((inner ℝ (rotatingHallwayParts s (t : Real.Angle)).innerCorner
          (normalVector (u : Real.Angle)) - h) /
          inner ℝ (tangentVector (t : Real.Angle)) (normalVector (u : Real.Angle)))) := by
  let x := (rotatingHallwayParts s (t : Real.Angle)).innerCorner
  let v := tangentVector (t : Real.Angle)
  let d := inner ℝ v (normalVector (u : Real.Angle))
  let α := (inner ℝ x (normalVector (u : Real.Angle)) - h) / d
  have hd : 0 < d := htrans
  have hxn : inner ℝ x (normalVector (t : Real.Angle)) =
      supportValue s (t : Real.Angle) - 1 := by
    change inner ℝ (supportingPlacement s (t : Real.Angle) (0 : Point))
      (normalVector (t : Real.Angle)) = _
    rw [inner_supportingPlacement_normalVector]
    simp
  have hxt : inner ℝ x v =
      supportValue s ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1 := by
    change inner ℝ (supportingPlacement s (t : Real.Angle) (0 : Point))
      (tangentVector (t : Real.Angle)) = _
    rw [inner_supportingPlacement_tangentVector]
    simp only [PiLp.zero_apply]
    ring
  have hvn : inner ℝ v (normalVector (t : Real.Angle)) = 0 := by
    rw [real_inner_comm, inner_normalVector_tangentVector]
  have hvv : inner ℝ v v = 1 := inner_tangentVector_self t
  have hpoint (p : Point) (lam : ℝ)
      (hn : inner ℝ p (normalVector (t : Real.Angle)) =
        inner ℝ x (normalVector (t : Real.Angle)))
      (ht : inner ℝ p v = inner ℝ x v - lam) : p = x - lam • v := by
    rw [← inner_normalVector_smul_add_inner_tangentVector_smul p (t : Real.Angle),
      ← inner_normalVector_smul_add_inner_tangentVector_smul x (t : Real.Angle)]
    rw [hn, ht]
    module
  by_cases hα : 0 ≤ α
  · have hset : (rotatingHallwayParts s (t : Real.Angle)).bRay ∩
        normalHalfPlane (u : Real.Angle) h true false = segment ℝ x (x - α • v) := by
      ext p
      change (p ∈ (rotatingHallwayParts s (t : Real.Angle)).bRay ∧
        h ≤ inner ℝ p (normalVector (u : Real.Angle))) ↔ _
      constructor
      · rintro ⟨hray, hu⟩
        rw [mem_rotatingHallwayParts_bRay_iff] at hray
        let lam := inner ℝ x v - inner ℝ p v
        have hlam0 : 0 ≤ lam := by dsimp [lam]; rw [hxt]; linarith [hray.2]
        have hp : p = x - lam • v := by
          apply hpoint p lam
          · rw [hray.1, hxn]
          · dsimp [lam]
            ring
        have hlamα : lam ≤ α := by
          rw [hp, inner_sub_left, real_inner_smul_left] at hu
          apply (le_div_iff₀ hd).2
          dsimp [d]
          nlinarith
        by_cases hα0 : α = 0
        · have : lam = 0 := le_antisymm (hα0 ▸ hlamα) hlam0
          simp [hα0, hp, this]
        · rw [segment_eq_image]
          refine ⟨lam / α,
            ⟨div_nonneg hlam0 hα, (div_le_one (lt_of_le_of_ne hα ?_)).2 hlamα⟩, ?_⟩
          · exact Ne.symm hα0
          · change (1 - lam / α) • x + (lam / α) • (x - α • v) = p
            rw [hp]
            rw [smul_sub, smul_smul, div_mul_cancel₀ _ hα0]
            module
      · intro hp
        rw [segment_eq_image] at hp
        obtain ⟨r, hr, rfl⟩ := hp
        have heq : (1 - r) • x + r • (x - α • v) = x - (r * α) • v := by module
        rw [show (fun θ : ℝ ↦ (1 - θ) • x + θ • (x - α • v)) r =
          x - (r * α) • v from heq]
        constructor
        · rw [mem_rotatingHallwayParts_bRay_iff]
          constructor
          · simp only [inner_sub_left, real_inner_smul_left, hvn, mul_zero, sub_zero, hxn]
          · simp only [inner_sub_left, real_inner_smul_left]
            change inner ℝ x v - r * α * inner ℝ v v ≤ _
            rw [hvv, mul_one, hxt]
            nlinarith [mul_nonneg hr.1 hα]
        · simp only [inner_sub_left, real_inner_smul_left]
          have hrα : r * α ≤ α := by nlinarith [hr.1, hr.2, hα]
          have hαeq : inner ℝ x (normalVector (u : Real.Angle)) - h = α * d := by
            dsimp [α]
            rw [div_mul_cancel₀ _ hd.ne']
          dsimp [d] at hαeq ⊢
          nlinarith
    rw [hset, MeasureTheory.hausdorffMeasure_segment, edist_dist, dist_eq_norm]
    have hvnorm : ‖v‖ = 1 := by
      dsimp [v]
      rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
      rw [EuclideanSpace.norm_sq_eq]
      simp [tangentVector, frame, Fin.sum_univ_two, Real.sin_sq_add_cos_sq]
    have hsub : x - (x - α • v) = α • v := by module
    rw [hsub, norm_smul, hvnorm, mul_one]
    simp only [Real.norm_eq_abs, abs_of_nonneg hα]
    simp only [x, v, d, α, max_eq_right hα]
  · have hset : (rotatingHallwayParts s (t : Real.Angle)).bRay ∩
        normalHalfPlane (u : Real.Angle) h true false = ∅ := by
      ext p
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hp
      change p ∈ (rotatingHallwayParts s (t : Real.Angle)).bRay ∧
        h ≤ inner ℝ p (normalVector (u : Real.Angle)) at hp
      rw [mem_rotatingHallwayParts_bRay_iff] at hp
      let lam := inner ℝ x v - inner ℝ p v
      have hlam0 : 0 ≤ lam := by dsimp [lam]; rw [hxt]; linarith [hp.1.2]
      have hp' : p = x - lam • v := by
        apply hpoint p lam
        · rw [hp.1.1, hxn]
        · dsimp [lam]
          ring
      have hlamα : lam ≤ α := by
        have hu := hp.2
        rw [hp', inner_sub_left, real_inner_smul_left] at hu
        apply (le_div_iff₀ hd).2
        dsimp [d]
        nlinarith
      linarith
    rw [hset]
    have hα' : α ≤ 0 := le_of_not_ge hα
    simp only [measure_empty, ENNReal.ofReal_zero, x, v, d, α, max_eq_left hα']

/-- A planar set on one line of a moving frame, with bounded tangent coordinate, is short. -/
theorem hausdorffMeasure_le_of_frame_bounds {S : Set Point} {t e lo hi : ℝ}
    (hS : ∀ p ∈ S, inner ℝ p (normalVector (t : Real.Angle)) = e ∧
      lo ≤ inner ℝ p (tangentVector (t : Real.Angle)) ∧
      inner ℝ p (tangentVector (t : Real.Angle)) ≤ hi) :
    Measure.hausdorffMeasure 1 S ≤ ENNReal.ofReal (max 0 (hi - lo)) := by
  have hvv : inner ℝ (tangentVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = 1 :=
    inner_tangentVector_self t
  have hnorm : ‖tangentVector (t : Real.Angle)‖ = 1 := by
    have h := real_inner_self_eq_norm_mul_norm (tangentVector (t : Real.Angle))
    rw [hvv] at h
    nlinarith [norm_nonneg (tangentVector (t : Real.Angle))]
  have hsub : S ⊆ segment ℝ
      (e • normalVector (t : Real.Angle) + lo • tangentVector (t : Real.Angle))
      (e • normalVector (t : Real.Angle) + max lo hi • tangentVector (t : Real.Angle)) := by
    intro p hp
    obtain ⟨hpn, hplo, hphi⟩ := hS p hp
    obtain ⟨y, hy⟩ : ∃ y : ℝ, inner ℝ p (tangentVector (t : Real.Angle)) = y := ⟨_, rfl⟩
    rw [hy] at hplo hphi
    have hdecomp : p = e • normalVector (t : Real.Angle) + y • tangentVector (t : Real.Angle) := by
      conv_lhs => rw [← inner_normalVector_smul_add_inner_tangentVector_smul p (t : Real.Angle)]
      rw [hpn, hy]
    have hym : y ≤ max lo hi := hphi.trans (le_max_right lo hi)
    rcases le_or_gt (max lo hi) lo with hml | hml
    · have hylo : y = lo := le_antisymm (hym.trans hml) hplo
      rw [hdecomp, hylo]
      exact left_mem_segment ℝ _ _
    · rw [segment_eq_image]
      refine ⟨(y - lo) / (max lo hi - lo),
        ⟨div_nonneg (by linarith) (by linarith), ?_⟩, ?_⟩
      · rw [div_le_one (by linarith)]
        linarith
      · have hθ : lo + (y - lo) / (max lo hi - lo) * (max lo hi - lo) = y := by
          field_simp
          ring
        have hexp : (1 - (y - lo) / (max lo hi - lo)) •
              (e • normalVector (t : Real.Angle) + lo • tangentVector (t : Real.Angle)) +
            ((y - lo) / (max lo hi - lo)) •
              (e • normalVector (t : Real.Angle) +
                max lo hi • tangentVector (t : Real.Angle)) =
            e • normalVector (t : Real.Angle) +
              (lo + (y - lo) / (max lo hi - lo) * (max lo hi - lo)) •
                tangentVector (t : Real.Angle) := by
          module
        change (1 - (y - lo) / (max lo hi - lo)) •
              (e • normalVector (t : Real.Angle) + lo • tangentVector (t : Real.Angle)) +
            ((y - lo) / (max lo hi - lo)) •
              (e • normalVector (t : Real.Angle) +
                max lo hi • tangentVector (t : Real.Angle)) = p
        rw [hexp, hθ]
        exact hdecomp.symm
  refine (measure_mono hsub).trans (le_of_eq ?_)
  rw [MeasureTheory.hausdorffMeasure_segment, edist_dist, dist_eq_norm]
  congr 1
  have hdiff : e • normalVector (t : Real.Angle) + lo • tangentVector (t : Real.Angle) -
      (e • normalVector (t : Real.Angle) + max lo hi • tangentVector (t : Real.Angle)) =
      (lo - max lo hi) • tangentVector (t : Real.Angle) := by module
  rw [hdiff, norm_smul, hnorm, mul_one, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr (le_max_left lo hi)), neg_sub]
  rcases le_total hi lo with hle | hle
  · rw [max_eq_left hle, max_eq_left (by linarith), sub_self]
  · rw [max_eq_right hle, max_eq_right (by linarith)]

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
# Geometry / Hallway Support
-/

@[expose] public section

noncomputable section

namespace MovingSofa

theorem outerCorner_eq_support_sum (K : ConvexBody Point) (t : ℝ) :
    (rotatingHallwayParts (K : Set Point) (t : Real.Angle)).outerCorner =
      supportValue K (t : Real.Angle) • normalVector (t : Real.Angle) +
      supportValue K ((t + Real.pi / 2 : ℝ) : Real.Angle) • tangentVector (t : Real.Angle) := by
  have hrot : rotationMap (t : Real.Angle) (!₂[1, 1] : Point) =
      normalVector (t : Real.Angle) + tangentVector (t : Real.Angle) := by
    unfold rotationMap
    rw [Orientation.rotation_apply, rightAngleRotation_apply]
    ext i
    fin_cases i <;> simp [normalVector, tangentVector, frame]
    ring
  simp only [rotatingHallwayParts, supportingPlacement, hallwayParts, hrot, Real.Angle.coe_add]
  module

/-- Two supporting lines at angular difference exactly `π / 2` meet at the outer corner of the
rotating supporting hallway. -/
theorem supportingIntersection_add_pi_div_two_eq_outerCorner (K : ConvexBody Point) (t : ℝ) :
    supportingIntersection K (t : Real.Angle) ((t + Real.pi / 2 : ℝ) : Real.Angle) =
      (rotatingHallwayParts (K : Set Point) (t : Real.Angle)).outerCorner := by
  have hd : ((t + Real.pi / 2 : ℝ) : Real.Angle) - (t : Real.Angle) =
      ((Real.pi / 2 : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_sub, show t + Real.pi / 2 - t = Real.pi / 2 from by ring]
  rw [supportingIntersection, hd, Real.Angle.cos_coe, Real.Angle.sin_coe, Real.cos_pi_div_two,
    Real.sin_pi_div_two, outerCorner_eq_support_sum]
  simp only [mul_zero, sub_zero, div_one]

/-- The outer corner of the rotating supporting hallway is its inner corner translated by the
frame sum `u_t + v_t`. -/
theorem outerCorner_eq_innerCorner_add (K : ConvexBody Point) (t : ℝ) :
    (rotatingHallwayParts (K : Set Point) (t : Real.Angle)).outerCorner =
      (rotatingHallwayParts (K : Set Point) (t : Real.Angle)).innerCorner +
        (normalVector (t : Real.Angle) + tangentVector (t : Real.Angle)) := by
  rw [outerCorner_eq_support_sum]
  simp only [rotatingHallwayParts, hallwayParts, supportingPlacement, rotationMap,
    map_zero, zero_add, Real.Angle.coe_add]
  module

theorem continuous_outerCorner (K : ConvexBody Point) :
    Continuous
      (fun s : ℝ ↦ (rotatingHallwayParts (K : Set Point) (s : Real.Angle)).outerCorner) := by
  simp_rw [outerCorner_eq_support_sum]
  exact ((continuous_supportValue_real K).smul continuous_normalVector_real).add
    (((continuous_supportValue_real K).comp (continuous_id.add_const _)).smul
      (continuous_iff_continuousAt.mpr fun t ↦ (hasDerivAt_tangentVector t).continuousAt))

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
# Geometry / Parallelogram
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The strip intersection is described by its vertical and rotated coordinates. -/
theorem mem_stripParallelogram_iff (ω : ℝ) (p : Point) :
    p ∈ (stripParallelogram ω).1 ↔
      (0 ≤ p 1 ∧ p 1 ≤ 1) ∧
      (0 ≤ inner ℝ p (normalVector (ω : Real.Angle)) ∧
        inner ℝ p (normalVector (ω : Real.Angle)) ≤ 1) := by
  change ((0 ≤ p 1 ∧ p 1 ≤ 1) ∧
    p ∈ rotationMap (ω : Real.Angle) '' {q : Point | 0 ≤ q 0 ∧ q 0 ≤ 1}) ↔ _
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa only [inner_rotationMap_normalVector, Set.mem_ofPred_eq] using hq
  · intro hp
    obtain ⟨q, rfl⟩ := (EuclideanGeometry.o.rotation (ω : Real.Angle)).surjective p
    change 0 ≤ inner ℝ (rotationMap (ω : Real.Angle) q)
        (normalVector (ω : Real.Angle)) ∧
      inner ℝ (rotationMap (ω : Real.Angle) q) (normalVector (ω : Real.Angle)) ≤ 1 at hp
    exact ⟨q, by
      simpa only [inner_rotationMap_normalVector, Set.mem_ofPred_eq] using hp, rfl⟩

/-- Projection on the downward unit normal negates the vertical coordinate. -/
theorem inner_normalVector_three_pi_div_two (p : Point) :
    inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) = -p 1 := by
  simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
    show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring, Real.cos_add, Real.sin_add,
    -Real.Angle.coe_add]

/-- The horizontal coordinate is the projection on the normal at angle zero. -/
theorem inner_normalVector_zero (p : Point) :
    inner ℝ p (normalVector ((0 : ℝ) : Real.Angle)) = p 0 := by
  simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]

/-- The vertical coordinate is the projection on the tangent at angle zero. -/
theorem inner_tangentVector_zero (p : Point) :
    inner ℝ p (tangentVector ((0 : ℝ) : Real.Angle)) = p 1 := by
  simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two]

/-- The vertical coordinate is the projection on the upward unit normal. -/
theorem inner_normalVector_pi_div_two (p : Point) :
    inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = p 1 := by
  simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]

/-- Projection on the leftward tangent at a right angle negates the horizontal coordinate. -/
theorem inner_tangentVector_pi_div_two (p : Point) :
    inner ℝ p (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) = -p 0 := by
  simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two]

/-- Projection on the leftward tangent at the straight angle negates the vertical coordinate. -/
theorem inner_tangentVector_pi (p : Point) :
    inner ℝ p (tangentVector ((Real.pi : ℝ) : Real.Angle)) = -p 1 := by
  simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two]

/-- The projection of a multiple of the horizontal normal on another unit normal. -/
theorem inner_smul_normalVector_zero (x t : ℝ) :
    inner ℝ (x • normalVector (0 : Real.Angle)) (normalVector (t : Real.Angle)) =
      x * Real.cos t := by
  simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

/-- The horizontal bottom of the strip intersection has zero downward support. -/
theorem supportValue_stripParallelogram_bottom (ω : ℝ) :
    supportValue (stripParallelogram ω).1 ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
  have hzero : (0 : Point) ∈ (stripParallelogram ω).1 := by
    rw [mem_stripParallelogram_iff]
    simp
  have hbound : ∀ y ∈ (fun p ↦ inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle))) ''
      (stripParallelogram ω).1, y ≤ 0 := by
    rintro y ⟨p, hp, rfl⟩
    dsimp only
    rw [inner_normalVector_three_pi_div_two]
    exact neg_nonpos.mpr ((mem_stripParallelogram_iff ω p).1 hp).1.1
  have hmem : (0 : ℝ) ∈ (fun p ↦ inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle))) ''
      (stripParallelogram ω).1 := ⟨0, hzero, by simp⟩
  exact le_antisymm (csSup_le ⟨0, hmem⟩ hbound) (le_csSup ⟨0, hbound⟩ hmem)

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
# Geometry / Parallelogram Gap
-/

@[expose] public section

noncomputable section

namespace MovingSofa

theorem parallelogram_gap (ω : ℝ) (hω : ω ∈ Set.Ico 0 (Real.pi / 2)) :
    (stripParallelogram ω).2.2 - tangentVector 0 =
      Real.tan ((Real.pi / 2 - ω) / 2) • normalVector 0 ∧
    (stripParallelogram ω).2.2 - normalVector (ω : Real.Angle) =
      Real.tan ((Real.pi / 2 - ω) / 2) • tangentVector (ω : Real.Angle) ∧
    (stripParallelogram ω).1 ∩
        (supportingLineHalfPlane (stripParallelogram ω).1
          ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1 =
      segment ℝ (0 : Point) ((Real.cos ω)⁻¹ • normalVector 0) ∧
    normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 ∩
        normalLine (ω : Real.Angle) 1 =
      {((Real.cos ω)⁻¹ • normalVector 0 : Point)} ∧
    Real.tan ((Real.pi / 2 - ω) / 2) = (Real.cos ω)⁻¹ - Real.tan ω := by
  have hcos : 0 < Real.cos ω :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hω.1], hω.2⟩
  have hgap := Real.tan_pi_div_two_sub_div_two ω hω
  have hfirst : (stripParallelogram ω).2.2 - tangentVector 0 =
      Real.tan ((Real.pi / 2 - ω) / 2) • normalVector 0 := by
    ext i
    fin_cases i <;> simp [stripParallelogram, normalVector, tangentVector, frame]
    ring_nf
  have hsecond : (stripParallelogram ω).2.2 - normalVector (ω : Real.Angle) =
      Real.tan ((Real.pi / 2 - ω) / 2) • tangentVector (ω : Real.Angle) := by
    have harg : Real.pi / 4 - ω / 2 = (Real.pi / 2 - ω) / 2 := by ring
    have hc : Real.tan ((Real.pi / 2 - ω) / 2) * Real.cos ω = 1 - Real.sin ω := by
      rw [hgap, Real.tan_eq_sin_div_cos]
      field_simp [hcos.ne']
    have hc' : Real.tan ((Real.pi / 2 - ω) / 2) * (1 + Real.sin ω) =
        Real.cos ω := by
      rw [hgap, Real.tan_eq_sin_div_cos]
      field_simp [hcos.ne']
      nlinarith [Real.sin_sq_add_cos_sq ω]
    ext i
    fin_cases i <;>
      simp [stripParallelogram, normalVector, tangentVector, frame, harg] <;> nlinarith
  have hedge : (stripParallelogram ω).1 ∩
        (supportingLineHalfPlane (stripParallelogram ω).1
          ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1 =
      segment ℝ (0 : Point) ((Real.cos ω)⁻¹ • normalVector 0) := by
    rw [supportingLineHalfPlane, supportValue_stripParallelogram_bottom]
    ext p
    simp only [Set.mem_inter_iff, mem_stripParallelogram_iff, normalLine,
      Set.mem_ofPred_eq, segment_eq_image, Set.mem_image, Set.mem_Icc]
    rw [inner_normalVector_three_pi_div_two]
    constructor
    · rintro ⟨⟨⟨hp₀, hp₁⟩, hq₀, hq₁⟩, hbottom⟩
      have hpzero : p 1 = 0 := by linarith
      have hx₀ : 0 ≤ p 0 * Real.cos ω := by
        simpa [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two, hpzero,
          mul_comm] using hq₀
      have hx₁ : p 0 * Real.cos ω ≤ 1 := by
        simpa [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two, hpzero,
          mul_comm] using hq₁
      refine ⟨p 0 * Real.cos ω, ⟨hx₀, hx₁⟩, ?_⟩
      ext i
      fin_cases i <;> simp [normalVector, frame, hpzero, hcos.ne']
    · rintro ⟨x, hx, rfl⟩
      have hinner : inner ℝ (x • (Real.cos ω)⁻¹ • normalVector 0)
          (normalVector (ω : Real.Angle)) = x := by
        simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
        field_simp [hcos.ne']
      constructor
      · exact ⟨by simp [normalVector, frame], by simpa [hinner] using hx⟩
      · simp [normalVector, frame]
  have hintersection : normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 ∩
        normalLine (ω : Real.Angle) 1 =
      {((Real.cos ω)⁻¹ • normalVector 0 : Point)} := by
    ext p
    simp only [Set.mem_inter_iff, normalLine, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hvertical, hrotated⟩
      have hpone : p 1 = 0 := by
        simpa [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] using hvertical
      have hpzero : p 0 * Real.cos ω = 1 := by
        simpa [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two, hpone,
          mul_comm] using hrotated
      ext i
      fin_cases i
      · simp [normalVector, frame]
        field_simp [hcos.ne']
        exact hpzero
      · simp [normalVector, frame, hpone]
    · intro hp
      rw [hp]
      constructor
      · simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
      · simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
        field_simp [hcos.ne']
  exact ⟨hfirst, hsecond, hedge, hintersection, hgap⟩

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
# Geometry / Path Half Plane Cap
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The set satisfying the horizontal base and all upper support constraints of a path. -/
def outerPathConstraintSet (x : Set.Icc (0 : ℝ) (Real.pi / 2) → Point) : Set Point :=
  {q | 0 ≤ q 1 ∧ ∀ t,
    inner ℝ q (normalVector (t.val : Real.Angle)) ≤
      inner ℝ (x t) (normalVector (t.val : Real.Angle)) + 1 ∧
    inner ℝ q (tangentVector (t.val : Real.Angle)) ≤
      inner ℝ (x t) (tangentVector (t.val : Real.Angle)) + 1}

theorem outerPathConstraintSet_isCap
    (x : Set.Icc (0 : ℝ) (Real.pi / 2) → Point)
    (hx : x ⟨0, le_rfl, by positivity⟩ = 0)
    (hbottom : ∃ p ∈ outerPathConstraintSet x, p 1 = 0)
    (htop : ∃ p ∈ outerPathConstraintSet x, p 1 = 1) :
    ∃ K : ConvexBody Point, (K : Set Point) = outerPathConstraintSet x ∧
      IsCap (Real.pi / 2) K := by
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hxO : x ⟨0, le_rfl, hpi⟩ = 0 := hx
  -- half-plane representation with cap-admissible normals
  obtain ⟨C, hCnormals, hrep⟩ :
      ∃ C : Set (Real.Angle × ℝ),
        (∀ c ∈ C, c.1 ∈ ((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles (Real.pi / 2)) ∪
          capLowerNormals (Real.pi / 2)) ∧
        outerPathConstraintSet x = ⋂ c ∈ C, normalHalfPlane c.1 c.2 false false := by
    refine ⟨{(((3 * Real.pi / 2 : ℝ) : Real.Angle), (0 : ℝ))} ∪
      ((Set.range fun t : Set.Icc (0 : ℝ) (Real.pi / 2) ↦
          (((t.val : ℝ) : Real.Angle),
            inner ℝ (x t) (normalVector ((t.val : ℝ) : Real.Angle)) + 1)) ∪
        (Set.range fun t : Set.Icc (0 : ℝ) (Real.pi / 2) ↦
          (((t.val + Real.pi / 2 : ℝ) : Real.Angle),
            inner ℝ (x t) (tangentVector ((t.val : ℝ) : Real.Angle)) + 1))), ?_, ?_⟩
    · rintro c (rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩)
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl ⟨t.val, Or.inl ⟨t.2.1, t.2.2⟩, rfl⟩
      · exact Or.inl ⟨t.val + Real.pi / 2,
          Or.inr ⟨by linarith [t.2.1], by linarith [t.2.2]⟩, rfl⟩
    · ext q
      simp only [Set.mem_iInter, Set.mem_union, Set.mem_singleton_iff, Set.mem_range]
      constructor
      · rintro ⟨hq0, hqt⟩ c (rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩)
        · change inner ℝ q (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤ 0
          rw [inner_normalVector_three_pi_div_two]
          linarith
        · exact (hqt t).1
        · change inner ℝ q (normalVector ((t.val + Real.pi / 2 : ℝ) : Real.Angle)) ≤ _
          rw [normalVector_add_pi_div_two_real]
          exact (hqt t).2
      · intro hq
        refine ⟨?_, fun t ↦ ⟨?_, ?_⟩⟩
        · have h : inner ℝ q (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤ 0 :=
            hq _ (Or.inl rfl)
          rw [inner_normalVector_three_pi_div_two] at h
          linarith
        · exact hq _ (Or.inr (Or.inl ⟨t, rfl⟩))
        · have h : inner ℝ q (normalVector ((t.val + Real.pi / 2 : ℝ) : Real.Angle)) ≤
              inner ℝ (x t) (tangentVector ((t.val : ℝ) : Real.Angle)) + 1 :=
            hq _ (Or.inr (Or.inr ⟨t, rfl⟩))
          rwa [normalVector_add_pi_div_two_real] at h
  -- the constraints at the two endpoints confine the set to a bounded rectangle
  have hxbox : ∀ q ∈ outerPathConstraintSet x,
      x ⟨Real.pi / 2, hpi, le_rfl⟩ 0 - 1 ≤ q 0 ∧ q 0 ≤ 1 ∧ 0 ≤ q 1 ∧ q 1 ≤ 1 := by
    rintro q ⟨hq0, hqt⟩
    have h0n : inner ℝ q (normalVector ((0 : ℝ) : Real.Angle)) ≤
        inner ℝ (x ⟨0, le_rfl, hpi⟩) (normalVector ((0 : ℝ) : Real.Angle)) + 1 :=
      (hqt ⟨0, le_rfl, hpi⟩).1
    have h0t : inner ℝ q (tangentVector ((0 : ℝ) : Real.Angle)) ≤
        inner ℝ (x ⟨0, le_rfl, hpi⟩) (tangentVector ((0 : ℝ) : Real.Angle)) + 1 :=
      (hqt ⟨0, le_rfl, hpi⟩).2
    have hTt : inner ℝ q (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≤
        inner ℝ (x ⟨Real.pi / 2, hpi, le_rfl⟩)
          (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) + 1 :=
      (hqt ⟨Real.pi / 2, hpi, le_rfl⟩).2
    rw [hxO, inner_zero_left, inner_normalVector_zero] at h0n
    rw [hxO, inner_zero_left, inner_tangentVector_zero] at h0t
    rw [inner_tangentVector_pi_div_two, inner_tangentVector_pi_div_two] at hTt
    exact ⟨by linarith, by linarith, hq0, by linarith⟩
  obtain ⟨pb, hpb, hpb1⟩ := hbottom
  obtain ⟨pt, hpt, hpt1⟩ := htop
  obtain ⟨K, hKset⟩ : ∃ K : ConvexBody Point, (K : Set Point) = outerPathConstraintSet x := by
    refine ⟨{ carrier := outerPathConstraintSet x
              convex' := ?_
              isCompact' := ?_
              nonempty' := ⟨pb, hpb⟩ }, rfl⟩
    · rw [hrep]
      exact convex_iInter fun c ↦ convex_iInter fun _ ↦ convex_normalHalfPlane c.1 c.2 false
    · refine Metric.isCompact_iff_isClosed_bounded.2 ⟨?_, ?_⟩
      · rw [hrep]
        exact isClosed_iInter fun c ↦ isClosed_iInter fun _ ↦
          isClosed_normalHalfPlane c.1 c.2 false
      · refine (EuclideanSpace.isBounded_coordinate_rectangle
          (x ⟨Real.pi / 2, hpi, le_rfl⟩ 0 - 1) 1 0 1).subset fun q hq ↦ ?_
        obtain ⟨h1, h2, h3, h4⟩ := hxbox q hq
        exact ⟨h1, h2, h3, h4⟩
  -- the strip inclusion and the two contacts fix the four normalized support values
  have hsvTop : supportValue (K : Set Point) ((Real.pi / 2 : ℝ) : Real.Angle) = 1 := by
    refine le_antisymm (supportValue_le_of_subset_normalHalfPlane K _ 1 fun q hq ↦ ?_) ?_
    · change inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≤ 1
      rw [inner_normalVector_pi_div_two]
      rw [hKset] at hq
      exact (hxbox q hq).2.2.2
    · have h := inner_le_supportValue K (hKset ▸ hpt) ((Real.pi / 2 : ℝ) : Real.Angle)
      rwa [inner_normalVector_pi_div_two, hpt1] at h
  have hsvBot : supportValue (K : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
    refine le_antisymm (supportValue_le_of_subset_normalHalfPlane K _ 0 fun q hq ↦ ?_) ?_
    · change inner ℝ q (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤ 0
      rw [inner_normalVector_three_pi_div_two]
      rw [hKset] at hq
      linarith [(hxbox q hq).2.2.1]
    · have h := inner_le_supportValue K (hKset ▸ hpb) ((3 * Real.pi / 2 : ℝ) : Real.Angle)
      rwa [inner_normalVector_three_pi_div_two, hpb1, neg_zero] at h
  have hang : ((Real.pi / 2 + Real.pi : ℝ) : Real.Angle) =
      ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
    congr 1
    ring
  exact ⟨K, hKset, by positivity, le_rfl, hsvTop, hsvTop, by rw [hang]; exact hsvBot, hsvBot,
    C, hCnormals, hKset.trans hrep⟩

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
# Geometry / Reflection
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- Exchange the two coordinates of the Euclidean plane. -/
def coordinateSwap : Point ≃ₗᵢ[ℝ] Point :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap 0 1)

/-- Reflection exchanging the normals at angles zero and `ω + π / 2`. -/
def capReflection (ω : ℝ) : Point ≃ₗᵢ[ℝ] Point :=
  coordinateSwap.trans (EuclideanGeometry.o.rotation (ω : Real.Angle))

/-- First coordinate of the cap reflection. -/
theorem capReflection_apply_zero (ω : ℝ) (p : Point) :
    capReflection ω p 0 = -Real.sin ω * p 0 + Real.cos ω * p 1 := by
  rw [capReflection, LinearIsometryEquiv.trans_apply, Orientation.rotation_apply,
    rightAngleRotation_apply]
  simp [coordinateSwap]
  ring

/-- Second coordinate of the cap reflection. -/
theorem capReflection_apply_one (ω : ℝ) (p : Point) :
    capReflection ω p 1 = Real.cos ω * p 0 + Real.sin ω * p 1 := by
  rw [capReflection, LinearIsometryEquiv.trans_apply, Orientation.rotation_apply,
    rightAngleRotation_apply]
  simp [coordinateSwap]

/-- Reflection across the line through the upper vertex of the cap strip. -/
def stripTopReflection (ω : ℝ) (p : Point) : Point :=
  (2 * inner ℝ p (stripParallelogram ω).2.2 /
    inner ℝ (stripParallelogram ω).2.2 (stripParallelogram ω).2.2) •
      (stripParallelogram ω).2.2 - p

/-- The strip-top reflection is the explicit cap reflection. -/
theorem stripTopReflection_eq_capReflection (ω : ℝ)
    (hω0 : 0 < ω) (hωle : ω ≤ Real.pi / 2) :
    stripTopReflection ω = capReflection ω := by
  funext p
  by_cases hωtop : ω = Real.pi / 2
  · subst ω
    have harg : Real.pi / 4 - (Real.pi / 2) / 2 = 0 := by ring
    ext i
    fin_cases i
    · change stripTopReflection (Real.pi / 2) p 0 = capReflection (Real.pi / 2) p 0
      rw [capReflection_apply_zero]
      simp [stripTopReflection, stripParallelogram, harg, PiLp.inner_apply,
        Fin.sum_univ_two]
    · change stripTopReflection (Real.pi / 2) p 1 = capReflection (Real.pi / 2) p 1
      rw [capReflection_apply_one]
      have hnorm : ‖(!₂[0, 1] : Point)‖ ^ 2 = 1 := by
        simpa [Fin.sum_univ_two] using
          (EuclideanSpace.norm_sq_eq (!₂[0, 1] : Point))
      simp [stripTopReflection, stripParallelogram, harg, PiLp.inner_apply,
        Fin.sum_univ_two, hnorm]
      ring
  · have hωlt : ω < Real.pi / 2 := lt_of_le_of_ne hωle hωtop
    let C := Real.cos ω
    let S := Real.sin ω
    let c := Real.tan (Real.pi / 4 - ω / 2)
    have hC : 0 < C :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hω0], hωlt⟩
    have hgap : c = C⁻¹ - Real.tan ω := by
      simpa [c, show Real.pi / 4 - ω / 2 = (Real.pi / 2 - ω) / 2 by ring]
        using Real.tan_pi_div_two_sub_div_two ω ⟨hω0.le, hωlt⟩
    have htan : Real.tan ω = S / C := Real.tan_eq_sin_div_cos ω
    have hcC : c * C = 1 - S := by
      rw [hgap, htan]
      field_simp [hC.ne']
    have hc : c * (1 + S) = C := by
      rw [hgap, htan]
      field_simp [hC.ne']
      nlinarith [hcC, Real.sin_sq_add_cos_sq ω]
    have hcsq : c * c * (1 + S) = 1 - S := by
      calc
        c * c * (1 + S) = c * (c * (1 + S)) := by ring
        _ = c * C := by rw [hc]
        _ = 1 - S := hcC
    have hcoef₀ : c * c - 1 = -S * (c * c + 1) := by
      nlinarith [hcsq]
    have hbase : 2 = (1 + S) * (c * c + 1) := by
      nlinarith [hcoef₀]
    have hcoef₁ : 2 * c = C * (c * c + 1) := by
      rw [← hc]
      linear_combination c * hbase
    have hcoef₂ : 1 - c * c = S * (c * c + 1) := by
      nlinarith [hcsq]
    have hden : c * c + 1 ≠ 0 := by nlinarith [sq_nonneg c]
    ext i
    fin_cases i
    · change stripTopReflection ω p 0 = capReflection ω p 0
      rw [capReflection_apply_zero]
      simp only [stripTopReflection, stripParallelogram, PiLp.inner_apply,
        Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Real.inner_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      simp only [mul_one]
      change 2 * (p 0 * c + p 1) / (c * c + 1) * c - p 0 =
        -S * p 0 + C * p 1
      field_simp [hden]
      linear_combination (p 0) * hcoef₀ + (p 1) * hcoef₁
    · change stripTopReflection ω p 1 = capReflection ω p 1
      rw [capReflection_apply_one]
      simp only [stripTopReflection, stripParallelogram, PiLp.inner_apply,
        Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Real.inner_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      simp only [mul_one]
      change 2 * (p 0 * c + p 1) / (c * c + 1) - p 1 =
        C * p 0 + S * p 1
      field_simp [hden]
      linear_combination (p 0) * hcoef₁ + (p 1) * hcoef₂

/-- The strip-top reflection fixes the upper strip vertex. -/
theorem stripTopReflection_stripTop (ω : ℝ) :
    stripTopReflection ω (stripParallelogram ω).2.2 =
      (stripParallelogram ω).2.2 := by
  have ho : (stripParallelogram ω).2.2 ≠ (0 : Point) := by
    intro h
    have h1 := congrArg (fun p : Point ↦ p 1) h
    simp [stripParallelogram] at h1
  unfold stripTopReflection
  have hden : inner ℝ (stripParallelogram ω).2.2
      (stripParallelogram ω).2.2 ≠ 0 := inner_self_ne_zero.mpr ho
  rw [mul_div_assoc, div_self hden]
  module

/-- The cap reflection is an involution. -/
theorem capReflection_involutive (ω : ℝ) (p : Point) :
    capReflection ω (capReflection ω p) = p := by
  ext i
  fin_cases i
  · change capReflection ω (capReflection ω p) 0 = p 0
    rw [capReflection_apply_zero, capReflection_apply_zero, capReflection_apply_one]
    linear_combination (p 0) * (Real.sin_sq_add_cos_sq ω)
  · change capReflection ω (capReflection ω p) 1 = p 1
    rw [capReflection_apply_one, capReflection_apply_zero, capReflection_apply_one]
    linear_combination (p 1) * (Real.sin_sq_add_cos_sq ω)

/-- Reflection of a normal angle across the cap-reflection axis. -/
def reflectedAngle (ω : ℝ) (a : Real.Angle) : Real.Angle :=
  ((ω + Real.pi / 2 : ℝ) : Real.Angle) - a

/-- Reflection of normal angles is involutive. -/
theorem reflectedAngle_involutive (ω : ℝ) (a : Real.Angle) :
    reflectedAngle ω (reflectedAngle ω a) = a := by
  simp only [reflectedAngle]
  abel

/-- Coercion formula for a reflected real angle. -/
theorem reflectedAngle_coe (ω t : ℝ) :
    reflectedAngle ω (t : Real.Angle) =
      ((ω + Real.pi / 2 - t : ℝ) : Real.Angle) := by
  simp only [reflectedAngle, Real.Angle.coe_sub, Real.Angle.coe_add]

/-- The cap reflection transports normal vectors at real angles. -/
theorem capReflection_normalVector (ω a : ℝ) :
    capReflection ω (normalVector (a : Real.Angle)) =
      normalVector ((ω + Real.pi / 2 - a : ℝ) : Real.Angle) := by
  have hrho : (ω : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) -
      (a : Real.Angle) = ((ω + Real.pi / 2 - a : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_add, ← Real.Angle.coe_sub]
  ext i
  fin_cases i
  · change capReflection ω (normalVector (a : Real.Angle)) 0 =
      normalVector ((ω + Real.pi / 2 - a : ℝ) : Real.Angle) 0
    rw [capReflection_apply_zero, ← hrho]
    simp only [Fin.isValue, normalVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe,
      Matrix.cons_val_zero, neg_mul, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [hrho, Real.Angle.cos_coe, Real.cos_sub, Real.sin_add, Real.cos_add]
    simp
  · change capReflection ω (normalVector (a : Real.Angle)) 1 =
      normalVector ((ω + Real.pi / 2 - a : ℝ) : Real.Angle) 1
    rw [capReflection_apply_one, ← hrho]
    simp only [Fin.isValue, normalVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [hrho, Real.Angle.sin_coe, Real.sin_sub, Real.sin_add, Real.cos_add]
    simp

/-- The cap reflection reverses tangent vectors at real angles. -/
theorem capReflection_tangentVector (ω a : ℝ) :
    capReflection ω (tangentVector (a : Real.Angle)) =
      -tangentVector ((ω + Real.pi / 2 - a : ℝ) : Real.Angle) := by
  have hrho : (ω : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) -
      (a : Real.Angle) = ((ω + Real.pi / 2 - a : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_add, ← Real.Angle.coe_sub]
  ext i
  fin_cases i
  · change capReflection ω (tangentVector (a : Real.Angle)) 0 =
      (-tangentVector ((ω + Real.pi / 2 - a : ℝ) : Real.Angle)) 0
    rw [capReflection_apply_zero, ← hrho]
    simp only [Fin.isValue, tangentVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe,
      Matrix.cons_val_zero, mul_neg, neg_mul, neg_neg, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, PiLp.neg_apply]
    rw [hrho, Real.Angle.sin_coe, Real.sin_sub, Real.sin_add, Real.cos_add]
    simp
    ring
  · change capReflection ω (tangentVector (a : Real.Angle)) 1 =
      (-tangentVector ((ω + Real.pi / 2 - a : ℝ) : Real.Angle)) 1
    rw [capReflection_apply_one, ← hrho]
    simp only [Fin.isValue, tangentVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe,
      Matrix.cons_val_zero, mul_neg, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      PiLp.neg_apply]
    rw [hrho, Real.Angle.cos_coe, Real.cos_sub, Real.sin_add, Real.cos_add]
    simp

/-- The cap reflection transports normal vectors by reflected angles. -/
theorem capReflection_normalVector_angle (ω : ℝ) (a : Real.Angle) :
    capReflection ω (normalVector a) = normalVector (reflectedAngle ω a) := by
  calc
    capReflection ω (normalVector a) =
        capReflection ω (normalVector (a.toReal : Real.Angle)) := by rw [a.coe_toReal]
    _ = normalVector ((ω + Real.pi / 2 - a.toReal : ℝ) : Real.Angle) :=
      capReflection_normalVector ω a.toReal
    _ = normalVector (reflectedAngle ω a) := by
      congr 1
      simp only [reflectedAngle, Real.Angle.coe_sub, Real.Angle.coe_add, a.coe_toReal]

/-- The cap reflection reverses tangent vectors at reflected angles. -/
theorem capReflection_tangentVector_angle (ω : ℝ) (a : Real.Angle) :
    capReflection ω (tangentVector a) = -tangentVector (reflectedAngle ω a) := by
  calc
    capReflection ω (tangentVector a) =
        capReflection ω (tangentVector (a.toReal : Real.Angle)) := by rw [a.coe_toReal]
    _ = -tangentVector ((ω + Real.pi / 2 - a.toReal : ℝ) : Real.Angle) :=
      capReflection_tangentVector ω a.toReal
    _ = -tangentVector (reflectedAngle ω a) := by
      congr 2
      simp only [reflectedAngle, Real.Angle.coe_sub, Real.Angle.coe_add, a.coe_toReal]

/-- Inner products with normals transform under the cap reflection. -/
theorem inner_capReflection_normalVector (ω : ℝ) (p : Point)
    (a : Real.Angle) :
    inner ℝ (capReflection ω p) (normalVector a) =
      inner ℝ p (normalVector (reflectedAngle ω a)) := by
  have hn : capReflection ω (normalVector (reflectedAngle ω a)) =
      normalVector a := by
    rw [capReflection_normalVector_angle, reflectedAngle_involutive]
  rw [← hn]
  exact (capReflection ω).inner_map_map p (normalVector (reflectedAngle ω a))

/-- Inner products with tangents transform under the cap reflection. -/
theorem inner_capReflection_tangentVector (ω : ℝ) (p : Point)
    (a : Real.Angle) :
    inner ℝ (capReflection ω p) (tangentVector a) =
      -inner ℝ p (tangentVector (reflectedAngle ω a)) := by
  have ht : capReflection ω (-tangentVector (reflectedAngle ω a)) =
      tangentVector a := by
    rw [map_neg, capReflection_tangentVector_angle, reflectedAngle_involutive,
      neg_neg]
  rw [← ht, (capReflection ω).inner_map_map, inner_neg_right]

/-- The cap reflection transports every open or closed normal half-plane. -/
theorem capReflection_image_normalHalfPlane (ω h : ℝ)
    (a : Real.Angle) (upper strict : Bool) :
    capReflection ω '' normalHalfPlane a h upper strict =
      normalHalfPlane (reflectedAngle ω a) h upper strict := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    cases upper <;> cases strict <;>
      simp only [normalHalfPlane, Bool.false_eq_true, ↓reduceIte,
        Set.mem_ofPred_eq] at hq ⊢ <;>
      rwa [inner_capReflection_normalVector, reflectedAngle_involutive]
  · intro hp
    refine ⟨capReflection ω p, ?_, capReflection_involutive ω p⟩
    cases upper <;> cases strict <;>
      simp only [normalHalfPlane, Bool.false_eq_true, ↓reduceIte,
        Set.mem_ofPred_eq] at hp ⊢ <;>
      rwa [inner_capReflection_normalVector]

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
# Geometry / Supporting Hallway
-/

@[expose] public section

noncomputable section

namespace MovingSofa

private theorem supportValue_le_of_subset_rotatedHallway (s : Set Point) (t : Real.Angle)
    (hs : s.Nonempty) (v : Point)
    (hv : s ⊆ (fun p ↦ rotationMap t p + v) '' hallway) :
    supportValue s t ≤ 1 + inner ℝ v (normalVector t) ∧
      supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) ≤
        1 + inner ℝ v (tangentVector t) := by
  have hbound₁ : supportValue s t ≤ 1 + inner ℝ v (normalVector t) := by
    apply csSup_le (hs.image _)
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨q, hq, rfl⟩ := hv hp
    dsimp only
    rw [inner_add_left, inner_rotationMap_normalVector]
    linarith [(mem_hallway_iff q).mp hq |>.1.1]
  have hbound₂ : supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) ≤
      1 + inner ℝ v (tangentVector t) := by
    apply csSup_le (hs.image _)
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨q, hq, rfl⟩ := hv hp
    dsimp only
    rw [normalVector_add_pi_div_two, inner_add_left, inner_rotationMap_tangentVector]
    linarith [(mem_hallway_iff q).mp hq |>.1.2]
  exact ⟨hbound₁, hbound₂⟩

theorem subset_supportingHallway (s : Set Point) (t : Real.Angle)
    (hs : s.Nonempty) (hc : IsCompact s)
    (hL : ∃ v : Point, s ⊆ (fun p ↦ rotationMap t p + v) '' hallway) :
    s ⊆ supportingHallway s t := by
  rcases hL with ⟨v, hv⟩
  obtain ⟨hbound₁, hbound₂⟩ := supportValue_le_of_subset_rotatedHallway s t hs v hv
  intro p hp
  obtain ⟨x, hx⟩ := (EuclideanGeometry.o.rotation t).surjective
    (p - (supportValue s t - 1) • normalVector t -
      (supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) • tangentVector t)
  have hxp : supportingPlacement s t x = p := by
    simp only [supportingPlacement, rotationMap, hx]
    abel
  have hx₀ := inner_supportingPlacement_normalVector s t x
  have hx₁ := inner_supportingPlacement_tangentVector s t x
  rw [hxp] at hx₀ hx₁
  have hsup (w : Real.Angle) : inner ℝ p (normalVector w) ≤ supportValue s w :=
    le_csSup (hc.bddAbove_image (continuous_id.inner continuous_const).continuousOn)
      ⟨p, hp, rfl⟩
  have hupper₀ := hsup t
  have hupper₁ := hsup (t + ((Real.pi / 2 : ℝ) : Real.Angle))
  rw [normalVector_add_pi_div_two] at hupper₁
  refine ⟨x, (mem_hallway_iff x).mpr ⟨⟨by linarith, by linarith⟩, ?_⟩, hxp⟩
  obtain ⟨q, hq, hqp⟩ := hv hp
  rcases (mem_hallway_iff q).mp hq |>.2 with hq₀ | hq₁
  · have hcoord : inner ℝ p (normalVector t) = q 0 + inner ℝ v (normalVector t) := by
      rw [← hqp, inner_add_left, inner_rotationMap_normalVector]
    exact Or.inl (by linarith)
  · have hcoord : inner ℝ p (tangentVector t) = q 1 + inner ℝ v (tangentVector t) := by
      rw [← hqp, inner_add_left, inner_rotationMap_tangentVector]
    exact Or.inr (by linarith)

end MovingSofa

end

end

end

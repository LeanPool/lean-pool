/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.Foundation.Batch001
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Foundation.Batch001
public import LeanPool.MovingSofa.GerverSofa.Foundation.Batch002
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic
public import Mathlib.Topology.Algebra.ContinuousAffineMap.Topology
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartF.F01AffineOrder`.
* `KernelOnly.PartF.F01PhaseAlgebra`.
* `KernelOnly.PartF.F01SetMotion`.
* `KernelOnly.PartF.F02Coordinates`.
* `KernelOnly.PartF.F04IntegralPrimitives`.
* `KernelOnly.PartF.F04IntegralEvaluation`.
* `KernelOnly.PartF.F05DictionaryEquations`.
* `KernelOnly.PartF.F06ReverseSystem`.
* `KernelOnly.PartF.F06FullReconstruction`.
-/

@[expose] public section

noncomputable section


section

/-!
# F01: the affine-order bridge for issue #5270

The two constructors are deliberately given different names. No upstream
definition is changed or imported, and no theorem from the conjecture file
is used. Both application conventions and the conversion between them are
proved for an arbitrary linear isometry equivalence.
-/

@[expose] public section

noncomputable section

namespace GerverSofa.PartF

/-- The Euclidean plane used for the continuous rigid-motion formulation. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)
/-- Affine isometries of the Euclidean plane. -/
abbrev Rigid := Plane ≃ᵃⁱ[ℝ] Plane

/-- The ordered coordinate-basis orientation used by the pinned upstream
`FormalConjecturesForMathlib/Geometry/2d.lean`. Importing `Mathlib` alone
does not install that project's plane-orientation instance. -/
instance planeOriented : Module.Oriented ℝ Plane (Fin 2) :=
  ⟨Module.Basis.orientation <| PiLp.basisFun 2 _ _⟩

/-- The second instance supplied by the same upstream plane helper. -/
instance planeFactFinrank : Fact (Module.finrank ℝ Plane = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The topology used by the pinned `MovingSofa.IsMovingSofa` definition. -/
instance rigidTopology : TopologicalSpace Rigid :=
  .induced (fun e => e.toAffineIsometry.toContinuousAffineMap) inferInstance

/-- The composition currently implemented upstream: `q ↦ R q + p`. -/
def rotateThenTranslate (R : Plane ≃ₗᵢ[ℝ] Plane) (p : Plane) : Rigid :=
  R.toAffineIsometryEquiv.trans (AffineIsometryEquiv.vaddConst ℝ p)

/-- The documented composition: `q ↦ R (q + p)`. -/
def translateThenRotate (R : Plane ≃ₗᵢ[ℝ] Plane) (p : Plane) : Rigid :=
  (AffineIsometryEquiv.vaddConst ℝ p).trans R.toAffineIsometryEquiv

@[simp] theorem rotateThenTranslate_apply
    (R : Plane ≃ₗᵢ[ℝ] Plane) (p q : Plane) :
    rotateThenTranslate R p q = R q + p := rfl

@[simp] theorem translateThenRotate_apply
    (R : Plane ≃ₗᵢ[ℝ] Plane) (p q : Plane) :
    translateThenRotate R p q = R (q + p) := rfl

/-- Keeping the old composition is equivalent to rotating the translation. -/
theorem translateThenRotate_eq_rotateThenTranslate
    (R : Plane ≃ₗᵢ[ℝ] Plane) (p : Plane) :
    translateThenRotate R p = rotateThenTranslate R (R p) := by
  ext q
  simp only [translateThenRotate_apply, rotateThenTranslate_apply, map_add]

/-- Counterclockwise rotation of the oriented plane through angle `t`. -/
def rotation (t : ℝ) : Plane ≃ₗᵢ[ℝ] Plane :=
  EuclideanGeometry.o.rotation (t : Real.Angle)

/-- Translate by the body-frame offset and then rotate through `t`. -/
def bodyFrame (t : ℝ) (p : Plane) : Rigid :=
  translateThenRotate (rotation t) p

/-- Rotate through `t` and then translate by the world position. -/
def worldFrame (t : ℝ) (x : Plane) : Rigid :=
  rotateThenTranslate (rotation t) x

theorem bodyFrame_eq_worldFrame (t : ℝ) (p : Plane) :
    bodyFrame t p = worldFrame t (rotation t p) :=
  translateThenRotate_eq_rotateThenTranslate (rotation t) p

end GerverSofa.PartF

end

end

end

section

/-!
# F01: algebraic half of the integral-to-five-phase representation

The coefficient dictionary and the five explicit body-frame branches come
from the 4 September integral-motion excerpt. They are compared to the
actual `Romik.path1` ... `Romik.path5` definitions, then assembled using the
same `if` boundaries as `Romik.path`.

This module does NOT evaluate the integrals: `closedPath` is explicitly
named as a closed-form candidate. Proving that the pinned integral path
equals it, and identifying `dictionary d` with the certified 22D tuple,
remain separate obligations. No such equality is assumed here.
-/

@[expose] public section

noncomputable section
namespace GerverSofa.PartF.Phases

/-- The terminal rotation angle π/2. -/
def T : ℝ := Real.pi / 2
/-- The auxiliary height parameter `(a + θ - φ - 1) / 2`. -/
def hStar (d : Reduced.Params) : ℝ := (d.a + d.theta - d.phi - 1) / 2
/-- Phase 4 integration constant for the vertical primitive. -/
def U4 (d : Reduced.Params) : ℝ :=
  (1 + d.a) / 2 * Real.cos d.phi - (d.b + 1 / 2) * Real.sin d.phi
/-- Phase 4 integration constant for the horizontal primitive. -/
def V4 (d : Reduced.Params) : ℝ :=
  1 - (d.b + 1 / 2) * Real.cos d.phi - (1 + d.a) / 2 * Real.sin d.phi
/-- Phase 3 integration constant for the vertical primitive. -/
def U3 (d : Reduced.Params) : ℝ :=
  U4 d + 1 / 2 * Real.sin d.theta - hStar d * Real.cos d.theta
/-- Phase 3 integration constant for the horizontal primitive. -/
def V3 (d : Reduced.Params) : ℝ :=
  V4 d + 1 / 2 * Real.cos d.theta + hStar d * Real.sin d.theta
/-- Phase 2 integration constant for the vertical primitive. -/
def U2 (d : Reduced.Params) : ℝ := U4 d
/-- Phase 2 integration constant for the horizontal primitive. -/
def V2 (d : Reduced.Params) : ℝ :=
  V4 d + Real.cos d.theta + 2 * hStar d * Real.sin d.theta
/-- Phase 1 integration constant for the vertical primitive. -/
def U1 (d : Reduced.Params) : ℝ :=
  U2 d + d.a / 2 * Real.cos d.phi - 1 / 2 * Real.sin d.phi
/-- Phase 1 integration constant for the horizontal primitive. -/
def V1 (d : Reduced.Params) : ℝ :=
  V2 d + d.a / 2 * Real.sin d.phi + 1 / 2 * Real.cos d.phi
/-- The first-phase offset determined by `4 V1 - 2`. -/
def ell (d : Reduced.Params) : ℝ := 4 * V1 d - 2

theorem U1_eq_half (d : Reduced.Params) (hd : Reduced.Equations d) :
    U1 d = 1 / 2 := by
  change Reduced.system d = 0 at hd
  have h := congrFun hd (2 : Fin 4)
  change d.a * Real.cos d.phi - Real.sin d.phi - 1 / 2 +
    1 / 2 * Real.cos d.phi - d.b * Real.sin d.phi = 0 at h
  dsimp [U1, U2, U4]
  linear_combination h

theorem ell_eq (d : Reduced.Params) (hd : Reduced.Equations d) :
    ell d = V2 d + V4 d := by
  change Reduced.system d = 0 at hd
  have h := congrFun hd (1 : Fin 4)
  change d.a * (3 * Real.sin d.theta + Real.sin d.phi) -
    2 * d.b * Real.cos d.phi +
    3 * (d.theta - d.phi - 1) * Real.sin d.theta +
    3 * Real.cos d.theta - Real.sin d.phi + Real.cos d.phi = 0 at h
  dsimp [ell, V1, V2, V4, hStar]
  linear_combination h

theorem ell_eq_two_V3 (d : Reduced.Params) (hd : Reduced.Equations d) :
    ell d = 2 * V3 d := by
  rw [ell_eq d hd]
  dsimp [V2, V3]
  ring

/-- Express all twenty-two Romik parameters in terms of the four reduced parameters. -/
def dictionary (d : Reduced.Params) : Romik.Params where
  k11 := 1 - 3 / 2 * (1 - V1 d)
  k12 := 1 / 4
  k21 := V4 d
  k22 := U4 d
  k31 := V3 d
  k32 := U3 d
  k41 := V2 d
  k42 := U4 d
  k51 := V1 d - 3 / 2 * (1 - V1 d)
  k52 := 1 / 4
  a1 := 3 / 2 * (1 - V1 d)
  a2 := -1 / 4
  b1 := (d.phi - 1 - d.a) / 2
  b2 := d.b - 1 / 2 + (1 + d.a) / 2 * d.phi - d.phi ^ 2 / 4
  c1 := d.a + T - d.phi - 1
  c2 := d.a - d.phi - 1
  d1 := (T - d.phi + 1 + d.a) / 2
  d2 := d.b - 1 / 2 - (1 + d.a) / 2 * (T - d.phi) - (T - d.phi)^2 / 4
  e1 := 3 / 2 * (1 - V1 d)
  e2 := 1 / 4
  phi := d.phi
  theta := d.theta

@[simp] theorem dictionary_phi (d : Reduced.Params) : (dictionary d).phi = d.phi := rfl
@[simp] theorem dictionary_theta (d : Reduced.Params) : (dictionary d).theta = d.theta := rfl

/-- The polynomial profile for phase 2 of the path. -/
def g2 (d : Reduced.Params) (t : ℝ) : ℝ := (1 + d.a + t - d.phi) / 2
/-- The polynomial profile for phase 3 of the path. -/
def g3 (d : Reduced.Params) (t : ℝ) : ℝ := d.a + t - d.phi
/-- The polynomial profile for phase 4 of the path. -/
def g4 (d : Reduced.Params) (t : ℝ) : ℝ :=
  d.b + 1 / 2 - (T - d.phi - t) * (1 + d.a) / 2 - (T - d.phi - t)^2 / 4

/-- The closed rotation-path formula for phase 1. -/
def closed1 (d : Reduced.Params) (t : ℝ) : Point :=
  (Real.cos t - 1,
    -1 / 2 + 1 / 2 * Real.cos t + (V1 d - ell d) * Real.sin t)

/-- The closed rotation-path formula for phase 2. -/
def closed2 (d : Reduced.Params) (t : ℝ) : Point :=
  (g4 d (T - t) + U4 d * Real.sin t + V4 d * Real.cos t - 1,
    g2 d t + U4 d * Real.cos t + (V2 d - ell d) * Real.sin t - 1)

/-- The closed rotation-path formula for phase 3. -/
def closed3 (d : Reduced.Params) (t : ℝ) : Point :=
  (g3 d (T - t) + U3 d * Real.sin t + V3 d * Real.cos t - 1,
    g3 d t + U3 d * Real.cos t + (V3 d - ell d) * Real.sin t - 1)

/-- The closed rotation-path formula for phase 4. -/
def closed4 (d : Reduced.Params) (t : ℝ) : Point :=
  (g2 d (T - t) + U4 d * Real.sin t + V2 d * Real.cos t - 1,
    g4 d t + U4 d * Real.cos t + (V4 d - ell d) * Real.sin t - 1)

/-- The closed rotation-path formula for phase 5. -/
def closed5 (d : Reduced.Params) (t : ℝ) : Point :=
  (-1 / 2 + V1 d * Real.cos t + 1 / 2 * Real.sin t,
    (1 - ell d) * Real.sin t - 1)

theorem phase1 (d : Reduced.Params) (t : ℝ) :
    Romik.rot t (closed1 d t) = Romik.path1 (dictionary d) t := by
  apply Prod.ext
  · dsimp [Romik.rot, closed1, Romik.path1, Romik.addK, dictionary, ell]
    linear_combination (1 - 3 / 2 * (1 - V1 d)) * Real.sin_sq_add_cos_sq t
  · dsimp [Romik.rot, closed1, Romik.path1, Romik.addK, dictionary, ell]
    linear_combination (1 / 4 : ℝ) * Real.sin_sq_add_cos_sq t

theorem phase2 (d : Reduced.Params) (hd : Reduced.Equations d) (t : ℝ) :
    Romik.rot t (closed2 d t) = Romik.path2 (dictionary d) t := by
  unfold closed2
  rw [ell_eq d hd]
  apply Prod.ext
  · dsimp [Romik.rot, Romik.path2, Romik.addK, dictionary, g2, g4, T]
    linear_combination V4 d * Real.sin_sq_add_cos_sq t
  · dsimp [Romik.rot, Romik.path2, Romik.addK, dictionary, g2, g4, T]
    linear_combination U4 d * Real.sin_sq_add_cos_sq t

theorem phase3 (d : Reduced.Params) (hd : Reduced.Equations d) (t : ℝ) :
    Romik.rot t (closed3 d t) = Romik.path3 (dictionary d) t := by
  unfold closed3
  rw [ell_eq_two_V3 d hd]
  apply Prod.ext
  · dsimp [Romik.rot, Romik.path3, Romik.addK, dictionary, g3, T]
    linear_combination V3 d * Real.sin_sq_add_cos_sq t
  · dsimp [Romik.rot, Romik.path3, Romik.addK, dictionary, g3, T]
    linear_combination U3 d * Real.sin_sq_add_cos_sq t

theorem phase4 (d : Reduced.Params) (hd : Reduced.Equations d) (t : ℝ) :
    Romik.rot t (closed4 d t) = Romik.path4 (dictionary d) t := by
  unfold closed4
  rw [ell_eq d hd]
  apply Prod.ext
  · dsimp [Romik.rot, Romik.path4, Romik.addK, dictionary, g2, g4, T]
    linear_combination V2 d * Real.sin_sq_add_cos_sq t
  · dsimp [Romik.rot, Romik.path4, Romik.addK, dictionary, g2, g4, T]
    linear_combination U4 d * Real.sin_sq_add_cos_sq t

theorem phase5 (d : Reduced.Params) (t : ℝ) :
    Romik.rot t (closed5 d t) = Romik.path5 (dictionary d) t := by
  apply Prod.ext
  · dsimp [Romik.rot, closed5, Romik.path5, Romik.addK, dictionary, ell]
    linear_combination (V1 d - 3 / 2 * (1 - V1 d)) * Real.sin_sq_add_cos_sq t
  · dsimp [Romik.rot, closed5, Romik.path5, Romik.addK, dictionary, ell]
    linear_combination (1 / 4 : ℝ) * Real.sin_sq_add_cos_sq t

/-- The five-branch closed formula for the rotation path. -/
def closedPath (d : Reduced.Params) (t : ℝ) : Point :=
  if t ≤ d.phi then closed1 d t
  else if t ≤ d.theta then closed2 d t
  else if t ≤ Real.pi / 2 - d.theta then closed3 d t
  else if t ≤ Real.pi / 2 - d.phi then closed4 d t
  else closed5 d t

/-- Exact assembly for the explicit closed path, including every switching
endpoint. This is not yet the corresponding theorem for the integral path. -/
theorem fivePhaseRepresentation (d : Reduced.Params)
    (hd : Reduced.Equations d) (t : ℝ) :
    Romik.rot t (closedPath d t) = Romik.path (dictionary d) t := by
  -- Expose both sets of conditions, including the local `eta` and `tau`
  -- definitions inside `Romik.path`, before choosing a branch.
  change Romik.rot t
      (if t ≤ d.phi then closed1 d t
       else if t ≤ d.theta then closed2 d t
       else if t ≤ Real.pi / 2 - d.theta then closed3 d t
       else if t ≤ Real.pi / 2 - d.phi then closed4 d t
       else closed5 d t) =
    (if t ≤ d.phi then Romik.path1 (dictionary d) t
     else if t ≤ d.theta then Romik.path2 (dictionary d) t
     else if t ≤ Real.pi / 2 - d.theta then Romik.path3 (dictionary d) t
     else if t ≤ Real.pi / 2 - d.phi then Romik.path4 (dictionary d) t
     else Romik.path5 (dictionary d) t)
  by_cases h1 : t ≤ d.phi
  · simpa only [ite_eq_left h1] using phase1 d t
  by_cases h2 : t ≤ d.theta
  · simpa only [ite_eq_right h1, ite_eq_left h2] using phase2 d hd t
  by_cases h3 : t ≤ Real.pi / 2 - d.theta
  · simpa only [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3] using phase3 d hd t
  by_cases h4 : t ≤ Real.pi / 2 - d.phi
  · simpa only [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_left h4] using phase4 d
      hd t
  · simpa only [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4] using phase5 d t

end GerverSofa.PartF.Phases

end

end

end

section

/-!
# F01: supporting intersections and their continuous inverse motion

`Model.IsMovingSofa` has the seven fields and the rigid-motion topology of
the upstream definition. This local, independently named model avoids
importing upstream conjectures with unfinished proof terms. Its concrete
instantiation for the integral Gerver path still needs the analytic bridge.
-/

@[expose] public section

noncomputable section
open scoped unitInterval

namespace GerverSofa.PartF

/-- Intersect the endpoint hallway arms and all intermediate moving hallways. -/
def frameIntersection (F : I → Rigid) (H V L : Set Plane) : Set Plane :=
  F 0 '' H ∩ F 1 '' V ∩ ⋂ s, F s '' L

/-- The hallway intersection parametrized by angles from zero to π/2. -/
def angleIntersection (F : ℝ → Rigid) (H V L : Set Plane) : Set Plane :=
  F 0 '' H ∩ F (Real.pi / 2) '' V ∩
    ⋂ t ∈ Set.Icc 0 (Real.pi / 2), F t '' L

/-- The hallway intersection generated by a path in body-frame coordinates. -/
def bodySofa (p : ℝ → Plane) (H V L : Set Plane) : Set Plane :=
  angleIntersection (fun t => bodyFrame t (p t)) H V L

/-- The hallway intersection generated by a path in world-frame coordinates. -/
def worldSofa (x : ℝ → Plane) (H V L : Set Plane) : Set Plane :=
  angleIntersection (fun t => worldFrame t (x t)) H V L

theorem bodySofa_eq_worldSofa_of_path_identity
    (p x : ℝ → Plane) (H V L : Set Plane)
    (hpath : ∀ t ∈ Set.Icc 0 (Real.pi / 2), x t = rotation t (p t)) :
    bodySofa p H V L = worldSofa x H V L := by
  have hT : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have h0 := hpath 0 ⟨le_rfl, hT⟩
  have h1 := hpath (Real.pi / 2) ⟨hT, le_rfl⟩
  -- Expose the applications before rewriting under the image coercions.
  change
    bodyFrame 0 (p 0) '' H ∩
      bodyFrame (Real.pi / 2) (p (Real.pi / 2)) '' V ∩
        (⋂ t ∈ Set.Icc 0 (Real.pi / 2), bodyFrame t (p t) '' L) =
    worldFrame 0 (x 0) '' H ∩
      worldFrame (Real.pi / 2) (x (Real.pi / 2)) '' V ∩
        (⋂ t ∈ Set.Icc 0 (Real.pi / 2), worldFrame t (x t) '' L)
  rw [bodyFrame_eq_worldFrame, ← h0, bodyFrame_eq_worldFrame, ← h1]
  congr 1
  apply Set.iInter_congr
  intro t
  apply Set.iInter_congr
  intro ht
  rw [bodyFrame_eq_worldFrame, ← hpath t ht]

/-- Normalizing the physical angle does not change the intersection. -/
theorem angleIntersection_eq_frameIntersection
    (F : ℝ → Rigid) (H V L : Set Plane) :
    angleIntersection F H V L =
      frameIntersection (fun s : I => F ((s : ℝ) * (Real.pi / 2))) H V L := by
  have hT : (0 : ℝ) < Real.pi / 2 := by positivity
  have hz : ((0 : I) : ℝ) = 0 := rfl
  have ho : ((1 : I) : ℝ) = 1 := rfl
  ext q
  simp only [angleIntersection, frameIntersection, Set.mem_inter_iff,
    Set.mem_iInter, hz, ho, zero_mul, one_mul]
  constructor
  · rintro ⟨hends, hall⟩
    refine ⟨hends, ?_⟩
    intro s
    apply hall
    exact ⟨mul_nonneg s.property.1 hT.le,
      by nlinarith [s.property.2]⟩
  · rintro ⟨hends, hall⟩
    refine ⟨hends, ?_⟩
    intro t ht
    let s : I := ⟨t / (Real.pi / 2), div_nonneg ht.1 hT.le,
      (div_le_iff₀ hT).2 (by simpa using ht.2)⟩
    have h := hall s
    simpa only [s, div_mul_cancel₀ t (ne_of_gt hT)] using h

namespace Model

/-- The horizontal unit-width hallway arm extending to the left. -/
def horizontalHallway : Set Plane := {q | q 0 ≤ 1 ∧ 0 ≤ q 1 ∧ q 1 ≤ 1}
/-- The vertical unit-width hallway arm extending downwards. -/
def verticalHallway : Set Plane := {q | 0 ≤ q 0 ∧ q 0 ≤ 1 ∧ q 1 ≤ 1}
/-- The union of the two perpendicular unit-width hallway arms. -/
def hallway : Set Plane := horizontalHallway ∪ verticalHallway

/-- A nonempty closed connected set moving continuously between the hallway arms. -/
structure IsMovingSofa (S : Set Plane) (m : I → Rigid) : Prop where
  isConnected : IsConnected S
  isClosed : IsClosed S
  continuous : Continuous m
  zero : m 0 = AffineIsometryEquiv.refl ℝ Plane
  initial : S ⊆ horizontalHallway
  subset_hallway : ∀ s, m s '' S ⊆ hallway
  final : m 1 '' S ⊆ verticalHallway

end Model

end GerverSofa.PartF

end

end

end

section

/-!
# F02: the coordinate homeomorphism

The product `Point = ℝ × ℝ` and `Plane = EuclideanSpace ℝ (Fin 2)`
have the same coordinates and topology. Their norms differ. Accordingly,
the coordinate identification below is a linear equivalence and a
homeomorphism. Euclidean isometries are constructed separately.
-/

@[expose] public section

noncomputable section

namespace GerverSofa.PartF.Coordinates

/-- Convert a pair of real coordinates to a Euclidean vector. -/
def toPlane (q : Point) : Plane := WithLp.toLp 2 ![q.1, q.2]

/-- Extract the two real coordinates of a Euclidean vector. -/
def fromPlane (q : Plane) : Point := (q 0, q 1)

@[simp] theorem toPlane_zero_coord (q : Point) : toPlane q 0 = q.1 := rfl
@[simp] theorem toPlane_one_coord (q : Point) : toPlane q 1 = q.2 := rfl

theorem plane_ext {q r : Plane} (h0 : q 0 = r 0) (h1 : q 1 = r 1) : q = r := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

@[simp] theorem fromPlane_toPlane (q : Point) : fromPlane (toPlane q) = q := rfl

@[simp] theorem toPlane_fromPlane (q : Plane) : toPlane (fromPlane q) = q := by
  exact plane_ext rfl rfl

theorem toPlane_add (q r : Point) : toPlane (q + r) = toPlane q + toPlane r := by
  exact plane_ext rfl rfl

theorem toPlane_smul (c : ℝ) (q : Point) : toPlane (c • q) = c • toPlane q := by
  exact plane_ext rfl rfl

/-- The coordinate equivalence, without any assertion that the two norms agree. -/
def linearEquiv : Point ≃ₗ[ℝ] Plane where
  toFun := toPlane
  invFun := fromPlane
  left_inv := fromPlane_toPlane
  right_inv := toPlane_fromPlane
  map_add' := toPlane_add
  map_smul' := toPlane_smul

/-- The coordinate homeomorphism between real pairs and the Euclidean plane. -/
def homeomorph : Point ≃ₜ Plane := linearEquiv.toContinuousLinearEquiv.toHomeomorph

theorem continuous_toPlane : Continuous toPlane :=
  linearEquiv.toContinuousLinearEquiv.continuous

theorem continuous_fromPlane : Continuous fromPlane :=
  linearEquiv.toContinuousLinearEquiv.symm.continuous

theorem image_eq_preimage (S : Set Point) :
    toPlane '' S = fromPlane ⁻¹' S := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro hq
    exact ⟨fromPlane q, hq, toPlane_fromPlane q⟩

theorem isClosed_image {S : Set Point} (hS : IsClosed S) : IsClosed (toPlane '' S) := by
  rw [image_eq_preimage]
  exact hS.preimage continuous_fromPlane

theorem isConnected_image {S : Set Point} (hS : IsConnected S) :
    IsConnected (toPlane '' S) :=
  hS.image toPlane continuous_toPlane.continuousOn

theorem horizontal_image : toPlane '' horizontalArm = Model.horizontalHallway := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro hq
    exact ⟨fromPlane q, hq, toPlane_fromPlane q⟩

theorem vertical_image : toPlane '' verticalArm = Model.verticalHallway := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro hq
    exact ⟨fromPlane q, hq, toPlane_fromPlane q⟩

theorem hallway_image : toPlane '' GerverSofa.hallway = Model.hallway := by
  simp only [GerverSofa.hallway, Model.hallway, Set.image_union,
    horizontal_image, vertical_image]

end GerverSofa.PartF.Coordinates

end

end

end

section

/-!
# F04: literal integral data and its branch primitives

The parameterized definitions below are the pinned upstream scalar integrals.
The phase boundaries are preserved. Integrating across the jumps will use
equality on open intervals, not an incorrect global continuity assertion for r.
-/

@[expose] public section

noncomputable section
open MeasureTheory
namespace GerverSofa.PartF.Integrals

open Phases

/-- The reflected second switching angle `π/2 - θ`. -/
def eta (d : Reduced.Params) : ℝ := T - d.theta
/-- The reflected first switching angle `π/2 - φ`. -/
def tau (d : Reduced.Params) : ℝ := T - d.phi
/-- The switching-angle condition `0 ≤ φ ≤ θ ≤ π/4`. -/
def Ordered (d : Reduced.Params) : Prop :=
  0 ≤ d.phi ∧ d.phi ≤ d.theta ∧ d.theta ≤ Real.pi / 4

theorem ordered_knots (d : Reduced.Params) (ho : Ordered d) :
    0 ≤ d.phi ∧ d.phi ≤ d.theta ∧ d.theta ≤ eta d ∧
      eta d ≤ tau d ∧ tau d ≤ T := by
  rcases ho with ⟨h0, h1, h2⟩
  dsimp [eta, tau, T]
  exact ⟨h0, h1, by linarith, by linarith, by linarith⟩

/-- The integrand profile on phase 1. -/
def r1 (_d : Reduced.Params) (_t : ℝ) : ℝ := 1 / 2
/-- The integrand profile on phase 2. -/
def r2 (d : Reduced.Params) (t : ℝ) : ℝ := g2 d t
/-- The integrand profile on phase 3. -/
def r3 (d : Reduced.Params) (t : ℝ) : ℝ := g3 d t
/-- The integrand profile on phase 4. -/
def r4 (d : Reduced.Params) (t : ℝ) : ℝ :=
  d.b - (T - t - d.phi) * (1 + d.a) / 2 - (T - t - d.phi) ^ 2 / 4

/-- The piecewise phase profile used in the integral representation. -/
def r (d : Reduced.Params) (t : ℝ) : ℝ :=
  if t ≤ d.phi then r1 d t
  else if t ≤ d.theta then r2 d t
  else if t ≤ eta d then r3 d t
  else if t ≤ tau d then r4 d t
  else 0

/-- One minus the cosine-weighted profile integral from `t` to the last switching angle. -/
def xi (d : Reduced.Params) (t : ℝ) : ℝ :=
  1 - ∫ s in t..tau d, r d s * Real.cos s
/-- The sine-weighted profile integral from `t` to the last switching angle. -/
def zeta (d : Reduced.Params) (t : ℝ) : ℝ :=
  ∫ s in t..tau d, r d s * Real.sin s

/-- The rotation path expressed using the two profile integrals. -/
def path (d : Reduced.Params) (t : ℝ) : Point :=
  (if t ≤ d.phi then Real.cos t - 1
   else xi d (T - t) * Real.cos t + zeta d (T - t) * Real.sin t - 1,
   if t ≤ tau d then
     zeta d t * Real.cos t - (4 * xi d 0 - 2 - xi d t) * Real.sin t - 1
   else -(4 * xi d 0 - 3) * Real.sin t - 1)

/-- The derivative formula for the fourth phase profile. -/
def dg4 (d : Reduced.Params) (t : ℝ) : ℝ :=
  (1 + d.a) / 2 + (T - d.phi - t) / 2

/-- The horizontal primitive assembled from a profile, its derivative, and an offset. -/
def primitiveX (V : ℝ) (g gp : ℝ → ℝ) (t : ℝ) : ℝ :=
  V + g t * Real.sin t + gp t * Real.cos t
/-- The vertical primitive assembled from a profile, its derivative, and an offset. -/
def primitiveY (U : ℝ) (g gp : ℝ → ℝ) (t : ℝ) : ℝ :=
  U + g t * Real.cos t - gp t * Real.sin t

/-- Horizontal primitive specialized to phase 1. -/
def X1 (d : Reduced.Params) : ℝ → ℝ := primitiveX (V1 d) (r1 d) (fun _ => 0)
/-- Vertical primitive specialized to phase 1. -/
def Y1 (d : Reduced.Params) : ℝ → ℝ := primitiveY (U1 d) (r1 d) (fun _ => 0)
/-- Horizontal primitive specialized to phase 2. -/
def X2 (d : Reduced.Params) : ℝ → ℝ := primitiveX (V2 d) (g2 d) (fun _ => 1 / 2)
/-- Vertical primitive specialized to phase 2. -/
def Y2 (d : Reduced.Params) : ℝ → ℝ := primitiveY (U2 d) (g2 d) (fun _ => 1 / 2)
/-- Horizontal primitive specialized to phase 3. -/
def X3 (d : Reduced.Params) : ℝ → ℝ := primitiveX (V3 d) (g3 d) (fun _ => 1)
/-- Vertical primitive specialized to phase 3. -/
def Y3 (d : Reduced.Params) : ℝ → ℝ := primitiveY (U3 d) (g3 d) (fun _ => 1)
/-- Horizontal primitive specialized to phase 4. -/
def X4 (d : Reduced.Params) : ℝ → ℝ := primitiveX (V4 d) (g4 d) (dg4 d)
/-- Vertical primitive specialized to phase 4. -/
def Y4 (d : Reduced.Params) : ℝ → ℝ := primitiveY (U4 d) (g4 d) (dg4 d)

/-- F05 repair: normalize only the scalar derivative, never typeclass arguments. -/
theorem primitiveX_hasDerivAt (V : ℝ) {g gp : ℝ → ℝ} {t gpp : ℝ}
    (hg : HasDerivAt g (gp t) t) (hgp : HasDerivAt gp gpp t) :
    HasDerivAt (primitiveX V g gp) ((g t + gpp) * Real.cos t) t := by
  change HasDerivAt (fun s => V + g s * Real.sin s + gp s * Real.cos s) _ t
  have h := ((hasDerivAt_const t V).fun_add
    (hg.fun_mul (Real.hasDerivAt_sin t))).fun_add
    (hgp.fun_mul (Real.hasDerivAt_cos t))
  exact h.congr_deriv (by ring)

theorem primitiveY_hasDerivAt (U : ℝ) {g gp : ℝ → ℝ} {t gpp : ℝ}
    (hg : HasDerivAt g (gp t) t) (hgp : HasDerivAt gp gpp t) :
    HasDerivAt (primitiveY U g gp) (-(g t + gpp) * Real.sin t) t := by
  change HasDerivAt (fun s => U + g s * Real.cos s - gp s * Real.sin s) _ t
  have h := ((hasDerivAt_const t U).fun_add
    (hg.fun_mul (Real.hasDerivAt_cos t))).fun_sub
    (hgp.fun_mul (Real.hasDerivAt_sin t))
  exact h.congr_deriv (by ring)

theorem g2_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (g2 d) (1 / 2) t := by
  change HasDerivAt (fun s => (1 + d.a + s - d.phi) / 2) _ t
  have h := (((hasDerivAt_const t (1 + d.a)).fun_add
    (hasDerivAt_id t)).fun_sub (hasDerivAt_const t d.phi)).div_const 2
  exact h.congr_deriv (by ring)

theorem g3_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (g3 d) 1 t := by
  change HasDerivAt (fun s => d.a + s - d.phi) _ t
  have h := ((hasDerivAt_const t d.a).fun_add
    (hasDerivAt_id t)).fun_sub (hasDerivAt_const t d.phi)
  exact h.congr_deriv (by ring)

theorem g4_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (g4 d) (dg4 d t) t := by
  change HasDerivAt (fun s => d.b + 1 / 2 -
    (T - d.phi - s) * (1 + d.a) / 2 - (T - d.phi - s)^2 / 4) _ t
  have h := (hasDerivAt_const t (T - d.phi)).fun_sub (hasDerivAt_id t)
  have hfull := ((hasDerivAt_const t (d.b + 1 / 2)).fun_sub
    ((h.mul_const (1 + d.a)).div_const 2)).fun_sub ((h.pow 2).div_const 4)
  exact hfull.congr_deriv (by dsimp [dg4]; ring)

theorem dg4_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (dg4 d) (-1 / 2) t := by
  change HasDerivAt (fun s => (1 + d.a) / 2 + (T - d.phi - s) / 2) _ t
  have h := (hasDerivAt_const t ((1 + d.a) / 2)).fun_add
    (((hasDerivAt_const t (T - d.phi)).fun_sub (hasDerivAt_id t)).div_const 2)
  exact h.congr_deriv (by ring)

theorem X1_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (X1 d) (r1 d t * Real.cos t) t := by
  have h := primitiveX_hasDerivAt (V1 d) (g := r1 d) (gp := fun _ => 0)
    (hasDerivAt_const t (1 / 2 : ℝ)) (hasDerivAt_const t (0 : ℝ))
  exact h.congr_deriv (by dsimp [r1, r2, r3, r4, g2, g3, g4]; ring)

theorem Y1_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (Y1 d) (-r1 d t * Real.sin t) t := by
  have h := primitiveY_hasDerivAt (U1 d) (g := r1 d) (gp := fun _ => 0)
    (hasDerivAt_const t (1 / 2 : ℝ)) (hasDerivAt_const t (0 : ℝ))
  exact h.congr_deriv (by dsimp [r1, r2, r3, r4, g2, g3, g4]; ring)

theorem X2_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (X2 d) (r2 d t * Real.cos t) t := by
  have h := primitiveX_hasDerivAt (V2 d) (g := g2 d) (gp := fun _ => 1 / 2)
    (g2_hasDerivAt d t) (hasDerivAt_const t (1 / 2 : ℝ))
  exact h.congr_deriv (by dsimp [r1, r2, r3, r4, g2, g3, g4]; ring)

theorem Y2_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (Y2 d) (-r2 d t * Real.sin t) t := by
  have h := primitiveY_hasDerivAt (U2 d) (g := g2 d) (gp := fun _ => 1 / 2)
    (g2_hasDerivAt d t) (hasDerivAt_const t (1 / 2 : ℝ))
  exact h.congr_deriv (by dsimp [r1, r2, r3, r4, g2, g3, g4]; ring)

theorem X3_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (X3 d) (r3 d t * Real.cos t) t := by
  have h := primitiveX_hasDerivAt (V3 d) (g := g3 d) (gp := fun _ => 1)
    (g3_hasDerivAt d t) (hasDerivAt_const t (1 : ℝ))
  exact h.congr_deriv (by dsimp [r1, r2, r3, r4, g2, g3, g4]; ring)

theorem Y3_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (Y3 d) (-r3 d t * Real.sin t) t := by
  have h := primitiveY_hasDerivAt (U3 d) (g := g3 d) (gp := fun _ => 1)
    (g3_hasDerivAt d t) (hasDerivAt_const t (1 : ℝ))
  exact h.congr_deriv (by dsimp [r1, r2, r3, r4, g2, g3, g4]; ring)

theorem X4_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (X4 d) (r4 d t * Real.cos t) t := by
  have h := primitiveX_hasDerivAt (V4 d) (g := g4 d) (gp := dg4 d)
    (g4_hasDerivAt d t) (dg4_hasDerivAt d t)
  exact h.congr_deriv (by dsimp [r1, r2, r3, r4, g2, g3, g4]; ring)

theorem Y4_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (Y4 d) (-r4 d t * Real.sin t) t := by
  have h := primitiveY_hasDerivAt (U4 d) (g := g4 d) (gp := dg4 d)
    (g4_hasDerivAt d t) (dg4_hasDerivAt d t)
  exact h.congr_deriv (by dsimp [r1, r2, r3, r4, g2, g3, g4]; ring)

theorem X1_join (d : Reduced.Params) :
    X1 d d.phi = X2 d d.phi := by
  dsimp [X1, X2, primitiveX, r1, g2, g3,
    U1, U2, U3, V1, V2, V3, hStar]
  ring

theorem Y1_join (d : Reduced.Params) :
    Y1 d d.phi = Y2 d d.phi := by
  dsimp [Y1, Y2, primitiveY, r1, g2, g3,
    U1, U2, U3, V1, V2, V3, hStar]
  ring

theorem X2_join (d : Reduced.Params) :
    X2 d d.theta = X3 d d.theta := by
  dsimp [X2, X3, primitiveX, r1, g2, g3,
    U1, U2, U3, V1, V2, V3, hStar]
  ring

theorem Y2_join (d : Reduced.Params) :
    Y2 d d.theta = Y3 d d.theta := by
  dsimp [Y2, Y3, primitiveY, r1, g2, g3,
    U1, U2, U3, V1, V2, V3, hStar]
  ring

theorem fourth_equation (d : Reduced.Params) (hd : Reduced.Equations d) :
    d.a + T - d.phi - d.theta - d.b +
      (1 / 2 : ℝ) * (d.theta - d.phi) * (1 + d.a) +
      (1 / 4 : ℝ) * (d.theta - d.phi) * (d.theta - d.phi) = 0 := by
  exact congrFun hd (3 : Fin 4)

theorem X3_join (d : Reduced.Params) (hd : Reduced.Equations d) :
    X3 d (eta d) = X4 d (eta d) := by
  have he := fourth_equation d hd
  dsimp [X3, X4, primitiveX, eta, g3, g4, dg4, U3, V3, hStar, T] at *
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  linear_combination Real.cos d.theta * he

theorem Y3_join (d : Reduced.Params) (hd : Reduced.Equations d) :
    Y3 d (eta d) = Y4 d (eta d) := by
  have he := fourth_equation d hd
  dsimp [Y3, Y4, primitiveY, eta, g3, g4, dg4, U3, V3, hStar, T] at *
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  linear_combination Real.sin d.theta * he

theorem X4_terminal (d : Reduced.Params) :
    X4 d (tau d) = 1 := by
  dsimp [X4, primitiveX, tau, g4, dg4, U4, V4, T]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  ring

theorem Y4_terminal (d : Reduced.Params) :
    Y4 d (tau d) = 0 := by
  dsimp [Y4, primitiveY, tau, g4, dg4, U4, V4, T]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  ring

theorem r_phase1 (d : Reduced.Params) {t : ℝ} (ht : t ≤ d.phi) :
    r d t = r1 d t := by simp only [r, ite_eq_left ht]

theorem r_phase2 (d : Reduced.Params) {t : ℝ}
    (hlo : d.phi < t) (hhi : t ≤ d.theta) : r d t = r2 d t := by
  simp only [r, ite_eq_right (not_le.mpr hlo), ite_eq_left hhi]

theorem r_phase3 (d : Reduced.Params) (ho : Ordered d) {t : ℝ}
    (hlo : d.theta < t) (hhi : t ≤ eta d) : r d t = r3 d t := by
  have hphi : d.phi < t := lt_of_le_of_lt ho.2.1 hlo
  simp only [r, ite_eq_right (not_le.mpr hphi), ite_eq_right (not_le.mpr hlo), ite_eq_left hhi]

theorem r_phase4 (d : Reduced.Params) (ho : Ordered d) {t : ℝ}
    (hlo : eta d < t) (hhi : t ≤ tau d) : r d t = r4 d t := by
  have htheta : d.theta < t := lt_of_le_of_lt (ordered_knots d ho).2.2.1 hlo
  have hphi : d.phi < t := lt_of_le_of_lt ho.2.1 htheta
  simp only [r, ite_eq_right (not_le.mpr hphi), ite_eq_right (not_le.mpr htheta),
    ite_eq_right (not_le.mpr hlo), ite_eq_left hhi]

end GerverSofa.PartF.Integrals

end

end

end

section

/-!
# F04: evaluation of the literal integrals on all four closed intervals

The fundamental theorem is applied to smooth branch primitives. Equality with
the discontinuous integrand is required only on the open interval. Adjacent
integrals are then added, using the proved matching values at every switch.
-/

@[expose] public section

noncomputable section
open MeasureTheory
namespace GerverSofa.PartF.Integrals

open Phases

theorem integrate_branch (f f' P : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hf' : Continuous f')
    (hderiv : ∀ t, HasDerivAt P (f' t) t)
    (heq : ∀ t ∈ Set.Ioo a b, f t = f' t) :
    IntervalIntegrable f volume a b ∧
      (∫ t in a..b, f t) = P b - P a := by
  have hi : IntervalIntegrable f' volume a b := hf'.intervalIntegrable a b
  have hf : IntervalIntegrable f volume a b := hi.congr_uIoo (by
    rw [Set.uIoo_of_le hab]
    intro t ht
    exact (heq t ht).symm)
  refine ⟨hf, ?_⟩
  calc
    (∫ t in a..b, f t) = ∫ t in a..b, f' t :=
      intervalIntegral.integral_congr_Ioo_of_le hab heq
    _ = P b - P a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hi

theorem cos_tail4 (d : Reduced.Params) (ho : Ordered d)
    (t : ℝ) (ht : t ∈ Set.Icc (eta d) (tau d)) :
    IntervalIntegrable (fun u => r d u * Real.cos u) volume t (tau d) ∧
      (∫ u in t..tau d, r d u * Real.cos u) = 1 - X4 d t := by
  have hpiece := integrate_branch
    (fun u => r d u * Real.cos u) (fun u => r4 d u * Real.cos u)
    (X4 d) t (tau d) ht.2
    (by dsimp [r1, r2, r3, r4, g2, g3]; fun_prop)
    (by
      intro u
      exact X4_hasDerivAt d u)
    (by
      intro u hu
      rw [r_phase4 d ho (lt_of_le_of_lt ht.1 hu.1) (le_of_lt hu.2)])
  refine ⟨hpiece.1, ?_⟩
  rw [hpiece.2]
  rw [X4_terminal]

theorem sin_tail4 (d : Reduced.Params) (ho : Ordered d)
    (t : ℝ) (ht : t ∈ Set.Icc (eta d) (tau d)) :
    IntervalIntegrable (fun u => r d u * Real.sin u) volume t (tau d) ∧
      (∫ u in t..tau d, r d u * Real.sin u) = Y4 d t := by
  have hpiece := integrate_branch
    (fun u => r d u * Real.sin u) (fun u => r4 d u * Real.sin u)
    (fun u => -Y4 d u) t (tau d) ht.2
    (by dsimp [r1, r2, r3, r4, g2, g3]; fun_prop)
    (by
      intro u
      exact (Y4_hasDerivAt d u).fun_neg.congr_deriv (by ring))
    (by
      intro u hu
      rw [r_phase4 d ho (lt_of_le_of_lt ht.1 hu.1) (le_of_lt hu.2)])
  refine ⟨hpiece.1, ?_⟩
  rw [hpiece.2]
  rw [Y4_terminal]; ring

theorem cos_tail3 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (d.theta) (eta d)) :
    IntervalIntegrable (fun u => r d u * Real.cos u) volume t (tau d) ∧
      (∫ u in t..tau d, r d u * Real.cos u) = 1 - X3 d t := by
  have hpiece := integrate_branch
    (fun u => r d u * Real.cos u) (fun u => r3 d u * Real.cos u)
    (X3 d) t (eta d) ht.2
    (by dsimp [r1, r2, r3, r4, g2, g3]; fun_prop)
    (by
      intro u
      exact X3_hasDerivAt d u)
    (by
      intro u hu
      rw [r_phase3 d ho (lt_of_le_of_lt ht.1 hu.1) (le_of_lt hu.2)])
  have hrest := cos_tail4 d ho (eta d) ⟨le_rfl, (ordered_knots d ho).2.2.2.1⟩
  refine ⟨hpiece.1.trans hrest.1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hpiece.1 hrest.1,
    hpiece.2, hrest.2]
  rw [X3_join d hd]; ring

theorem sin_tail3 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (d.theta) (eta d)) :
    IntervalIntegrable (fun u => r d u * Real.sin u) volume t (tau d) ∧
      (∫ u in t..tau d, r d u * Real.sin u) = Y3 d t := by
  have hpiece := integrate_branch
    (fun u => r d u * Real.sin u) (fun u => r3 d u * Real.sin u)
    (fun u => -Y3 d u) t (eta d) ht.2
    (by dsimp [r1, r2, r3, r4, g2, g3]; fun_prop)
    (by
      intro u
      exact (Y3_hasDerivAt d u).fun_neg.congr_deriv (by ring))
    (by
      intro u hu
      rw [r_phase3 d ho (lt_of_le_of_lt ht.1 hu.1) (le_of_lt hu.2)])
  have hrest := sin_tail4 d ho (eta d) ⟨le_rfl, (ordered_knots d ho).2.2.2.1⟩
  refine ⟨hpiece.1.trans hrest.1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hpiece.1 hrest.1,
    hpiece.2, hrest.2]
  rw [Y3_join d hd]; ring

theorem cos_tail2 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (d.phi) (d.theta)) :
    IntervalIntegrable (fun u => r d u * Real.cos u) volume t (tau d) ∧
      (∫ u in t..tau d, r d u * Real.cos u) = 1 - X2 d t := by
  have hpiece := integrate_branch
    (fun u => r d u * Real.cos u) (fun u => r2 d u * Real.cos u)
    (X2 d) t (d.theta) ht.2
    (by dsimp [r1, r2, r3, r4, g2, g3]; fun_prop)
    (by
      intro u
      exact X2_hasDerivAt d u)
    (by
      intro u hu
      rw [r_phase2 d (lt_of_le_of_lt ht.1 hu.1) (le_of_lt hu.2)])
  have hrest := cos_tail3 d ho hd (d.theta) ⟨le_rfl, (ordered_knots d ho).2.2.1⟩
  refine ⟨hpiece.1.trans hrest.1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hpiece.1 hrest.1,
    hpiece.2, hrest.2]
  rw [X2_join d]; ring

theorem sin_tail2 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (d.phi) (d.theta)) :
    IntervalIntegrable (fun u => r d u * Real.sin u) volume t (tau d) ∧
      (∫ u in t..tau d, r d u * Real.sin u) = Y2 d t := by
  have hpiece := integrate_branch
    (fun u => r d u * Real.sin u) (fun u => r2 d u * Real.sin u)
    (fun u => -Y2 d u) t (d.theta) ht.2
    (by dsimp [r1, r2, r3, r4, g2, g3]; fun_prop)
    (by
      intro u
      exact (Y2_hasDerivAt d u).fun_neg.congr_deriv (by ring))
    (by
      intro u hu
      rw [r_phase2 d (lt_of_le_of_lt ht.1 hu.1) (le_of_lt hu.2)])
  have hrest := sin_tail3 d ho hd (d.theta) ⟨le_rfl, (ordered_knots d ho).2.2.1⟩
  refine ⟨hpiece.1.trans hrest.1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hpiece.1 hrest.1,
    hpiece.2, hrest.2]
  rw [Y2_join d]; ring

theorem cos_tail1 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (0) (d.phi)) :
    IntervalIntegrable (fun u => r d u * Real.cos u) volume t (tau d) ∧
      (∫ u in t..tau d, r d u * Real.cos u) = 1 - X1 d t := by
  have hpiece := integrate_branch
    (fun u => r d u * Real.cos u) (fun u => r1 d u * Real.cos u)
    (X1 d) t (d.phi) ht.2
    (by dsimp [r1, r2, r3, r4, g2, g3]; fun_prop)
    (by
      intro u
      exact X1_hasDerivAt d u)
    (by
      intro u hu
      rw [r_phase1 d (le_of_lt hu.2)])
  have hrest := cos_tail2 d ho hd (d.phi) ⟨le_rfl, ho.2.1⟩
  refine ⟨hpiece.1.trans hrest.1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hpiece.1 hrest.1,
    hpiece.2, hrest.2]
  rw [X1_join d]; ring

theorem sin_tail1 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (0) (d.phi)) :
    IntervalIntegrable (fun u => r d u * Real.sin u) volume t (tau d) ∧
      (∫ u in t..tau d, r d u * Real.sin u) = Y1 d t := by
  have hpiece := integrate_branch
    (fun u => r d u * Real.sin u) (fun u => r1 d u * Real.sin u)
    (fun u => -Y1 d u) t (d.phi) ht.2
    (by dsimp [r1, r2, r3, r4, g2, g3]; fun_prop)
    (by
      intro u
      exact (Y1_hasDerivAt d u).fun_neg.congr_deriv (by ring))
    (by
      intro u hu
      rw [r_phase1 d (le_of_lt hu.2)])
  have hrest := sin_tail2 d ho hd (d.phi) ⟨le_rfl, ho.2.1⟩
  refine ⟨hpiece.1.trans hrest.1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hpiece.1 hrest.1,
    hpiece.2, hrest.2]
  rw [Y1_join d]; ring

theorem xi_zeta_phase1 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (0) (d.phi)) :
    xi d t = X1 d t ∧ zeta d t = Y1 d t := by
  constructor
  · unfold xi
    rw [(cos_tail1 d ho hd t ht).2]
    ring
  · exact (sin_tail1 d ho hd t ht).2

theorem xi_zeta_phase2 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (d.phi) (d.theta)) :
    xi d t = X2 d t ∧ zeta d t = Y2 d t := by
  constructor
  · unfold xi
    rw [(cos_tail2 d ho hd t ht).2]
    ring
  · exact (sin_tail2 d ho hd t ht).2

theorem xi_zeta_phase3 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (d.theta) (eta d)) :
    xi d t = X3 d t ∧ zeta d t = Y3 d t := by
  constructor
  · unfold xi
    rw [(cos_tail3 d ho hd t ht).2]
    ring
  · exact (sin_tail3 d ho hd t ht).2

theorem xi_zeta_phase4 (d : Reduced.Params) (ho : Ordered d)
    (t : ℝ) (ht : t ∈ Set.Icc (eta d) (tau d)) :
    xi d t = X4 d t ∧ zeta d t = Y4 d t := by
  constructor
  · unfold xi
    rw [(cos_tail4 d ho t ht).2]
    ring
  · exact (sin_tail4 d ho t ht).2

theorem xi_zero (d : Reduced.Params) (ho : Ordered d)
    (hd : Reduced.Equations d) : xi d 0 = V1 d := by
  have h := (xi_zeta_phase1 d ho hd 0 ⟨le_rfl, ho.1⟩).1
  simpa [X1, primitiveX] using h

/-- The projection `ξ sin t + ζ cos t` used in the integral identities. -/
def W (d : Reduced.Params) (t : ℝ) : ℝ :=
  xi d t * Real.sin t + zeta d t * Real.cos t

theorem primitive_W (g gp U V t : ℝ) :
    (V + g * Real.sin t + gp * Real.cos t) * Real.sin t +
      (U + g * Real.cos t - gp * Real.sin t) * Real.cos t =
      g + U * Real.cos t + V * Real.sin t := by
  linear_combination g * Real.sin_sq_add_cos_sq t

theorem W_phase1 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (0) (d.phi)) :
    W d t = r1 d t + U1 d * Real.cos t + V1 d * Real.sin t := by
  rcases xi_zeta_phase1 d ho hd t ht with ⟨hx, hy⟩
  unfold W
  rw [hx, hy]
  exact primitive_W (r1 d t) (0) (U1 d) (V1 d) t

theorem W_phase2 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (d.phi) (d.theta)) :
    W d t = g2 d t + U2 d * Real.cos t + V2 d * Real.sin t := by
  rcases xi_zeta_phase2 d ho hd t ht with ⟨hx, hy⟩
  unfold W
  rw [hx, hy]
  exact primitive_W (g2 d t) (1 / 2) (U2 d) (V2 d) t

theorem W_phase3 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (d.theta) (eta d)) :
    W d t = g3 d t + U3 d * Real.cos t + V3 d * Real.sin t := by
  rcases xi_zeta_phase3 d ho hd t ht with ⟨hx, hy⟩
  unfold W
  rw [hx, hy]
  exact primitive_W (g3 d t) (1) (U3 d) (V3 d) t

theorem W_phase4 (d : Reduced.Params) (ho : Ordered d)
    (t : ℝ) (ht : t ∈ Set.Icc (eta d) (tau d)) :
    W d t = g4 d t + U4 d * Real.cos t + V4 d * Real.sin t := by
  rcases xi_zeta_phase4 d ho t ht with ⟨hx, hy⟩
  unfold W
  rw [hx, hy]
  exact primitive_W (g4 d t) (dg4 d t) (U4 d) (V4 d) t

end GerverSofa.PartF.Integrals

end

end

end

section

/-!
# F05: the four-parameter dictionary satisfies the full 22 equations

These polynomial certificates use the four reduced equations and the two
trigonometric circle identities. No box membership or uniqueness is assumed.
They do not identify the dictionary with the independently certified 22D root.
The module is independent of the F04 integral evaluation.
-/

@[expose] public section

noncomputable section
namespace GerverSofa.PartF.Phases

theorem dictionary_equations (d : Reduced.Params) (hd : Reduced.Equations d) :
    Romik.Equations (dictionary d) := by
  have h1 := congrFun hd (0 : Fin 4)
  have h2 := congrFun hd (1 : Fin 4)
  have h3 := congrFun hd (2 : Fin 4)
  have h4 := congrFun hd (3 : Fin 4)
  change d.a * (Real.cos d.theta - Real.cos d.phi) -
    2 * d.b * Real.sin d.phi + (d.theta - d.phi - 1) * Real.cos d.theta -
    Real.sin d.theta + Real.cos d.phi + Real.sin d.phi = 0 at h1
  change d.a * (3 * Real.sin d.theta + Real.sin d.phi) -
    2 * d.b * Real.cos d.phi + 3 * (d.theta - d.phi - 1) * Real.sin d.theta +
    3 * Real.cos d.theta - Real.sin d.phi + Real.cos d.phi = 0 at h2
  change d.a * Real.cos d.phi - Real.sin d.phi - 1 / 2 +
    1 / 2 * Real.cos d.phi - d.b * Real.sin d.phi = 0 at h3
  change d.a + Real.pi / 2 - d.phi - d.theta - d.b +
    1 / 2 * (d.theta - d.phi) * (1 + d.a) +
    1 / 4 * (d.theta - d.phi) * (d.theta - d.phi) = 0 at h4
  have hcphi := Real.sin_sq_add_cos_sq d.phi
  have hctheta := Real.sin_sq_add_cos_sq d.theta
  change Romik.system (dictionary d) = 0
  funext i
  fin_cases i
  -- Row 0: exact scalar certificate.
  · change (dictionary d).e1 - (dictionary d).a1 = 0
    dsimp [dictionary, T]; ring
  -- Row 1: exact scalar certificate.
  · change (dictionary d).e2 + (dictionary d).a2 = 0
    dsimp [dictionary, T]; ring
  -- Row 2: exact scalar certificate.
  · change (dictionary d).d1 + (dictionary d).b1 - Real.pi / 4 = 0
    dsimp [dictionary, T]; ring
  -- Row 3: exact scalar certificate.
  · change (dictionary d).d2 - (dictionary d).b2 - Real.pi / 4 * (2 * (dictionary d).b1 - Real.pi
    / 4) = 0
    dsimp [dictionary, T]; ring
  -- Row 4: exact scalar certificate.
  · change (dictionary d).c2 - (dictionary d).c1 + Real.pi / 2 = 0
    dsimp [dictionary, T]; ring
  -- Row 5: exact scalar certificate.
  · change (dictionary d).k11 - 1 + (dictionary d).a1 = 0
    dsimp [dictionary, T]; ring
  -- Row 6: exact scalar certificate.
  · change (dictionary d).k12 - 1 / 4 = 0
    dsimp [dictionary, T]; ring
  -- Row 7: exact scalar certificate.
  · change (dictionary d).a2 + 1 / 4 = 0
    dsimp [dictionary, T]; ring
  -- Row 8: exact scalar certificate.
  · change (Romik.path1 (dictionary d) (d.phi)).1 - (Romik.path2 (dictionary d) (d.phi)).1 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    linear_combination ((Real.sin d.phi) ^ 2) * h2 +
      ((Real.sin d.phi) * (Real.cos d.phi)) * h3 +
      (-1 * (d.a) * (Real.sin d.phi) + (-3 / 2 : ℝ) * (d.a) * (Real.sin d.theta) + (3 / 2 : ℝ) *
        (d.b) * (Real.cos d.phi) + (3 / 2 : ℝ) * (d.phi) * (Real.sin d.theta) + (-3 / 2 : ℝ) *
        (d.theta) * (Real.sin d.theta) + (1 / 4 : ℝ) * (Real.sin d.phi) + (3 / 2 : ℝ) * (Real.sin
        d.theta) + (-3 / 2 : ℝ) * (Real.cos d.theta)) * hcphi
  -- Row 9: exact scalar certificate.
  · change (Romik.path1 (dictionary d) (d.phi)).2 - (Romik.path2 (dictionary d) (d.phi)).2 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    linear_combination (-1 * (Real.sin d.phi) * (Real.cos d.phi)) * h2 +
      ((Real.sin d.phi) ^ 2 + -1) * h3 +
      ((d.b) * (Real.sin d.phi) + (Real.sin d.phi) + (1 / 4 : ℝ)) * hcphi
  -- Row 10: exact scalar certificate.
  · change (Romik.rot (d.phi) (Romik.alphaBeta1 (dictionary d) (d.phi))).1 - (Romik.rot (d.phi)
    (Romik.alphaBeta2 (dictionary d) (d.phi))).1 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    linear_combination (2 * (Real.sin d.phi) * (Real.cos d.phi)) * h2 +
      (-2 * (Real.sin d.phi) ^ 2 + 1) * h3 +
      (-2 * (d.b) * (Real.sin d.phi) + -2 * (Real.sin d.phi) + (-1 / 2 : ℝ)) * hcphi
  -- Row 11: exact scalar certificate.
  · change (Romik.rot (d.phi) (Romik.alphaBeta1 (dictionary d) (d.phi))).2 - (Romik.rot (d.phi)
    (Romik.alphaBeta2 (dictionary d) (d.phi))).2 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    linear_combination (2 * (Real.sin d.phi) ^ 2 + -1) * h2 +
      (2 * (Real.sin d.phi) * (Real.cos d.phi)) * h3 +
      (-2 * (d.a) * (Real.sin d.phi) + -3 * (d.a) * (Real.sin d.theta) + 3 * (d.b) * (Real.cos
        d.phi) + 3 * (d.phi) * (Real.sin d.theta) + -3 * (d.theta) * (Real.sin d.theta) + (1 / 2 :
        ℝ) * (Real.sin d.phi) + 3 * (Real.sin d.theta) + -3 * (Real.cos d.theta)) * hcphi
  -- Row 12: exact scalar certificate.
  · change (Romik.path2 (dictionary d) (d.theta)).1 - (Romik.path3 (dictionary d) (d.theta)).1 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    linear_combination (-1 * (Real.cos d.theta)) * h4
  -- Row 13: exact scalar certificate.
  · change (Romik.path2 (dictionary d) (d.theta)).2 - (Romik.path3 (dictionary d) (d.theta)).2 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    linear_combination (-1 * (Real.sin d.theta)) * h4
  -- Row 14: exact scalar certificate.
  · change (Romik.rot (d.theta) (Romik.alphaBeta2 (dictionary d) (d.theta))).1 - (Romik.rot
    (d.theta) (Romik.alphaBeta3 (dictionary d) (d.theta))).1 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    linear_combination ((Real.sin d.theta)) * h4
  -- Row 15: exact scalar certificate.
  · change (Romik.rot (d.theta) (Romik.alphaBeta2 (dictionary d) (d.theta))).2 - (Romik.rot
    (d.theta) (Romik.alphaBeta3 (dictionary d) (d.theta))).2 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    linear_combination (-1 * (Real.cos d.theta)) * h4
  -- Row 16: exact scalar certificate.
  · change (Romik.path3 (dictionary d) (Real.pi / 2 - d.theta)).1 - (Romik.path4 (dictionary d)
    (Real.pi / 2 - d.theta)).1 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    linear_combination (-1 * (Real.cos d.theta)) * h4
  -- Row 17: exact scalar certificate.
  · change (Romik.path3 (dictionary d) (Real.pi / 2 - d.theta)).2 - (Romik.path4 (dictionary d)
    (Real.pi / 2 - d.theta)).2 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    linear_combination ((Real.sin d.theta)) * h4
  -- Row 18: exact scalar certificate.
  · change (Romik.path4 (dictionary d) (Real.pi / 2 - d.phi)).1 - (Romik.path5 (dictionary d)
    (Real.pi / 2 - d.phi)).1 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    linear_combination ((Real.sin d.phi) ^ 2 + -1) * h2 +
      ((Real.sin d.phi) * (Real.cos d.phi)) * h3 +
      (-1 * (d.a) * (Real.sin d.phi) + (-3 / 2 : ℝ) * (d.a) * (Real.sin d.theta) + (3 / 2 : ℝ) *
        (d.b) * (Real.cos d.phi) + (3 / 2 : ℝ) * (d.phi) * (Real.sin d.theta) + (-3 / 2 : ℝ) *
        (d.theta) * (Real.sin d.theta) + (1 / 4 : ℝ) * (Real.sin d.phi) + (3 / 2 : ℝ) * (Real.sin
        d.theta) + (-3 / 2 : ℝ) * (Real.cos d.theta)) * hcphi
  -- Row 19: exact scalar certificate.
  · change (Romik.path4 (dictionary d) (Real.pi / 2 - d.phi)).2 - (Romik.path5 (dictionary d)
    (Real.pi / 2 - d.phi)).2 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    linear_combination ((Real.sin d.phi) * (Real.cos d.phi)) * h2 +
      (-1 * (Real.sin d.phi) ^ 2 + 1) * h3 +
      (-1 * (d.b) * (Real.sin d.phi) + -1 * (Real.sin d.phi) + (-1 / 4 : ℝ)) * hcphi
  -- Row 20: exact scalar certificate.
  · change (Romik.path1 (dictionary d) d.phi).1 - ((Romik.path3 (dictionary d) (Real.pi / 2 -
    d.theta)).1 - (Romik.alphaBeta3 (dictionary d) (Real.pi / 2 - d.theta)).1 * Real.sin (Real.pi
    / 2 - d.theta)) = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    linear_combination ((Real.sin d.phi) ^ 2 + (-1 / 2 : ℝ)) * h2 +
      ((Real.sin d.phi) * (Real.cos d.phi)) * h3 +
      (-1 * (d.a) * (Real.sin d.phi) + (-3 / 2 : ℝ) * (d.a) * (Real.sin d.theta) + (3 / 2 : ℝ) *
        (d.b) * (Real.cos d.phi) + (3 / 2 : ℝ) * (d.phi) * (Real.sin d.theta) + (-3 / 2 : ℝ) *
        (d.theta) * (Real.sin d.theta) + (1 / 4 : ℝ) * (Real.sin d.phi) + (3 / 2 : ℝ) * (Real.sin
        d.theta) + (-3 / 2 : ℝ) * (Real.cos d.theta)) * hcphi
  -- Row 21: exact scalar certificate.
  · change (Romik.path1 (dictionary d) d.phi).2 - ((Romik.path3 (dictionary d) (Real.pi / 2 -
    d.theta)).2 + (Romik.alphaBeta3 (dictionary d) (Real.pi / 2 - d.theta)).1 * Real.cos (Real.pi
    / 2 - d.theta)) = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    linear_combination ((-1 / 2 : ℝ)) * h1 +
      (-1 * (Real.sin d.phi) * (Real.cos d.phi)) * h2 +
      ((Real.sin d.phi) ^ 2 + -1) * h3 +
      ((d.b) * (Real.sin d.phi) + (Real.sin d.phi) + (1 / 4 : ℝ)) * hcphi

/-- Read back the four free parameters from the 22D representation. -/
def undictionary (p : Romik.Params) : Reduced.Params where
  a := p.phi - 1 - 2 * p.b1
  b := p.b2 + 1 / 2 - (1 + (p.phi - 1 - 2 * p.b1)) * p.phi / 2 + p.phi ^ 2 / 4
  phi := p.phi
  theta := p.theta

theorem undictionary_dictionary (d : Reduced.Params) :
    undictionary (dictionary d) = d := by
  rcases d with ⟨a, b, phi, theta⟩
  dsimp [undictionary, dictionary]
  congr 1 <;> ring

end GerverSofa.PartF.Phases

end

end

end

section

/-!
# F06: reverse reduction from the full Romik equations

This direction uses velocity matching and the two contact equations. It does
not assume membership in either numerical box or any strict angle inequality.
-/

@[expose] public section

noncomputable section
namespace GerverSofa.PartF.Phases

theorem rot_injective (t : ℝ) : Function.Injective (Romik.rot t) := by
  intro z w h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp [Romik.rot] at hx hy
  apply Prod.ext
  · linear_combination Real.cos t * hx + Real.sin t * hy -
      (z.1 - w.1) * Real.sin_sq_add_cos_sq t
  · linear_combination -Real.sin t * hx + Real.cos t * hy -
      (z.2 - w.2) * Real.sin_sq_add_cos_sq t

theorem alphaBeta12_eq {p : Romik.Params} (hp : Romik.Equations p) :
    Romik.alphaBeta1 p p.phi = Romik.alphaBeta2 p p.phi := by
  apply rot_injective p.phi
  apply Prod.ext
  · have h := congrFun hp (10 : Fin 22)
    change (Romik.rot p.phi (Romik.alphaBeta1 p p.phi)).1 -
      (Romik.rot p.phi (Romik.alphaBeta2 p p.phi)).1 = 0 at h
    exact sub_eq_zero.mp h
  · have h := congrFun hp (11 : Fin 22)
    change (Romik.rot p.phi (Romik.alphaBeta1 p p.phi)).2 -
      (Romik.rot p.phi (Romik.alphaBeta2 p p.phi)).2 = 0 at h
    exact sub_eq_zero.mp h

theorem alphaBeta23_eq {p : Romik.Params} (hp : Romik.Equations p) :
    Romik.alphaBeta2 p p.theta = Romik.alphaBeta3 p p.theta := by
  apply rot_injective p.theta
  apply Prod.ext
  · have h := congrFun hp (14 : Fin 22)
    change (Romik.rot p.theta (Romik.alphaBeta2 p p.theta)).1 -
      (Romik.rot p.theta (Romik.alphaBeta3 p p.theta)).1 = 0 at h
    exact sub_eq_zero.mp h
  · have h := congrFun hp (15 : Fin 22)
    change (Romik.rot p.theta (Romik.alphaBeta2 p p.theta)).2 -
      (Romik.rot p.theta (Romik.alphaBeta3 p p.theta)).2 = 0 at h
    exact sub_eq_zero.mp h

theorem c2_eq_of_full {p : Romik.Params} (hp : Romik.Equations p) :
    p.c2 = -2 - 2 * p.b1 := by
  have h := congrArg Prod.fst (alphaBeta23_eq hp)
  dsimp [Romik.alphaBeta2, Romik.alphaBeta3] at h
  linarith only [h]

theorem c1_eq_of_full {p : Romik.Params} (hp : Romik.Equations p) :
    p.c1 = Real.pi / 2 - 2 - 2 * p.b1 := by
  have hs := Romik.c2_eq_c1_sub_halfPi_of_equations hp
  have hc := c2_eq_of_full hp
  linarith only [hs, hc]

theorem reverse_equation4 {p : Romik.Params} (hp : Romik.Equations p) :
    Reduced.system (undictionary p) 3 = 0 := by
  have h := congrArg Prod.snd (alphaBeta23_eq hp)
  dsimp [Romik.alphaBeta2, Romik.alphaBeta3] at h
  rw [c1_eq_of_full hp] at h
  change (undictionary p).a + Real.pi / 2 - (undictionary p).phi -
    (undictionary p).theta - (undictionary p).b +
    1 / 2 * ((undictionary p).theta - (undictionary p).phi) *
      (1 + (undictionary p).a) +
    1 / 4 * ((undictionary p).theta - (undictionary p).phi) *
      ((undictionary p).theta - (undictionary p).phi) = 0
  dsimp [undictionary]
  linear_combination -h

theorem reverse_equation3 {p : Romik.Params} (hp : Romik.Equations p) :
    Reduced.system (undictionary p) 2 = 0 := by
  have ha := congrArg Prod.fst (alphaBeta12_eq hp)
  have hb := congrArg Prod.snd (alphaBeta12_eq hp)
  dsimp [Romik.alphaBeta1, Romik.alphaBeta2] at ha hb
  rw [Romik.a2_eq_neg_quarter_of_equations hp] at ha hb
  change (undictionary p).a * Real.cos (undictionary p).phi -
    Real.sin (undictionary p).phi - 1 / 2 +
    1 / 2 * Real.cos (undictionary p).phi -
    (undictionary p).b * Real.sin (undictionary p).phi = 0
  dsimp [undictionary]
  linear_combination Real.cos p.phi * ha + Real.sin p.phi * hb +
    (1 / 2 : ℝ) * Real.sin_sq_add_cos_sq p.phi

theorem reverse_equation1 {p : Romik.Params} (hp : Romik.Equations p) :
    Reduced.system (undictionary p) 0 = 0 := by
  have h9 := congrFun hp (9 : Fin 22)
  have h13 := congrFun hp (13 : Fin 22)
  have h21 := congrFun hp (21 : Fin 22)
  change (Romik.path1 p p.phi).2 - (Romik.path2 p p.phi).2 = 0 at h9
  change (Romik.path2 p p.theta).2 - (Romik.path3 p p.theta).2 = 0 at h13
  change (Romik.path1 p p.phi).2 -
    ((Romik.path3 p (Real.pi / 2 - p.theta)).2 +
      (Romik.alphaBeta3 p (Real.pi / 2 - p.theta)).1 *
        Real.cos (Real.pi / 2 - p.theta)) = 0 at h21
  dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.rot, Romik.addK,
    Romik.alphaBeta3] at h9 h13 h21
  simp only [c1_eq_of_full hp, c2_eq_of_full hp] at h13 h21
  simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub] at h21
  have h4 := reverse_equation4 hp
  change (undictionary p).a + Real.pi / 2 - (undictionary p).phi -
    (undictionary p).theta - (undictionary p).b +
    1 / 2 * ((undictionary p).theta - (undictionary p).phi) *
      (1 + (undictionary p).a) +
    1 / 4 * ((undictionary p).theta - (undictionary p).phi) *
      ((undictionary p).theta - (undictionary p).phi) = 0 at h4
  change (undictionary p).a * (Real.cos (undictionary p).theta -
    Real.cos (undictionary p).phi) - 2 * (undictionary p).b *
    Real.sin (undictionary p).phi +
    ((undictionary p).theta - (undictionary p).phi - 1) *
    Real.cos (undictionary p).theta - Real.sin (undictionary p).theta +
    Real.cos (undictionary p).phi + Real.sin (undictionary p).phi = 0
  dsimp [undictionary] at h4 ⊢
  linear_combination -2 * h21 + 2 * h9 + 2 * h13 + 2 * Real.sin p.theta * h4

theorem reverse_equation2 {p : Romik.Params} (hp : Romik.Equations p) :
    Reduced.system (undictionary p) 1 = 0 := by
  have h8 := congrFun hp (8 : Fin 22)
  have h12 := congrFun hp (12 : Fin 22)
  have h20 := congrFun hp (20 : Fin 22)
  change (Romik.path1 p p.phi).1 - (Romik.path2 p p.phi).1 = 0 at h8
  change (Romik.path2 p p.theta).1 - (Romik.path3 p p.theta).1 = 0 at h12
  change (Romik.path1 p p.phi).1 -
    ((Romik.path3 p (Real.pi / 2 - p.theta)).1 -
      (Romik.alphaBeta3 p (Real.pi / 2 - p.theta)).1 *
        Real.sin (Real.pi / 2 - p.theta)) = 0 at h20
  dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.rot, Romik.addK,
    Romik.alphaBeta3] at h8 h12 h20
  simp only [c1_eq_of_full hp, c2_eq_of_full hp] at h12 h20
  simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub] at h20
  have h4 := reverse_equation4 hp
  change (undictionary p).a + Real.pi / 2 - (undictionary p).phi -
    (undictionary p).theta - (undictionary p).b +
    1 / 2 * ((undictionary p).theta - (undictionary p).phi) *
      (1 + (undictionary p).a) +
    1 / 4 * ((undictionary p).theta - (undictionary p).phi) *
      ((undictionary p).theta - (undictionary p).phi) = 0 at h4
  change (undictionary p).a * (3 * Real.sin (undictionary p).theta +
    Real.sin (undictionary p).phi) - 2 * (undictionary p).b *
    Real.cos (undictionary p).phi +
    3 * ((undictionary p).theta - (undictionary p).phi - 1) *
    Real.sin (undictionary p).theta + 3 * Real.cos (undictionary p).theta -
    Real.sin (undictionary p).phi + Real.cos (undictionary p).phi = 0
  dsimp [undictionary] at h4 ⊢
  linear_combination -2 * h20 + 2 * h8 + 2 * h12 + 2 * Real.cos p.theta * h4

theorem undictionary_equations {p : Romik.Params} (hp : Romik.Equations p) :
    Reduced.Equations (undictionary p) := by
  change Reduced.system (undictionary p) = 0
  funext i
  fin_cases i
  · exact reverse_equation1 hp
  · exact reverse_equation2 hp
  · exact reverse_equation3 hp
  · exact reverse_equation4 hp

end GerverSofa.PartF.Phases

end

end

end

section

/-!
# F06: the reverse parameters determine the full solution

Velocity matching determines the shape coefficients. Positional matching
then determines each successive translation. No numerical enclosure is used.
-/

@[expose] public section

noncomputable section
namespace GerverSofa.PartF.Phases

theorem full_equations_injective {p q : Romik.Params}
    (hp : Romik.Equations p) (hq : Romik.Equations q)
    (h : undictionary p = undictionary q) : p = q := by
  have hphi : p.phi = q.phi := congrArg Reduced.Params.phi h
  have htheta : p.theta = q.theta := congrArg Reduced.Params.theta h
  have ha := congrArg Reduced.Params.a h
  have hb := congrArg Reduced.Params.b h
  dsimp [undictionary] at ha hb
  have hb1 : p.b1 = q.b1 := by
    rw [hphi] at ha
    linarith only [ha]
  have hb2 : p.b2 = q.b2 := by
    simp only [hphi, hb1] at hb
    linarith only [hb]
  have ha2 : p.a2 = q.a2 := by
    rw [Romik.a2_eq_neg_quarter_of_equations hp,
      Romik.a2_eq_neg_quarter_of_equations hq]
  have ha1 : p.a1 = q.a1 := by
    have hpa := congrArg Prod.fst (alphaBeta12_eq hp)
    have hpb := congrArg Prod.snd (alphaBeta12_eq hp)
    have hqa := congrArg Prod.fst (alphaBeta12_eq hq)
    have hqb := congrArg Prod.snd (alphaBeta12_eq hq)
    dsimp [Romik.alphaBeta1, Romik.alphaBeta2] at hpa hpb hqa hqb
    simp only [hphi, hb1, hb2, ha2] at hpa hpb
    linear_combination (-Real.sin q.phi / 2) * hpa +
      (Real.sin q.phi / 2) * hqa + (Real.cos q.phi / 2) * hpb -
      (Real.cos q.phi / 2) * hqb -
      (p.a1 - q.a1) * Real.sin_sq_add_cos_sq q.phi
  have hc1 : p.c1 = q.c1 := by
    rw [c1_eq_of_full hp, c1_eq_of_full hq, hb1]
  have hc2 : p.c2 = q.c2 := by
    rw [c2_eq_of_full hp, c2_eq_of_full hq, hb1]
  have hd1 : p.d1 = q.d1 := by
    rw [Romik.d1_eq_quarterPi_sub_b1_of_equations hp,
      Romik.d1_eq_quarterPi_sub_b1_of_equations hq, hb1]
  have hd2 : p.d2 = q.d2 := by
    rw [Romik.d2_eq_b2_add_quarterPi_correction_of_equations hp,
      Romik.d2_eq_b2_add_quarterPi_correction_of_equations hq, hb1, hb2]
  have he1 : p.e1 = q.e1 := by
    rw [Romik.e1_eq_a1_of_equations hp, Romik.e1_eq_a1_of_equations hq, ha1]
  have he2 : p.e2 = q.e2 := by
    rw [Romik.e2_eq_neg_a2_of_equations hp, Romik.e2_eq_neg_a2_of_equations hq, ha2]
  have hk11 : p.k11 = q.k11 := by
    have h5p := congrFun hp (5 : Fin 22)
    have h5q := congrFun hq (5 : Fin 22)
    change p.k11 - 1 + p.a1 = 0 at h5p
    change q.k11 - 1 + q.a1 = 0 at h5q
    linarith only [h5p, h5q, ha1]
  have hk12 : p.k12 = q.k12 := by
    rw [Romik.k12_eq_quarter_of_equations hp, Romik.k12_eq_quarter_of_equations hq]
  have hpath1 (t : ℝ) : Romik.path1 p t = Romik.path1 q t := by
    simp only [Romik.path1, ha1, ha2, hk11, hk12]
  have hj2 : Romik.path1 p (q.phi) = Romik.path2 p (q.phi) := by
    simpa only [hphi] using Romik.match_path12_of_equations hp
  have hx2 : Romik.path2 p (q.phi) = Romik.path2 q (q.phi) :=
    hj2.symm.trans ((hpath1 (q.phi)).trans (Romik.match_path12_of_equations hq))
  dsimp [Romik.path2, Romik.addK] at hx2
  simp only [hb1, hb2] at hx2
  have hk21 : p.k21 = q.k21 := add_left_cancel (congrArg Prod.fst hx2)
  have hk22 : p.k22 = q.k22 := add_left_cancel (congrArg Prod.snd hx2)
  have hpath2 (t : ℝ) : Romik.path2 p t = Romik.path2 q t := by
    simp only [Romik.path2, hb1, hb2, hk21, hk22]
  have hj3 : Romik.path2 p (q.theta) = Romik.path3 p (q.theta) := by
    simpa only [htheta] using Romik.match_path23_of_equations hp
  have hx3 : Romik.path3 p (q.theta) = Romik.path3 q (q.theta) :=
    hj3.symm.trans ((hpath2 (q.theta)).trans (Romik.match_path23_of_equations hq))
  dsimp [Romik.path3, Romik.addK] at hx3
  simp only [hc1, hc2] at hx3
  have hk31 : p.k31 = q.k31 := add_left_cancel (congrArg Prod.fst hx3)
  have hk32 : p.k32 = q.k32 := add_left_cancel (congrArg Prod.snd hx3)
  have hpath3 (t : ℝ) : Romik.path3 p t = Romik.path3 q t := by
    simp only [Romik.path3, hc1, hc2, hk31, hk32]
  have hj4 : Romik.path3 p (Real.pi / 2 - q.theta) = Romik.path4 p (Real.pi / 2 - q.theta) := by
    simpa only [htheta] using Romik.match_path34_of_equations hp
  have hx4 : Romik.path4 p (Real.pi / 2 - q.theta) = Romik.path4 q (Real.pi / 2 - q.theta) :=
    hj4.symm.trans ((hpath3 (Real.pi / 2 - q.theta)).trans (Romik.match_path34_of_equations hq))
  dsimp [Romik.path4, Romik.addK] at hx4
  simp only [hd1, hd2] at hx4
  have hk41 : p.k41 = q.k41 := add_left_cancel (congrArg Prod.fst hx4)
  have hk42 : p.k42 = q.k42 := add_left_cancel (congrArg Prod.snd hx4)
  have hpath4 (t : ℝ) : Romik.path4 p t = Romik.path4 q t := by
    simp only [Romik.path4, hd1, hd2, hk41, hk42]
  have hj5 : Romik.path4 p (Real.pi / 2 - q.phi) = Romik.path5 p (Real.pi / 2 - q.phi) := by
    simpa only [hphi] using Romik.match_path45_of_equations hp
  have hx5 : Romik.path5 p (Real.pi / 2 - q.phi) = Romik.path5 q (Real.pi / 2 - q.phi) :=
    hj5.symm.trans ((hpath4 (Real.pi / 2 - q.phi)).trans (Romik.match_path45_of_equations hq))
  dsimp [Romik.path5, Romik.addK] at hx5
  simp only [he1, he2] at hx5
  have hk51 : p.k51 = q.k51 := add_left_cancel (congrArg Prod.fst hx5)
  have hk52 : p.k52 = q.k52 := add_left_cancel (congrArg Prod.snd hx5)
  cases p
  cases q
  congr 1

theorem dictionary_undictionary_of_equations {p : Romik.Params}
    (hp : Romik.Equations p) : dictionary (undictionary p) = p := by
  apply full_equations_injective (dictionary_equations _ (undictionary_equations hp)) hp
  exact undictionary_dictionary (undictionary p)

end GerverSofa.PartF.Phases

end

end

end

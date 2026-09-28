/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartF.Semantics.Batch002
public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Moving sofa: related mathematical developments

* `Canonical.Definitions`.
* `Canonical.GerverDefinitions`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 The Formal Conjectures Authors and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors, Dean Cureton
-/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/


/-!
# Definitions for the moving sofa problem

The definitions of `MovingSofaSubmission/Challenge.lean`, copied from
`FormalConjectures/Wikipedia/MovingSofa.lean` in google-deepmind/formal-conjectures at commit
`ddfbaf90f4482030d88aae5233fe933874296a23`. Here `ABφθSpec.existsUnique` is proved, from the
certificate in GerverSofaLean, so that Gerver's constants are defined from a proved statement.
-/

@[expose] public section

noncomputable section

scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open scoped EuclideanGeometry

/-- The plane `ℝ²` with the orientation of its standard basis, so that rotations are
counterclockwise. -/
noncomputable instance Module.orientedEuclideanSpaceFinTwo : Module.Oriented ℝ ℝ² (Fin 2) :=
  ⟨Module.Basis.orientation <| PiLp.basisFun 2 _ _⟩

/-- The plane `ℝ²` has dimension two. -/
instance fact_finrank_euclideanSpace_fin_two : Fact (Module.finrank ℝ ℝ² = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

namespace MovingSofa

open Topology
open scoped Real unitInterval EuclideanGeometry

/-- The **horizontal side** of the hallway is $(-\infty, 1] \times [0, 1]$. -/
def horizontalHallway : Set ℝ² := {!₂[x, y] | (x) (y) (_ : x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1)}

/-- The **vertical side** of the hallway is $[0, 1] \times (-\infty, 1]$. -/
def verticalHallway : Set ℝ² := {!₂[x, y] | (x) (y) (_ : 0 ≤ x ∧ x ≤ 1 ∧ y ≤ 1)}

/-- The **hallway** is the union of its horizontal and vertical sides. -/
def hallway : Set ℝ² := horizontalHallway ∪ verticalHallway

scoped notation "E(2)" => ℝ² ≃ᵃⁱ[ℝ] ℝ²

/-- The topology on the isometry group `E(2)`, induced from the continuous affine maps of the
plane. -/
instance rigidMotionTopology : TopologicalSpace E(2) :=
  .induced (·.toAffineIsometry.toContinuousAffineMap) inferInstance

/--
A connected closed set $s$ is a **moving sofa** according to a rigid motion $m:I\to\mathrm{SE}(2)$,
if the sofa is initially in the horizontal side of the hallway and ends up in the vertical side.
Here, since $\mathrm{SE}(2)$ is not in Mathlib yet, we use $\mathrm{E}(2)$ and rely on continuity
and $m(0) = \mathrm{id}$ to ensure $m$ is in $\mathrm{SE}(2)$.
-/
structure IsMovingSofa (s : Set ℝ²) (m : I → E(2)) : Prop where
  isConnected : IsConnected s
  isClosed : IsClosed s
  continuous : Continuous m
  zero : m 0 = .refl ℝ ℝ²
  initial : s ⊆ horizontalHallway
  subset_hallway : ∀ t, m t '' s ⊆ hallway
  final : m 1 '' s ⊆ verticalHallway

/--
The rigid motion that translates by $p$ and then rotates counterclockwise by $\alpha$.
Note that [Ge92] used this definition while [Ro18] used rotation first and then translation.
-/
def rotateTranslate (α : Real.Angle) (p : ℝ²) : E(2) :=
  (AffineIsometryEquiv.vaddConst ℝ p).trans
    (EuclideanGeometry.o.rotation α).toAffineIsometryEquiv

/--
The sofa according to a rotation path $p : [0, \pi/2] \to \mathbb{R}^2$ as in [Ge92] is the
intersection over $\alpha \in [0, \pi/2]$ of hallways each translated by $p(\alpha)$ and then
rotated by $\alpha$, with the special cases that the hallway at $0$ is the horizontal side
and the hallway at $\pi/2$ is the vertical side.
-/
def sofaOfRotateTranslatePath (p : ℝ → ℝ²) : Set ℝ² :=
  rotateTranslate 0 (p 0) '' horizontalHallway ∩
  rotateTranslate ↑(π / 2) (p (π / 2)) '' verticalHallway ∩
  ⋂ α ∈ Set.Icc 0 (π / 2), rotateTranslate α (p α) '' hallway

namespace GerversSofa

/-
Gerver's constants defining the sofa.

This section follows Theorem 2 of Gerver's paper [Ge92].
-/

/--
Eq. 1-4 of [Ro18], which specifies the constants $A$, $B$, $\varphi$, and $\theta$ of [Ge92].
-/
def ABφθSpec (A B φ θ : ℝ) : Prop :=
  0 ≤ φ ∧ φ ≤ θ ∧ θ ≤ π / 4 ∧ 0 ≤ A ∧ 0 ≤ B ∧
  A * (θ.cos - φ.cos) - 2 * B * φ.sin
    + (θ - φ - 1) * θ.cos - θ.sin + φ.cos + φ.sin = 0 ∧
  A * (3 * θ.sin + φ.sin) - 2 * B * φ.cos
    + 3 * (θ - φ - 1) * θ.sin + 3 * θ.cos - φ.sin + φ.cos = 0 ∧
  A * φ.cos - (φ.sin + 1 / 2 - φ.cos / 2 + B * φ.sin) = 0 ∧
  (A + π / 2 - φ - θ) - (B - (θ - φ) * (1 + A) / 2 - (θ - φ)^2 / 4) = 0

/-- There exist unique constants $A$, $B$, $\varphi$, and $\theta$ satisfying the spec. -/
theorem ABφθSpec.existsUnique : ∃! ABφθ : ℝ × ℝ × ℝ × ℝ,
    ABφθSpec ABφθ.1 ABφθ.2.1 ABφθ.2.2.1 ABφθ.2.2.2 :=
  GerverSofa.PartF.Parameters.existsUnique

/-- Gerver's constant $A$: the first component of the unique solution of `ABφθSpec`. -/
def A : ℝ := ABφθSpec.existsUnique.choose.1
/-- Gerver's constant $B$: the second component of the unique solution of `ABφθSpec`. -/
def B : ℝ := ABφθSpec.existsUnique.choose.2.1
/-- Gerver's angle $\varphi$: the third component of the unique solution of `ABφθSpec`. -/
def φ : ℝ := ABφθSpec.existsUnique.choose.2.2.1
/-- Gerver's angle $\theta$: the fourth component of the unique solution of `ABφθSpec`. -/
def θ : ℝ := ABφθSpec.existsUnique.choose.2.2.2

/-- The integral-path auxiliary function $r$, with break points $\varphi$, $\theta$,
$\pi/2 - \theta$ and $\pi/2 - \varphi$. The functions `x` and `y` are integrals of it. -/
def r (α : ℝ) : ℝ :=
  if α ≤ φ then
    1 / 2
  else if α ≤ θ then
    (1 + A + α - φ) / 2
  else if α ≤ π / 2 - θ then
    A + α - φ
  else if α ≤ π / 2 - φ then
    B - (π / 2 - α - φ) * (1 + A) / 2 - (π / 2 - α - φ) ^ 2 / 4
  else
    0

/-- $y(\alpha) = \int_\alpha^{\pi/2 - \varphi} r(t) \sin t \, dt$, used in the canonical
integral-path definition. -/
def y (α : ℝ) : ℝ :=
  ∫ t in α..π / 2 - φ, r t * t.sin

/-- $x(\alpha) = 1 - \int_\alpha^{\pi/2 - \varphi} r(t) \cos t \, dt$, used in the canonical
integral-path definition. -/
def x (α : ℝ) : ℝ :=
  1 - ∫ t in α..π / 2 - φ, r t * t.cos

/-- The rotation path of Gerver's sofa: `p α` is the translation applied to the hallway before it
is rotated by the angle $\alpha \in [0, \pi/2]$, in the convention of `rotateTranslate`. -/
def p (α : ℝ) : ℝ² :=
  !₂[if α ≤ φ
      then α.cos - 1
      else x (π / 2 - α) * α.cos + y (π / 2 - α) * α.sin - 1,
    if α ≤ π / 2 - φ
      then y α * α.cos - (4 * x 0 - 2 - x α) * α.sin - 1
      else -(4 * x 0 - 3) * α.sin - 1]

end GerversSofa

/-- Gerver's sofa is the sofa according to the rotation path `GerversSofa.p`. -/
def gerversSofa : Set ℝ² :=
  sofaOfRotateTranslatePath GerversSofa.p

open MeasureTheory
open scoped ENNReal

/-- The **sofa constant** is the maximal area of a moving sofa. -/
def sofaConstant : ℝ≥0∞ := ⨆ (s : Set ℝ²) (_ : ∃ m, IsMovingSofa s m), volume s

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
/-
MIT License

Copyright (c) 2026 Dawid Trela

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/



/-!
# Gerver's definitions in GerverSofaLean agree with the ones used here

Adapted from `F07UpstreamAdapter` in GerverSofaLean v1.1.0 (MIT). GerverSofaLean states its results
for its own copy of the moving sofa definitions. This file identifies that copy with the
definitions of `MovingSofa.Canonical.Definitions`.
-/

@[expose] public section

noncomputable section
open scoped unitInterval

namespace GerverSofa.PartF.ProjectAdapter

open Coordinates

theorem horizontalHallway_eq_model :
    MovingSofa.horizontalHallway = Model.horizontalHallway := by
  ext q
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    exact hxy
  · intro hq
    exact ⟨q 0, q 1, hq, plane_ext rfl rfl⟩

theorem verticalHallway_eq_model :
    MovingSofa.verticalHallway = Model.verticalHallway := by
  ext q
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    exact hxy
  · intro hq
    exact ⟨q 0, q 1, hq, plane_ext rfl rfl⟩

theorem hallway_eq_model : MovingSofa.hallway = Model.hallway := by
  unfold MovingSofa.hallway Model.hallway
  rw [horizontalHallway_eq_model, verticalHallway_eq_model]

theorem isMovingSofa_iff_model (s : Set Plane) (m : I → Rigid) :
    MovingSofa.IsMovingSofa s m ↔ Model.IsMovingSofa s m := by
  constructor
  · intro h
    refine ⟨h.isConnected, h.isClosed, h.continuous, h.zero, ?_, ?_, ?_⟩
    · simpa only [horizontalHallway_eq_model] using h.initial
    · intro t
      simpa only [hallway_eq_model] using h.subset_hallway t
    · simpa only [verticalHallway_eq_model] using h.final
  · intro h
    refine ⟨h.isConnected, h.isClosed, h.continuous, h.zero, ?_, ?_, ?_⟩
    · simpa only [horizontalHallway_eq_model] using h.initial
    · intro t
      simpa only [hallway_eq_model] using h.subset_hallway t
    · simpa only [verticalHallway_eq_model] using h.final

theorem sofaOfRotateTranslatePath_eq_bodySofa (p : ℝ → Plane) :
    MovingSofa.sofaOfRotateTranslatePath p =
      bodySofa p Model.horizontalHallway Model.verticalHallway Model.hallway := by
  unfold MovingSofa.sofaOfRotateTranslatePath bodySofa angleIntersection
  rw [horizontalHallway_eq_model, verticalHallway_eq_model, hallway_eq_model]
  rfl

/-- The reduced parameter tuple corresponding to the canonical choice of the unique angle
solution. -/
def selected : Reduced.Params :=
  PartE.tupleEquiv MovingSofa.GerversSofa.ABφθSpec.existsUnique.choose

theorem selected_eq_certified : selected = Integrals.certified := by
  have h : MovingSofa.GerversSofa.ABφθSpec.existsUnique.choose = Parameters.certified :=
    Parameters.choice_independent MovingSofa.GerversSofa.ABφθSpec.existsUnique
  exact (congrArg PartE.tupleEquiv h).trans (PartE.tupleEquiv.apply_symm_apply _)

theorem p_eq_selected (t : ℝ) :
    MovingSofa.GerversSofa.p t = toPlane (Integrals.path selected t) := rfl

theorem p_eq_certified : MovingSofa.GerversSofa.p =
    fun t => toPlane (Integrals.path Integrals.certified t) := by
  funext t
  rw [p_eq_selected, selected_eq_certified]

theorem integral_rotation_to_full (t : ℝ) (ht : t ∈ Set.Icc 0 (Real.pi / 2)) :
    rotation t (MovingSofa.GerversSofa.p t) = toPlane (Romik.path PartC.params t) := by
  rw [p_eq_certified]
  exact Integrals.certified_integral_rotation_to_full t ht

theorem gerversSofa_eq_certified : MovingSofa.gerversSofa = EuclideanMotion.sofa := by
  unfold MovingSofa.gerversSofa
  rw [sofaOfRotateTranslatePath_eq_bodySofa, p_eq_certified]
  exact Integrals.integral_sofa_eq_certified

end GerverSofa.PartF.ProjectAdapter

end

end

end

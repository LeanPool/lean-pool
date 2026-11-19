/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors, Adam McKenna
-/
module

public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Finset.Prod

/-!
# Planar general-position primitives

Original copyright: Copyright 2025 The Formal Conjectures Authors.
These Apache-2.0 definitions were copied verbatim from the formal-conjectures support library.

A small set of planar-geometry predicates that the
Elekes–Sharir / Guth–Katz base reduction layer (`namespace Esgk`) consumes.
None of these exist in mathlib v4.30 — they are originals from the
[`formal-conjectures`](https://github.com/google-deepmind/formal-conjectures)
support layer (`FormalConjecturesForMathlib/Geometry/2d.lean` and
`.../Data/Set/Triplewise.lean`, Apache 2.0), copied **verbatim** and given a
permanent home here so the project stays mathlib-only with no cross-version
dependency.

What they are *built on* — `Collinear`, `EuclideanGeometry.Cospherical`,
`EuclideanSpace ℝ (Fin 2)` — are mathlib citizens; only the predicates
themselves (`Set.Triplewise`, `NonTrilinear`, `distinctDistances`,
`InGeneralPosition`) and the `ℝ²` notation are formal-conjectures-specific.

Provided here:

* the `ℝ²` notation (scoped to `EuclideanGeometry`);
* `Set.Triplewise` — a ternary "holds on all distinct triples of a set" relation;
* `NonTrilinear` — no three points of a set are collinear;
* `distinctDistances` — the number of distinct pairwise distances of a finite set;
* `InGeneralPosition` — no three collinear and no four cocircular.

The earlier `FormalConjectures/Util.lean` shim hosted these alongside the
`answer( … )` / `category` / `AMS` macro-and-attribute machinery and the
vendored Erdős problem statements (96/97/98). Those statements have been
removed (`formal-conjectures` now tracks mathlib v4.30 directly), and the dead
`ConvexIndep` / `unitDistancePairsCount` / bare `Triplewise` defs and the shim
machinery went with them; only the live primitives survive here.
-/

/-! ## `ℝ²` notation (verbatim: `FormalConjecturesForMathlib/Geometry/2d.lean`) -/

@[expose] public section

/-- The Euclidean plane over the real numbers. -/
scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! ## `Set.Triplewise` (verbatim: `FormalConjecturesForMathlib/Data/Set/Triplewise.lean`) -/

namespace Set

variable {α : Type*}

/--
The ternary relation `r` holds triplewise on the set `s`
if `r x y z` for all *distinct* `x y z ∈ s`.
-/
protected def Triplewise (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s → x ≠ y → y ≠ z → x ≠ z → r x y z

end Set

/-! ## Planar geometry (verbatim: `FormalConjecturesForMathlib/Geometry/2d.lean`) -/

open scoped EuclideanGeometry Finset

namespace EuclideanGeometry

variable {V P : Type*} {n : ℕ}

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-- We say a subset `A` of points in the plane is non-trilinear
if it contains no three points that lie on the same line. -/
def NonTrilinear (A : Set P) : Prop :=
  A.Triplewise (fun x y z ↦ ¬ Collinear ℝ {x, y, z})

/--
Given a finite set of points in the plane, we define the number of distinct distances between pairs
of points.
-/
noncomputable def distinctDistances (points : Finset ℝ²) : ℕ :=
  #(points.offDiag.image fun (pair : ℝ² × ℝ²) => dist pair.1 pair.2)

/-- A collection $x_1, \dots, x_n\in\mathbb{R}^2$ is in _general position_
if no three are collinear and no four lie on a circle. -/
def InGeneralPosition (X : Finset ℝ²) : Prop :=
  NonTrilinear (SetLike.coe X) ∧ ∀ T ⊆ X, #T = 4 → ¬Cospherical (SetLike.coe T)

end EuclideanGeometry

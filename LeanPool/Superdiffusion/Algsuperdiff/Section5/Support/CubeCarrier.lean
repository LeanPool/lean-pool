/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.HighContrastHomogenization.Support.Geometry.ConvexDomain
public import LeanPool.HighContrastHomogenization.Support.Geometry.CubeMeasure

/-!
# CubeCarrier

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The translated triadic cube `y + □_n`

Section 5 localizes its Dirichlet problems on cubes `y + □_n` whose centre `y`
is an arbitrary point of `ℝ^d`, not a triadic lattice point.  The triadic-cube
descriptor `TriadicCube d` carries an *integer* index, so `y + □_n` is not of
the form `openCubeSet Q`; this file introduces the translated carrier as a set
and proves the geometric facts the Section 5 solvability and regularity
statements consume.

## Main definitions

* `cubeSetAt y n` — the open cube of side `3^n` centred at `y`, realized as the
  image of `openCubeSet (originCube d n)` under `x ↦ y + x`.

## Main results

* `cubeSetAt_eq_translateSet` — the image carrier agrees with the ambient
  translation operator `translateSet`, whose Sobolev transport API is available.
* `mem_cubeSetAt_iff` — membership is membership of the recentred point.
* `isOpen_cubeSetAt`, `measurableSet_cubeSetAt`, `convex_cubeSetAt`,
  `isOpenBoundedConvexDomain_cubeSetAt` — the domain hypotheses required by the
  variational solvability theory.
* `mem_cubeSetAt_self` — the centre belongs to its own cube, so the carrier is
  never empty.
* `norm_sub_lt_of_mem_cubeSetAt` — the diameter bound `‖x - z‖ < 3^n` in the
  ambient supremum norm.

## References

* ABK26, the localized Dirichlet problems of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open HCPolySupport

variable {d : ℕ}

/-- **The cube `y + □_n`**: the open triadic cube of side `3^n` centred at the
origin, translated so that its centre is `y`. -/
def cubeSetAt (y : Vec d) (n : ℤ) : Set (Vec d) :=
  (fun x => y + x) '' openCubeSet (originCube d n)

/-- The translated cube centred at the origin is the origin cube. -/
theorem cubeSetAt_zero_eq_openCubeSet (n : ℤ) :
    cubeSetAt (0 : Vec d) n = openCubeSet (originCube d n) := by
  ext x
  simp [cubeSetAt]

/-- The image realization of `y + □_n` is the ambient translation of the origin
cube; this is the form the Sobolev transport API is stated in. -/
theorem cubeSetAt_eq_translateSet (y : Vec d) (n : ℤ) :
    cubeSetAt y n = translateSet y (openCubeSet (originCube d n)) := by
  ext x
  rw [mem_translateSet_iff_sub_mem]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [add_sub_cancel_left]
  · intro hx
    exact ⟨x - y, hx, add_sub_cancel _ _⟩

/-- Membership in `y + □_n` is membership of the recentred point in `□_n`. -/
theorem mem_cubeSetAt_iff {y : Vec d} {n : ℤ} {x : Vec d} :
    x ∈ cubeSetAt y n ↔ x - y ∈ openCubeSet (originCube d n) := by
  rw [cubeSetAt_eq_translateSet, mem_translateSet_iff_sub_mem]

/-- The coordinate description of `y + □_n`. -/
theorem mem_cubeSetAt_iff_forall_coord {y : Vec d} {n : ℤ} {x : Vec d} :
    x ∈ cubeSetAt y n ↔
      ∀ i, (-(1 / 2 : ℝ)) * (3 : ℝ) ^ n < x i - y i ∧
        x i - y i < (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
  rw [mem_cubeSetAt_iff, mem_openCubeSet_originCube_iff]
  simp only [Pi.sub_apply]

theorem isOpen_cubeSetAt (y : Vec d) (n : ℤ) : IsOpen (cubeSetAt y n) := by
  rw [cubeSetAt_eq_translateSet]
  exact (isOpenBoundedConvexDomain_openCubeSet (originCube d n)).translateSet y |>.isOpen

theorem measurableSet_cubeSetAt (y : Vec d) (n : ℤ) :
    MeasurableSet (cubeSetAt y n) :=
  (isOpen_cubeSetAt y n).measurableSet

theorem convex_cubeSetAt (y : Vec d) (n : ℤ) : Convex ℝ (cubeSetAt y n) := by
  rw [cubeSetAt_eq_translateSet]
  exact (isOpenBoundedConvexDomain_openCubeSet (originCube d n)).translateSet y |>.convex

/-- `y + □_n` is an open bounded convex domain, the hypothesis under which the
variational Dirichlet theory is available. -/
theorem isOpenBoundedConvexDomain_cubeSetAt (y : Vec d) (n : ℤ) :
    IsOpenBoundedConvexDomain (cubeSetAt y n) := by
  rw [cubeSetAt_eq_translateSet]
  exact (isOpenBoundedConvexDomain_openCubeSet (originCube d n)).translateSet y

/-- The centre lies in its own cube; in particular `y + □_n` is nonempty. -/
theorem mem_cubeSetAt_self (y : Vec d) (n : ℤ) : y ∈ cubeSetAt y n := by
  rw [mem_cubeSetAt_iff, mem_openCubeSet_originCube_iff]
  intro i
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  simp only [Pi.sub_apply, sub_self]
  constructor <;> linarith only [h3]

theorem cubeSetAt_nonempty (y : Vec d) (n : ℤ) : (cubeSetAt y n).Nonempty :=
  ⟨y, mem_cubeSetAt_self y n⟩

/-- Two points of `y + □_n` are less than `3^n` apart in the ambient supremum
norm. -/
theorem norm_sub_lt_of_mem_cubeSetAt {y : Vec d} {n : ℤ} {x z : Vec d}
    (hx : x ∈ cubeSetAt y n) (hz : z ∈ cubeSetAt y n) :
    ‖x - z‖ < (3 : ℝ) ^ n := by
  rw [mem_cubeSetAt_iff_forall_coord] at hx hz
  refine (pi_norm_lt_iff (zpow_pos (by norm_num) n)).2 fun i => ?_
  have h1 := hx i
  have h2 := hz i
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_lt]
  constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2]

end Algsuperdiff.Section5.Support

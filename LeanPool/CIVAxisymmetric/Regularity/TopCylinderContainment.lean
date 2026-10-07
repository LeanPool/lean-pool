/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Core.Iteration.Arithmetic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder

/-!
# Containment of parabolic cylinders inside the unit cylinder

The two theorems below establish that a parabolic cylinder based at `(x, s)` with
`s < 0` and radius `r` satisfying `r ≤ r'` and `r² - s ≤ r'²` is contained in the
`r'`-thickened unit cylinder `vec3Ball x r' ×ˢ (-r'², 0)`.  The second theorem
replaces the cylinder by its closure and uses the unit cylinder itself, the
natural ambient set for the interior partial-regularity estimates of
arXiv:2609.20803.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- A parabolic cylinder based at `(x, s)` with `s < 0` and radius `r` is contained in
`vec3Ball x r' ×ˢ (-r'², 0)` whenever `r ≤ r'` and `r² - s ≤ r'²`. -/
theorem parabolicCylinder_subset_topCylinder {x : Vec3} {s r r' : ℝ}
    (hs : s < 0) (hrr' : r ≤ r') (hsq : r ^ 2 - s ≤ r' ^ 2) :
    parabolicCylinder x s r ⊆ vec3Ball x r' ×ˢ Ioo (-(r' ^ 2)) 0 := by
  rintro ⟨y, τ⟩ ⟨hy, hτ₁, hτ₂⟩
  have h1 : -(r' ^ 2) ≤ s - r ^ 2 := by linarith only [hsq]
  exact ⟨lt_of_lt_of_le hy hrr', ⟨lt_of_le_of_lt h1 hτ₁, lt_of_le_of_lt hτ₂ hs⟩⟩

/-- The closure of a parabolic cylinder based at `(x, s)` with `s < 0` is contained in
the unit cylinder `spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0)` provided the cylinder
itself is already trapped inside the unit ball in the spatial direction and its lower
time boundary is above `-1`. -/
theorem closure_parabolicCylinder_subset_unitCylinder (x : Vec3) (s r : ℝ) (hr : 0 < r)
    (hs : s < 0) (hlow : -1 < s - r ^ 2)
    (hball : ∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ r → vec3EuclideanNorm (y - 0) < 1) :
    closure (parabolicCylinder x s r) ⊆ spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0) := by
  rw [closure_parabolicCylinder hr]
  rintro ⟨y, τ⟩ ⟨hy, hτ⟩
  refine ⟨?_, ?_⟩
  · -- y ∈ vec3Ball 0 1
    have hmem : vec3EuclideanNorm (y - x) ≤ r := by
      -- from hy : y ∈ {y | vec3EuclideanNorm (y - x) ≤ r}
      simpa using hy
    exact hball y hmem
  · -- τ ∈ Ioo (-1) 0
    refine ⟨by linarith only [hlow, hτ.1], ?_⟩
    linarith only [hτ.2, hs]

end CIV

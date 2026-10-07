/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Geometry.TriangleHalfspaces
public import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic

/-!
# Owners

Geometry and verified arithmetic for the Conway–Soifer covering theorem at n = 3.
-/

/-
Adapted from https://github.com/AnanasClassic/conway-soifer-n3-lean
at b71b1d22b6f7ebb0f0173fc70a66075f44c86ce6 (public release: 11 September 2026).
The original MIT grant is retained below; the Lean Pool adaptation is released under Apache 2.0.

MIT License

Copyright (c) 2026 Vladislav Kuznetsov

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

@[expose] public section

noncomputable section
namespace ConwaySoifer

/-- These are only the hypotheses of the proposed counterexample, with owners
relabelled by their anchors. No area or certificate conclusion is a field. -/
structure AnchoredCover (r : ℝ) where
  /-- The ten triangles indexed by their distinguished anchors. -/
  triangles : Configuration
  common : CommonSide triangles r
  covers : Covers triangles
  subunit : r < 1
  anchored : ∀ i, anchor i ∈ (triangles i).carrier

namespace AnchoredCover
variable {r : ℝ}

theorem exists_of_cover (T : Configuration) (hside : CommonSide T r)
    (hcover : Covers T) (hr : r < 1) : Nonempty (AnchoredCover r) := by
  obtain ⟨owner, hbij, hmem⟩ :=
    exists_anchor_owners r T (fun i => (hside i).le) hr hcover
  refine ⟨⟨fun i => T (owner i), ?_, ?_, hr, hmem⟩⟩
  · intro i
    exact hside (owner i)
  · intro p hp
    obtain ⟨j, hj⟩ := hcover p hp
    obtain ⟨i, rfl⟩ := hbij.surjective j
    exact ⟨i, hj⟩

theorem side_eq (C : AnchoredCover r) (i : Fin 10) : (C.triangles i).side = r := C.common i

theorem nonneg (C : AnchoredCover r) : 0 ≤ r := by
  rw [← C.side_eq 0]
  exact (C.triangles 0).side_nonneg

theorem unique_anchor (C : AnchoredCover r) (i j : Fin 10)
    (hi : anchor i ∈ (C.triangles j).carrier) : i = j := by
  by_contra hne
  exact (C.triangles j).cannot_contain_unit_chord
    (by rw [C.side_eq]; exact C.subunit)
    (anchors_separated i j hne) hi (C.anchored j)

end AnchoredCover

/-- The owner index assigned to a hexagon vertex. -/
def sideIndex (i : Fin 6) : Fin 10 := ⟨i.val+1, by omega⟩
/-- The owner index assigned to a target corner. -/
def cornerIndex (j : Fin 3) : Fin 10 := ⟨j.val+7, by omega⟩

@[simp] theorem anchor_sideIndex (i : Fin 6) : anchor (sideIndex i) = vertex i := by
  fin_cases i <;> norm_num [anchor, sideIndex, vertex]
@[simp] theorem anchor_cornerIndex (j : Fin 3) : anchor (cornerIndex j) = corner j := by
  fin_cases j <;> norm_num [anchor, cornerIndex, corner]

/-- The next or previous cyclic hexagon vertex, selected by the direction flag. -/
def neighbor (i : Fin 6) (right : Bool) : Fin 6 := if right then i+1 else i+5

/-- The unit direction from a hexagon vertex to its selected neighbor. -/
def sideDirection (i : Fin 6) (right : Bool) : Point := vertex (neighbor i right)-vertex i

theorem sideDirection_unit (i : Fin 6) (right : Bool) :
    sqDist (sideDirection i right) (0, 0) = 1 := by
  fin_cases i <;> cases right
  · change sqDist ((1, -1)-(1, 0)) (0, 0) = 1
    norm_num [sqDist]
  · change sqDist ((0, 1)-(1, 0)) (0, 0) = 1
    norm_num [sqDist]
  · change sqDist ((1, 0)-(0, 1)) (0, 0) = 1
    norm_num [sqDist]
  · change sqDist ((-1, 1)-(0, 1)) (0, 0) = 1
    norm_num [sqDist]
  · change sqDist ((0, 1)-(-1, 1)) (0, 0) = 1
    norm_num [sqDist]
  · change sqDist ((-1, 0)-(-1, 1)) (0, 0) = 1
    norm_num [sqDist]
  · change sqDist ((-1, 1)-(-1, 0)) (0, 0) = 1
    norm_num [sqDist]
  · change sqDist ((0, -1)-(-1, 0)) (0, 0) = 1
    norm_num [sqDist]
  · change sqDist ((-1, 0)-(0, -1)) (0, 0) = 1
    norm_num [sqDist]
  · change sqDist ((1, -1)-(0, -1)) (0, 0) = 1
    norm_num [sqDist]
  · change sqDist ((0, -1)-(1, -1)) (0, 0) = 1
    norm_num [sqDist]
  · change sqDist ((1, 0)-(1, -1)) (0, 0) = 1
    norm_num [sqDist]

theorem vertex_mem_target (i : Fin 6) : vertex i ∈ target := by
  fin_cases i <;> norm_num [vertex, target]

theorem target_convex : Convex ℝ target := by
  intro p hp q hq a b ha hb hab
  rcases hp with ⟨hp₁, hp₂, hp₃⟩
  rcases hq with ⟨hq₁, hq₂, hq₃⟩
  change a*p.1+b*q.1 ≤ 1 ∧ a*p.2+b*q.2 ≤ 1 ∧
    -1 ≤ a*p.1+b*q.1+(a*p.2+b*q.2)
  constructor
  · nlinarith [mul_nonneg ha (sub_nonneg.mpr hp₁), mul_nonneg hb (sub_nonneg.mpr hq₁)]
  constructor
  · nlinarith [mul_nonneg ha (sub_nonneg.mpr hp₂), mul_nonneg hb (sub_nonneg.mpr hq₂)]
  · nlinarith [mul_nonneg ha (show 0 ≤ p.1+p.2+1 by linarith),
      mul_nonneg hb (show 0 ≤ q.1+q.2+1 by linarith)]

theorem sidePoint_mem_target (i : Fin 6) (right : Bool) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    linePoint (vertex i) (sideDirection i right) t ∈ target := by
  have h1 : linePoint (vertex i) (sideDirection i right) 1 = vertex (neighbor i right) := by
    simp [linePoint, sideDirection]
  apply linePoint_between target_convex (vertex_mem_target i) (u := 1) ?_ ht.1 ht.2
  rw [h1]
  exact vertex_mem_target _

namespace AnchoredCover
variable {r : ℝ}

/-- The covering triangle assigned to one hexagon vertex. -/
def sideOwner (C : AnchoredCover r) (i : Fin 6) : EquilateralTriangle := C.triangles (sideIndex i)
/-- The covering triangle assigned to one target corner. -/
def cornerOwner (C : AnchoredCover r) (j : Fin 3) : EquilateralTriangle := C.triangles (cornerIndex
    j)
/-- The covering triangle assigned to the centre anchor. -/
def centre (C : AnchoredCover r) : EquilateralTriangle := C.triangles 0

theorem side_anchor_mem (C : AnchoredCover r) (i : Fin 6) : vertex i ∈ (C.sideOwner i).carrier := by
  simpa [sideOwner] using C.anchored (sideIndex i)

theorem corner_anchor_mem (C : AnchoredCover r) (j : Fin 3) : corner j ∈ (C.cornerOwner j).carrier
    := by
  simpa [cornerOwner] using C.anchored (cornerIndex j)

/-- The full contained ray section of a side owner towards a selected neighbor. -/
def sideLen (C : AnchoredCover r) (i : Fin 6) (right : Bool) : ℝ :=
  rayLen (C.sideOwner i) (vertex i) (sideDirection i right)

theorem sideLen_pos (C : AnchoredCover r) (i : Fin 6) (right : Bool) :
    0 < C.sideLen i right := by
  apply rayLen_pos_of_unique_owner C.triangles C.covers (sideIndex i)
    (C.side_anchor_mem i) (sideDirection_unit i right) ?_ (b := 1) (by norm_num)
    (fun t ht => sidePoint_mem_target i right ht)
  intro j hji hj
  have hij := C.unique_anchor (sideIndex i) j (by simpa using hj)
  exact hji hij.symm

theorem sideLen_le_side (C : AnchoredCover r) (i : Fin 6) (right : Bool) :
    C.sideLen i right ≤ r := by
  have h := rayLen_le_side (C.sideOwner i) (C.side_anchor_mem i) (sideDirection_unit i right)
  simpa [sideLen, sideOwner, C.side_eq] using h

theorem pos (C : AnchoredCover r) : 0 < r :=
  lt_of_lt_of_le (C.sideLen_pos 0 false) (C.sideLen_le_side 0 false)

theorem sideLen_lt_one (C : AnchoredCover r) (i : Fin 6) (right : Bool) :
    C.sideLen i right < 1 := lt_of_le_of_lt (C.sideLen_le_side i right) C.subunit

/-- Choose an actual minimizer from the twelve full ray lengths. -/
def minRay (C : AnchoredCover r) : Fin 6 × Bool :=
  Classical.choose (Finite.exists_min (fun k : Fin 6 × Bool => C.sideLen k.1 k.2))

/-- The minimum of the twelve full side-owner ray sections. -/
def minimum (C : AnchoredCover r) : ℝ := C.sideLen C.minRay.1 C.minRay.2

theorem minimum_le (C : AnchoredCover r) (i : Fin 6) (right : Bool) :
    C.minimum ≤ C.sideLen i right :=
  Classical.choose_spec (Finite.exists_min (fun k : Fin 6 × Bool => C.sideLen k.1 k.2)) (i, right)

theorem minimum_pos (C : AnchoredCover r) : 0 < C.minimum :=
  C.sideLen_pos _ _

theorem minimum_lt_one (C : AnchoredCover r) : C.minimum < 1 := C.sideLen_lt_one _ _

theorem mandatory_sidePoint (C : AnchoredCover r) (i : Fin 6) (right : Bool) :
    linePoint (vertex i) (sideDirection i right) C.minimum ∈ (C.sideOwner i).carrier := by
  apply (linePoint_mem_iff_le_rayLen (C.sideOwner i) (C.side_anchor_mem i)
    (sideDirection_unit i right) C.minimum_pos.le).mpr
  exact C.minimum_le i right

theorem minRay_endpoint_mem (C : AnchoredCover r) :
    linePoint (vertex C.minRay.1) (sideDirection C.minRay.1 C.minRay.2) C.minimum ∈
      (C.sideOwner C.minRay.1).carrier := C.mandatory_sidePoint _ _

theorem minRay_endpoint_transfers (C : AnchoredCover r) :
    ∃ j : Fin 10, j ≠ sideIndex C.minRay.1 ∧
      linePoint (vertex C.minRay.1) (sideDirection C.minRay.1 C.minRay.2) C.minimum ∈
        (C.triangles j).carrier := by
  exact rayLen_transfers C.triangles C.covers (sideIndex C.minRay.1)
    (C.side_anchor_mem _) (sideDirection_unit _ _) C.minimum_lt_one
    (fun t ht => sidePoint_mem_target _ _ ht)

end AnchoredCover
end ConwaySoifer

/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Geometry.Canonical
public import LeanPool.ConwaySoifer.Geometry.Support
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# The symmetry group of the target triangle

`rot` (rotation by 120 degrees) and `refl (a, b) = (b, a)` preserve `sqDist`, the target
triangle, the hexagon, permute the ten anchors and transport full ray lengths.  A configuration
is relabelled along the induced anchor permutation, so that the minimal full side section can
be moved to `vertex 0`, towards `vertex 5` (external side) or towards `vertex 1` (internal side).
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

/-- Reflection that exchanges the two triangular coordinates. -/
def refl (p : Point) : Point := (p.2, p.1)

theorem refl_refl (p : Point) : refl (refl p) = p := by
  rcases p with ⟨a, b⟩; rfl
theorem refl_add (p q : Point) : refl (p + q) = refl p + refl q := by
  rcases p with ⟨a, b⟩; rcases q with ⟨c, d⟩; rfl
theorem refl_smul (t : ℝ) (p : Point) : refl (t • p) = t • refl p := by
  rcases p with ⟨a, b⟩; rfl
theorem refl_sub (p q : Point) : refl (p - q) = refl p - refl q := by
  rcases p with ⟨a, b⟩; rcases q with ⟨c, d⟩; rfl

theorem sqDist_rot' (p q : Point) : sqDist (rot p) (rot q) = sqDist p q := by
  rw [sqDist_eq_normSq_sub, sqDist_eq_normSq_sub, ← rot_sub, normSq_rot]
theorem sqDist_refl (p q : Point) : sqDist (refl p) (refl q) = sqDist p q := by
  rcases p with ⟨a, b⟩; rcases q with ⟨c, d⟩; simp [sqDist, refl]; ring

/-- Rotation through 120 degrees as a real linear map. -/
def rotL : Point →ₗ[ℝ] Point where
  toFun := rot
  map_add' := rot_add
  map_smul' := rot_smul
/-- Coordinate reflection as a real linear map. -/
def reflL : Point →ₗ[ℝ] Point where
  toFun := refl
  map_add' := refl_add
  map_smul' := refl_smul

theorem rot_bijective : Function.Bijective rot :=
  Function.bijective_iff_has_inverse.2 ⟨fun p => rot (rot p), rot_rot_rot, fun p => rot_rot_rot p⟩
theorem refl_bijective : Function.Bijective refl :=
  Function.bijective_iff_has_inverse.2 ⟨refl, refl_refl, refl_refl⟩

theorem rot_mem_target (p : Point) : rot p ∈ target ↔ p ∈ target := by
  rcases p with ⟨a, b⟩
  simp only [target, rot, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> refine ⟨?_, ?_, ?_⟩ <;> linarith
theorem refl_mem_target (p : Point) : refl p ∈ target ↔ p ∈ target := by
  rcases p with ⟨a, b⟩
  simp only [target, refl, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> refine ⟨?_, ?_, ?_⟩ <;> linarith
theorem rot_mem_hexagon (p : Point) : rot p ∈ hexagon ↔ p ∈ hexagon := by
  rcases p with ⟨a, b⟩
  simp only [hexagon, rot, Set.mem_ofPred_eq, abs_le]
  constructor <;> rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩⟩ <;>
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith
theorem refl_mem_hexagon (p : Point) : refl p ∈ hexagon ↔ p ∈ hexagon := by
  rcases p with ⟨a, b⟩
  simp only [hexagon, refl, Set.mem_ofPred_eq, abs_le]
  constructor <;> rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩⟩ <;>
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith

/-! ### Anchor permutations -/

/-- `rot` sends `anchor i` to `anchor (rotIdx i)`: centre fixed, `v_i ↦ v_{i+2}`,
`w_j ↦ w_{j+1}`. -/
def rotIdx : Fin 10 → Fin 10 := ![0, 3, 4, 5, 6, 1, 2, 8, 9, 7]
/-- The inverse owner permutation induced by rotation of the target. -/
def rotIdxInv : Fin 10 → Fin 10 := ![0, 5, 6, 1, 2, 3, 4, 9, 7, 8]
/-- `refl` sends `v_i ↦ v_{1-i}`, `w_0 ↦ w_0`, `w_1 ↔ w_2`. -/
def reflIdx : Fin 10 → Fin 10 := ![0, 2, 1, 6, 5, 4, 3, 7, 9, 8]
/-- The corner permutation of `refl`. -/
def reflCorner : Fin 3 → Fin 3 := ![0, 2, 1]

theorem rotIdxInv_rotIdx (i : Fin 10) : rotIdxInv (rotIdx i) = i := by
  fin_cases i <;> rfl
theorem rotIdx_rotIdxInv (i : Fin 10) : rotIdx (rotIdxInv i) = i := by
  fin_cases i <;> rfl
theorem reflIdx_reflIdx (i : Fin 10) : reflIdx (reflIdx i) = i := by
  fin_cases i <;> rfl
theorem rot_anchor (i : Fin 10) : rot (anchor i) = anchor (rotIdx i) := by
  fin_cases i <;> simp [anchor, rot, rotIdx] <;> norm_num
theorem refl_anchor (i : Fin 10) : refl (anchor i) = anchor (reflIdx i) := by
  fin_cases i <;> simp [anchor, refl, reflIdx]
theorem rotIdx_sideIndex (i : Fin 6) : rotIdx (sideIndex i) = sideIndex (i + 2) := by
  fin_cases i <;> rfl
theorem reflIdx_sideIndex (i : Fin 6) : reflIdx (sideIndex i) = sideIndex (1 - i) := by
  fin_cases i <;> rfl
theorem rotIdx_cornerIndex (j : Fin 3) : rotIdx (cornerIndex j) = cornerIndex (j + 1) := by
  fin_cases j <;> rfl
theorem reflIdx_cornerIndex (j : Fin 3) : reflIdx (cornerIndex j) = cornerIndex (reflCorner j) := by
  fin_cases j <;> rfl
theorem rotIdx_zero : rotIdx 0 = 0 := rfl
theorem reflIdx_zero : reflIdx 0 = 0 := rfl

theorem rot_vertex (i : Fin 6) : rot (vertex i) = vertex (i + 2) := by
  fin_cases i <;> simp [vertex, rot]
theorem refl_vertex (i : Fin 6) : refl (vertex i) = vertex (1 - i) := by
  fin_cases i <;> simp [vertex, refl]
theorem rot_corner (j : Fin 3) : rot (corner j) = corner (j + 1) := by
  fin_cases j <;> simp [corner, rot] <;> norm_num
theorem refl_corner (j : Fin 3) : refl (corner j) = corner (reflCorner j) := by
  fin_cases j <;> simp [corner, refl, reflCorner]
theorem rot_sideDirection (i : Fin 6) (right : Bool) :
    rot (sideDirection i right) = sideDirection (i + 2) right := by
  cases right <;> fin_cases i <;> simp [sideDirection, neighbor, vertex, rot]
theorem refl_sideDirection (i : Fin 6) (right : Bool) :
    refl (sideDirection i right) = sideDirection (1 - i) (!right) := by
  cases right <;> fin_cases i <;> simp [sideDirection, neighbor, vertex, refl]
theorem rot_cornerDirection (j : Fin 3) (m : Fin 2) :
    rot (cornerDirection j m) = cornerDirection (j + 1) m := by
  fin_cases j <;> fin_cases m <;> simp [cornerDirection, vertex, corner, rot] <;> norm_num
theorem refl_cornerDirection (j : Fin 3) (m : Fin 2) :
    refl (cornerDirection j m) = cornerDirection (reflCorner j) (1 - m) := by
  fin_cases j <;> fin_cases m <;> simp [cornerDirection, vertex, corner, refl, reflCorner]
theorem rot_coreDir (j : Fin 6) : rot (coreDir j) = coreDir (j + 2) := by
  fin_cases j <;> simp [coreDir, rot] <;> norm_num
theorem refl_coreDir (j : Fin 6) : refl (coreDir j) = coreDir (-j) := by
  fin_cases j <;> simp [coreDir, refl]
theorem rot_coreVertex (u : ℝ) (j : Fin 6) : rot (coreVertex u j) = coreVertex u (j + 2) := by
  rw [coreVertex, coreVertex, rot_smul, rot_coreDir]
theorem refl_coreVertex (u : ℝ) (j : Fin 6) : refl (coreVertex u j) = coreVertex u (-j) := by
  rw [coreVertex, coreVertex, refl_smul, refl_coreDir]
theorem rot_cornerMid (j : Fin 3) (m : Fin 2) : rot (cornerMid j m) = cornerMid (j + 1) m := by
  rw [cornerMid, cornerMid, rot_add, rot_smul, rot_corner, rot_cornerDirection]
theorem refl_cornerMid (j : Fin 3) (m : Fin 2) :
    refl (cornerMid j m) = cornerMid (reflCorner j) (1 - m) := by
  rw [cornerMid, cornerMid, refl_add, refl_smul, refl_corner, refl_cornerDirection]

/-! ### Transformed triangles and configurations -/

/-- The image of a triangle under an isometry given as a linear map. -/
def EquilateralTriangle.mapIso (T : EquilateralTriangle) (f : Point →ₗ[ℝ] Point)
    (hf : ∀ p q, sqDist (f p) (f q) = sqDist p q) : EquilateralTriangle where
  vertices := fun i => f (T.vertices i)
  side := T.side
  side_nonneg := T.side_nonneg
  equilateral := fun i j hij => by rw [hf]; exact T.equilateral i j hij

theorem EquilateralTriangle.carrier_mapIso (T : EquilateralTriangle) (f : Point →ₗ[ℝ] Point)
    (hf : ∀ p q, sqDist (f p) (f q) = sqDist p q) : (T.mapIso f hf).carrier = f '' T.carrier := by
  change convexHull ℝ (Set.range (f ∘ T.vertices)) = f '' convexHull ℝ (Set.range T.vertices)
  rw [Set.range_comp, LinearMap.image_convexHull]

theorem EquilateralTriangle.mem_mapIso (T : EquilateralTriangle) (f : Point →ₗ[ℝ] Point)
    (hf : ∀ p q, sqDist (f p) (f q) = sqDist p q) (hinj : Function.Injective f) (p : Point) :
    f p ∈ (T.mapIso f hf).carrier ↔ p ∈ T.carrier := by
  rw [T.carrier_mapIso f hf]
  exact hinj.mem_set_image

theorem rayLen_mapIso (T : EquilateralTriangle) (f : Point →ₗ[ℝ] Point)
    (hf : ∀ p q, sqDist (f p) (f q) = sqDist p q) (hinj : Function.Injective f) (v d : Point) :
    rayLen (T.mapIso f hf) (f v) (f d) = rayLen T v d := by
  unfold rayLen rayParams
  congr 1
  ext t
  simp only [Set.mem_ofPred_eq, linePoint]
  rw [← map_smul, ← map_add, T.mem_mapIso f hf hinj]

/-- Relabelled and transformed configuration: owner `i` of the new configuration is the image
of the owner of the anchor sent to `anchor i`. -/
def Configuration.transform (T : Configuration) (f : Point →ₗ[ℝ] Point)
    (hf : ∀ p q, sqDist (f p) (f q) = sqDist p q) (σinv : Fin 10 → Fin 10) : Configuration :=
  fun i => (T (σinv i)).mapIso f hf

theorem Configuration.transform_common {T : Configuration} {r : ℝ} (h : CommonSide T r)
    (f : Point →ₗ[ℝ] Point) (hf : ∀ p q, sqDist (f p) (f q) = sqDist p q) (σinv : Fin 10 → Fin 10) :
    CommonSide (T.transform f hf σinv) r := fun i => h (σinv i)

theorem Configuration.transform_covers {T : Configuration} (h : Covers T) (f : Point →ₗ[ℝ] Point)
    (hf : ∀ p q, sqDist (f p) (f q) = sqDist p q) (hbij : Function.Bijective f)
    (htarget : ∀ p, f p ∈ target ↔ p ∈ target) (σinv : Fin 10 → Fin 10)
    (hσ : Function.Surjective σinv) : Covers (T.transform f hf σinv) := by
  intro p hp
  obtain ⟨q, rfl⟩ := hbij.2 p
  obtain ⟨j, hj⟩ := h q ((htarget q).mp hp)
  obtain ⟨i, rfl⟩ := hσ j
  exact ⟨i, ((T (σinv i)).mem_mapIso f hf hbij.1 q).mpr hj⟩

theorem Configuration.transform_anchored {T : Configuration} (h : ∀ i, anchor i ∈ (T i).carrier)
    (f : Point →ₗ[ℝ] Point) (hf : ∀ p q, sqDist (f p) (f q) = sqDist p q)
    (hinj : Function.Injective f) (σ σinv : Fin 10 → Fin 10) (hσ : ∀ i, σ (σinv i) = i)
    (hanchor : ∀ i, f (anchor i) = anchor (σ i)) : ∀ i, anchor i ∈ ((T.transform f hf σinv)
        i).carrier := by
  intro i
  have := h (σinv i)
  rw [← (T (σinv i)).mem_mapIso f hf hinj, hanchor, hσ] at this
  exact this

/-- The rotated configuration. -/
def Configuration.rotate (T : Configuration) : Configuration :=
  T.transform rotL sqDist_rot' rotIdxInv

/-- The reflected configuration. -/
def Configuration.reflect (T : Configuration) : Configuration :=
  T.transform reflL sqDist_refl reflIdx

theorem rotate_common {T : Configuration} {r : ℝ} (h : CommonSide T r) : CommonSide T.rotate r :=
  Configuration.transform_common h _ _ _
theorem reflect_common {T : Configuration} {r : ℝ} (h : CommonSide T r) : CommonSide T.reflect r :=
  Configuration.transform_common h _ _ _
theorem rotate_covers {T : Configuration} (h : Covers T) : Covers T.rotate :=
  Configuration.transform_covers h rotL sqDist_rot' rot_bijective rot_mem_target rotIdxInv
    (Function.bijective_iff_has_inverse.2 ⟨rotIdx, rotIdx_rotIdxInv, rotIdxInv_rotIdx⟩).2
theorem reflect_covers {T : Configuration} (h : Covers T) : Covers T.reflect :=
  Configuration.transform_covers h reflL sqDist_refl refl_bijective refl_mem_target reflIdx
    (Function.bijective_iff_has_inverse.2 ⟨reflIdx, reflIdx_reflIdx, reflIdx_reflIdx⟩).2
theorem rotate_anchored {T : Configuration} (h : ∀ i, anchor i ∈ (T i).carrier) :
    ∀ i, anchor i ∈ (T.rotate i).carrier :=
  Configuration.transform_anchored h rotL sqDist_rot' rot_bijective.1 rotIdx rotIdxInv
    rotIdx_rotIdxInv rot_anchor
theorem reflect_anchored {T : Configuration} (h : ∀ i, anchor i ∈ (T i).carrier) :
    ∀ i, anchor i ∈ (T.reflect i).carrier :=
  Configuration.transform_anchored h reflL sqDist_refl refl_bijective.1 reflIdx reflIdx
    reflIdx_reflIdx refl_anchor

/-- Membership transport for the rotated owners. -/
theorem mem_rotate (T : Configuration) (i : Fin 10) (p : Point) :
    rot p ∈ (T.rotate (rotIdx i)).carrier ↔ p ∈ (T i).carrier := by
  change rotL p ∈ ((T (rotIdxInv (rotIdx i))).mapIso rotL sqDist_rot').carrier ↔ _
  rw [rotIdxInv_rotIdx]
  exact (T i).mem_mapIso rotL sqDist_rot' rot_bijective.1 p
theorem mem_reflect (T : Configuration) (i : Fin 10) (p : Point) :
    refl p ∈ (T.reflect (reflIdx i)).carrier ↔ p ∈ (T i).carrier := by
  change reflL p ∈ ((T (reflIdx (reflIdx i))).mapIso reflL sqDist_refl).carrier ↔ _
  rw [reflIdx_reflIdx]
  exact (T i).mem_mapIso reflL sqDist_refl refl_bijective.1 p

theorem rayLen_rotate (T : Configuration) (i : Fin 10) (v d : Point) :
    rayLen (T.rotate (rotIdx i)) (rot v) (rot d) = rayLen (T i) v d := by
  change rayLen ((T (rotIdxInv (rotIdx i))).mapIso rotL sqDist_rot') (rotL v) (rotL d) = _
  rw [rotIdxInv_rotIdx]
  exact rayLen_mapIso (T i) rotL sqDist_rot' rot_bijective.1 v d
theorem rayLen_reflect (T : Configuration) (i : Fin 10) (v d : Point) :
    rayLen (T.reflect (reflIdx i)) (refl v) (refl d) = rayLen (T i) v d := by
  change rayLen ((T (reflIdx (reflIdx i))).mapIso reflL sqDist_refl) (reflL v) (reflL d) = _
  rw [reflIdx_reflIdx]
  exact rayLen_mapIso (T i) reflL sqDist_refl refl_bijective.1 v d

/-- Side sections of the rotated configuration. -/
theorem sideLen_rotate (T : Configuration) (i : Fin 6) (right : Bool) :
    rayLen (T.rotate (sideIndex (i + 2))) (vertex (i + 2)) (sideDirection (i + 2) right) =
      rayLen (T (sideIndex i)) (vertex i) (sideDirection i right) := by
  rw [← rotIdx_sideIndex, ← rot_vertex, ← rot_sideDirection, rayLen_rotate]
theorem sideLen_reflect (T : Configuration) (i : Fin 6) (right : Bool) :
    rayLen (T.reflect (sideIndex (1 - i))) (vertex (1 - i)) (sideDirection (1 - i) (!right)) =
      rayLen (T (sideIndex i)) (vertex i) (sideDirection i right) := by
  rw [← reflIdx_sideIndex, ← refl_vertex, ← refl_sideDirection, rayLen_reflect]
theorem cornerLen_rotate (T : Configuration) (j : Fin 3) (m : Fin 2) :
    rayLen (T.rotate (cornerIndex (j + 1))) (corner (j + 1)) (cornerDirection (j + 1) m) =
      rayLen (T (cornerIndex j)) (corner j) (cornerDirection j m) := by
  rw [← rotIdx_cornerIndex, ← rot_corner, ← rot_cornerDirection, rayLen_rotate]
theorem cornerLen_reflect (T : Configuration) (j : Fin 3) (m : Fin 2) :
    rayLen (T.reflect (cornerIndex (reflCorner j))) (corner (reflCorner j))
        (cornerDirection (reflCorner j) (1 - m)) =
      rayLen (T (cornerIndex j)) (corner j) (cornerDirection j m) := by
  rw [← reflIdx_cornerIndex, ← refl_corner, ← refl_cornerDirection, rayLen_reflect]

end ConwaySoifer

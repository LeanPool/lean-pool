/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Geometry.Area
public import LeanPool.ConwaySoifer.SevenTriangles.Geometry.Wedge
import Mathlib.Tactic

/-!
# Bridge to the vendored oblique-coordinate library

`toOblique (a, b) = (a + b/2, b)` is the linear change of coordinates from the triangular
coordinates of this project to the oblique coordinates of the vendored `SevenTriangles`
library (pinned commit `b17ca52a395519f43fc15f83fb49a5dd69996225`).  It preserves `sqDist`,
maps the hexagon onto `unitHexagon`, the six vertices onto the six vertices with the same
index, and has determinant one, so it preserves Lebesgue measure.  Consequently every
nondegenerate triangle of this project is a triangle of the vendored library with the same
side, and the 120-degree wedge area-loss lemma transfers verbatim.
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
open MeasureTheory
namespace ConwaySoifer

/-- The inverse linear coordinate change from oblique to triangular coordinates. -/
def ofOblique (p : Point) : Point := (p.1 - p.2 / 2, p.2)

@[simp] theorem ofOblique_toOblique (p : Point) : ofOblique (toOblique p) = p := by
  rcases p with ⟨a, b⟩; simp [ofOblique, toOblique]

@[simp] theorem toOblique_ofOblique (p : Point) : toOblique (ofOblique p) = p := by
  rcases p with ⟨a, b⟩; simp [ofOblique, toOblique]

theorem toOblique_add (p q : Point) : toOblique (p + q) = toOblique p + toOblique q := by
  rcases p with ⟨a, b⟩; rcases q with ⟨c, d⟩
  apply Prod.ext <;> simp [toOblique]; ring

theorem toOblique_sub (p q : Point) : toOblique (p - q) = toOblique p - toOblique q := by
  rcases p with ⟨a, b⟩; rcases q with ⟨c, d⟩
  apply Prod.ext <;> simp [toOblique]; ring

theorem toOblique_smul (t : ℝ) (p : Point) : toOblique (t • p) = t • toOblique p := by
  rcases p with ⟨a, b⟩
  apply Prod.ext <;> simp [toOblique]; ring

@[simp] theorem toOblique_zero : toOblique (0 : Point) = 0 := by
  simp [toOblique]

/-- The determinant-one linear coordinate change to the borrowed oblique-coordinate geometry. -/
def obliqueL : Point →ₗ[ℝ] Point where
  toFun := toOblique
  map_add' := toOblique_add
  map_smul' := toOblique_smul

@[simp] theorem obliqueL_apply (p : Point) : obliqueL p = toOblique p := rfl

theorem toOblique_injective : Function.Injective toOblique :=
  Function.LeftInverse.injective ofOblique_toOblique

theorem toOblique_surjective : Function.Surjective toOblique :=
  Function.RightInverse.surjective toOblique_ofOblique

theorem toOblique_bijective : Function.Bijective toOblique :=
  ⟨toOblique_injective, toOblique_surjective⟩

theorem sqDist_oblique (p q : Point) :
    SevenTriangles.sqDist (toOblique p) (toOblique q) = sqDist p q := by
  rcases p with ⟨a, b⟩; rcases q with ⟨c, d⟩
  simp [SevenTriangles.sqDist, sqDist, toOblique]; ring

theorem toOblique_vertex (i : Fin 6) : toOblique (vertex i) = SevenTriangles.vertex i := by
  fin_cases i <;> simp [vertex, SevenTriangles.vertex, toOblique] <;> norm_num

theorem mem_unitHexagon_toOblique (p : Point) :
    toOblique p ∈ SevenTriangles.unitHexagon ↔ p ∈ hexagon := by
  rcases p with ⟨a, b⟩
  simp only [SevenTriangles.unitHexagon, hexagon, toOblique, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h1, ?_⟩
    · convert h3 using 2; ring
    · convert h2 using 2; ring
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h2, ?_, ?_⟩
    · convert h3 using 2; ring
    · convert h1 using 2; ring

theorem image_hexagon : toOblique '' hexagon = SevenTriangles.unitHexagon := by
  ext p
  obtain ⟨q, rfl⟩ := toOblique_surjective p
  rw [toOblique_injective.mem_set_image, mem_unitHexagon_toOblique]

theorem det_obliqueL : LinearMap.det obliqueL = 1 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Module.Basis.coe_finTwoProd_repr, obliqueL, toOblique]

theorem volume_image_toOblique (s : Set Point) : volume (toOblique '' s) = volume s := by
  have h : toOblique '' s = obliqueL '' s := rfl
  rw [h, Measure.addHaar_image_linearMap, det_obliqueL]
  simp

/-- A nondegenerate triangle of this project as a triangle of the vendored library. -/
def EquilateralTriangle.toST (T : EquilateralTriangle) (hs : 0 < T.side) :
    SevenTriangles.EquilateralTriangle where
  vertices := fun j => toOblique (T.vertices j)
  side := T.side
  side_pos := hs
  equilateral := fun i j hij => by rw [sqDist_oblique]; exact T.equilateral i j hij

theorem EquilateralTriangle.carrier_toST (T : EquilateralTriangle) (hs : 0 < T.side) :
    (T.toST hs).carrier = toOblique '' T.carrier := by
  change convexHull ℝ (Set.range (obliqueL ∘ T.vertices)) =
    obliqueL '' convexHull ℝ (Set.range T.vertices)
  rw [Set.range_comp, LinearMap.image_convexHull]

theorem EquilateralTriangle.mem_carrier_toST (T : EquilateralTriangle) (hs : 0 < T.side)
    (p : Point) : toOblique p ∈ (T.toST hs).carrier ↔ p ∈ T.carrier := by
  rw [T.carrier_toST hs]
  exact toOblique_injective.mem_set_image

theorem EquilateralTriangle.volume_diff_toST (T : EquilateralTriangle) (hs : 0 < T.side) :
    volume ((T.toST hs).carrier \ SevenTriangles.unitHexagon) =
      volume (T.carrier \ hexagon) := by
  rw [T.carrier_toST hs, ← image_hexagon, ← Set.image_sdiff toOblique_injective,
    volume_image_toOblique]

theorem toOblique_sidePoint (i : Fin 6) (right : Bool) (t : ℝ) :
    toOblique (linePoint (vertex i) (sideDirection i right) t) =
      SevenTriangles.vertex i + t • (SevenTriangles.vertex (neighbor i right) -
        SevenTriangles.vertex i) := by
  simp only [linePoint, sideDirection, toOblique_add, toOblique_smul, toOblique_sub,
    toOblique_vertex]

theorem neighbor_false (i : Fin 6) : neighbor i false = SevenTriangles.previous i := rfl
theorem neighbor_true (i : Fin 6) : neighbor i true = SevenTriangles.next i := rfl

/-- The weak 120-degree wedge area-loss lemma in triangular coordinates: a triangle
containing `vertex i` and the points at ray parameters `a` (towards `vertex (i+5)`) and `b`
(towards `vertex (i+1)`) loses volume at least `min(a², b²)/2` outside the hexagon. -/
theorem wedge_area_weak (i : Fin 6) (T : EquilateralTriangle) (hs : 0 < T.side) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hv : vertex i ∈ T.carrier)
    (hpa : linePoint (vertex i) (sideDirection i false) a ∈ T.carrier)
    (hpb : linePoint (vertex i) (sideDirection i true) b ∈ T.carrier) :
    min (a ^ 2) (b ^ 2) / 2 ≤ (volume (T.carrier \ hexagon)).toReal := by
  rw [← T.volume_diff_toST hs]
  refine le_trans ?_ (SevenTriangles.volume_diff_wedge_le i (T.toST hs))
  apply SevenTriangles.wedge_area_weak i (T.toST hs) ha hb
  · rw [← toOblique_vertex, T.mem_carrier_toST hs]; exact hv
  · rw [← neighbor_false, ← toOblique_sidePoint, T.mem_carrier_toST hs]; exact hpa
  · rw [← neighbor_true, ← toOblique_sidePoint, T.mem_carrier_toST hs]; exact hpb

/-- The strong version, valid when the two contained lengths exceed the side. -/
theorem wedge_area_strong (i : Fin 6) (T : EquilateralTriangle) (hs : 0 < T.side) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hv : vertex i ∈ T.carrier)
    (hpa : linePoint (vertex i) (sideDirection i false) a ∈ T.carrier)
    (hpb : linePoint (vertex i) (sideDirection i true) b ∈ T.carrier)
    (hab : T.side < a + b) :
    max (a ^ 2) (b ^ 2) / 2 ≤ (volume (T.carrier \ hexagon)).toReal := by
  rw [← T.volume_diff_toST hs]
  refine le_trans ?_ (SevenTriangles.volume_diff_wedge_le i (T.toST hs))
  apply SevenTriangles.wedge_area_strong i (T.toST hs) ha hb
  · rw [← toOblique_vertex, T.mem_carrier_toST hs]; exact hv
  · rw [← neighbor_false, ← toOblique_sidePoint, T.mem_carrier_toST hs]; exact hpa
  · rw [← neighbor_true, ← toOblique_sidePoint, T.mem_carrier_toST hs]; exact hpb
  · exact hab

end ConwaySoifer

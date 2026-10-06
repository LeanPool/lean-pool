/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Geometry.ForbiddenCorner
public import LeanPool.ConwaySoifer.Simplified.Geometry.Affine
import Mathlib.Tactic

/-!
# Midpoint

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
namespace ConwaySoifer.Simplified

/-- The affine local coordinate system at the first target corner. -/
def cornerCoordinates : Point →ᵃ[ℝ] Point :=
  (-reflL).toAffineMap + AffineMap.const ℝ Point (1, 1)

theorem cornerCoordinates_apply (p : Point) : cornerCoordinates p = (1 - p.2, 1 - p.1) := by
  ext <;> simp [cornerCoordinates, reflL, refl] <;> ring

theorem cornerCoordinates_isometry (p q : Point) :
    sqDist (cornerCoordinates p) (cornerCoordinates q) = sqDist p q := by
  rw [cornerCoordinates_apply, cornerCoordinates_apply]
  simp [sqDist]; ring

/-- The forbidden midpoint used in canonical normalization, now by geometry. -/
theorem midpoint_exclusion {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 2)
    {Q : EquilateralTriangle} (hQ : 0 < Q.side) (hQ1 : Q.side < 1)
    (hw : corner 0 ∈ Q.carrier)
    (hs : linePoint (corner 0) (cornerDirection 0 1) u ∈ Q.carrier)
    (hp : linePoint (vertex 0) (sideDirection 0 true) u ∈ Q.carrier)
    (hm : extMid0 ∈ Q.carrier) : False := by
  let Q' := Q.mapAffineIso cornerCoordinates cornerCoordinates_isometry
  have mem {p : Point} (h : p ∈ Q.carrier) : cornerCoordinates p ∈ Q'.carrier :=
    Q.mem_mapAffineIso _ _ h
  have hge : 1 ≤ Q'.side := by
    refine forbidden_corner_section (Q := Q') (s := u) (c := 1 / 2) hu0.le hu (by norm_num)
      (by nlinarith [mul_nonneg hu0.le (sub_nonneg.mpr hu)]) hQ ?_ ?_ ?_ ?_
    · simpa [cornerCoordinates_apply, corner] using mem hw
    · simpa [cornerCoordinates_apply, extMid0] using mem hm
    · simpa [cornerCoordinates_apply, linePoint, corner, cornerDirection, vertex] using mem hs
    · simpa [cornerCoordinates_apply, linePoint, vertex, sideDirection, neighbor] using mem hp
  exact (not_le.mpr hQ1) hge

/-- A triangle containing a corner and both half-edge points misses the base. -/
theorem half_midpoints_base {Q : EquilateralTriangle} {u : ℝ}
    (hQ : 0 < Q.side) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (h0 : (0, 0) ∈ Q.carrier) (he : (1 / 2, 0) ∈ Q.carrier)
    (hf : (0, 1 / 2) ∈ Q.carrier) (hp : (1 - u, u) ∈ Q.carrier) : 1 ≤ Q.side := by
  have half {U : EquilateralTriangle} {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / 2)
      (hU : 0 < U.side) (h0 : (0, 0) ∈ U.carrier) (he : (1 / 2, 0) ∈ U.carrier)
      (hf : (0, 1 / 2) ∈ U.carrier) (hp : (1 - v, v) ∈ U.carrier) : 1 ≤ U.side := by
    apply forbidden_corner_section hv0 hv1 (c := 1 / 2) (by norm_num)
      (by nlinarith [mul_nonneg hv0 (sub_nonneg.mpr hv1)]) hU h0 (by norm_num; exact he) _ hp
    have hm := U.convex_carrier h0 hf (a := 1 - 2 * v) (b := 2 * v)
      (by linarith) (by linarith) (by ring)
    convert hm using 1; ext <;> simp; ring
  by_cases hu : u ≤ 1 / 2
  · exact half hu0 hu hQ h0 he hf hp
  · let Q' := Q.mapIso reflL sqDist_refl
    have mem {p : Point} (h : p ∈ Q.carrier) : refl p ∈ Q'.carrier := by
      change reflL p ∈ (Q.mapIso reflL sqDist_refl).carrier
      rw [Q.carrier_mapIso reflL sqDist_refl]
      exact Set.mem_image_of_mem reflL h
    refine half (U := Q') (v := 1 - u) (by linarith) (by linarith) hQ ?_ ?_ ?_ ?_
    · simpa [refl] using mem h0
    · simpa [refl] using mem hf
    · simpa [refl] using mem he
    · simpa [refl] using mem hp

end ConwaySoifer.Simplified

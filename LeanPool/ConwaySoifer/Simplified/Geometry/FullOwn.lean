/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Geometry.SupportFan
public import LeanPool.ConwaySoifer.Simplified.Geometry.Affine
import Mathlib.Tactic

/-!
# FullOwn

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

/-- A full minimal section restricts the face direction to a single cone.
One fixed triple proves the side bound on both boundaries of that cone. -/
theorem full_own_obstruction {Q : EquilateralTriangle} {s c : ℝ}
    (hs : 0 < s) (hsc : s < c) (hQ : 0 < Q.side)
    (hv : vertex 0 ∈ Q.carrier) (hu : (1, -s) ∈ Q.carrier) (hq : (1, c) ∈ Q.carrier)
    (hend : rayLen Q (vertex 0) (sideDirection 0 true) = s)
    (hlo : c ^ 2 - c * s + s ^ 2 ≤ (c * (c + s)) ^ 2)
    (hhi : 3 ≤ (2 * (c + s)) ^ 2) : 1 ≤ Q.side := by
  have hc : 0 < c := by
    linarith
  have hpt : (1 - s, s) ∈ Q.carrier := by
    have hh := rayLen_endpoint_mem Q hv (sideDirection_unit 0 true)
    rw [hend] at hh
    simpa [linePoint, vertex, sideDirection, neighbor, sub_eq_add_neg] using hh
  have hlow : len (s, c - s) ≤ supportNum (s, c - s) (1 - s, s) (1, -s) (1, c) := by
    apply support_of_sq
    · have he : supportNum (s, c - s) (1 - s, s) (1, -s) (1, c) = c * (c + s) := by
        simp [supportNum, cross, rot]; ring
      rw [he]; positivity
    · convert hlo using 1 <;> simp [normSq, supportNum, cross, rot] <;> ring
  have hhigh : len (-1, 2) ≤ supportNum (-1, 2) (1 - s, s) (1, -s) (1, c) := by
    apply support_of_sq
    · simp [supportNum, cross, rot]
      linarith
    · convert hhi using 1 <;> simp [normSq, supportNum, cross, rot] <;> ring
  obtain ⟨O, hleft, hright⟩ := Q.exists_orientation_in_arc hQ
  have hb : 0 ≤ O.dir.2 := by
    simpa [cross, eastDir] using hleft
  have hab : 0 ≤ O.dir.1 + O.dir.2 := by
    simpa [cross, eastDir, rot] using hright
  obtain ⟨j, hj, hf⟩ := O.full_endpoint hv (sideDirection_unit 0 true)
  rw [hend] at hf
  have hfu := hf _ hu
  have hfq := hf _ hq
  fin_cases j
  · have hpos : 0 < O.dir.1 + O.dir.2 := by
      simpa [rotPow, sideDirection, neighbor, vertex, cross] using hj
    have hcrosslow : 0 ≤ cross (s, c - s) O.dir := by
      simp [rotPow, linePoint, sideDirection, neighbor, vertex, cross] at hfq ⊢
      nlinarith
    have hcrosshigh : 0 ≤ cross O.dir (-1, 2) := by
      simp [rotPow, linePoint, sideDirection, neighbor, vertex, cross] at hfu ⊢
      nlinarith
    apply O.one_le_side_of_bound hpt hu hq
    exact support_bound_on_cone hlow hhigh
      (by simp [cross]; linarith) hcrosslow hcrosshigh
  · simp [rotPow, sideDirection, neighbor, vertex, cross, rot] at hj
    linarith
  · have ha : O.dir.1 < 0 := by
      simp [rotPow, sideDirection, neighbor, vertex, cross, rot] at hj
      linarith
    have hp := mul_pos (neg_pos.mpr ha) (sub_pos.mpr hsc)
    have hp' := mul_nonneg hab hc.le
    simp [rotPow, linePoint, sideDirection, neighbor, vertex, cross, rot] at hfq
    nlinarith

end ConwaySoifer.Simplified

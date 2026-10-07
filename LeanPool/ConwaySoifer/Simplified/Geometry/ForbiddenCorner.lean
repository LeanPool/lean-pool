/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Geometry.Support
import Mathlib.Tactic

/-! The forbidden corner section, proved directly on two closed orientation sectors.
No Boolean geometry checks or external polynomial results are used. -/

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

/-- The two linear supports dominate the triangular norm. -/
theorem two_supports_sq {U V a b : ℝ} (hU0 : 0 ≤ U)
    (hV0 : 0 ≤ V) (hUV : 2 ≤ U + V + U * V)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 2 + a * b + b ^ 2 ≤ max (a + V * b) (U * a + b) ^ 2 := by
  rcases le_total (U * a + b) (a + V * b) with h | h
  · rw [max_eq_left h]
    have h1 := mul_nonneg ha (show 0 ≤ U + V + U * V - 2 by linarith)
    have h2 := mul_nonneg (show 0 ≤ 1 + V by linarith)
      (show 0 ≤ (1 - U) * a - (1 - V) * b by nlinarith)
    have h3 : 0 ≤ (2 * V - 1) * a - (1 - V ^ 2) * b := by
      nlinarith
    nlinarith [mul_nonneg hb h3]
  · rw [max_eq_right h]
    have h1 := mul_nonneg hb (show 0 ≤ U + V + U * V - 2 by linarith)
    have h2 := mul_nonneg (show 0 ≤ 1 + U by linarith)
      (show 0 ≤ (1 - V) * b - (1 - U) * a by nlinarith)
    have h3 : 0 ≤ (2 * U - 1) * b - (1 - U ^ 2) * a := by
      nlinarith
    nlinarith [mul_nonneg ha h3]

/-- The handwritten corner-section obstruction in the standard 60-degree basis. -/
theorem forbidden_corner_section {Q : EquilateralTriangle} {s c : ℝ}
    (hs : 0 ≤ s) (hsc : s ≤ c) (hc : c ≤ 1) (hbound : c * (2 - s) + s ^ 2 ≤ 1)
    (hside : 0 < Q.side) (h0 : (0, 0) ∈ Q.carrier)
    (he : (1 - c, 0) ∈ Q.carrier) (hf : (0, s) ∈ Q.carrier)
    (hp : (1 - s, s) ∈ Q.carrier) : 1 ≤ Q.side := by
  obtain ⟨O, hleft, hright⟩ := Q.exists_orientation_in_arc hside
  have hy : 0 ≤ O.dir.2 := by
    simpa [eastDir, cross] using hleft
  have hxy : 0 ≤ O.dir.1 + O.dir.2 := by
    simpa [eastDir, cross, rot] using hright
  have hlen := len_sq O.dir
  have hn := len_nonneg O.dir
  by_cases hx : 0 ≤ O.dir.1
  · apply O.one_le_side_of_bound hf h0 hp
    have heq : supportNum O.dir (0, s) (0, 0) (1 - s, s) = O.dir.1 + O.dir.2 := by
      simp [supportNum, cross, rot]; ring
    rw [heq]
    dsimp [normSq] at hlen
    nlinarith [mul_nonneg hx hy]
  · have hx' : 0 ≤ -O.dir.1 := by
      linarith
    have hsq := two_supports_sq (U := 1 - c + s) (V := 1 - s)
      (a := -O.dir.1) (b := O.dir.1 + O.dir.2)
      (by linarith) (by linarith) (by nlinarith) hx' hxy
    have hB : supportNum O.dir (0, 0) (1 - s, s) (1 - s, s) =
        -O.dir.1 + (1 - s) * (O.dir.1 + O.dir.2) := by
      simp [supportNum, cross, rot]; ring
    have hE : supportNum O.dir (0, 0) (1 - c, 0) (1 - s, s) =
        (1 - c + s) * -O.dir.1 + (O.dir.1 + O.dir.2) := by
      simp [supportNum, cross, rot]; ring
    have hmax : 0 ≤ max (-O.dir.1 + (1 - s) * (O.dir.1 + O.dir.2))
        ((1 - c + s) * -O.dir.1 + (O.dir.1 + O.dir.2)) := by
      apply le_trans _ (le_max_left _ _)
      exact add_nonneg hx' (mul_nonneg (by linarith) hxy)
    have hb : len O.dir ≤ max (-O.dir.1 + (1 - s) * (O.dir.1 + O.dir.2))
        ((1 - c + s) * -O.dir.1 + (O.dir.1 + O.dir.2)) := by
      dsimp [normSq] at hlen
      nlinarith
    rw [← hB, ← hE] at hb
    rcases le_max_iff.mp hb with hb | hb
    · exact O.one_le_side_of_bound h0 hp hp hb
    · exact O.one_le_side_of_bound h0 he hp hb

end ConwaySoifer.Simplified

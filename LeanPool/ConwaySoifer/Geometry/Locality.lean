/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Geometry.Canonical
import Mathlib.Tactic

/-!
# Locality: which owners can meet a boundary segment

Every anchor other than the listed ones is at squared distance at least `1` from every point of
the segment, so its owner (a closed triangle of side `< 1`) cannot contain any point of the
segment.  Hexagon side `i` runs from `vertex i` to `vertex (i+1)`; its admissible owners are the
centre, `S_i`, `S_{i+1}` and, for even `i`, the corner owner `A_{i/2}`.  The corner segment from
`corner j` to `vertex (2j+m)` admits `A_j`, `S_{2j}`, `S_{2j+1}`.  This is the content of
`proof/verify_locality.py`.
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

/-- Admissible owners of hexagon side `i`. -/
def sideAllowed (i : Fin 6) (k : Fin 10) : Bool :=
  decide (k = 0) || decide (k = sideIndex i) || decide (k = sideIndex (i + 1)) ||
    (decide (i.val % 2 = 0) && decide (k.val = 7 + i.val / 2))

/-- Admissible owners of the corner segments of cell `j`. -/
def cornerAllowed (j : Fin 3) (k : Fin 10) : Bool :=
  decide (k = cornerIndex j) || decide (k.val = 2 * j.val + 1) || decide (k.val = 2 * j.val + 2)

theorem anchor_far_from_side (i : Fin 6) (k : Fin 10) (hk : sideAllowed i k = false) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    1 ≤ sqDist (anchor k) (linePoint (vertex i) (sideDirection i true) t) := by
  have h01 := mul_nonneg ht0 (sub_nonneg.2 ht1)
  have h11 := mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 ht1)
  have h00 := mul_nonneg ht0 ht0
  fin_cases i <;> fin_cases k <;> simp [sideAllowed, sideIndex] at hk <;>
    simp only [sqDist, anchor, Fin.reduceFinMk, Matrix.cons_val, linePoint, vertex, Fin.zero_eta,
        Fin.isValue, Matrix.cons_val_zero, sideDirection, neighbor, ↓reduceIte, zero_add,
        Matrix.cons_val_one, Prod.mk_sub_mk, zero_sub, sub_zero, Prod.smul_mk, smul_eq_mul, mul_neg,
        mul_one, Prod.mk_add_mk, ge_iff_le, even_two, Even.neg_pow, neg_add_rev, neg_neg,
        sub_add_cancel_left, Fin.mk_one, Fin.reduceAdd, sub_self, mul_zero, add_zero,
        sub_neg_eq_add, one_pow, le_add_iff_nonneg_left, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, one_le_sq_iff_one_le_abs, one_mul, neg_mul, neg_sub,
        add_sub_cancel, zero_mul] <;>
    first | nlinarith | (rw [le_abs]; left; linarith) | (rw [le_abs]; right; linarith)

theorem anchor_far_from_cornerSeg (j : Fin 3) (m : Fin 2) (k : Fin 10)
    (hk : cornerAllowed j k = false) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    1 ≤ sqDist (anchor k) (linePoint (corner j) (cornerDirection j m) t) := by
  have h01 := mul_nonneg ht0 (sub_nonneg.2 ht1)
  have h11 := mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 ht1)
  have h00 := mul_nonneg ht0 ht0
  fin_cases j <;> fin_cases m <;> fin_cases k <;> simp [cornerAllowed, cornerIndex] at hk <;>
    simp only [sqDist, anchor, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, linePoint, corner,
        cornerDirection, vertex, mul_zero, add_zero, Prod.mk_sub_mk, sub_self, zero_sub,
        Prod.smul_mk, smul_eq_mul, mul_neg, mul_one, Prod.mk_add_mk, even_two, Even.neg_pow,
        one_pow, neg_add_rev, neg_neg, neg_mul, one_mul, ge_iff_le, Fin.reduceFinMk,
        Matrix.cons_val, sub_add_cancel_left, neg_sub, sub_neg_eq_add, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_mul, zero_add, one_le_sq_iff_one_le_abs, Fin.mk_one,
        Matrix.cons_val_one, le_add_iff_nonneg_left, Nat.reduceAdd, Nat.reduceMul, add_sub_cancel]
        <;>
    first | nlinarith | (rw [le_abs]; left; linarith) | (rw [le_abs]; right; linarith)

/-- A point of hexagon side `i` can only belong to an admissible owner. -/
theorem side_owner_allowed {T : Configuration} {r : ℝ} (hcommon : CommonSide T r) (hr : r < 1)
    (hanch : ∀ i, anchor i ∈ (T i).carrier) (i : Fin 6) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {k : Fin 10} (hk : linePoint (vertex i) (sideDirection i true) t ∈ (T k).carrier) :
    sideAllowed i k = true := by
  by_contra h
  have h' : sideAllowed i k = false := by
    simpa using h
  exact (T k).cannot_contain_unit_chord (by rw [hcommon]; exact hr)
    (anchor_far_from_side i k h' ht0 ht1) (hanch k) hk

/-- A point of a corner segment of cell `j` can only belong to an admissible owner. -/
theorem cornerSeg_owner_allowed {T : Configuration} {r : ℝ} (hcommon : CommonSide T r) (hr : r < 1)
    (hanch : ∀ i, anchor i ∈ (T i).carrier) (j : Fin 3) (m : Fin 2) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) {k : Fin 10} (hk : linePoint (corner j) (cornerDirection j m) t ∈ (T k).carrier) :
    cornerAllowed j k = true := by
  by_contra h
  have h' : cornerAllowed j k = false := by
    simpa using h
  exact (T k).cannot_contain_unit_chord (by rw [hcommon]; exact hr)
    (anchor_far_from_cornerSeg j m k h' ht0 ht1) (hanch k) hk

/-- Points of the corner segments lie in the target triangle. -/
theorem cornerSeg_mem_target (j : Fin 3) (m : Fin 2) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    linePoint (corner j) (cornerDirection j m) t ∈ target := by
  fin_cases j <;> fin_cases m <;> refine ⟨?_, ?_, ?_⟩ <;>
    simp [corner, vertex, cornerDirection, linePoint] <;> linarith

end ConwaySoifer

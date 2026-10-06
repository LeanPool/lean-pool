/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Geometry.Symmetry
public import LeanPool.ConwaySoifer.Geometry.Owners
import Mathlib.Tactic

/-!
# Moving the minimal side section to `vertex 0`

`MinAt T r s i₀ r₀` records an anchored full cover of common side `r < 1` whose twelve full
side sections are all at least `s > 0`, with equality at the section of `S_{i₀}` towards its
neighbour selected by `r₀`.  Rotations shift `i₀` by two and reflections send `(i₀, r₀)` to
`(1 - i₀, ¬r₀)`, so every such cover can be moved to one with the minimum at `vertex 0`.
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

/-- Full length of the section of side owner `i` towards its neighbour. -/
def sideLenC (T : Configuration) (i : Fin 6) (right : Bool) : ℝ :=
  rayLen (T (sideIndex i)) (vertex i) (sideDirection i right)

/-- An anchored subunit cover with a positive minimal side section attained at one selected ray. -/
structure MinAt (T : Configuration) (r s : ℝ) (i₀ : Fin 6) (r₀ : Bool) : Prop where
  common : CommonSide T r
  covers : Covers T
  r_lt : r < 1
  anchored : ∀ i, anchor i ∈ (T i).carrier
  s_pos : 0 < s
  side_min : ∀ (i : Fin 6) (right : Bool), s ≤ sideLenC T i right
  attained : sideLenC T i₀ r₀ = s

theorem MinAt.rotate {T : Configuration} {r s : ℝ} {i₀ : Fin 6} {r₀ : Bool}
    (h : MinAt T r s i₀ r₀) : MinAt T.rotate r s (i₀ + 2) r₀ where
  common := rotate_common h.common
  covers := rotate_covers h.covers
  r_lt := h.r_lt
  anchored := rotate_anchored h.anchored
  s_pos := h.s_pos
  side_min := by
    intro i right
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 2 := ⟨i - 2, by abel⟩
    rw [sideLenC, sideLen_rotate]
    exact h.side_min i' right
  attained := by
    rw [sideLenC, sideLen_rotate]; exact h.attained

theorem MinAt.reflect {T : Configuration} {r s : ℝ} {i₀ : Fin 6} {r₀ : Bool}
    (h : MinAt T r s i₀ r₀) : MinAt T.reflect r s (1 - i₀) (!r₀) where
  common := reflect_common h.common
  covers := reflect_covers h.covers
  r_lt := h.r_lt
  anchored := reflect_anchored h.anchored
  s_pos := h.s_pos
  side_min := by
    intro i right
    obtain ⟨i', rfl⟩ : ∃ i', i = 1 - i' := ⟨1 - i, by abel⟩
    obtain ⟨right', rfl⟩ : ∃ right', right = !right' := ⟨!right, by simp⟩
    rw [sideLenC, sideLen_reflect]
    exact h.side_min i' right'
  attained := by
    rw [sideLenC, sideLen_reflect]; exact h.attained

/-- Every minimal section can be moved to `vertex 0`. -/
theorem MinAt.toZero {T : Configuration} {r s : ℝ} {i₀ : Fin 6} {r₀ : Bool}
    (h : MinAt T r s i₀ r₀) : ∃ (T' : Configuration) (right : Bool), MinAt T' r s 0 right := by
  fin_cases i₀
  · exact ⟨T, r₀, h⟩
  · exact ⟨T.reflect, !r₀, by simpa using h.reflect⟩
  · exact ⟨T.rotate.rotate, r₀, by simpa using h.rotate.rotate⟩
  · exact ⟨T.reflect.rotate, !r₀, by simpa using h.reflect.rotate⟩
  · exact ⟨T.rotate, r₀, by simpa using h.rotate⟩
  · exact ⟨T.reflect.rotate.rotate, !r₀, by simpa using h.reflect.rotate.rotate⟩

/-- The minimum of the twelve full sections of an anchored cover. -/
theorem AnchoredCover.minAt {r : ℝ} (C : AnchoredCover r) :
    MinAt C.triangles r C.minimum C.minRay.1 C.minRay.2 where
  common := C.common
  covers := C.covers
  r_lt := C.subunit
  anchored := C.anchored
  s_pos := C.minimum_pos
  side_min := fun i right => C.minimum_le i right
  attained := rfl

/-- From any full cover of common side `r < 1` to a cover with its minimal section at
`vertex 0`. -/
theorem exists_minAt_zero (r : ℝ) (T : Configuration) (hside : CommonSide T r) (hcover : Covers T)
    (hr : r < 1) : ∃ (T' : Configuration) (s : ℝ) (right : Bool), MinAt T' r s 0 right := by
  obtain ⟨C⟩ := AnchoredCover.exists_of_cover T hside hcover hr
  obtain ⟨T', right, h⟩ := C.minAt.toZero
  exact ⟨T', C.minimum, right, h⟩

end ConwaySoifer

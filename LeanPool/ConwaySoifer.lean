/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Theorem
import Mathlib.Tactic

/-!
# Conway–Soifer covering conjecture for n = 3

Source: doi:10.5281/zenodo.22712658, url:https://github.com/AnanasClassic/conway-soifer-n3-lean/tree/b71b1d22b6f7ebb0f0173fc70a66075f44c86ce6
Authors: Vladislav Kuznetsov
Status: verified
Main declarations: `ConwaySoifer.ten_triangle_cover_lower_bound`
Tags: discrete-geometry, triangle-covering, conway-soifer, bernstein-polynomials
MSC: 52C15, 51M16
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

namespace ConwaySoifer
open scoped Pointwise

/-- Any ten congruent closed equilateral triangles covering the side-three target
have common side at least one, with arbitrary positions and orientations. -/
theorem ten_triangle_cover_lower_bound : LowerBound := lowerBound_simplified

/-- Ten unit equilateral triangles cannot cover the target of side `3 + ε`. -/
theorem no_ten_unit_triangle_cover (ε : ℝ) (hε : 0 < ε) (T : Configuration)
    (hs : ∀ i, (T i).side = 1)
    (hcover : ∀ p ∈ (1 + ε / 3) • target, ∃ i, p ∈ (T i).carrier) : False :=
  no_ten_unit_triangle_cover_simplified ε hε T hs hcover

end ConwaySoifer

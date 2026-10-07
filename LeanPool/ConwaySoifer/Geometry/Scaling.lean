/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Geometry.Basic
import Mathlib.Tactic

/-! Scaling transfers any proof of the side-three lower bound. -/

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
open scoped Pointwise

/-! ## The scaling corollary -/

/-- The triangle scaled by `c > 0` about the origin. -/
def EquilateralTriangle.scale (T : EquilateralTriangle) (c : ℝ) (hc : 0 ≤ c) :
    EquilateralTriangle where
  vertices := fun i => c • T.vertices i
  side := c * T.side
  side_nonneg := mul_nonneg hc T.side_nonneg
  equilateral := fun i j hij => by rw [sqDist_smul, T.equilateral i j hij]; ring

theorem EquilateralTriangle.carrier_scale (T : EquilateralTriangle) (c : ℝ) (hc : 0 ≤ c) :
    (T.scale c hc).carrier = c • T.carrier := by
  unfold EquilateralTriangle.carrier EquilateralTriangle.scale
  simp only
  rw [← Set.smul_set_range, convexHull_smul]

/-- Ten unit triangles cannot cover the triangle of side `3 + ε`: the target scaled by
`(3 + ε)/3 = 1 + ε/3`. -/
theorem no_ten_unit_triangle_cover_of_lowerBound (hLB : LowerBound) (ε : ℝ) (hε : 0 < ε)
    (T : Configuration) (hs : ∀ i, (T i).side = 1)
    (hcover : ∀ p ∈ (1 + ε / 3) • target, ∃ i, p ∈ (T i).carrier) : False := by
  have h1 : (0 : ℝ) < 1 + ε / 3 := by
    linarith
  have hc : (0 : ℝ) < (1 + ε / 3)⁻¹ := inv_pos.mpr h1
  let T' : Configuration := fun i => (T i).scale (1 + ε / 3)⁻¹ hc.le
  have hs' : CommonSide T' (1 + ε / 3)⁻¹ := fun i => by
    change (1 + ε / 3)⁻¹ * (T i).side = (1 + ε / 3)⁻¹
    rw [hs i, mul_one]
  have hcov' : Covers T' := by
    intro p hp
    obtain ⟨i, hi⟩ := hcover ((1 + ε / 3) • p) (Set.smul_mem_smul_set hp)
    refine ⟨i, ?_⟩
    change p ∈ ((T i).scale (1 + ε / 3)⁻¹ hc.le).carrier
    rw [EquilateralTriangle.carrier_scale]
    refine Set.mem_smul_set.mpr ⟨(1 + ε / 3) • p, hi, ?_⟩
    rw [smul_smul, inv_mul_cancel₀ h1.ne', one_smul]
  have hge := hLB _ T' hs' hcov'
  have hlt : (1 + ε / 3)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  linarith

end ConwaySoifer

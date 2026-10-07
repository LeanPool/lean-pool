/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Geometry.Symmetry
import Mathlib.Tactic

/-!
# Affine

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

/-- Transport a filled equilateral triangle by an affine distance-preserving map. -/
def EquilateralTriangle.mapAffineIso (T : EquilateralTriangle) (f : Point →ᵃ[ℝ] Point)
    (hf : ∀ p q, sqDist (f p) (f q) = sqDist p q) : EquilateralTriangle where
  vertices := fun i => f (T.vertices i)
  side := T.side
  side_nonneg := T.side_nonneg
  equilateral := fun i j hij => by rw [hf]; exact T.equilateral i j hij

theorem EquilateralTriangle.carrier_mapAffineIso (T : EquilateralTriangle)
    (f : Point →ᵃ[ℝ] Point) (hf : ∀ p q, sqDist (f p) (f q) = sqDist p q) :
    (T.mapAffineIso f hf).carrier = f '' T.carrier := by
  change convexHull ℝ (Set.range (f ∘ T.vertices)) = f '' convexHull ℝ (Set.range T.vertices)
  rw [Set.range_comp, AffineMap.image_convexHull]

theorem EquilateralTriangle.mem_mapAffineIso (T : EquilateralTriangle)
    (f : Point →ᵃ[ℝ] Point) (hf : ∀ p q, sqDist (f p) (f q) = sqDist p q)
    {p : Point} (hp : p ∈ T.carrier) : f p ∈ (T.mapAffineIso f hf).carrier := by
  rw [T.carrier_mapAffineIso f hf]
  exact Set.mem_image_of_mem f hp

namespace Simplified

/-- The linear part of the side-owner receiver coordinate change. -/
def receiverLinear : Point →ₗ[ℝ] Point where
  toFun p := (-p.1, p.1 + p.2)
  map_add' p q := by
    ext <;> simp <;> ring
  map_smul' a p := by
    ext <;> simp; ring

/-- The affine coordinates at the minimal side-owner receiver. -/
def receiverCoordinates (s : ℝ) : Point →ᵃ[ℝ] Point :=
  receiverLinear.toAffineMap + AffineMap.const ℝ Point (1, s - 1)

theorem receiverCoordinates_apply (s : ℝ) (p : Point) :
    receiverCoordinates s p = (1 - p.1, p.1 + p.2 + s - 1) := by
  ext <;> simp [receiverCoordinates, receiverLinear] <;> ring

theorem receiverCoordinates_isometry (s : ℝ) (p q : Point) :
    sqDist (receiverCoordinates s p) (receiverCoordinates s q) = sqDist p q := by
  rw [receiverCoordinates_apply, receiverCoordinates_apply]
  simp [sqDist]; ring

end Simplified
end ConwaySoifer

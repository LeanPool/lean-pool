/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Geometry.BridgeLocal
public import LeanPool.ConwaySoifer.Simplified.Geometry.HexSymmetry
import Mathlib.Tactic

/-!
# Bridge

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

private theorem bridge_right {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 3)
    {Q : EquilateralTriangle} (hQ : 0 < Q.side)
    (hk : ∀ j, coreVertex u j ∈ Q.carrier)
    (hp : linePoint (vertex 0) (sideDirection 0 true) (2 * u) ∈ Q.carrier) :
    1 ≤ Q.side := by
  apply bridgeLocal_obstruction hu0 hu hQ
  intro j
  fin_cases j
  · convert hk 1 using 1; ext <;> simp [bridgeLocalPoint, coreVertex, coreDir] <;> ring
  · convert hk 2 using 1; ext <;> simp [bridgeLocalPoint, coreVertex, coreDir] <;> ring
  · convert hk 3 using 1; ext <;> simp [bridgeLocalPoint, coreVertex, coreDir] <;> ring
  · convert hk 4 using 1; ext <;> simp [bridgeLocalPoint, coreVertex, coreDir] <;> ring
  · simpa [bridgeLocalPoint, linePoint, sideDirection, neighbor, vertex] using hp

/-- The bridge in both directions at vertex zero, with no computed hypotheses. -/
theorem bridge_exclusion {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 3) (right : Bool)
    {Q : EquilateralTriangle} (hQ : 0 < Q.side) (hQ1 : Q.side < 1)
    (hk : ∀ j, coreVertex u j ∈ Q.carrier)
    (hp : linePoint (vertex 0) (sideDirection 0 right) (2 * u) ∈ Q.carrier) : False := by
  cases right
  · let Q' := Q.mapIso horizontal horizontal_isometry
    have mem {p : Point} (hm : p ∈ Q.carrier) : horizontal p ∈ Q'.carrier := by
      rw [EquilateralTriangle.carrier_mapIso]
      exact Set.mem_image_of_mem _ hm
    have hk' (j : Fin 6) : coreVertex u j ∈ Q'.carrier := by
      have h := mem (hk (5 - j))
      rw [horizontal_core] at h
      convert h using 1
      congr 1
      omega
    have hp' : linePoint (vertex 0) (sideDirection 0 true) (2 * u) ∈ Q'.carrier := by
      simpa [horizontal_sidePoint] using mem hp
    exact (not_le.mpr hQ1) (bridge_right hu0 hu (Q := Q') hQ hk' hp')
  · exact (not_le.mpr hQ1) (bridge_right hu0 hu hQ hk hp)

/-- The bridge at all six vertices. Rotating a local triangle does not assume
that a 60-degree rotation preserves the side-three target. -/
theorem bridge_all_exclusion {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 3)
    (i : Fin 6) (right : Bool) {Q : EquilateralTriangle} (hQ : 0 < Q.side) (hQ1 : Q.side < 1)
    (hk : ∀ j, coreVertex u j ∈ Q.carrier)
    (hp : linePoint (vertex i) (sideDirection i right) (2 * u) ∈ Q.carrier) : False := by
  let Q' := Q.mapIso (hexToZero i) (hexToZero_isometry i)
  have mem {p : Point} (hm : p ∈ Q.carrier) : hexToZero i p ∈ Q'.carrier := by
    rw [EquilateralTriangle.carrier_mapIso]
    exact Set.mem_image_of_mem _ hm
  have hk' (j : Fin 6) : coreVertex u j ∈ Q'.carrier := by
    have h := mem (hk (j + i))
    rw [hexToZero_core, add_sub_cancel_right] at h
    exact h
  exact bridge_exclusion hu0 hu right (Q := Q') hQ hQ1 hk'
    (by simpa [hexToZero_sidePoint] using mem hp)

end ConwaySoifer.Simplified

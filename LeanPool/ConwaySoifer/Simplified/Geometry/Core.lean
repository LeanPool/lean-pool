/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Geometry.CoreLocal
public import LeanPool.ConwaySoifer.Simplified.Geometry.HexSymmetry
import Mathlib.Tactic

/-!
# Core

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

private theorem core_zero {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 2)
    {Q : EquilateralTriangle} (hQ : 0 < Q.side) (hv : vertex 0 ∈ Q.carrier)
    (hp : linePoint (vertex 0) (sideDirection 0 false) u ∈ Q.carrier)
    (hn : linePoint (vertex 0) (sideDirection 0 true) u ∈ Q.carrier)
    (hk : coreVertex u 0 ∈ Q.carrier) : 1 ≤ Q.side := by
  apply adaptiveCoreLocal_obstruction hu0 hu hQ
  intro j
  fin_cases j
  · simpa [adaptiveCoreLocalPoint, vertex] using hv
  · simpa [adaptiveCoreLocalPoint, linePoint, vertex, sideDirection, neighbor] using hp
  · convert hk using 1; ext <;> simp [adaptiveCoreLocalPoint, coreVertex, coreDir] <;> ring
  · simpa [adaptiveCoreLocalPoint, linePoint, vertex, sideDirection, neighbor] using hn

private theorem core_at_zero {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 2) (j : Fin 6)
    {Q : EquilateralTriangle} (hQ : 0 < Q.side) (hQ1 : Q.side < 1)
    (hv : vertex 0 ∈ Q.carrier)
    (hp : linePoint (vertex 0) (sideDirection 0 false) u ∈ Q.carrier)
    (hn : linePoint (vertex 0) (sideDirection 0 true) u ∈ Q.carrier)
    (hk : coreVertex u j ∈ Q.carrier) : False := by
  have hu1 : 0 < u * (1 - u) := mul_pos hu0 (by linarith)
  fin_cases j
  · exact (not_le.mpr hQ1) (core_zero hu0 hu hQ hv hp hn hk)
  · apply Q.cannot_contain_unit_chord hQ1 _ hv hk
    simp [vertex, coreVertex, coreDir, sqDist]
    nlinarith [sq_nonneg (u * (1 - u))]
  · apply Q.cannot_contain_unit_chord hQ1 _ hv hk
    simp [vertex, coreVertex, coreDir, sqDist]
    nlinarith [sq_nonneg (u * (1 - u))]
  · apply Q.cannot_contain_unit_chord hQ1 _ hv hk
    simp [vertex, coreVertex, coreDir, sqDist]
    nlinarith [sq_nonneg (u * (1 - u))]
  · apply Q.cannot_contain_unit_chord hQ1 _ hv hk
    simp [vertex, coreVertex, coreDir, sqDist]
    nlinarith [sq_nonneg (u * (1 - u))]
  · let Q' := Q.mapIso horizontal horizontal_isometry
    have mem {p : Point} (hm : p ∈ Q.carrier) : horizontal p ∈ Q'.carrier := by
      rw [EquilateralTriangle.carrier_mapIso]
      exact Set.mem_image_of_mem _ hm
    have hge : 1 ≤ Q'.side := core_zero hu0 hu hQ
      (by simpa [horizontal, vertex] using mem hv)
      (by simpa [horizontal_sidePoint] using mem hn)
      (by simpa [horizontal_sidePoint] using mem hp)
      (by simpa [horizontal_core] using mem hk)
    exact (not_le.mpr hQ1) hge

/-- Adaptive-core exclusion, for every side owner and every core vertex. -/
theorem core_exclusion {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 2) (i j : Fin 6)
    {Q : EquilateralTriangle} (hQ : 0 < Q.side) (hQ1 : Q.side < 1)
    (hv : vertex i ∈ Q.carrier)
    (hp : linePoint (vertex i) (sideDirection i false) u ∈ Q.carrier)
    (hn : linePoint (vertex i) (sideDirection i true) u ∈ Q.carrier)
    (hk : coreVertex u j ∈ Q.carrier) : False := by
  let Q' := Q.mapIso (hexToZero i) (hexToZero_isometry i)
  have mem {p : Point} (hm : p ∈ Q.carrier) : hexToZero i p ∈ Q'.carrier := by
    rw [EquilateralTriangle.carrier_mapIso]
    exact Set.mem_image_of_mem _ hm
  exact core_at_zero hu0 hu (j - i) (Q := Q') hQ hQ1
    (by simpa [hexToZero_vertex] using mem hv)
    (by simpa [hexToZero_sidePoint] using mem hp)
    (by simpa [hexToZero_sidePoint] using mem hn)
    (by simpa [hexToZero_core] using mem hk)

end ConwaySoifer.Simplified

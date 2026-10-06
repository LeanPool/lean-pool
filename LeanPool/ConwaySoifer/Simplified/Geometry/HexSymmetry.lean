/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Geometry.Affine
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# HexSymmetry

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

/-- Rotation by `-i * 60°`. Only a local hexagon symmetry is asserted. -/
def hexToZeroFun (i : Fin 6) (p : Point) : Point :=
  ![p, (p.1 + p.2, -p.1), (p.2, -p.1 - p.2), (-p.1, -p.2),
    (-p.1 - p.2, p.1), (-p.2, p.1 + p.2)] i

/-- The linear hexagon symmetry moving a selected vertex to the first vertex. -/
def hexToZero (i : Fin 6) : Point →ₗ[ℝ] Point where
  toFun := hexToZeroFun i
  map_add' p q := by
    fin_cases i <;> ext <;> simp [hexToZeroFun] <;> ring
  map_smul' a p := by
    fin_cases i <;> ext <;> simp [hexToZeroFun] <;> ring

theorem hexToZero_isometry (i : Fin 6) (p q : Point) :
    sqDist (hexToZero i p) (hexToZero i q) = sqDist p q := by
  fin_cases i <;> simp [hexToZero, hexToZeroFun, sqDist] <;> ring

theorem hexToZero_vertex (i : Fin 6) : hexToZero i (vertex i) = vertex 0 := by
  fin_cases i <;> norm_num [hexToZero, hexToZeroFun, vertex]

theorem hexToZero_sidePoint (i : Fin 6) (right : Bool) (s : ℝ) :
    hexToZero i (linePoint (vertex i) (sideDirection i right) s) =
      linePoint (vertex 0) (sideDirection 0 right) s := by
  fin_cases i <;> cases right <;> ext <;>
    simp [hexToZero, hexToZeroFun, linePoint, sideDirection, neighbor, vertex] <;> ring

theorem hexToZero_core (i j : Fin 6) (s : ℝ) :
    hexToZero i (coreVertex s j) = coreVertex s (j - i) := by
  fin_cases i <;> fin_cases j <;> ext <;>
    dsimp [hexToZero, hexToZeroFun, coreVertex, coreDir, Fin.sub_def] <;> ring

/-- Reflection across the Euclidean horizontal axis, expressed in triangular coordinates. -/
def horizontal : Point →ₗ[ℝ] Point where
  toFun p := (p.1 + p.2, -p.2)
  map_add' p q := by
    ext <;> simp <;> ring
  map_smul' a p := by
    ext <;> simp; ring

theorem horizontal_isometry (p q : Point) :
    sqDist (horizontal p) (horizontal q) = sqDist p q := by
      simp [horizontal, sqDist]; ring

theorem horizontal_core (j : Fin 6) (s : ℝ) :
    horizontal (coreVertex s j) = coreVertex s (5 - j) := by
  fin_cases j <;> ext <;> dsimp [horizontal, coreVertex, coreDir, Fin.sub_def] <;> ring

theorem horizontal_sidePoint (right : Bool) (s : ℝ) :
    horizontal (linePoint (vertex 0) (sideDirection 0 right) s) =
      linePoint (vertex 0) (sideDirection 0 (!right)) s := by
  cases right <;> ext <;> simp [horizontal, linePoint, sideDirection, neighbor, vertex]

theorem hexToZero_mem_hexagon (i : Fin 6) (p : Point) :
    hexToZero i p ∈ hexagon ↔ p ∈ hexagon := by
  fin_cases i <;> simp only [hexagon, abs_le, hexToZero, Fin.zero_eta, Fin.isValue,
      LinearMap.coe_mk, AddHom.coe_mk, hexToZeroFun, Nat.succ_eq_add_one, Nat.reduceAdd,
      Matrix.cons_val_zero, Set.mem_ofPred_eq, Fin.mk_one, Matrix.cons_val_one, neg_le_neg_iff,
      add_neg_cancel_comm, Fin.reduceFinMk, Matrix.cons_val, neg_le_sub_iff_le_add,
      le_neg_add_iff_add_le, tsub_le_iff_right, add_sub_cancel, le_add_neg_iff_add_le,
      neg_add_le_iff_le_add, add_neg_le_iff_le_add, neg_add_cancel_comm_assoc] <;>
    constructor <;> rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩⟩ <;>
    (repeat' constructor) <;> linarith

theorem sext_inverse (p : Point) : hexToZero 5 (hexToZero 1 p) = p := by
  ext <;> dsimp [hexToZero, hexToZeroFun] <;> ring

theorem sext_map_side (i : Fin 6) (d : Bool) (t : ℝ) :
    hexToZero 5 (linePoint (vertex (i + 5)) (sideDirection (i + 5) d) t) =
      linePoint (vertex i) (sideDirection i d) t := by
  fin_cases i <;> cases d <;> ext <;>
    dsimp [hexToZero, hexToZeroFun, linePoint, sideDirection, neighbor, vertex] <;> ring

theorem sint_map_side (i : Fin 6) (d : Bool) (t : ℝ) :
    reflL (linePoint (vertex (1 - i)) (sideDirection (1 - i) (!d)) t) =
      linePoint (vertex i) (sideDirection i d) t := by
  fin_cases i <;> cases d <;> ext <;>
    dsimp [reflL, refl, linePoint, sideDirection, neighbor, vertex, Fin.sub_def]

end ConwaySoifer.Simplified

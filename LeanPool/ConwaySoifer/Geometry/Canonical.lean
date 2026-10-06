/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Geometry.Owners
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# The four normalized contact cases

After the geometric normalization (owner relabelling, symmetries of `T₃`, choice of the minimal
full section) a hypothetical cover is described by `Canonical c T r s`: ten anchored owners of
common side `r < 1`, the parameter `s` bounding all twelve full side sections from below and
attained by the section of `S₀` towards `v_jj` (`jj = 5` for `Sext`, `1` otherwise), the corner
sections of length at least `s`, the adaptive core `K_s ⊆ C`, and the case-specific contact.
`SmallStrengthening` records the additional necessary conditions proved for `s ≤ 1/14`.

Owner indices: `0` = centre `C`, `sideIndex i = i+1` = `S_i`, `cornerIndex j = j+7` = `A_j`.
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

/-- The six directions of the central hexagon `𝒦`. -/
def coreDir : Fin 6 → Point := ![(1, 1), (-1, 2), (-2, 1), (-1, -1), (1, -2), (2, -1)]

/-- The vertices of `K_u = (u(1-u)/3) 𝒦`. -/
def coreVertex (u : ℝ) (j : Fin 6) : Point := (u * (1 - u) / 3) • coreDir j

/-- Unit direction from corner `j` towards `vertex (2j + k)`. -/
def cornerDirection (j : Fin 3) (k : Fin 2) : Point :=
  vertex ⟨2 * j.val + k.val, by omega⟩ - corner j

theorem cornerDirection_unit (j : Fin 3) (k : Fin 2) : sqDist (cornerDirection j k) (0, 0) = 1 := by
  fin_cases j <;> fin_cases k <;> simp [cornerDirection, vertex, corner, sqDist] <;> norm_num

/-- The external midpoint `(w_j + v_{2j+k}) / 2` of corner cell `j`. -/
def cornerMid (j : Fin 3) (k : Fin 2) : Point :=
  corner j + (1 / 2 : ℝ) • cornerDirection j k

/-- `M₀ = (1, 1/2)`, the midpoint of `[w₀, v₀]`. -/
def extMid0 : Point := (1, 1 / 2)

theorem extMid0_eq : extMid0 = cornerMid 0 0 := by
  simp [extMid0, cornerMid, cornerDirection, corner, vertex]; norm_num

/-- The receiving vertex index of the minimal section. -/
inductive ContactCase where
  | Sext | Sint | Aown | Across
  deriving DecidableEq, Repr

/-- The neighbor direction of the attained minimal section in this contact case. -/
def ContactCase.right : ContactCase → Bool
  | .Sext => false
  | _ => true

/-- Whether the minimal endpoint is received by a side owner. -/
def ContactCase.isS : ContactCase → Prop
  | .Sext => True
  | .Sint => True
  | _ => False

/-- The minimal endpoint `v₀ + s (v_jj - v₀)`. -/
def minEndpoint (c : ContactCase) (s : ℝ) : Point :=
  linePoint (vertex 0) (sideDirection 0 c.right) s

/-- The case-specific contact conditions. -/
def BranchHolds : ContactCase → Configuration → ℝ → Prop
  | .Sext, T, s => minEndpoint .Sext s ∈ (T 6).carrier
  | .Sint, T, s => minEndpoint .Sint s ∈ (T 2).carrier
  | .Aown, T, s => minEndpoint .Aown s ∈ (T 7).carrier ∧ minEndpoint .Aown s ∉ (T 2).carrier ∧
      extMid0 ∈ (T 1).carrier
  | .Across, T, s => minEndpoint .Across s ∈ (T 7).carrier ∧ minEndpoint .Across s ∉ (T 2).carrier ∧
      extMid0 ∈ (T 2).carrier

/-- A normalized hypothetical cover in contact case `c` with parameter `s`. -/
structure Canonical (c : ContactCase) (T : Configuration) (r s : ℝ) : Prop where
  common : CommonSide T r
  covers : Covers T
  r_pos : 0 < r
  r_lt : r < 1
  anchored : ∀ i, anchor i ∈ (T i).carrier
  s_pos : 0 < s
  s_lt : s < 11 / 25
  side_min : ∀ (i : Fin 6) (right : Bool),
    s ≤ rayLen (T (sideIndex i)) (vertex i) (sideDirection i right)
  corner_min : ∀ (j : Fin 3) (k : Fin 2),
    s ≤ rayLen (T (cornerIndex j)) (corner j) (cornerDirection j k)
  core : ∀ j : Fin 6, coreVertex s j ∈ (T 0).carrier
  endpoint : rayLen (T 1) (vertex 0) (sideDirection 0 c.right) = s
  contact : BranchHolds c T s

/-- The strengthenings available for `s ≤ 1/14`: non-overfull side owners and corner owners
containing both external midpoints (outside the cell of the receiver). -/
structure SmallStrengthening (c : ContactCase) (T : Configuration) (r : ℝ) : Prop where
  nonOverfull : ∀ i : Fin 6,
    (c = .Sext → i ≠ 5) → (c = .Sint → i ≠ 1) → (c = .Aown → i ≠ 0) → c ≠ .Across →
    rayLen (T (sideIndex i)) (vertex i) (sideDirection i false) +
      rayLen (T (sideIndex i)) (vertex i) (sideDirection i true) ≤ r
  mids : ∀ (j : Fin 3) (k : Fin 2),
    (c = .Sext → j ≠ 2) → (c = .Sint → j ≠ 0) → (c = .Aown → j ≠ 0) → c ≠ .Across →
    cornerMid j k ∈ (T (cornerIndex j)).carrier

end ConwaySoifer

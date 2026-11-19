/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/ExteriorArea.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Foundation

/-! Cubic exterior-area transport derived from the two endpoint fields. -/

@[expose] public section

namespace LeanDirac

variable {Site : Type} {Edge : Type*}

noncomputable section
open Complex

/-- The exterior product of two vectors in `C3`, written in the basis `e₀ ∧ e₁`, `e₀ ∧ e₂`,
`e₁ ∧ e₂` of the second exterior power. -/
def wedge (u v : C3) : C3
  | 0 => u 0 * v 1 - u 1 * v 0
  | 1 => u 0 * v 2 - u 2 * v 0
  | _ => u 1 * v 2 - u 2 * v 1

/-- The exterior-area energy of a bond: its weight divided by `2 * chi0 ^ 2`, times the squared
norm of the difference of `wedge (state.chi x) (state.psi x)` between the target and source. -/
def exteriorAreaBond (chi0 : ℝ) (state : State Site)
    (edge : Bond Site) : ℝ :=
  edge.weight / (2 * chi0 ^ 2) * density
    (difference
      (wedge (state.chi edge.source) (state.psi edge.source))
      (wedge (state.chi edge.target) (state.psi edge.target)))

theorem exterior_area_bond_nonnegative
    (chi0 : ℝ) (state : State Site) (edge : Bond Site)
    (hchi : 0 < chi0) (hweight : 0 ≤ edge.weight) :
    0 ≤ exteriorAreaBond chi0 state edge := by
  unfold exteriorAreaBond
  exact mul_nonneg (div_nonneg hweight (by positivity))
    (density_nonnegative _)

/-- The standard basis vector of `C3` with entry `1` in position `selected` and `0` elsewhere. -/
def basis (selected : Fin 3) : C3 :=
  fun component => if component = selected then 1 else 0

/-- A rescaled exterior product on `C3` whose three components are those of `wedge u v`
multiplied by `a`, `b` and `c` respectively. -/
def alternatingCandidate (a b c : ℂ) (u v : C3) : C3
  | 0 => a * (u 0 * v 1 - u 1 * v 0)
  | 1 => b * (u 0 * v 2 - u 2 * v 0)
  | _ => c * (u 1 * v 2 - u 2 * v 1)

theorem wedge_alternating (u : C3) : wedge u u = 0 := by
  funext component
  fin_cases component <;> simp [wedge] <;> ring

theorem cubic_unit_area_forces_wedge
    (a b c : ℂ)
    (h01 : alternatingCandidate a b c (basis 0) (basis 1) 0 = 1)
    (h02 : alternatingCandidate a b c (basis 0) (basis 2) 1 = 1)
    (h12 : alternatingCandidate a b c (basis 1) (basis 2) 2 = 1) :
    alternatingCandidate a b c = wedge := by
  have ha : a = 1 := by simpa [alternatingCandidate, basis] using h01
  have hb : b = 1 := by simpa [alternatingCandidate, basis] using h02
  have hc : c = 1 := by simpa [alternatingCandidate, basis] using h12
  subst a; subst b; subst c
  funext u v component
  fin_cases component <;> simp [alternatingCandidate, wedge]

end
end LeanDirac

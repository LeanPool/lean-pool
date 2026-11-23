/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Fin

/-! # Transverse native phases at signed frequency -/

@[expose] public section

namespace LeanDirac.V2

open Complex BigOperators
noncomputable section

/-- The two complex components transverse to the chosen uniform axial vacuum. -/
abbrev UniformCell2 := Fin 2 → ℂ

/-- The sum of squared moduli of the two transverse components. -/
def uniformCell2Density (z : UniformCell2) : ℝ :=
  ∑ component, Complex.normSq (z component)

/-- The position and velocity of the two transverse components of one native mode. -/
abbrev UniformTwoChannelPhase := UniformCell2 × UniformCell2

/-- The pure-frequency native phase with the given signed energy. -/
def uniformPositiveFrequencyPhase
    (energy : ℝ) (position : UniformCell2) : UniformTwoChannelPhase :=
  (position, fun component => -I * (energy : ℂ) * position component)

end
end LeanDirac.V2

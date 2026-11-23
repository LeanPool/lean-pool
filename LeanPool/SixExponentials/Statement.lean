/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.RingTheory.Algebraic.Defs
import LeanPool.SixExponentials.Main

/-!
# The six exponentials theorem: statements

`six_exponentials_theorem` is the statement registered with Palomar as `PALOMAR-2026-11-22-000020`,
unchanged. It is `six_exponentials`, the case `d = 2`, `l = 3` of `exists_transcendental_exp`
(both in `LeanPool.SixExponentials.Main`).
-/

@[expose] public section

namespace SixExponentials

/-- **The six exponentials theorem** (Lang 1966; Ramachandra 1968). If `x₁, x₂` are linearly
independent over `ℚ` and `y₁, y₂, y₃` are linearly independent over `ℚ`, then at least one of
the six numbers `exp (xᵢ yⱼ)` is transcendental. -/
theorem six_exponentials_theorem (x : Fin 2 → ℂ) (y : Fin 3 → ℂ)
    (hx : LinearIndependent ℚ x) (hy : LinearIndependent ℚ y) :
    ∃ i j, Transcendental ℚ (Complex.exp (x i * y j)) :=
  six_exponentials x y hx hy

end SixExponentials

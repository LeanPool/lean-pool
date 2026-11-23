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
import LeanPool.SixExponentials.NumberField
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# The six exponentials theorem: statements

`exists_transcendental_exp` is the theorem of Lang and Ramachandra for every pair `(d, l)` with
`d + l < d l`, derived from the number-field form `SX.six_exponentials_of_numberField` exactly as
`six_exponentials` derives the case `d = 2`, `l = 3`. `six_exponentials_theorem` is the statement
registered with Palomar as `PALOMAR-2026-11-22-000020`, unchanged.
-/

@[expose] public section

namespace SixExponentials

/-- **Lang–Ramachandra.** If `d + l < d l` and the complex families `x` and `y` are each linearly
independent over `ℚ`, then some `exp (x i * y j)` is transcendental over `ℚ`. -/
theorem exists_transcendental_exp {d l : ℕ} (hdl : d + l < d * l) (x : Fin d → ℂ)
    (y : Fin l → ℂ) (hx : LinearIndependent ℚ x) (hy : LinearIndependent ℚ y) :
    ∃ i j, Transcendental ℚ (Complex.exp (x i * y j)) := by
  classical
  by_contra hcon
  simp only [Transcendental, not_exists, not_not] at hcon
  set S : Set ℂ := Set.range (fun q : Fin d × Fin l => Complex.exp (x q.1 * y q.2)) with hS
  have hSfin : S.Finite := Set.finite_range _
  have : Finite S := hSfin.to_subtype
  have hint : ∀ z ∈ S, IsIntegral ℚ z := by
    rintro z ⟨q, rfl⟩
    exact (hcon q.1 q.2).isIntegral
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) :=
    IntermediateField.finiteDimensional_adjoin hint
  obtain ⟨i, j, hij⟩ :=
    SX.six_exponentials_of_numberField hdl x y hx hy (IntermediateField.adjoin ℚ S)
  exact hij (IntermediateField.subset_adjoin ℚ S ⟨(i, j), rfl⟩)

/-- **The six exponentials theorem** (Lang 1966; Ramachandra 1968). If `x₁, x₂` are linearly
independent over `ℚ` and `y₁, y₂, y₃` are linearly independent over `ℚ`, then at least one of
the six numbers `exp (xᵢ yⱼ)` is transcendental. -/
theorem six_exponentials_theorem (x : Fin 2 → ℂ) (y : Fin 3 → ℂ)
    (hx : LinearIndependent ℚ x) (hy : LinearIndependent ℚ y) :
    ∃ i j, Transcendental ℚ (Complex.exp (x i * y j)) :=
  six_exponentials x y hx hy

end SixExponentials

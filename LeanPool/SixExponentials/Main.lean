/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.RingTheory.Algebraic.Defs
import LeanPool.SixExponentials.NumberField
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# The six exponentials theorem

The case `d = 2`, `l = 3` of the number-field form, with transcendence over `ℚ` as conclusion.

From `SixExponentials/Basic/six_exponentials.lean` of `carlok/six-exponentials-lean`;
see `LeanPool.SixExponentials` for provenance.
-/

@[expose] public section

namespace SixExponentials

open Complex ComplexConjugate

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

/-- The six exponentials theorem: the case `d = 2`, `l = 3` of `exists_transcendental_exp`. -/
theorem six_exponentials (x : Fin 2 → ℂ) (y : Fin 3 → ℂ)
    (hx : LinearIndependent ℚ x) (hy : LinearIndependent ℚ y) :
    ∃ i j, Transcendental ℚ (Complex.exp (x i * y j)) :=
  exists_transcendental_exp (by omega) x y hx hy

end SixExponentials

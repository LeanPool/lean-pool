/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import LeanPool.SixExponentials.AuxiliaryFunction
import LeanPool.SixExponentials.CharacterIndependence
import LeanPool.SixExponentials.DescentStep

/-!
# The six exponentials theorem relative to a number field

For `d` complex numbers `x` and `l` complex numbers `y`, each family linearly independent over `ℚ`,
with `d + l < d l`, and every subfield `K` of `ℂ` of finite degree over `ℚ`, some `exp(xᵢ yⱼ)` lies
outside `K`.

From `SixExponentials/Basic/six_exponentials_of_numberField.lean` of `carlok/six-exponentials-lean`;
see `LeanPool.SixExponentials` for provenance.
-/

@[expose] public section

namespace SixExponentials.SX

open Complex

theorem six_exponentials_of_numberField
    {d l : ℕ} (hdl : d + l < d * l)
    (x : Fin d → ℂ) (y : Fin l → ℂ)
    (hx : LinearIndependent ℚ x) (hy : LinearIndependent ℚ y)
    (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] :
    ∃ i j, Complex.exp (x i * y j) ∉ K := by
  classical
  have hl2 : 2 ≤ l := by
    by_contra hcl
    push Not at hcl
    interval_cases l <;> omega
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hc, M₁, haux⟩ := SX.exists_aux_expSum hdl x y hx hy K hcon
  obtain ⟨M₀, hdesc⟩ := SX.descent_step hdl x y hy K hcon c hc
  set M : ℕ := max M₀ M₁ + 1 with hMdef
  obtain ⟨L, hL0, hLc, p, ⟨lam0, hlam0mem, hlam0⟩, hph, hvan⟩ :=
    haux M (by omega)
  have key : ∀ N : ℕ, M ≤ N →
      ∀ m : Fin l → ℕ, (∀ j, m j < N) → SX.expSum x L p (SX.latticeSum y m) = 0 := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => exact hvan
    | succ N hN ih => exact hdesc M (by omega) L hL0 hLc p hph N hN ih
  have hall : ∀ m : Fin l → ℕ, SX.expSum x L p (SX.latticeSum y m) = 0 := by
    intro m
    refine key (max M (Finset.univ.sup m + 1)) (le_max_left _ _) m fun j => ?_
    exact lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ j)))
      (le_max_right _ _)
  exact hlam0 (SX.eq_zero_of_expSum_vanishes hl2 x y hx hy L p hall lam0 hlam0mem)

end SixExponentials.SX

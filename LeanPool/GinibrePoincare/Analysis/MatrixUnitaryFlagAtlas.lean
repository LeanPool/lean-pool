/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixUnitaryFlagAtlas.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

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

module

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurAngularChart
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Algebra.Star.Unitary

/-!
# Matrix unitary flag atlas

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixUnitaryFlagSaturation_countable_cover`.
-/

@[expose] public section

open Matrix NormedSpace Filter Set
open scoped Matrix Matrix.Norms.Operator Topology
namespace GinibrePoincare
noncomputable section

/-- Every unitary flag is covered by a countable family of translated copies of the
actual phase-saturated angular chart. -/
theorem matrixUnitaryFlagSaturation_countable_cover (n : ℕ)
    (V : Set (SchurLowerIndex n → ℂ)) (h0 : 0 ∈ V)
    (hopen : IsOpen {U : Matrix.unitaryGroup (Fin n) ℂ |
      (U : Matrix (Fin n) (Fin n) ℂ) ∈ matrixUnitaryFlagSaturation n V}) :
    ∃ C : ℕ → Matrix.unitaryGroup (Fin n) ℂ,
      ∀ U : Matrix.unitaryGroup (Fin n) ℂ, ∃ k,
        ((C k : Matrix (Fin n) (Fin n) ℂ)ᴴ * (U : Matrix (Fin n) (Fin n) ℂ)) ∈
          matrixUnitaryFlagSaturation n V := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  let H := Matrix.unitaryGroup (Fin n) ℂ
  let S : Set H := {U | (U : Matrix (Fin n) (Fin n) ℂ) ∈ matrixUnitaryFlagSaturation n V}
  let O : H → Set H := fun C => (fun U : H => star C * U) ⁻¹' S
  have hO : ∀ C, IsOpen (O C) := fun C => hopen.preimage (continuous_const.mul continuous_id)
  have hcover : (Set.univ : Set H) ⊆ ⋃ C, O C := by
    intro U hU
    apply Set.mem_iUnion.mpr
    refine ⟨U, ?_⟩
    change ((U : Matrix (Fin n) (Fin n) ℂ)ᴴ * (U : Matrix (Fin n) (Fin n) ℂ)) ∈
      matrixUnitaryFlagSaturation n V
    rw [show (U : Matrix (Fin n) (Fin n) ℂ)ᴴ * (U : Matrix (Fin n) (Fin n) ℂ) = 1 from
      Matrix.mem_unitaryGroup_iff'.mp U.property]
    exact matrixUnitaryFlagSaturation_one V h0
  obtain ⟨C, hC⟩ := isLindelof_univ.indexed_countable_subcover O hO hcover
  refine ⟨C, fun U => ?_⟩
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hC (Set.mem_univ U))
  exact ⟨k, hk⟩

end
end GinibrePoincare

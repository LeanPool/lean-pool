/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixUnitaryFlagSlice.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixUnitaryDiagonalPhase
public import LeanPool.GinibrePoincare.Analysis.MatrixSchurExponentialJacobian

/-!
# Matrix unitary flag slice

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixUnitary_lower_flag_slice`.
-/

@[expose] public section

open Matrix NormedSpace Filter Set
open scoped Matrix Matrix.Norms.Operator Topology
namespace GinibrePoincare
noncomputable section

/-- A genuine neighborhood on which the lower exponential section represents each
unitary flag at most once: two frames differing only by diagonal phases coincide. -/
theorem matrixUnitary_lower_flag_slice (n : ℕ) :
    ∃ V : Set (SchurLowerIndex n → ℂ), V ∈ 𝓝 0 ∧
      ∀ x ∈ V, ∀ y ∈ V,
        (∀ i j, i ≠ j →
          ((matrixSchurExponentialFrame n y)ᴴ * matrixSchurExponentialFrame n x) i j = 0) → x = y :=
              by
  let X := SchurLowerIndex n → ℂ
  let M := Matrix (Fin n) (Fin n) ℂ
  let Q := matrixSchurExponentialFrame n
  let e := matrixUnitaryPhaseLocalChart n
  have he0 : (0 : MatrixSkewCoordinates n) ∈ e.source :=
      matrixUnitaryPhaseLocalChart_zero_mem_source n
  obtain ⟨U, hU, W, hW, hUW⟩ := mem_nhds_prod_iff.mp (e.open_source.mem_nhds he0)
  let D : X × X → M := fun p => (Q p.2)ᴴ * Q p.1
  have hQc : Continuous Q := (matrixSchurExponentialFrame_differentiable n).continuous
  have hDc : Continuous D :=
    (((schurConjTransposeCLM n).continuous.comp (hQc.comp continuous_snd)).mul
      (hQc.comp continuous_fst))
  have hD0 : D (0, 0) = 1 := by
    simp [D, Q, matrixSchurExponentialFrame, ← schurSkewCLM_apply, exp_zero]
  have hsmall := matrixUnitary_diagonal_phase_small n W hW
  have hpair : ∀ᶠ p in 𝓝 ((0, 0) : X × X),
      D p ∈ Matrix.unitaryGroup (Fin n) ℂ →
      (∀ i j, i ≠ j → D p i j = 0) →
      ∃ d ∈ W, D p = exp (matrixSkewDiagonalCLM n d) := by
    have hc : ContinuousAt D ((0, 0) : X × X) := hDc.continuousAt
    change Tendsto D (𝓝 ((0, 0) : X × X)) (𝓝 (D (0, 0))) at hc
    rw [hD0] at hc
    exact hc hsmall
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hpair
  refine ⟨U ∩ A ∩ B, inter_mem (inter_mem hU hA) hB, ?_⟩
  intro x hx y hy hdiag
  have hpx : (x, (0 : Fin n → ℝ)) ∈ e.source := hUW ⟨hx.1.1, mem_of_mem_nhds hW⟩
  have hDunit : D (x, y) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    have hyy : (Q y)ᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
      apply Matrix.mem_unitaryGroup_iff'.mpr
      change ((Q y)ᴴ)ᴴ * (Q y)ᴴ = 1
      rw [Matrix.conjTranspose_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff.mp (matrixSchurExponentialFrame_unitary n y)
    exact (Matrix.unitaryGroup (Fin n) ℂ).mul_mem hyy (matrixSchurExponentialFrame_unitary n x)
  obtain ⟨d, hdW, hd⟩ := hAB ⟨hx.1.2, hy.2⟩ hDunit hdiag
  have hpy : (y, d) ∈ e.source := hUW ⟨hy.1.1, hdW⟩
  have hYY : Q y * (Q y)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp (matrixSchurExponentialFrame_unitary
      n y)
  have hequal : matrixUnitaryPhaseParameter n (x, 0) = matrixUnitaryPhaseParameter n (y, d) := by
    change Q x * exp (matrixSkewDiagonalCLM n 0) = Q y * exp (matrixSkewDiagonalCLM n d)
    rw [map_zero, exp_zero, Matrix.mul_one, ← hd]
    change Q x = Q y * ((Q y)ᴴ * Q x)
    rw [← Matrix.mul_assoc, hYY, Matrix.one_mul]
  have hcoords : e (x, 0) = e (y, d) := by
    change matrixUnitaryPhaseCoordinates n (x, 0) = matrixUnitaryPhaseCoordinates n (y, d)
    rw [matrixUnitaryPhaseCoordinates, matrixUnitaryPhaseCoordinates, hequal]
  exact congrArg Prod.fst (e.injOn hpx hpy hcoords)

end
end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixUnitaryFlagSaturation.lean.
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
public import LeanPool.GinibrePoincare.Analysis.MatrixSchurProductIntegration

/-!
# Matrix unitary flag saturation

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixDiagonalPhase_diagonal`, `matrixUnitaryFlagSaturation_isOpen`.
-/

@[expose] public section

open Matrix NormedSpace Filter Set
open scoped Matrix Matrix.Norms.Operator Topology
namespace GinibrePoincare
noncomputable section

/-- The matrices `Q(x) D` with `x ∈ V`, `Q(x)` the exponential Schur frame and `D` a diagonal
unitary matrix. -/
def matrixUnitaryFlagSaturation (n : ℕ) (V : Set (SchurLowerIndex n → ℂ)) :
    Set (Matrix (Fin n) (Fin n) ℂ) :=
  {U | ∃ x ∈ V, ∃ D : Matrix (Fin n) (Fin n) ℂ,
    D ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ (∀ i j, i ≠ j → D i j = 0) ∧
      U = matrixSchurExponentialFrame n x * D}

theorem matrixDiagonalPhase_unitary (n : ℕ) (d : Fin n → ℝ) :
    exp (matrixSkewDiagonalCLM n d) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hh := matrixUnitaryPhaseParameter_unitary n ((0 : SchurLowerIndex n → ℂ), d)
  simpa [matrixUnitaryPhaseParameter, ← schurSkewCLM_apply, exp_zero] using hh

theorem matrixDiagonalPhase_diagonal (n : ℕ) (d : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j) :
    exp (matrixSkewDiagonalCLM n d) i j = 0 := by
  rw [matrixSkewDiagonalCLM_apply, Matrix.exp_diagonal]
  simp [hij]

/-- The phase-saturated angular section is open within the actual unitary group. -/
theorem matrixUnitaryFlagSaturation_isOpen (n : ℕ) (V : Set (SchurLowerIndex n → ℂ))
    (hV : IsOpen V)
    (hsource : ∀ x ∈ V, (x, (0 : Fin n → ℝ)) ∈ (matrixUnitaryPhaseLocalChart n).source)
    (hden : ∀ x ∈ V, IsUnit (matrixSchurExponentialFrame n x + 1)) :
    IsOpen {U : Matrix.unitaryGroup (Fin n) ℂ | (U : Matrix (Fin n) (Fin n) ℂ) ∈
        matrixUnitaryFlagSaturation n V} := by
  apply isOpen_iff_mem_nhds.mpr
  intro U hU
  obtain ⟨x, hx, D, hDunit, hDdiag, hrep⟩ := hU
  let M := Matrix (Fin n) (Fin n) ℂ
  have hDD : D * Dᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hDunit
  have hDD' : Dᴴ * D = 1 := Matrix.mem_unitaryGroup_iff'.mp hDunit
  have hDstar : Dᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    change (Dᴴ)ᴴ * Dᴴ = 1
    rw [Matrix.conjTranspose_conjTranspose]
    exact hDD
  have hpbase : matrixUnitaryPhaseParameter n (x, (0 : Fin n → ℝ)) =
      matrixSchurExponentialFrame n x := by
    simp [matrixUnitaryPhaseParameter, matrixSchurExponentialFrame, exp_zero]
  have hN : V ×ˢ (Set.univ : Set (Fin n → ℝ)) ∈ 𝓝 (x, (0 : Fin n → ℝ)) :=
    prod_mem_nhds (hV.mem_nhds hx) (Filter.univ_mem)
  have hcent := matrixUnitary_centered_phase_factorization n (x, 0)
    (hsource x hx) (hpbase.symm ▸ hden x hx) (V ×ˢ Set.univ) hN
  rw [hpbase] at hcent
  have hmul : ContinuousAt (fun Z : M => Z * Dᴴ) (U : M) := by fun_prop
  have hbase : (U : M) * Dᴴ = matrixSchurExponentialFrame n x := by
    rw [hrep, Matrix.mul_assoc, hDD, Matrix.mul_one]
  change Tendsto (fun Z : M => Z * Dᴴ) (𝓝 (U : M)) (𝓝 ((U : M) * Dᴴ)) at hmul
  rw [hbase] at hmul
  have hpre := hmul hcent
  have hevent : ∀ᶠ Z : M in 𝓝 (U : M),
      Z ∈ Matrix.unitaryGroup (Fin n) ℂ → Z ∈ matrixUnitaryFlagSaturation n V := by
    filter_upwards [hpre] with Z hZ
    intro hZunit
    obtain ⟨p, hp, he⟩ := hZ ((Matrix.unitaryGroup (Fin n) ℂ).mul_mem hZunit hDstar)
    refine ⟨p.1, hp.1, exp (matrixSkewDiagonalCLM n p.2) * D,
      (Matrix.unitaryGroup (Fin n) ℂ).mul_mem (matrixDiagonalPhase_unitary n p.2) hDunit, ?_, ?_⟩
    · intro i j hij
      rw [matrixSkewDiagonalCLM_apply, Matrix.exp_diagonal, Matrix.diagonal_mul, hDdiag i j hij,
          mul_zero]
    · calc
        Z = (Z * Dᴴ) * D := by rw [Matrix.mul_assoc, hDD', Matrix.mul_one]
        _ = matrixUnitaryPhaseParameter n p * D := by rw [he]
        _ = _ := by rw [matrixUnitaryPhaseParameter, Matrix.mul_assoc]; rfl
  have hcoe : ContinuousAt (fun Z : Matrix.unitaryGroup (Fin n) ℂ => (Z : M)) U :=
    continuous_subtype_val.continuousAt
  filter_upwards [hcoe hevent] with Z hZ
  exact hZ Z.property

end
end GinibrePoincare

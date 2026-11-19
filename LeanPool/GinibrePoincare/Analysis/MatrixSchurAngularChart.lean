/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurAngularChart.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixUnitaryFlagSaturation

/-!
# Matrix Schur angular chart

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixSchurAngularChart_exists`, `matrixUnitaryFlagSaturation_one`.
-/

@[expose] public section

open Matrix NormedSpace Filter Set
open scoped Matrix Matrix.Norms.Operator Topology
namespace GinibrePoincare
noncomputable section

/-- An angular Schur chart is simultaneously injective, phase-saturated open, and
contained in the genuine phase-coordinate source and Cayley domain. -/
theorem matrixSchurAngularChart_exists (n : ℕ) :
    ∃ V : Set (SchurLowerIndex n → ℂ), IsOpen V ∧ 0 ∈ V ∧
      InjOn (matrixSchurFrameChart (matrixSchurExponentialFrame n) (0 : Matrix (Fin n) (Fin n) ℂ))
        (V ×ˢ matrixSchurSortedUpperDomain n) ∧
      (∀ x ∈ V, (x, (0 : Fin n → ℝ)) ∈ (matrixUnitaryPhaseLocalChart n).source) ∧
      (∀ x ∈ V, IsUnit (matrixSchurExponentialFrame n x + 1)) ∧
      IsOpen {U : Matrix.unitaryGroup (Fin n) ℂ |
        (U : Matrix (Fin n) (Fin n) ℂ) ∈ matrixUnitaryFlagSaturation n V} := by
  let X := SchurLowerIndex n → ℂ
  let M := Matrix (Fin n) (Fin n) ℂ
  obtain ⟨V0, hV0, hzero, hinj⟩ := matrixSchurSortedDomain_exists_injective n
  let S : Set X := {x | (x, (0 : Fin n → ℝ)) ∈ (matrixUnitaryPhaseLocalChart n).source}
  have hS : IsOpen S := (matrixUnitaryPhaseLocalChart n).open_source.preimage
    (continuous_id.prodMk continuous_const)
  have hS0 : (0 : X) ∈ S := matrixUnitaryPhaseLocalChart_zero_mem_source n
  let D : Set X := {x | (matrixSchurExponentialFrame n x + 1).det ≠ 0}
  have hcont : Continuous (fun x : X => (matrixSchurExponentialFrame n x + 1).det) := by
    have hQ := (matrixSchurExponentialFrame_differentiable n).continuous
    fun_prop
  have hD : IsOpen D := isOpen_ne_fun hcont continuous_const
  have hD0 : (0 : X) ∈ D := by
    change (matrixSchurExponentialFrame n 0 + 1).det ≠ 0
    have hQ0 : matrixSchurExponentialFrame n 0 = (1 : M) := by
      simp [matrixSchurExponentialFrame, ← schurSkewCLM_apply, exp_zero]
    rw [hQ0, ← two_smul ℂ (1 : M), Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (by norm_num)
  let V := V0 ∩ S ∩ D
  have hV : IsOpen V := (hV0.inter hS).inter hD
  have hsource : ∀ x ∈ V, (x, (0 : Fin n → ℝ)) ∈ (matrixUnitaryPhaseLocalChart n).source :=
    fun x hx => hx.1.2
  have hden : ∀ x ∈ V, IsUnit (matrixSchurExponentialFrame n x + 1) := fun x hx =>
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hx.2)
  refine ⟨V, hV, ⟨⟨hzero, hS0⟩, hD0⟩, hinj.mono ?_, hsource, hden,
    matrixUnitaryFlagSaturation_isOpen n V hV hsource hden⟩
  intro p hp
  exact ⟨hp.1.1.1, hp.2⟩

theorem matrixUnitaryFlagSaturation_one {n : ℕ} (V : Set (SchurLowerIndex n → ℂ))
    (h0 : 0 ∈ V) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ matrixUnitaryFlagSaturation n V := by
  refine ⟨0, h0, 1, (Matrix.unitaryGroup (Fin n) ℂ).one_mem, ?_, ?_⟩
  · intro i j hij
    simp [hij]
  · simp [matrixSchurExponentialFrame, ← schurSkewCLM_apply, exp_zero]

end
end GinibrePoincare

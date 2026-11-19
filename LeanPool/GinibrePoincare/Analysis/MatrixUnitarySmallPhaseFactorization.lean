/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixUnitarySmallPhaseFactorization.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixUnitaryPhaseChart
public import LeanPool.GinibrePoincare.Analysis.MatrixUnitaryLowerChart

/-!
# Matrix unitary small phase factorization

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixUnitary_local_phase_factorization_small`.
-/

@[expose] public section

open Matrix NormedSpace Filter
open scoped Matrix Matrix.Norms.Operator Topology
namespace GinibrePoincare
noncomputable section

theorem matrixUnitary_local_phase_factorization_small (n : ℕ)
    (N : Set (MatrixSkewCoordinates n)) (hN : N ∈ 𝓝 0) :
    ∀ᶠ U : Matrix (Fin n) (Fin n) ℂ in 𝓝 1,
      U ∈ Matrix.unitaryGroup (Fin n) ℂ →
        ∃ p : MatrixSkewCoordinates n, p ∈ N ∧ matrixUnitaryPhaseParameter n p = U := by
  let M := Matrix (Fin n) (Fin n) ℂ
  let C := MatrixSkewCoordinates n
  let e := matrixUnitaryPhaseLocalChart n
  let R : M →L[ℝ] C := (matrixSkewReadCoordinates n).toContinuousLinearMap
  let w : M → C := fun U => R (matrixInverseCayley U)
  have hw0 : w 1 = 0 := by
    simp [w, R, matrixInverseCayley]
  have hw : ContinuousAt w 1 := R.continuous.continuousAt.comp
    (matrixInverseCayley_hasStrictFDerivAt_one (n := n)).continuousAt
  have he0 : e 0 = 0 := matrixUnitaryPhaseCoordinates_zero n
  have hsource : (0 : C) ∈ e.source := matrixUnitaryPhaseLocalChart_zero_mem_source n
  have htarget : (0 : C) ∈ e.target := he0 ▸ e.map_source hsource
  have hsym0 : e.symm 0 = 0 := by
    simpa only [he0] using e.left_inv hsource
  let p : M → C := fun U => e.symm (w U)
  have hp0 : p 1 = 0 := by simp [p, hw0, hsym0]
  have hsym : ContinuousAt e.symm (w 1) := by rw [hw0]; exact e.continuousAt_symm htarget
  have hp : ContinuousAt p 1 := hsym.comp hw
  have hparam : ContinuousAt (matrixUnitaryPhaseParameter n) (p 1) := by
    rw [hp0]
    exact (matrixUnitaryPhaseParameter_hasStrictFDerivAt n).continuousAt
  have hdP : ContinuousAt (fun U : M => (matrixUnitaryPhaseParameter n (p U) + 1).det) 1 := by
    have hh := hparam.comp hp
    fun_prop
  have hnP : (matrixUnitaryPhaseParameter n (p 1) + 1).det ≠ 0 := by
    rw [hp0, matrixUnitaryPhaseParameter_zero]
    rw [← two_smul ℂ (1 : M), Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (by norm_num)
  have hdU : ContinuousAt (fun U : M => (U + 1).det) 1 := by fun_prop
  have hnU : ((1 : M) + 1).det ≠ 0 := by
    rw [← two_smul ℂ (1 : M), Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (by norm_num)
  have hevent : ∀ᶠ U : M in 𝓝 1, w U ∈ e.target :=
    hw (by rw [hw0]; exact e.open_target.mem_nhds htarget)
  have hpN : ∀ᶠ U : M in 𝓝 1, p U ∈ N := hp (by rw [hp0]; exact hN)
  filter_upwards [hevent, hdP.eventually_ne hnP, hdU.eventually_ne hnU, hpN] with U htargetU hP
      hdenU hmem
  intro hunit
  refine ⟨p U, hmem, matrixUnitaryPhaseParameter_eq_of_coordinates n U hunit
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdenU)) (p U)
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hP)) ?_⟩
  exact e.right_inv htargetU

end
end GinibrePoincare

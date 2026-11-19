/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixUnitaryPhaseChart.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixCayleyChart
public import LeanPool.GinibrePoincare.Analysis.MatrixSkewCoordinates
public import Mathlib.Topology.Instances.Matrix

/-!
# Matrix unitary phase chart

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixUnitary_local_phase_factorization`.
-/

@[expose] public section

open Matrix NormedSpace Filter
open scoped Topology
open scoped Matrix Matrix.Norms.Operator
namespace GinibrePoincare
noncomputable section

/-- The unitary matrix `exp (schurSkewCombination x) * exp (diagonal (i t))` for skew
coordinates `p = (x, t)`. -/
def matrixUnitaryPhaseParameter (n : ℕ) (p : MatrixSkewCoordinates n) :
    Matrix (Fin n) (Fin n) ℂ :=
  exp (schurSkewCombination p.1) * exp (matrixSkewDiagonalCLM n p.2)

@[simp] theorem matrixUnitaryPhaseParameter_zero (n : ℕ) :
    matrixUnitaryPhaseParameter n 0 = 1 := by
  simp [matrixUnitaryPhaseParameter, ← schurSkewCLM_apply, exp_zero]

theorem matrixUnitaryPhaseParameter_unitary (n : ℕ) (p : MatrixSkewCoordinates n) :
    matrixUnitaryPhaseParameter n p ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hs : schurSkewCombination p.1 ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℂ) :=
    skewAdjoint.mem_iff.mpr (schurSkewCombination_conjTranspose p.1)
  have hd : (matrixSkewDiagonalCLM n p.2)ᴴ = -matrixSkewDiagonalCLM n p.2 := by
    have hh := matrixSkewCoordinateMap_skew n ((0 : SchurLowerIndex n → ℂ), p.2)
    simpa [matrixSkewCoordinateMap, ← schurSkewCLM_apply] using hh
  exact (Matrix.unitaryGroup (Fin n) ℂ).mul_mem
    (@exp_mem_unitary_of_mem_skewAdjoint (Matrix (Fin n) (Fin n) ℂ) _ _ _ _
      ⟨Continuous.matrix_conjTranspose continuous_id⟩ _ hs)
    (@exp_mem_unitary_of_mem_skewAdjoint (Matrix (Fin n) (Fin n) ℂ) _ _ _ _
      ⟨Continuous.matrix_conjTranspose continuous_id⟩ _ (skewAdjoint.mem_iff.mpr hd))

theorem matrixUnitaryPhaseParameter_hasStrictFDerivAt (n : ℕ) :
    HasStrictFDerivAt (matrixUnitaryPhaseParameter n) (matrixSkewCoordinateMap n) 0 := by
  let C := MatrixSkewCoordinates n
  let M := Matrix (Fin n) (Fin n) ℂ
  let S : C →L[ℝ] M := (schurSkewCLM n).comp (ContinuousLinearMap.fst ℝ _ _)
  let D : C →L[ℝ] M := (matrixSkewDiagonalCLM n).comp (ContinuousLinearMap.snd ℝ _ _)
  have hs : S 0 = 0 := map_zero S
  have hd : D 0 = 0 := map_zero D
  have hexp : HasStrictFDerivAt (exp : M → M) (1 : M →L[ℝ] M) 0 := hasStrictFDerivAt_exp_zero
  have hsexp := (hs ▸ hexp).comp (0 : C) S.hasStrictFDerivAt
  have hdexp := (hd ▸ hexp).comp (0 : C) D.hasStrictFDerivAt
  have hprod := hsexp.mul' hdexp
  have hf : (matrixUnitaryPhaseParameter n : C → M) = (fun p => exp (S p)) * (fun p => exp (D p)) :=
      by
    funext p
    change exp (schurSkewCombination p.1) * exp (matrixSkewDiagonalCLM n p.2) =
      exp (schurSkewCLM n p.1) * exp (matrixSkewDiagonalCLM n p.2)
    rw [schurSkewCLM_apply]
  rw [hf]
  have he : exp (S 0) • (1 : M →L[ℝ] M).comp D +
      MulOpposite.op (exp (D 0)) • (1 : M →L[ℝ] M).comp S = matrixSkewCoordinateMap n := by
    rw [hs, hd, exp_zero]
    apply ContinuousLinearMap.ext
    intro p
    simp [matrixSkewCoordinateMap, S, D, ContinuousLinearMap.comp_apply, add_comm]
  rw [← he]
  exact hprod

/-- The skew coordinates of the inverse Cayley transform of `matrixUnitaryPhaseParameter n p`. -/
def matrixUnitaryPhaseCoordinates (n : ℕ) (p : MatrixSkewCoordinates n) : MatrixSkewCoordinates n :=
  matrixSkewReadCoordinates n (matrixInverseCayley (matrixUnitaryPhaseParameter n p))

@[simp] theorem matrixUnitaryPhaseCoordinates_zero (n : ℕ) :
    matrixUnitaryPhaseCoordinates n 0 = 0 := by
  simp [matrixUnitaryPhaseCoordinates, matrixInverseCayley, matrixSkewReadCoordinates]
  constructor <;> rfl

theorem matrixUnitaryPhaseCoordinates_hasStrictFDerivAt (n : ℕ) :
    HasStrictFDerivAt (matrixUnitaryPhaseCoordinates n)
      ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (MatrixSkewCoordinates n)) 0 := by
  let M := Matrix (Fin n) (Fin n) ℂ
  let C := MatrixSkewCoordinates n
  let R : M →L[ℝ] C := (matrixSkewReadCoordinates n).toContinuousLinearMap
  have hI := matrixInverseCayley_hasStrictFDerivAt_one (n := n)
  rw [← matrixUnitaryPhaseParameter_zero n] at hI
  have hIP := hI.comp (0 : C) (matrixUnitaryPhaseParameter_hasStrictFDerivAt n)
  have hR := R.hasStrictFDerivAt.comp (0 : C) hIP
  have he : R.comp (((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ M).comp
      (matrixSkewCoordinateMap n)) = (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ C := by
    apply ContinuousLinearMap.ext
    intro p
    change matrixSkewReadCoordinates n ((1 / 2 : ℝ) • matrixSkewCoordinateMap n p) =
      (1 / 2 : ℝ) • p
    rw [map_smul, matrixSkewReadCoordinates_map]
  rw [← he]
  exact hR

/-- The local homeomorphism given by `matrixUnitaryPhaseCoordinates n` via the inverse function
theorem, with strict derivative `(1 / 2) • id`. -/
def matrixUnitaryPhaseLocalChart (n : ℕ) :
    OpenPartialHomeomorph (MatrixSkewCoordinates n) (MatrixSkewCoordinates n) :=
  let E : MatrixSkewCoordinates n ≃L[ℝ] MatrixSkewCoordinates n :=
    (LinearEquiv.smulOfNeZero ℝ (MatrixSkewCoordinates n) (1 / 2 : ℝ) (by
        norm_num)).toContinuousLinearEquiv
  HasStrictFDerivAt.toOpenPartialHomeomorph (f' := E) (matrixUnitaryPhaseCoordinates n)
    (matrixUnitaryPhaseCoordinates_hasStrictFDerivAt n)

theorem matrixUnitaryPhaseLocalChart_zero_mem_source (n : ℕ) :
    0 ∈ (matrixUnitaryPhaseLocalChart n).source :=
  HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source
    (f' := (LinearEquiv.smulOfNeZero ℝ (MatrixSkewCoordinates n) (1 / 2 : ℝ)
      (by norm_num)).toContinuousLinearEquiv) (matrixUnitaryPhaseCoordinates_hasStrictFDerivAt n)

theorem matrixUnitaryPhaseParameter_eq_of_coordinates (n : ℕ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hu : IsUnit (U + 1)) (p : MatrixSkewCoordinates n)
    (hp : IsUnit (matrixUnitaryPhaseParameter n p + 1))
    (he : matrixUnitaryPhaseCoordinates n p = matrixSkewReadCoordinates n (matrixInverseCayley U)) :
    matrixUnitaryPhaseParameter n p = U := by
  have hsP := matrixInverseCayley_skew (matrixUnitaryPhaseParameter n p)
    (matrixUnitaryPhaseParameter_unitary n p) hp
  have hsU := matrixInverseCayley_skew U hU hu
  have hh := congrArg (matrixSkewCoordinateMap n) he
  rw [matrixUnitaryPhaseCoordinates, matrixSkewCoordinateMap_reconstruct n _ hsP,
    matrixSkewCoordinateMap_reconstruct n _ hsU] at hh
  have hh' := congrArg matrixCayley hh
  rw [matrixCayley_inverseCayley _ hp, matrixCayley_inverseCayley U hu] at hh'
  exact hh'

/-- Every unitary matrix sufficiently near the identity admits the actual local
factorization into a lower skew exponential and diagonal unitary phases. -/
theorem matrixUnitary_local_phase_factorization (n : ℕ) :
    ∀ᶠ U : Matrix (Fin n) (Fin n) ℂ in 𝓝 1,
      U ∈ Matrix.unitaryGroup (Fin n) ℂ →
        ∃ p : MatrixSkewCoordinates n, matrixUnitaryPhaseParameter n p = U := by
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
  filter_upwards [hevent, hdP.eventually_ne hnP, hdU.eventually_ne hnU] with U htargetU hP hdenU
  intro hunit
  refine ⟨p U, matrixUnitaryPhaseParameter_eq_of_coordinates n U hunit
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdenU)) (p U)
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hP)) ?_⟩
  exact e.right_inv htargetU

end
end GinibrePoincare

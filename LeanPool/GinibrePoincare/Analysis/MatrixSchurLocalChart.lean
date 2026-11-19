/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurLocalChart.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurLinearCoordinates
public import LeanPool.GinibrePoincare.Analysis.MatrixSchurChartDerivative
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Matrix Schur local chart

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `schurLocalChart_apply`, `schurLocalChart_zero_mem_source`,
`schurLocalChart_self_mem_target`.
-/

@[expose] public section

open Matrix NormedSpace
open scoped Matrix Matrix.Norms.Operator
namespace GinibrePoincare
noncomputable section

/-- The Schur chart `(x, y) ↦ exp S (T + Y) exp (-S)` around `T`, with `S` the skew-Hermitian
matrix built from `x` and `Y` the upper-triangular matrix built from `y`. -/
def schurCoordinateChart {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (p : SchurCoordinates n) : Matrix (Fin n) (Fin n) ℂ :=
  schurAmbientChart T (schurCoordinateEmbedding n p)

@[simp] theorem schurCoordinateChart_zero {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) :
    schurCoordinateChart T 0 = T := by
  simp [schurCoordinateChart, schurAmbientChart, exp_zero]

theorem schurCoordinateChart_hasStrictFDerivAt {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) :
    HasStrictFDerivAt (schurCoordinateChart T) (schurCoordinateTangentCLM T) 0 := by
  let M := Matrix (Fin n) (Fin n) ℂ
  have hfst : HasStrictFDerivAt (Prod.fst : M × M → M)
      (ContinuousLinearMap.fst ℝ M M) (0, 0) := hasStrictFDerivAt_fst
  have hsnd : HasStrictFDerivAt (Prod.snd : M × M → M)
      (ContinuousLinearMap.snd ℝ M M) (0, 0) := hasStrictFDerivAt_snd
  have hexp : HasStrictFDerivAt (exp : M → M) (1 : M →L[ℝ] M) 0 :=
    hasStrictFDerivAt_exp_zero
  have hL := hexp.comp ((0, 0) : M × M) hfst
  have hx : (-Prod.fst) ((0, 0) : M × M) = 0 := by simp
  rw [← hx] at hexp
  have hR := hexp.comp ((0, 0) : M × M) hfst.neg
  have hM := (hasStrictFDerivAt_const T ((0, 0) : M × M)).add hsnd
  have hd := (hL.mul' hM).mul' hR
  have hz : schurCoordinateEmbedding n 0 = ((0, 0) : M × M) := by
    rw [map_zero]
    rfl
  have ha : DifferentiableAt ℝ (schurAmbientChart T) ((0, 0) : M × M) :=
    hd.hasFDerivAt.differentiableAt
  rw [← hz] at hd
  have hc := hd.comp (0 : SchurCoordinates n) (schurCoordinateEmbedding n).hasStrictFDerivAt
  have hs : ∃ D : SchurCoordinates n →L[ℝ] Matrix (Fin n) (Fin n) ℂ,
      HasStrictFDerivAt (schurCoordinateChart T) D 0 := ⟨_, hc⟩
  obtain ⟨D, hD⟩ := hs
  have he : D = schurCoordinateTangentCLM T := by
    have haa : HasFDerivAt (schurAmbientChart T)
        (fderiv ℝ (schurAmbientChart T) (0, 0)) (schurCoordinateEmbedding n 0) := by
      rw [hz]
      exact ha.hasFDerivAt
    have hdf : HasFDerivAt (schurCoordinateChart T)
        ((fderiv ℝ (schurAmbientChart T) (0, 0)).comp (schurCoordinateEmbedding n))
        (0 : SchurCoordinates n) :=
      haa.comp _ (schurCoordinateEmbedding n).hasFDerivAt
    rw [hD.hasFDerivAt.unique hdf]
    apply ContinuousLinearMap.ext
    intro p
    rw [ContinuousLinearMap.comp_apply, schurCoordinateEmbedding_apply,
      schurAmbientChart_fderiv, schurCoordinateTangentCLM_apply]
    rfl
  exact he ▸ hD

/-- For upper-triangular `T` with distinct diagonal entries, the local homeomorphism given by
`schurCoordinateChart T` via the inverse function theorem. -/
def schurLocalChart {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) (hd : Function.Injective (fun i => T i i)) :
    OpenPartialHomeomorph (SchurCoordinates n) (Matrix (Fin n) (Fin n) ℂ) :=
  HasStrictFDerivAt.toOpenPartialHomeomorph (f' := schurCoordinateTangentEquiv T hT hd)
    (schurCoordinateChart T) (schurCoordinateChart_hasStrictFDerivAt T)

@[simp] theorem schurLocalChart_apply {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) (hd : Function.Injective (fun i => T i i))
    (p : SchurCoordinates n) : schurLocalChart T hT hd p = schurCoordinateChart T p := rfl

theorem schurLocalChart_zero_mem_source {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) (hd : Function.Injective (fun i => T i i)) :
    0 ∈ (schurLocalChart T hT hd).source :=
  HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source
    (f' := schurCoordinateTangentEquiv T hT hd) (schurCoordinateChart_hasStrictFDerivAt T)

theorem schurLocalChart_self_mem_target {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) (hd : Function.Injective (fun i => T i i)) :
    T ∈ (schurLocalChart T hT hd).target := by
  simpa only [schurLocalChart, schurCoordinateChart_zero] using
      HasStrictFDerivAt.image_mem_toOpenPartialHomeomorph_target
    (f' := schurCoordinateTangentEquiv T hT hd) (schurCoordinateChart_hasStrictFDerivAt T)

end
end GinibrePoincare

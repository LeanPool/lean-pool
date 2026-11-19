/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurLinearCoordinates.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurCoordinates
public import Mathlib.Analysis.Matrix.Normed

/-!
# Matrix Schur linear coordinates

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `schurCoordinateEmbedding_apply`.
-/

@[expose] public section

open Matrix
open scoped Matrix Matrix.Norms.Operator BigOperators
namespace GinibrePoincare
noncomputable section

/-- `schurLowerCombination` as a continuous `ℂ`-linear map. -/
def schurLowerCLM (n : ℕ) : (SchurLowerIndex n → ℂ) →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  ∑ p, (ContinuousLinearMap.proj p).smulRight (Matrix.single (schurLowerRow p) (schurLowerCol p) 1)

/-- `schurUpperCombination` as a continuous `ℂ`-linear map. -/
def schurUpperCLM (n : ℕ) : (SchurUpperIndex n → ℂ) →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  ∑ p, (ContinuousLinearMap.proj p).smulRight (Matrix.single p.val.1 p.val.2 1)

theorem schurLowerCLM_apply (n : ℕ) (x : SchurLowerIndex n → ℂ) :
    schurLowerCLM n x = schurLowerCombination x := by
  simp [schurLowerCLM, schurLowerCombination]

theorem schurUpperCLM_apply (n : ℕ) (x : SchurUpperIndex n → ℂ) :
    schurUpperCLM n x = schurUpperCombination x := by
  simp [schurUpperCLM, schurUpperCombination]

/-- The conjugate transpose `A ↦ Aᴴ` as a continuous real-linear map. -/
def schurConjTransposeCLM (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.conjTranspose
      map_add' := Matrix.conjTranspose_add
      map_smul' := fun r A => by simp [Matrix.conjTranspose_smul] }

/-- `schurSkewCombination` as a continuous real-linear map. -/
def schurSkewCLM (n : ℕ) : (SchurLowerIndex n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  (schurLowerCLM n).restrictScalars ℝ -
    (schurConjTransposeCLM n).comp ((schurLowerCLM n).restrictScalars ℝ)

theorem schurSkewCLM_apply (n : ℕ) (x : SchurLowerIndex n → ℂ) :
    schurSkewCLM n x = schurSkewCombination x := by
  simp [schurSkewCLM, schurConjTransposeCLM, schurLowerCLM_apply, schurSkewCombination]

/-- The map `(x, y) ↦ (schurSkewCombination x, schurUpperCombination y)` into pairs of
matrices. -/
def schurCoordinateEmbedding (n : ℕ) : SchurCoordinates n →L[ℝ]
    (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) :=
  ((schurSkewCLM n).comp (ContinuousLinearMap.fst ℝ _ _)).prod
    (((schurUpperCLM n).restrictScalars ℝ).comp (ContinuousLinearMap.snd ℝ _ _))

theorem schurCoordinateEmbedding_apply (n : ℕ) (p : SchurCoordinates n) :
    schurCoordinateEmbedding n p = (schurSkewCombination p.1, schurUpperCombination p.2) := by
  simp [schurCoordinateEmbedding, schurSkewCLM_apply, schurUpperCLM_apply]

/-- `schurCoordinateTangent T` as a continuous real-linear map. -/
def schurCoordinateTangentCLM {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) :
    SchurCoordinates n →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  let S : SchurCoordinates n →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    (schurSkewCLM n).comp (ContinuousLinearMap.fst ℝ _ _)
  ((ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℂ)).flip T).comp S -
    ((ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℂ)) T).comp S +
      ((schurUpperCLM n).restrictScalars ℝ).comp (ContinuousLinearMap.snd ℝ _ _)

theorem schurCoordinateTangentCLM_apply {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (p : SchurCoordinates n) : schurCoordinateTangentCLM T p = schurCoordinateTangent T p := by
  unfold schurCoordinateTangent
  change schurSkewCLM n p.1 * T - T * schurSkewCLM n p.1 + schurUpperCLM n p.2 = _
  rw [schurSkewCLM_apply, schurUpperCLM_apply]

/-- For upper-triangular `T` with distinct diagonal entries, `schurCoordinateTangentCLM T` as a
continuous linear equivalence. -/
def schurCoordinateTangentEquiv {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) (hd : Function.Injective (fun i => T i i)) :
    SchurCoordinates n ≃L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
by
  have he : (schurCoordinateTangentCLM T : SchurCoordinates n → Matrix (Fin n) (Fin n) ℂ) =
      schurCoordinateTangent T := funext (schurCoordinateTangentCLM_apply T)
  have hb : Function.Bijective (schurCoordinateTangentCLM T) :=
    he.symm ▸ schurCoordinateTangent_bijective T hT hd
  exact ContinuousLinearEquiv.ofBijective (schurCoordinateTangentCLM T)
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)

end
end GinibrePoincare

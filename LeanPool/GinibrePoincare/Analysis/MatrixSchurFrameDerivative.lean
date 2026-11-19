/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurFrameDerivative.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurMovingJacobian
public import LeanPool.GinibrePoincare.Analysis.MatrixUnitaryDerivative

/-!
# Matrix Schur frame derivative

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixSchurFrameChart_normalized_fderiv`.
-/

@[expose] public section

open Matrix Filter
open scoped Matrix Matrix.Norms.Operator Topology
namespace GinibrePoincare
noncomputable section

/-- The map `v ↦ Qᴴ * D v`, pulling a frame derivative `D` back to the identity by `Qᴴ`. -/
def matrixUnitaryConnection {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ)
    (D : (SchurLowerIndex n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :
    (SchurLowerIndex n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  (((ContinuousLinearMap.mul ℂ (Matrix (Fin n) (Fin n) ℂ)) Qᴴ).restrictScalars ℝ).comp D

theorem matrixUnitaryConnection_apply {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ)
    (D : (SchurLowerIndex n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (v : SchurLowerIndex n → ℂ) : matrixUnitaryConnection Q D v = Qᴴ * D v := rfl

/-- The Schur chart `(x, y) ↦ Q x (T + Y) (Q x)ᴴ` built from a frame `Q`, where `Y` is the
upper-triangular matrix with entries `y`. -/
def matrixSchurFrameChart {n : ℕ} (Q : (SchurLowerIndex n → ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (T : Matrix (Fin n) (Fin n) ℂ) (p : SchurCoordinates n) : Matrix (Fin n) (Fin n) ℂ :=
  Q p.1 * (T + schurUpperCombination p.2) * (Q p.1)ᴴ

theorem matrixSchurFrameChart_normalized_fderiv {n : ℕ}
    (Q : (SchurLowerIndex n → ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (T : Matrix (Fin n) (Fin n) ℂ) (x v : SchurLowerIndex n → ℂ)
    (y h : SchurUpperIndex n → ℂ)
    (D : (SchurLowerIndex n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (hQ : HasFDerivAt Q D x) (hunit : ∀ᶠ z in 𝓝 x, Q z ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (Q x)ᴴ * fderiv ℝ (matrixSchurFrameChart Q T) (x, y) (v, h) * Q x =
      schurMovingTangent (T + schurUpperCombination y) (matrixUnitaryConnection (Q x) D)
        (v, h) := by
  let X := SchurLowerIndex n → ℂ
  let Y := SchurUpperIndex n → ℂ
  let M := Matrix (Fin n) (Fin n) ℂ
  let F := ContinuousLinearMap.fst ℝ X Y
  let S := ContinuousLinearMap.snd ℝ X Y
  have hq := hQ.comp ((x, y) : X × Y) F.hasFDerivAt
  have hu := ((schurUpperCLM n).restrictScalars ℝ).hasFDerivAt.comp ((x, y) : X × Y) S.hasFDerivAt
  have ht := (hasFDerivAt_const (𝕜 := ℝ) T ((x, y) : X × Y)).add hu
  have ha := (schurConjTransposeCLM n).hasFDerivAt.comp ((x, y) : X × Y) hq
  have hp := (hq.mul' ht).mul' ha
  have hf : (matrixSchurFrameChart Q T : X × Y → M) =
      (Q ∘ ⇑F * ((fun _ => T) + ⇑((schurUpperCLM n).restrictScalars ℝ) ∘ ⇑S) *
        ⇑(schurConjTransposeCLM n) ∘ Q ∘ ⇑F) := by
    funext p
    change Q p.1 * (T + schurUpperCombination p.2) * (Q p.1)ᴴ =
      Q p.1 * (T + schurUpperCLM n p.2) * (Q p.1)ᴴ
    rw [schurUpperCLM_apply]
  have hpf := hp.fderiv
  rw [hf]
  erw [hpf]
  have hux : Q x ∈ Matrix.unitaryGroup (Fin n) ℂ := hunit.self_of_nhds
  have h1 : (Q x)ᴴ * Q x = 1 := Matrix.mem_unitaryGroup_iff'.mp hux
  have h2 : Q x * (Q x)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hux
  have hw := matrixUnitary_left_derivative_skew hQ hunit v
  rw [schurMovingTangent_apply, matrixUnitaryConnection_apply]
  have hh : (D v)ᴴ * Q x = -((Q x)ᴴ * D v) := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using hw
  change (Q x)ᴴ *
      ((Q x * (T + schurUpperCLM n y)) * (D v)ᴴ +
        (Q x * (0 + schurUpperCLM n h) + D v * (T + schurUpperCLM n y)) * (Q x)ᴴ) * Q x =
    ((Q x)ᴴ * D v) * (T + schurUpperCombination y) -
      (T + schurUpperCombination y) * ((Q x)ᴴ * D v) + schurUpperCombination h
  rw [zero_add, schurUpperCLM_apply, schurUpperCLM_apply]
  calc
    _ = ((Q x)ᴴ * Q x) * (T + schurUpperCombination y) * (D v)ᴴ * Q x +
        ((Q x)ᴴ * Q x) * schurUpperCombination h * ((Q x)ᴴ * Q x) +
        (Q x)ᴴ * D v * (T + schurUpperCombination y) * ((Q x)ᴴ * Q x) := by noncomm_ring
    _ = (T + schurUpperCombination y) * ((D v)ᴴ * Q x) + schurUpperCombination h +
        ((Q x)ᴴ * D v) * (T + schurUpperCombination y) := by
      rw [h1]
      simp [Matrix.mul_assoc]
    _ = _ := by rw [hh]; noncomm_ring

end
end GinibrePoincare

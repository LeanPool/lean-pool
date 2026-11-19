/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralSobolevDirections.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevCoordinates

/-! # Exact real gradient directions under matrix entry reindexing -/

@[expose] public section
open Matrix
namespace GinibrePoincare
noncomputable section

/-- Real configuration coordinates `(k, c)` correspond to real matrix coordinates
`(e k, c)` under the entry labelling `e`. -/
def matrixEntryRealIndexEquiv {n m : ℕ} (e : Fin m ≃ Fin n × Fin n) :
    (Fin m × Fin 2) ≃ MatrixRealIndex n where
  toFun p := ⟨(e p.1).1, ⟨(e p.1).2, p.2⟩⟩
  invFun i := (e.symm (i.1, i.2.1), i.2.2)
  left_inv p := by simp
  right_inv i := by cases i with | mk i q => cases q with | mk j k => simp

theorem matrixComplexEntryEquiv_direction {n m : ℕ} (e : Fin m ≃ Fin n × Fin n)
    (p : Fin m × Fin 2) :
    matrixComplexEntryEquiv e (ginibreCoordinateDirection p) =
      matrixRealCoordinates n (Pi.single (matrixEntryRealIndexEquiv e p) 1) := by
  classical
  rw [matrixEntryRealIndexEquiv, matrixRealCoordinates_direction]
  funext i j
  have he (a b : Fin n) : e.symm (a, b) = p.1 ↔ a = (e p.1).1 ∧ b = (e p.1).2 := by
    rw [Equiv.symm_apply_eq, Prod.ext_iff]
  by_cases hp : p.2 = 0 <;>
    by_cases hi : i = (e p.1).1 <;> by_cases hj : j = (e p.1).2 <;>
    simp [matrixComplexEntryEquiv, ginibreCoordinateDirection, realCoordinateDirection,
      imaginaryCoordinateDirection, coordinateDirection, hp, hi, hj, he]

end
end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurEntryVolume.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurLocalIntegration

/-!
# Matrix Schur entry volume

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `schurEntryCoordinates_volume_preserving`.
-/

@[expose] public section

open Matrix MeasureTheory OrderDual
open scoped Matrix Matrix.Norms.Operator
namespace GinibrePoincare
noncomputable section

/-- Strictly lower positions `(i, j)` with `j < i` are equivalent to `SchurLowerIndex n`. -/
def schurLowerRawEquiv (n : ℕ) :
    {p : Fin n × Fin n // p.2 < p.1} ≃ SchurLowerIndex n where
  toFun p := ⟨toLex (p.val.2, toDual p.val.1), p.property⟩
  invFun q := ⟨(schurLowerRow q, schurLowerCol q), q.property⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv q := by apply Subtype.ext; rfl

/-- Positions `(i, j)` with `¬ j < i` are equivalent to `SchurUpperIndex n`. -/
def schurUpperRawEquiv (n : ℕ) :
    {p : Fin n × Fin n // ¬p.2 < p.1} ≃ SchurUpperIndex n where
  toFun p := ⟨p.val, le_of_not_gt p.property⟩
  invFun q := ⟨q.val, not_lt_of_ge q.property⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv q := by apply Subtype.ext; rfl

theorem matrixVolume_uncurry_preserving (n : ℕ) :
    MeasurePreserving (Function.uncurry : (Fin n → Fin n → ℂ) → (Fin n × Fin n → ℂ)) := by
  refine ⟨by fun_prop, ?_⟩
  change Measure.map Function.uncurry (Measure.pi (fun _ : Fin n =>
    Measure.pi (fun _ : Fin n => (volume : Measure ℂ)))) =
    Measure.pi (fun _ : Fin n × Fin n => (volume : Measure ℂ))
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
  have hpre : (Function.uncurry : (Fin n → Fin n → ℂ) → (Fin n × Fin n → ℂ)) ⁻¹'
      Set.univ.pi s = Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
    ext G
    simp only [Set.mem_preimage, Set.mem_univ_pi, Function.uncurry_apply_pair, Prod.forall]
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

/-- Splitting matrix entries into lower and upper coordinates preserves actual product
Lebesgue volume; no Jacobian normalization constant is left implicit. -/
theorem schurEntryCoordinates_volume_preserving (n : ℕ) :
    MeasurePreserving (schurEntryCoordinates (n := n))
      (volume : Measure (Fin n → Fin n → ℂ)) (volume : Measure (SchurCoordinates n)) := by
  let P := fun p : Fin n × Fin n => p.2 < p.1
  let L := MeasurableEquiv.piCongrLeft (fun _ : SchurLowerIndex n => ℂ)
    (schurLowerRawEquiv n)
  let R := MeasurableEquiv.piCongrLeft (fun _ : SchurUpperIndex n => ℂ)
    (schurUpperRawEquiv n)
  have hL := measurePreserving_piCongrLeft
    (fun _ : SchurLowerIndex n => (volume : Measure ℂ))
    (schurLowerRawEquiv n)
  have hR := measurePreserving_piCongrLeft
    (fun _ : SchurUpperIndex n => (volume : Measure ℂ))
    (schurUpperRawEquiv n)
  have hsplit := measurePreserving_piEquivPiSubtypeProd
    (fun _ : Fin n × Fin n => (volume : Measure ℂ)) P
  have hp := (hL.prod hR).comp (hsplit.comp (matrixVolume_uncurry_preserving n))
  have hf : (fun G : Fin n → Fin n → ℂ =>
      (L ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n × Fin n => ℂ) P)
        (Function.uncurry G)).1,
       R ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n × Fin n => ℂ) P)
        (Function.uncurry G)).2)) = schurEntryCoordinates := by
    rfl
  rw [← hf]
  exact hp

end
end GinibrePoincare

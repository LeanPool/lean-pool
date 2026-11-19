/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurUpperSplit.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurGaussianGlobal

/-!
# Matrix Schur upper split

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `schurUpperSplit_sorted_lintegral`.
-/

@[expose] public section

open Matrix MeasureTheory Set
open scoped Matrix Matrix.Norms.Operator ENNReal
namespace GinibrePoincare
noncomputable section

/-- Strictly upper-triangular positions: upper positions off the diagonal. -/
abbrev SchurStrictUpperIndex (n : ℕ) := {p : SchurUpperIndex n // p.val.1 ≠ p.val.2}

/-- Diagonal upper positions `(i, i)` are equivalent to `Fin n`. -/
def schurUpperDiagonalEquiv (n : ℕ) :
    {p : SchurUpperIndex n // p.val.1 = p.val.2} ≃ Fin n where
  toFun p := p.val.val.1
  invFun i := ⟨⟨(i, i), le_refl i⟩, rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl p.property
  right_inv i := rfl

/-- Splits upper coordinates into the diagonal entries and the strictly upper entries. -/
def schurUpperSplit (n : ℕ) : (SchurUpperIndex n → ℂ) →
    (Fin n → ℂ) × (SchurStrictUpperIndex n → ℂ) :=
  fun y => (fun i => y ⟨(i, i), le_refl i⟩, fun p => y p.val)

theorem schurUpperSplit_volume_preserving (n : ℕ) :
    MeasurePreserving (schurUpperSplit n)
      (volume : Measure (SchurUpperIndex n → ℂ))
      (volume : Measure ((Fin n → ℂ) × (SchurStrictUpperIndex n → ℂ))) := by
  let P := fun p : SchurUpperIndex n => p.val.1 = p.val.2
  let L := MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℂ) (schurUpperDiagonalEquiv n)
  have hL := measurePreserving_piCongrLeft (fun _ : Fin n => (volume : Measure ℂ))
    (schurUpperDiagonalEquiv n)
  have hsplit := measurePreserving_piEquivPiSubtypeProd
    (fun _ : SchurUpperIndex n => (volume : Measure ℂ)) P
  have hp := (hL.prod (MeasurePreserving.id (volume : Measure (SchurStrictUpperIndex n → ℂ)))).comp
      hsplit
  have he : (fun y : SchurUpperIndex n → ℂ =>
      (L ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : SchurUpperIndex n => ℂ) P) y).1,
        ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : SchurUpperIndex n => ℂ) P) y).2)) =
      schurUpperSplit n := rfl
  rw [← he]
  exact hp

/-- Configurations `z` that are strictly increasing in the lexicographic order on
`(re, im)`. -/
def matrixSchurOrderedConfigurations (n : ℕ) : Set (Fin n → ℂ) :=
  {z | matrixSchurOrderedDiagonal (Matrix.diagonal z)}

theorem measurableSet_matrixSchurOrderedConfigurations (n : ℕ) :
    MeasurableSet (matrixSchurOrderedConfigurations n) := by
  let : BorelSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (BorelSpace (Fin n → Fin n → ℂ))
  have hd : Measurable (Matrix.diagonal : (Fin n → ℂ) → Matrix (Fin n) (Fin n) ℂ) := by
    fun_prop
  exact hd (measurableSet_matrixSchurOrderedDiagonal n)

theorem schurUpperSplit_sorted_preimage (n : ℕ) :
    schurUpperSplit n ⁻¹' (matrixSchurOrderedConfigurations n ×ˢ Set.univ) =
      matrixSchurSortedUpperDomain n := by
  ext y
  change (matrixSchurOrderedDiagonal (Matrix.diagonal (schurUpperSplit n y).1) ∧ True) ↔
    matrixSchurOrderedDiagonal (schurUpperCombination y)
  rw [and_true]
  have hd : ∀ i : Fin n, Matrix.diagonal (schurUpperSplit n y).1 i i =
      schurUpperCombination y i i := by
    intro i
    simp only [Matrix.diagonal_apply_eq, schurUpperSplit]
    exact (schurUpperCombination_entry y ⟨(i, i), le_refl i⟩).symm
  unfold matrixSchurOrderedDiagonal
  simp only [hd]

theorem schurUpperSplit_sorted_lintegral {n : ℕ}
    (f : (Fin n → ℂ) → ℝ≥0∞) (hf : Measurable f)
    (k : (SchurStrictUpperIndex n → ℂ) → ℝ≥0∞) (hk : Measurable k) :
    ∫⁻ y in matrixSchurSortedUpperDomain n,
      f (schurUpperSplit n y).1 * k (schurUpperSplit n y).2 =
      (∫⁻ z in matrixSchurOrderedConfigurations n, f z) * ∫⁻ u, k u := by
  have hs : MeasurableSet (matrixSchurOrderedConfigurations n ×ˢ
      (Set.univ : Set (SchurStrictUpperIndex n → ℂ))) :=
    (measurableSet_matrixSchurOrderedConfigurations n).prod MeasurableSet.univ
  have hp := (schurUpperSplit_volume_preserving n).setLIntegral_comp_preimage hs
    ((hf.comp measurable_fst).mul (hk.comp measurable_snd))
  rw [schurUpperSplit_sorted_preimage] at hp
  simp only [Pi.mul_apply, Function.comp_apply] at hp
  rw [hp, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  exact lintegral_prod_mul hf.aemeasurable hk.aemeasurable

end
end GinibrePoincare

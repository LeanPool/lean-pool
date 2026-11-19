/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurChambers.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurOrderedSpectralLaw

/-!
# Matrix Schur chambers

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `measurableSet_matrixSchurPermutationChamber`,
`matrixSchurPermutationChamber_pairwise_disjoint`, `matrixSchurPermutationChamber_cover`.
-/

@[expose] public section

open Matrix MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator ENNReal
namespace GinibrePoincare
noncomputable section

theorem matrixSchurOrderedConfigurations_iff {n : ℕ} (z : Fin n → ℂ) :
    z ∈ matrixSchurOrderedConfigurations n ↔
      StrictMono (fun i => toLex ((z i).re, (z i).im)) := by
  unfold matrixSchurOrderedConfigurations matrixSchurOrderedDiagonal
  simp only [Set.mem_ofPred_eq, Matrix.diagonal_apply_eq]

theorem matrixSchurOrderedConfigurations_injective {n : ℕ} (z : Fin n → ℂ)
    (hz : z ∈ matrixSchurOrderedConfigurations n) : Function.Injective z := by
  have hi := ((matrixSchurOrderedConfigurations_iff z).mp hz).injective
  intro i j hij
  apply hi
  exact congrArg (fun w : ℂ => toLex (w.re, w.im)) hij

/-- The configurations `z` for which `z ∘ e` is lexicographically strictly ordered. -/
def matrixSchurPermutationChamber {n : ℕ} (e : Fin n ≃ Fin n) : Set (Fin n → ℂ) :=
  {z | z ∘ e ∈ matrixSchurOrderedConfigurations n}

theorem measurableSet_matrixSchurPermutationChamber {n : ℕ} (e : Fin n ≃ Fin n) :
    MeasurableSet (matrixSchurPermutationChamber e) :=
  (measurableSet_matrixSchurOrderedConfigurations n).preimage (by fun_prop)

theorem matrixSchurPermutationChamber_pairwise_disjoint (n : ℕ) :
    Pairwise (fun e f : Fin n ≃ Fin n => Disjoint (matrixSchurPermutationChamber e)
      (matrixSchurPermutationChamber f)) := by
  intro e f hne
  apply Set.disjoint_left.mpr
  intro z he hf
  have hme := (matrixSchurOrderedConfigurations_iff (z ∘ e)).mp he
  have hmf := (matrixSchurOrderedConfigurations_iff (z ∘ f)).mp hf
  let a : Fin n → ℝ ×ₗ ℝ := fun i => toLex ((z i).re, (z i).im)
  have hr : Set.range (a ∘ e) = Set.range (a ∘ f) := by
    simp only [Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
  have heq : a ∘ e = a ∘ f := Set.range_injOn_strictMono_of_wellFoundedLT hme hmf hr
  have hi : Function.Injective a := by
    intro i j hij
    have heinj : Function.Injective (a ∘ e) := hme.injective
    have h : e.symm i = e.symm j := by
      apply heinj
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hij
    exact e.symm.injective h
  apply hne
  apply Equiv.ext
  intro i
  exact hi (congrFun heq i)

theorem matrixSchurPermutationChamber_cover (n : ℕ) :
    (⋃ e : Fin n ≃ Fin n, matrixSchurPermutationChamber e) =
      {z : Fin n → ℂ | Function.Injective z} := by
  ext z
  constructor
  · intro hz
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hz
    have hi := matrixSchurOrderedConfigurations_injective (z ∘ e) he
    intro i j hij
    have h : e.symm i = e.symm j := by
      apply hi
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hij
    exact e.symm.injective h
  · intro hz
    obtain ⟨e, he⟩ := matrixEigenvalues_sorted_permutation n z hz
    exact Set.mem_iUnion.mpr ⟨e, (matrixSchurOrderedConfigurations_iff (z ∘ e)).mpr he⟩

end
end GinibrePoincare

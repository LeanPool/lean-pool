/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurSortedDomain.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurSortedDecomposition
public import LeanPool.GinibrePoincare.Analysis.MatrixSchurGaussianIntegration

/-!
# Matrix Schur sorted domain

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `measurableSet_matrixSchurSortedUpperDomain`,
`matrixSchurSortedDomain_exists_injective`.
-/

@[expose] public section

open Matrix NormedSpace MeasureTheory Filter Set Order
open scoped Matrix Matrix.Norms.Operator Topology
namespace GinibrePoincare
noncomputable section

theorem measurableSet_matrixSchurOrderedDiagonal (n : ℕ) :
    MeasurableSet {A : Matrix (Fin n) (Fin n) ℂ | matrixSchurOrderedDiagonal A} := by
  change MeasurableSet {A : Fin n → Fin n → ℂ |
    ∀ i j : Fin n, i < j → toLex ((A i i).re, (A i i).im) < toLex ((A j j).re, (A j j).im)}
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  by_cases hij : i < j
  · simp only [hij, iInter_true, Prod.Lex.toLex_lt_toLex]
    have hir : Measurable (fun A : Fin n → Fin n → ℂ => (A i i).re) := by fun_prop
    have hjr : Measurable (fun A : Fin n → Fin n → ℂ => (A j j).re) := by fun_prop
    have hii : Measurable (fun A : Fin n → Fin n → ℂ => (A i i).im) := by fun_prop
    have hji : Measurable (fun A : Fin n → Fin n → ℂ => (A j j).im) := by fun_prop
    exact (measurableSet_lt hir hjr).union ((measurableSet_eq_fun hir hjr).inter
      (measurableSet_lt hii hji))
  · simp [hij]

/-- Upper coordinates whose upper-triangular matrix has lexicographically ordered diagonal. -/
def matrixSchurSortedUpperDomain (n : ℕ) : Set (SchurUpperIndex n → ℂ) :=
  {y | matrixSchurOrderedDiagonal (schurUpperCombination y)}

theorem measurableSet_matrixSchurSortedUpperDomain (n : ℕ) :
    MeasurableSet (matrixSchurSortedUpperDomain n) := by
  let : BorelSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (BorelSpace (Fin n → Fin n → ℂ))
  have hc : Measurable (schurUpperCombination (n := n)) := by
    have he : (schurUpperCombination (n := n)) = schurUpperCLM n :=
      funext fun y => (schurUpperCLM_apply n y).symm
    rw [he]
    exact (schurUpperCLM n).continuous.measurable
  exact hc (measurableSet_matrixSchurOrderedDiagonal n)

theorem schurUpperCombination_injective (n : ℕ) :
    Function.Injective (schurUpperCombination (n := n)) := by
  intro y z he
  funext p
  have hp := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A p.val.1 p.val.2) he
  simpa only [schurUpperCombination_entry] using hp

/-- A single open angular neighborhood gives an injective Schur chart with all
ordered eigenvalues and all strict upper entries, including unbounded ones. -/
theorem matrixSchurSortedDomain_exists_injective (n : ℕ) :
    ∃ V : Set (SchurLowerIndex n → ℂ), IsOpen V ∧ 0 ∈ V ∧
      InjOn (matrixSchurFrameChart (matrixSchurExponentialFrame n) (0 : Matrix (Fin n) (Fin n) ℂ))
        (V ×ˢ matrixSchurSortedUpperDomain n) := by
  obtain ⟨N, hN, hslice⟩ := matrixSchur_uniform_sorted_slice n
  obtain ⟨V, hVN, hV, h0⟩ := mem_nhds_iff.mp hN
  refine ⟨V, hV, h0, ?_⟩
  rintro p hp q hq he
  have hx := hslice p.1 (hVN hp.1) q.1 (hVN hq.1)
    (schurUpperCombination p.2) (schurUpperCombination q.2)
    (fun i j hij => schurUpperCombination_lower_zero _ i j hij)
    (fun i j hij => schurUpperCombination_lower_zero _ i j hij) hp.2 hq.2
  have he' : matrixSchurExponentialFrame n p.1 * schurUpperCombination p.2 *
      (matrixSchurExponentialFrame n p.1)ᴴ =
    matrixSchurExponentialFrame n q.1 * schurUpperCombination q.2 *
      (matrixSchurExponentialFrame n q.1)ᴴ := by
    simpa only [matrixSchurFrameChart, zero_add] using he
  obtain ⟨hfirst, hsecond⟩ := hx he'
  exact Prod.ext hfirst (schurUpperCombination_injective n hsecond)

end
end GinibrePoincare

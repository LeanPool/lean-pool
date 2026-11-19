/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreFullGeneratorPolynomialCompatibility.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorPolynomialIdentification
public import LeanPool.GinibrePoincare.Analysis.PolynomialSectorSemigroup
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupEigenvectors

/-!
# Ginibre full generator polynomial compatibility

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreFullEvolution_polynomialSector`.
-/

@[expose] public section

noncomputable section
namespace GinibrePoincare
open scoped NNReal

/-- The entire actual closed polynomial sector consists of symmetric L²
classes, not only its finite polynomial subspace. -/
theorem ginibreFull_closedPolynomialSector_le (n : ℕ) (hn : 2 ≤ n) :
    closedPolynomialSector n hn ≤ ginibreSymmetricL2 n := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact (ginibreFullPolynomialEigenvector n hn i).property
  · exact isClosed_ginibreSymmetricL2 n

/-- Actual continuous inclusion of the closed polynomial sector into full
symmetric Ginibre L². -/
def ginibreFullPolynomialSectorInclusion (n : ℕ) (hn : 2 ≤ n) :
    closedPolynomialSector n hn →L[ℂ] ginibreSymmetricL2 n :=
  (closedPolynomialSector n hn).subtypeL.codRestrict (ginibreSymmetricL2 n)
    (fun u => ginibreFull_closedPolynomialSector_le n hn u.property)

@[simp] theorem ginibreFullPolynomialSectorInclusion_eigenvector (n : ℕ) (hn : 2 ≤ n)
    (i : PolynomialEigenfunctionData n) :
    ginibreFullPolynomialSectorInclusion n hn (polynomialSectorEigenvector n hn i) =
      ginibreFullPolynomialEigenvector n hn i := rfl

theorem ginibreFullEvolution_polynomial_eigenvector (n : ℕ) (hn : 2 ≤ n)
    (t : ℝ≥0) (i : PolynomialEigenfunctionData n) :
    ginibreFullEvolution n (by omega) t (ginibreFullPolynomialEigenvector n hn i) =
      Real.exp (-eigenvalue n i.a i.b i.m * (t : ℝ)) • ginibreFullPolynomialEigenvector n hn i := by
  have hg := ginibreFullGenerator_polynomial_eigenvector n hn i
  have hr : 0 ≤ eigenvalue n i.a i.b i.m := by unfold eigenvalue; positivity
  have h := resolventCfcEvolution_generator_eigenvector (ginibreFullComplexResolvent n (by omega))
    (ginibreFullComplexResolvent_isSelfAdjoint n (by omega))
    (ginibreFullComplexResolvent_injective n (by omega)) t (eigenvalue n i.a i.b i.m) hr
    (ginibreFullPolynomialEigenvector n hn i)
  apply h
  have hs : -(eigenvalue n i.a i.b i.m : ℂ) • ginibreFullPolynomialEigenvector n hn i =
      -(eigenvalue n i.a i.b i.m : ℝ) • ginibreFullPolynomialEigenvector n hn i := by
    rw [← algebraMap_smul ℂ (-(eigenvalue n i.a i.b i.m : ℝ))]
    simp only [map_neg]
    rfl
  rw [hs]
  exact hg

/-- The full diffusion agrees with the independently constructed polynomial
sector semigroup on its entire closed L² sector. -/
theorem ginibreFullEvolution_polynomialSector (n : ℕ) (hn : 2 ≤ n) (t : ℝ≥0)
    (u : closedPolynomialSector n hn) :
    ginibreFullEvolution n (by omega) t (ginibreFullPolynomialSectorInclusion n hn u) =
      ginibreFullPolynomialSectorInclusion n hn (polynomialSectorEvolution n hn t u) := by
  let L := (ginibreFullEvolution n (by omega) t).comp (ginibreFullPolynomialSectorInclusion n hn)
  let M := (ginibreFullPolynomialSectorInclusion n hn).comp (polynomialSectorEvolution n hn t)
  have heq : L = M := by
    apply ContinuousLinearMap.ext
    intro x
    refine (polynomialSectorCombination_dense n hn).induction_on x ?_ ?_
    · exact isClosed_eq L.continuous M.continuous
    · intro c
      unfold polynomialSectorCombination
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
      simp only [map_sum, map_smul]
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      change ginibreFullEvolution n (by omega) t
        (ginibreFullPolynomialSectorInclusion n hn (polynomialSectorEigenvector n hn i)) =
        ginibreFullPolynomialSectorInclusion n hn
          (polynomialSectorEvolution n hn t (polynomialSectorEigenvector n hn i))
      rw [ginibreFullPolynomialSectorInclusion_eigenvector, polynomialSectorEvolution_eigenvector,
        map_smul, ginibreFullPolynomialSectorInclusion_eigenvector,
        ginibreFullEvolution_polynomial_eigenvector]
      rw [← algebraMap_smul ℂ (Real.exp (-eigenvalue n i.a i.b i.m * (t : ℝ)))]
      rfl
  exact congrArg (fun A => A u) heq

end GinibrePoincare

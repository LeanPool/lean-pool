/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianHolomorphicPhasePolynomial.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianHermitePhaseSpectrum

/-! # Actual polynomial representatives of Gaussian holomorphic phase vectors -/


@[expose] public section


open MeasureTheory
open scoped BigOperators
namespace GinibrePoincare
open ComplexHermite
noncomputable section

/-- A finite Hermite vector with zero antiholomorphic support is an actual
finite holomorphic Hermite sum. -/
theorem finiteHermiteCombination_zeroAnti_as_finiteZero {n : ℕ} (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ)
    (hc : ∀ pq ∈ c.support, totalAntiDegree pq = 0) :
    ∃ S : Finset (Fin n → ℕ),
      finiteZeroHermiteL2 n hn S (fun p => c (p, 0)) = finiteHermiteCombination n hn c ∧
      ∀ p ∈ S, (p, 0) ∈ c.support := by
  classical
  have hq : ∀ pq ∈ c.support, pq.2 = 0 := by
    intro pq hpq
    funext i
    have hle : pq.2 i ≤ totalAntiDegree pq :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hz := hc pq hpq
    change pq.2 i = 0
    omega
  refine ⟨c.support.image Prod.fst, ?_, ?_⟩
  · unfold finiteZeroHermiteL2 finiteHermiteCombination
    simp only [Finsupp.linearCombination_apply, Finsupp.sum]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro pq hpq
      rw [← hq pq hpq]
    · intro a ha b hb hab
      exact Prod.ext hab ((hq a ha).trans (hq b hb).symm)
  · intro p hp
    obtain ⟨pq, hpq, rfl⟩ := Finset.mem_image.mp hp
    have he : (pq.1, 0) = pq := Prod.ext rfl (hq pq hpq).symm
    rw [he]
    exact hpq

/-- Every actual Gaussian holomorphic phase eigenvector has a finite
holomorphic Hermite representative of its precise homogeneous degree. -/
theorem gaussian_holomorphic_phase_finiteZero_reconstruction {n r : ℕ} (hn : 0 < n)
    (x : Lp ℂ 2 (complexGaussianMeasure n))
    (hx : x ∈ hermiteAntiDegreeClosedSpan n hn 0)
    (hphase : ∀ (u : ℂ) (hu : ‖u‖ = 1), gaussianGlobalPhaseL2 hn u hu x = u ^ r • x) :
    ∃ (S : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ),
      finiteZeroHermiteL2 n hn S c = x ∧
      ∀ p ∈ S, totalHolomorphicDegree p = r := by
  obtain ⟨c, hc, hs⟩ := gaussian_holomorphic_phase_finite_reconstruction hn x hx hphase
  obtain ⟨S, hS, hmem⟩ := finiteHermiteCombination_zeroAnti_as_finiteZero hn c
    (fun pq hpq => (hs pq hpq).1)
  exact ⟨S, fun p => c (p, 0), hS.trans hc, fun p hp => (hs (p, 0) (hmem p hp)).2⟩

end
end GinibrePoincare

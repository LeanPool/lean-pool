/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorNumberBochnerClosure.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberSecondBounds
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberForm
/-! # Bochner–Kodaira identity on the maximal number domain

The finite Hermite identity already controls the norm of every second derivative
by the number-image norm. Applied to differences of graph approximants, this
bound makes each second-derivative sequence Cauchy. Completeness of Gaussian
L² supplies its limit `Q`.

The final theorem first constructs the weak first derivatives `D`. Closedness
of the ordinary weak derivative graph identifies `Q j k` as the derivative of
`D j`. Finally, continuity of squared norms and finite sums passes the finite
Bochner–Kodaira identity to the limit. No extra second-derivative hypothesis is
needed beyond membership in the maximal number graph.
-/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators Topology
namespace GinibrePoincare
noncomputable section
open ComplexHermite
theorem correspondenceOperatorNumber_second_limits {n : ℕ} (hn : 0 < n)
    (u v : Lp ℂ 2 (complexGaussianMeasure n))
    (huv : (u, v) ∈ (correspondenceOperatorNumber n hn).graph) :
    ∃Q : Fin n→Fin n→Lp ℂ 2 (complexGaussianMeasure n),∀j k,
      Tendsto (fun s=>correspondenceOperatorFiniteSecond n hn j k
        (gaussianHermiteFiniteCoefficients hn u s)) atTop (𝓝 (Q j k)) := by
  -- Convergence of the number images controls the second derivatives of differences.
  have hnumberLimit := (correspondenceOperatorNumber_finite_core n hn u v huv).2
  have hnumberCauchy := hnumberLimit.cauchySeq
  have hsecondLimit_exists (j k : Fin n) : ∃q : Lp ℂ 2 (complexGaussianMeasure n),
      Tendsto (fun s=>correspondenceOperatorFiniteSecond n hn j k
        (gaussianHermiteFiniteCoefficients hn u s)) atTop (𝓝 q) := by
    apply cauchySeq_tendsto_of_complete
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨S, hS⟩ := Metric.cauchySeq_iff.mp hnumberCauchy ε hε
    refine ⟨S, fun s hs t ht=>?_⟩
    exact lt_of_le_of_lt (correspondenceOperatorFiniteSecond_dist_le n hn j k _ _) (hS s hs t ht)
  choose Q hsecondLimits using hsecondLimit_exists
  exact ⟨Q, hsecondLimits⟩

/-- Equation (6.9) on the exact full maximal number domain, with every second
derivative an internally constructed ordinary distributional Gaussian derivative. -/
theorem correspondenceOperatorNumber_full_bochner_kodaira {n : ℕ} (hn : 0 < n)
    (u v : Lp ℂ 2 (complexGaussianMeasure n))
    (huv : (u, v) ∈ (correspondenceOperatorNumber n hn).graph) :
    ∃(D : Fin n→Lp ℂ 2 (complexGaussianMeasure n))
      (Q : Fin n→Fin n→Lp ℂ 2 (complexGaussianMeasure n)),
      (∀j, IsGaussianWeakDbar n u (D j) j) ∧
      (∀j k, IsGaussianWeakDbar n (D j) (Q j k) k) ∧
      ‖v‖^2=(∑j : Fin n,∑k : Fin n, ‖Q j k‖^2)+(n : ℝ)*∑j : Fin n, ‖D j‖^2 := by
  choose D hD using correspondenceOperatorNumber_weak_dbar_exists hn u v huv
  obtain ⟨Q, hsecondLimits⟩ := correspondenceOperatorNumber_second_limits hn u v huv
  have hfirstLimits := (gaussianWeakDbar_finiteHermite_approximation hn u D hD).2
  have hnumberLimit := (correspondenceOperatorNumber_finite_core n hn u v huv).2
  refine ⟨D, Q, hD,?_,?_⟩
  · -- Identify the constructed limit through closedness of the weak graph.
    intro j k
    apply gaussianWeakDbar_of_tendsto (l := atTop) k
      (fun s=>(finiteDbarComponentL2 n hn (gaussianHermiteFiniteCoefficients hn u s) j,
        correspondenceOperatorFiniteSecond n hn j k (gaussianHermiteFiniteCoefficients hn u s)))
      (D j) (Q j k)
    · intro s
      rw [correspondenceOperatorFiniteSecond_eq]
      exact gaussian_finiteHermite_weak_dbar n hn
        (loweredCoefficients n (gaussianHermiteFiniteCoefficients hn u s) j) k
    · exact (hfirstLimits j).prodMk_nhds (hsecondLimits j k)
  · -- Pass the finite identity to the limit in each energy term.
    have hnumberNormLimit := hnumberLimit.norm.pow 2
    have hsecondEnergyLimit := tendsto_finsetSum Finset.univ (fun j _=>
      tendsto_finsetSum Finset.univ (fun k _=>(hsecondLimits j k).norm.pow 2))
    have hfirstEnergyLimit := tendsto_finsetSum Finset.univ (fun j _=>(hfirstLimits j).norm.pow 2)
    have henergyLimit := hsecondEnergyLimit.add (hfirstEnergyLimit.const_mul (n : ℝ))
    apply tendsto_nhds_unique hnumberNormLimit
    apply henergyLimit.congr
    intro s
    simp only [correspondenceOperatorFiniteSecond_eq]
    exact (bkFinite_integrated_identity n hn (gaussianHermiteFiniteCoefficients hn u s)).symm
/-- Named first and second weak derivatives, together with the maximal-domain
Bochner identity. The original existence theorem remains available; this record
lets clients refer to the derivative laws and energy identity by field name. -/
structure GaussianNumberBochnerData (n : ℕ)
    (u v : Lp ℂ 2 (complexGaussianMeasure n)) where
  /-- The first weak `∂̄`-derivatives of `u`, one for each coordinate. -/
  first : Fin n → Lp ℂ 2 (complexGaussianMeasure n)
  /-- The second weak derivatives: `second j k` is the weak `∂̄`-derivative of `first j` in
  coordinate `k`. -/
  second : Fin n → Fin n → Lp ℂ 2 (complexGaussianMeasure n)
  first_weak : ∀ j, IsGaussianWeakDbar n u (first j) j
  second_weak : ∀ j k, IsGaussianWeakDbar n (first j) (second j k) k
  energy_identity : ‖v‖ ^ 2 =
    (∑ j : Fin n, ∑ k : Fin n, ‖second j k‖ ^ 2) +
      (n : ℝ) * ∑ j : Fin n, ‖first j‖ ^ 2

/-- Every maximal number graph vector admits the named Bochner data interface. -/
theorem correspondenceOperatorNumber_has_bochner_data {n : ℕ} (hn : 0 < n)
    (u v : Lp ℂ 2 (complexGaussianMeasure n))
    (huv : (u, v) ∈ (correspondenceOperatorNumber n hn).graph) :
    Nonempty (GaussianNumberBochnerData n u v) := by
  obtain ⟨first, second, hfirst, hsecond, henergy⟩ :=
    correspondenceOperatorNumber_full_bochner_kodaira hn u v huv
  exact ⟨⟨first, second, hfirst, hsecond, henergy⟩⟩

end
end GinibrePoincare

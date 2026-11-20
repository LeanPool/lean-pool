/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorNumberForm.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberFiniteForm
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberWeakDomain
/-! # Identification with the ordinary Gaussian derivative form

The first theorem extends integration by parts from finite Hermite combinations
to an arbitrary maximal graph vector. Graph convergence controls the number
image, while weak-derivative approximation controls every first derivative;
continuity of inner products identifies the two limits.

For the converse, test the proposed variational identity against one Hermite
basis vector at a time. The finite integration-by-parts identity, conjugate
symmetry of the complex inner product, and the known number eigenvalue recover
exactly the coefficient relation defining the maximal graph. Thus the form tests
range over the ordinary weak derivative domain, not just polynomial tests.
-/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators Topology ComplexConjugate
namespace GinibrePoincare
noncomputable section
open ComplexHermite
/-- The number operator's defining variational identity uses the actual ordinary
distributional Gaussian dbar graph and every weak-form test. -/
theorem correspondenceOperatorNumber_form_identity {n : ℕ} (hn : 0 < n)
    (u v : Lp ℂ 2 (complexGaussianMeasure n))
    (huv : (u, v) ∈ (correspondenceOperatorNumber n hn).graph)
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hu : ∀ j, IsGaussianWeakDbar n u (D j) j)
    (w : Lp ℂ 2 (complexGaussianMeasure n))
    (E : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hw : ∀ j, IsGaussianWeakDbar n w (E j) j) :
    inner ℂ v w=∑j : Fin n, inner ℂ (D j) (E j) := by
  have hN := (correspondenceOperatorNumber_finite_core n hn u v huv).2
  have hD := (gaussianWeakDbar_finiteHermite_approximation hn u D hu).2
  have hleft := hN.inner (tendsto_const_nhds (x := w)) (𝕜 := ℂ)
  have hright : Tendsto (fun s=>∑j : Fin n, inner ℂ
      (finiteDbarComponentL2 n hn (gaussianHermiteFiniteCoefficients hn u s) j) (E j))
      atTop (𝓝 (∑j : Fin n, inner ℂ (D j) (E j))) := by
    apply tendsto_finsetSum
    intro j hj
    exact (hD j).inner tendsto_const_nhds (𝕜 := ℂ)
  apply tendsto_nhds_unique hleft
  exact hright.congr (fun s=>(correspondenceOperatorNumber_finite_form hn _ w E hw).symm)

/-- The concrete maximal Hermite number operator is exactly the operator
associated to the unrestricted ordinary distributional Gaussian dbar form. -/
theorem correspondenceOperatorNumber_graph_iff_ordinary_form {n : ℕ} (hn : 0 < n)
    (u v : Lp ℂ 2 (complexGaussianMeasure n)) :
    (u, v)∈(correspondenceOperatorNumber n hn).graph ↔
      ∃D : Fin n→Lp ℂ 2 (complexGaussianMeasure n),
        (∀j, IsGaussianWeakDbar n u (D j) j) ∧
        ∀(w : Lp ℂ 2 (complexGaussianMeasure n)) (E : Fin n→Lp ℂ 2 (complexGaussianMeasure n)),
          (∀j, IsGaussianWeakDbar n w (E j) j) →
          inner ℂ v w=∑j : Fin n, inner ℂ (D j) (E j) := by
  constructor
  · intro huv
    choose D hD using correspondenceOperatorNumber_weak_dbar_exists hn u v huv
    exact ⟨D, hD, fun w E hw=>correspondenceOperatorNumber_form_identity hn u v huv D hD w E hw⟩
  · rintro ⟨D, hD, hform⟩
    rw [correspondenceOperatorNumber_graph]
    intro pq
    let c : HermiteMultiIndex n→₀ℂ := Finsupp.single pq 1
    have he := hform (finiteHermiteCombination n hn c)
      (fun j=>finiteDbarComponentL2 n hn c j) (gaussian_finiteHermite_weak_dbar n hn c)
    have hf := correspondenceOperatorNumber_finite_form hn c u D hD
    have hf' := congrArg conj hf
    simp only [inner_conj_symm, map_sum] at hf'
    rw [← hf'] at he
    have hc : finiteHermiteCombination n hn c=multivariateNormalizedL2 n hn pq.1 pq.2 := by
      simp [c, finiteHermiteCombination, Finsupp.linearCombination_single, hermiteL2Family,
        multivariateNormalizedL2]
    have hnC : finiteGaussianNumberL2 n hn c=
        ((n*totalAntiDegree pq : ℕ) : ℂ) • multivariateNormalizedL2 n hn pq.1 pq.2 := by
      simp [c, finiteGaussianNumberL2, spectralNumberCoefficients, spectralDiagonalCoefficients,
        Finsupp.linearCombination_single, finiteHermiteCombination, hermiteL2Family,
        multivariateNormalizedL2]
    rw [hc, hnC, inner_smul_right] at he
    have hh := congrArg conj he
    simp only [map_mul, inner_conj_symm, Complex.conj_natCast] at hh
    simpa only [gaussianHermiteCoefficient_eq_inner] using hh
end
end GinibrePoincare

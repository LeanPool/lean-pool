/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorNumberDomain.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeSpectralNumberPolynomial
public import LeanPool.GinibrePoincare.Analysis.HermiteInverseSquareRoot
public import Mathlib.Topology.Algebra.Module.LinearPMap
/-! # Maximal graph and finite Hermite core

The pair `(u, v)` belongs to the number graph precisely when every Hermite
coefficient of `v` is `n * totalAntiDegree` times the corresponding coefficient
of `u`. Completeness of the Hilbert basis gives uniqueness of `v`. Conversely,
square summability of these multiplied coefficients constructs `v` by the
inverse Hilbert-basis representation; this proves the exact domain statement.

Closedness follows coefficient by coefficient from continuity of inner products.
Finite Hermite truncations converge in both components of the graph: the graph
relation identifies the truncated number image of `u` with the truncation of
`v`. The ordinary distributional interpretation is established downstream in
`CorrespondenceOperatorNumberForm`, rather than assumed in this definition.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section
open ComplexHermite
/-- The maximal Hermite number graph, with the paper's eigenvalues n|q|. -/
def correspondenceOperatorNumberGraph (n : ℕ) (hn : 0 < n) :
    Submodule ℂ (Lp ℂ 2 (complexGaussianMeasure n) × Lp ℂ 2 (complexGaussianMeasure n)) where
  carrier := {p | ∀pq, gaussianHermiteCoefficient hn p.2 pq =
    (n*totalAntiDegree pq : ℕ)*gaussianHermiteCoefficient hn p.1 pq}
  zero_mem' := by simp [gaussianHermiteCoefficient_eq_inner]
  add_mem' := by
    intro p q hp hq pq
    simp only [Prod.fst_add, Prod.snd_add, gaussianHermiteCoefficient_eq_inner,
        inner_add_right] at *
    rw [hp pq, hq pq, mul_add]
  smul_mem' := by
    intro a p hp pq
    change gaussianHermiteCoefficient hn (a • p.2) pq =
      (n*totalAntiDegree pq : ℕ)*gaussianHermiteCoefficient hn (a • p.1) pq
    simp only [gaussianHermiteCoefficient_eq_inner, inner_smul_right] at *
    rw [hp pq]
    ring

theorem correspondenceOperatorNumberGraph_singleValued (n : ℕ) (hn : 0 < n)
    (p : Lp ℂ 2 (complexGaussianMeasure n) × Lp ℂ 2 (complexGaussianMeasure n))
    (hp : p ∈ correspondenceOperatorNumberGraph n hn) (hx : p.1 = 0) : p.2=0 := by
  apply gaussianHermiteCoefficient_ext hn
  intro pq
  simpa [hx, gaussianHermiteCoefficient_eq_inner] using hp pq

/-- The genuine maximal unbounded number operator, rather than a compact-jet norm. -/
def correspondenceOperatorNumber (n : ℕ) (hn : 0 < n) :
    Lp ℂ 2 (complexGaussianMeasure n) →ₗ.[ℂ] Lp ℂ 2 (complexGaussianMeasure n) :=
  (correspondenceOperatorNumberGraph n hn).toLinearPMap

theorem correspondenceOperatorNumber_graph (n : ℕ) (hn : 0 < n) :
    (correspondenceOperatorNumber n hn).graph=correspondenceOperatorNumberGraph n hn :=
  Submodule.toLinearPMap_graph_eq _ (correspondenceOperatorNumberGraph_singleValued n hn)

/-- Exact maximal graph domain: the n|q| multiplier must be square summable. -/
theorem correspondenceOperatorNumber_domain_iff (n : ℕ) (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) :
    (∃v, (u, v)∈(correspondenceOperatorNumber n hn).graph) ↔
      Summable (fun pq : HermiteMultiIndex n =>
        ‖(n*totalAntiDegree pq : ℕ)*gaussianHermiteCoefficient hn u pq‖^2) := by
  rw [correspondenceOperatorNumber_graph]
  constructor
  · rintro ⟨v, hv⟩
    exact (hasSum_norm_sq_gaussianHermiteCoefficient hn v).summable.congr
      (fun pq=>by rw [hv pq])
  · intro hs
    let c : lp (fun _ : HermiteMultiIndex n=>ℂ) 2 :=
      ⟨fun pq=>(n*totalAntiDegree pq : ℕ)*gaussianHermiteCoefficient hn u pq,
        memℓp_gen (by simpa using hs)⟩
    refine ⟨(gaussianHermiteHilbertBasis n hn).repr.symm c,?_⟩
    intro pq
    change ((gaussianHermiteHilbertBasis n hn).repr
      ((gaussianHermiteHilbertBasis n hn).repr.symm c)) pq=_
    rw [LinearIsometryEquiv.apply_symm_apply]

/-- Literal finite differential number polynomials belong to the maximal graph. -/
theorem correspondenceOperatorNumber_finite_graph (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) :
    (finiteHermiteCombination n hn c, finiteGaussianNumberL2 n hn c)∈
      (correspondenceOperatorNumber n hn).graph := by
  rw [correspondenceOperatorNumber_graph]
  intro pq
  simp [finiteGaussianNumberL2, spectralNumberCoefficients,
    gaussianHermiteCoefficient_finiteHermiteCombination]

/-- The maximal number graph is closed in the literal value/operator L² topology. -/
theorem correspondenceOperatorNumberGraph_isClosed (n : ℕ) (hn : 0 < n) :
    IsClosed (correspondenceOperatorNumberGraph n hn : Set
      (Lp ℂ 2 (complexGaussianMeasure n) × Lp ℂ 2 (complexGaussianMeasure n))) := by
  change IsClosed {p : Lp ℂ 2 (complexGaussianMeasure n) × Lp ℂ 2 (complexGaussianMeasure n) | ∀pq,
      gaussianHermiteCoefficient hn p.2 pq =
    (n*totalAntiDegree pq : ℕ)*gaussianHermiteCoefficient hn p.1 pq}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro pq
  simp only [gaussianHermiteCoefficient_eq_inner]
  exact isClosed_eq (continuous_const.inner continuous_snd)
    (continuous_const.mul (continuous_const.inner continuous_fst))

/-- Finite Hermite number polynomials approximate every maximal graph vector,
simultaneously in the genuine value and number-operator norms. -/
theorem correspondenceOperatorNumber_finite_core (n : ℕ) (hn : 0 < n)
    (u v : Lp ℂ 2 (complexGaussianMeasure n))
    (huv : (u, v) ∈ (correspondenceOperatorNumber n hn).graph) :
    Tendsto (fun s=>finiteHermiteCombination n hn (gaussianHermiteFiniteCoefficients hn u s))
      atTop (𝓝 u) ∧
    Tendsto (fun s=>finiteGaussianNumberL2 n hn (gaussianHermiteFiniteCoefficients hn u s))
      atTop (𝓝 v) := by
  classical
  rw [correspondenceOperatorNumber_graph] at huv
  have hlim (x : Lp ℂ 2 (complexGaussianMeasure n)) :
      Tendsto (fun s=>finiteHermiteCombination n hn (gaussianHermiteFiniteCoefficients hn x s))
        atTop (𝓝 x) := by
    simp only [gaussianHermiteFiniteCoefficients_value]
    change HasSum (fun pq=>gaussianHermiteCoefficient hn x pq •
      (gaussianHermiteHilbertBasis n hn) pq) x
    simpa only [gaussianHermiteCoefficient] using (gaussianHermiteHilbertBasis n hn).hasSum_repr x
  refine ⟨hlim u,?_⟩
  have he (s : Finset (HermiteMultiIndex n)) :
      finiteGaussianNumberL2 n hn (gaussianHermiteFiniteCoefficients hn u s)=
        finiteHermiteCombination n hn (gaussianHermiteFiniteCoefficients hn v s) := by
    apply gaussianHermiteCoefficient_ext hn
    intro pq
    simp only [finiteGaussianNumberL2, gaussianHermiteCoefficient_finiteHermiteCombination,
      spectralNumberCoefficients, spectralDiagonalCoefficients_apply]
    change (n*totalAntiDegree pq : ℕ)*((s : Set _).indicator (gaussianHermiteCoefficient hn u) pq)=
      (s : Set _).indicator (gaussianHermiteCoefficient hn v) pq
    by_cases hp : pq∈s
    · simp only [Set.indicator_of_mem hp]
      exact (huv pq).symm
    · simp [hp]
  simpa only [he] using hlim v
end
end GinibrePoincare

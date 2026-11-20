/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorNumberSpectralSelfAdjoint.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberSpectralResolvent
/-!
# Correspondence operator number spectral self adjoint

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperatorNumberSpectral_isSelfAdjoint`,
`correspondenceOperatorNumberSpectral_nonnegative`.
-/

@[expose] public section
open MeasureTheory Set
open scoped Topology
namespace GinibrePoincare
noncomputable section
theorem correspondenceOperatorNumberSpectralResolvent_denseRange (n : ℕ) (hn : 0 < n) (f : ℝ → ℝ)
    (hf :
    ∀ x, 0 ≤ f x) :
    DenseRange (correspondenceOperatorNumberSpectralResolvent n hn f hf) := by
  let R := correspondenceOperatorNumberSpectralResolvent n hn f hf
  have hR : R.adjoint=R := correspondenceOperatorNumberSpectralResolvent_isSelfAdjoint n hn f hf
  have hk : R.ker=⊥ := LinearMap.ker_eq_bot.mpr
    (correspondenceOperatorNumberSpectralResolvent_injective n hn f hf)
  have he := R.orthogonal_ker
  rw [hR, hk, Submodule.bot_orthogonal_eq_top] at he
  change Dense (Set.range R)
  rw [dense_iff_closure_eq]
  change closure (R.range : Set (Lp ℂ 2 (complexGaussianMeasure n))) = Set.univ
  rw [← Submodule.topologicalClosure_coe,← he]
  rfl

theorem correspondenceOperatorNumberSpectral_range_pair (n : ℕ) (hn : 0 < n) (f : ℝ → ℝ) (hf : ∀ x,
    0
    ≤ f
    x)
    (x : Lp ℂ 2 (complexGaussianMeasure n)) :
    (correspondenceOperatorNumberSpectralResolvent n hn f hf x,
        x-correspondenceOperatorNumberSpectralResolvent n hn f hf x)∈
      (correspondenceOperatorNumberSpectral n hn f).graph := by
  rw [correspondenceOperatorNumberSpectral_graph_iff_resolvent n hn f hf]
  simp only [add_sub_cancel]

theorem correspondenceOperatorNumberSpectral_dense_domain (n : ℕ) (hn : 0 < n) (f : ℝ → ℝ) (hf : ∀
    x,
    0 ≤ f
    x) :
    Dense ((correspondenceOperatorNumberSpectral n hn f).domain : Set (Lp ℂ 2
        (complexGaussianMeasure n))) := by
  apply (correspondenceOperatorNumberSpectralResolvent_denseRange n hn f hf).mono
  rintro _ ⟨x, rfl⟩
  exact LinearPMap.mem_domain_of_mem_graph (correspondenceOperatorNumberSpectral_range_pair n hn f
      hf x)

theorem correspondenceOperatorNumberSpectralGraph_symmetric (n : ℕ) (hn : 0 < n) (f : ℝ → ℝ) (hf :
    ∀ x,
    0 ≤ f x)
    (p q : Lp ℂ 2 (complexGaussianMeasure n) × Lp ℂ 2 (complexGaussianMeasure n))
    (hp : p ∈ correspondenceOperatorNumberSpectralGraph n hn f)
    (hq : q ∈ correspondenceOperatorNumberSpectralGraph n hn f) :
    inner ℂ p.2 q.1=inner ℂ p.1 q.2 := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (correspondenceOperatorNumberSpectralResolvent_isSelfAdjoint n hn f hf)
  have h := hs (p.1+p.2) (q.1+q.2)
  have hpR := (correspondenceOperatorNumberSpectral_graph_iff_resolvent n hn f hf p.1 p.2).mp
    ((correspondenceOperatorNumberSpectral_graph n hn f) ▸ hp)
  have hqR := (correspondenceOperatorNumberSpectral_graph_iff_resolvent n hn f hf q.1 q.2).mp
    ((correspondenceOperatorNumberSpectral_graph n hn f) ▸ hq)
  change inner ℂ (correspondenceOperatorNumberSpectralResolvent n hn f hf (p.1+p.2)) (q.1+q.2)=
    inner ℂ (p.1+p.2) (correspondenceOperatorNumberSpectralResolvent n hn f hf (q.1+q.2)) at h
  rw [hpR, hqR, inner_add_left, inner_add_right] at h
  linear_combination -h

theorem correspondenceOperatorNumberSpectralGraph_adjoint (n : ℕ) (hn : 0 < n) (f : ℝ → ℝ) (hf : ∀
    x,
    0 ≤ f
    x) :
    (correspondenceOperatorNumberSpectralGraph n hn
        f).adjoint=correspondenceOperatorNumberSpectralGraph n hn f := by
  ext p
  rw [Submodule.mem_adjoint_iff]
  constructor
  · intro hp
    rw [← correspondenceOperatorNumberSpectral_graph]
    rw [correspondenceOperatorNumberSpectral_graph_iff_resolvent n hn f hf]
    apply ext_inner_left ℂ
    intro x
    have hpair := correspondenceOperatorNumberSpectral_range_pair n hn f hf x
    rw [correspondenceOperatorNumberSpectral_graph] at hpair
    have h := hp _ _ hpair
    have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (correspondenceOperatorNumberSpectralResolvent_isSelfAdjoint n hn f hf)
    have he := hs x (p.1+p.2)
    change inner ℂ (correspondenceOperatorNumberSpectralResolvent n hn f hf x) (p.1+p.2)=
      inner ℂ x (correspondenceOperatorNumberSpectralResolvent n hn f hf (p.1+p.2)) at he
    rw [inner_sub_left] at h
    rw [inner_add_right] at he
    linear_combination -he-h
  · intro hp a b hab
    exact sub_eq_zero.mpr (correspondenceOperatorNumberSpectralGraph_symmetric n hn f hf (a, b) p
        hab hp)

/-- The maximal Gaussian number operator is genuinely self-adjoint. -/
theorem correspondenceOperatorNumberSpectral_isSelfAdjoint (n : ℕ) (hn : 0 < n) (f : ℝ → ℝ) (hf :
    ∀ x,
    0 ≤ f x) :
    IsSelfAdjoint (correspondenceOperatorNumberSpectral n hn f) := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (correspondenceOperatorNumberSpectral_dense_domain n
      hn f hf),
    correspondenceOperatorNumberSpectral_graph n hn f,
        correspondenceOperatorNumberSpectralGraph_adjoint n hn f hf]

/-- The spectral operator is nonnegative on its full maximal graph. -/
theorem correspondenceOperatorNumberSpectral_nonnegative (n : ℕ) (hn : 0 < n)
    (f : ℝ → ℝ) (hf : ∀ x, 0 ≤ f x) (u v : Lp ℂ 2 (complexGaussianMeasure n))
    (huv : (u, v) ∈ (correspondenceOperatorNumberSpectral n hn f).graph) :
    0≤(inner ℂ u v).re := by
  rw [correspondenceOperatorNumberSpectral_graph] at huv
  have h := (lp.hasSum_inner ((gaussianHermiteHilbertBasis n hn).repr u)
    ((gaussianHermiteHilbertBasis n hn).repr v)).mapL Complex.reCLM
  rw [LinearIsometryEquiv.inner_map_map] at h
  have hp (pq : ComplexHermite.HermiteMultiIndex n) :
      0≤(inner ℂ (gaussianHermiteCoefficient hn u pq) (gaussianHermiteCoefficient hn v pq)).re := by
    rw [huv pq]
    have he : (inner ℂ (gaussianHermiteCoefficient hn u pq)
        ((f (n*ComplexHermite.totalAntiDegree pq : ℕ) : ℂ)*gaussianHermiteCoefficient hn u pq)).re=
        f (n*ComplexHermite.totalAntiDegree pq : ℕ)*
          ((gaussianHermiteCoefficient hn u pq).re^2+(gaussianHermiteCoefficient hn u pq).im^2) :=
              by
      simp only [RCLike.inner_apply, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [he]
    exact mul_nonneg (hf _) (add_nonneg (sq_nonneg _) (sq_nonneg _))
  apply ge_of_tendsto h
  apply Filter.Eventually.of_forall
  intro s
  exact Finset.sum_nonneg (fun pq _=>hp pq)
end
end GinibrePoincare

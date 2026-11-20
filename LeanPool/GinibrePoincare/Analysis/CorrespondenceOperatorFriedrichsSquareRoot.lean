/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorFriedrichsSquareRoot.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorFriedrichsSquareRootGraph
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorFriedrichsSquareRootForm
/-!
# Correspondence operator Friedrichs square root

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceFriedrichsSquareRoot_square`,
`correspondenceFriedrichsSquareRoot_nonnegative`,
`correspondenceFriedrichsSquareRoot_domain_ordinary_H1`.
-/

@[expose] public section
open MeasureTheory Set
namespace GinibrePoincare
noncomputable section

/-- The functional-calculus construction is a square root of the actual
nonnegative Friedrichs operator `−A`, with equality of maximal graph domains. -/
theorem correspondenceFriedrichsSquareRoot_square (n : ℕ) (hn : 0 < n)
    (u w : GinibreFullComplexL2 n) :
    (∃ v, (u, v) ∈ (correspondenceFriedrichsSquareRoot n hn).graph ∧
      (v, w) ∈ (correspondenceFriedrichsSquareRoot n hn).graph) ↔
    (u, -w) ∈ (correspondenceOperatorGenerator n hn).graph := by
  let B := correspondenceFriedrichsResolventSqrt n hn
  let C := correspondenceFriedrichsComplementSqrt n hn
  let R := correspondenceOperatorComplexResolvent n hn
  have hc x : B (C x) = C (B x) :=
    congrArg (fun L : GinibreFullComplexL2 n →L[ℂ] GinibreFullComplexL2 n => L x)
      (correspondenceFriedrichsSquareRoots_commute n hn).eq
  have hb x : B (B x) = R x :=
    congrArg (fun L : GinibreFullComplexL2 n →L[ℂ] GinibreFullComplexL2 n => L x)
      (correspondenceFriedrichsResolventSqrt_square n hn)
  have hcc x : C (C x) = x - R x := by
    have h := congrArg (fun L : GinibreFullComplexL2 n →L[ℂ] GinibreFullComplexL2 n => L x)
      (correspondenceFriedrichsComplementSqrt_square n hn)
    simpa using h
  simp only [correspondenceFriedrichsSquareRoot_graph, correspondenceFriedrichsSquareRootGraph,
    correspondenceSquareRootGraph_mem, correspondenceOperatorGenerator_graph_iff, sub_neg_eq_add]
  change (∃ v, B v = C u ∧ B w = C v) ↔ R (u + w) = u
  constructor
  · rintro ⟨v, hv, hw⟩
    have he : R w = u - R u := by
      rw [← hb, hw, hc, hv, hcc]
    rw [map_add, he]
    abel
  · intro h
    have hRw : R w = u - R u := by
      rw [map_add] at h
      exact eq_sub_of_add_eq' h
    let v := C (B (u + w))
    have hv : B v = C u := by
      change B (C (B (u + w))) = C u
      rw [hc, hb, h]
    refine ⟨v, hv, ?_⟩
    apply correspondenceFriedrichsResolventSqrt_injective n hn
    change B (B w) = B (C v)
    rw [hb, hc, hv, hcc, hRw]

/-- Positivity singles out the nonnegative self-adjoint square root. -/
theorem correspondenceFriedrichsSquareRoot_nonnegative (n : ℕ) (hn : 0 < n)
    (u v : GinibreFullComplexL2 n)
    (huv : (u, v) ∈ (correspondenceFriedrichsSquareRoot n hn).graph) :
    0 ≤ (inner ℂ u v).re := by
  obtain ⟨x, rfl, rfl⟩ := (correspondenceFriedrichsSquareRoot_graph_parametrize n hn u v).mp huv
  have hB : 0 ≤ correspondenceFriedrichsResolventSqrt n hn := CFC.sqrt_nonneg _
  have hC : 0 ≤ correspondenceFriedrichsComplementSqrt n hn := CFC.sqrt_nonneg _
  have hBC := Commute.mul_nonneg hB hC (correspondenceFriedrichsSquareRoots_commute n hn)
  have hp := ContinuousLinearMap.nonneg_iff_isPositive.mp hBC
  have hinner := (correspondenceFriedrichsResolventSqrt n hn).adjoint_inner_right x
    (correspondenceFriedrichsComplementSqrt n hn x)
  rw [show (correspondenceFriedrichsResolventSqrt n hn).adjoint =
      correspondenceFriedrichsResolventSqrt n hn from
    correspondenceFriedrichsResolventSqrt_selfAdjoint n hn] at hinner
  rw [← hinner]
  exact hp.re_inner_nonneg_right x

/-- Literal Section 1.5 square-root domain: the real and imaginary parts have
actual ordinary distributional gradients in the concrete weighted L² space. -/
theorem correspondenceFriedrichsSquareRoot_domain_ordinary_H1 (n : ℕ) (hn : 0 < n)
    (u : GinibreFullComplexL2 n) :
    u ∈ (correspondenceFriedrichsSquareRoot n hn).domain ↔
      (∃ g : GinibreFullGradientL2 n,
        IsGinibreDistributionalGradient n (ginibreFullComplexRe n u) g) ∧
      (∃ g : GinibreFullGradientL2 n,
        IsGinibreDistributionalGradient n (ginibreFullComplexIm n u) g) := by
  rw [← SetLike.mem_coe, correspondenceFriedrichsSquareRoot_domain,
      correspondenceFriedrichsResolventSqrt_range_form]
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨⟨correspondenceOperatorFormGradient n hn p.fst, by
      rw [correspondenceComplexFormValue_re]
      exact correspondenceOperatorFormSpace_weak n hn p.fst⟩,
      ⟨correspondenceOperatorFormGradient n hn p.snd, by
        rw [correspondenceComplexFormValue_im]
        exact correspondenceOperatorFormSpace_weak n hn p.snd⟩⟩
  · rintro ⟨⟨g, hg⟩, ⟨h, hh⟩⟩
    let pr := correspondenceOperatorFormOfWeak n hn ⟨(ginibreFullComplexRe n u, g), hg⟩
    let pi := correspondenceOperatorFormOfWeak n hn ⟨(ginibreFullComplexIm n u, h), hh⟩
    refine ⟨WithLp.toLp 2 (pr, pi), ?_⟩
    change ginibreFullComplexOfReal n (correspondenceOperatorFormValue n hn pr) +
      Complex.I • ginibreFullComplexOfReal n (correspondenceOperatorFormValue n hn pi) = u
    rw [correspondenceOperatorFormOfWeak_value, correspondenceOperatorFormOfWeak_value]
    exact ginibreFullComplex_decomposition n u

end
end GinibrePoincare

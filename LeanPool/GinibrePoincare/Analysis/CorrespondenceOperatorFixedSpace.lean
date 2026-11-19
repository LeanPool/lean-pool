/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorFixedSpace.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorZeroGradient
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorConservation
/-!
# Correspondence operator fixed space

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperatorComplexResolvent_fixed_iff_constant`.
-/

@[expose] public section
open Set MeasureTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
/-- Exact unrestricted real resolvent fixed space, obtained from the ordinary
weak form energy and the proved zero-gradient constant theorem. -/
theorem correspondenceOperatorValueResolvent_fixed_iff_constant {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) :
    correspondenceOperatorValueResolvent n hn u=u ↔∃c : ℝ, u=ginibreRealConstantL2 n hn c := by
  constructor
  · intro hu
    let p := correspondenceOperatorFormResolvent n hn u
    let g := correspondenceOperatorFormGradient n hn p
    have hv : correspondenceOperatorFormValue n hn p=u := hu
    have he := correspondenceOperatorFormSpace_inner n hn p p
    have hR := correspondenceOperatorFormResolvent_riesz n hn u p
    rw [hv] at he hR
    rw [hR] at he
    have hginner : inner ℝ g g=0 := by
      change inner ℝ u u=inner ℝ u u+(1/(n : ℝ))*inner ℝ g g at he
      have hnR : 0<(1/(n : ℝ)) := by positivity
      nlinarith
    have hg : g=0 := inner_self_eq_zero.mp hginner
    have hw := correspondenceOperatorFormSpace_weak n hn p
    rw [hv] at hw
    change IsGinibreDistributionalGradient n u g at hw
    rw [hg] at hw
    exact correspondenceOperator_zero_gradient_constant hn u hw
  · rintro ⟨c, rfl⟩
    exact correspondenceOperatorValueResolvent_constant n hn c

/-- Exact fixed-space identification on the literal unrestricted complex L². -/
theorem correspondenceOperatorComplexResolvent_fixed_iff_constant {n : ℕ} (hn : 0 < n)
    (u : GinibreFullComplexL2 n) :
    correspondenceOperatorComplexResolvent n hn u=u ↔
      ∃c : ℂ, u=(ginibreFullConstant n hn c).val := by
  constructor
  · intro hu
    have hr := congrArg (ginibreFullComplexRe n) hu
    have hi := congrArg (ginibreFullComplexIm n) hu
    rw [correspondenceOperatorComplexResolvent_re] at hr
    rw [correspondenceOperatorComplexResolvent_im] at hi
    obtain ⟨a, ha⟩ := (correspondenceOperatorValueResolvent_fixed_iff_constant hn _).mp hr
    obtain ⟨b, hb⟩ := (correspondenceOperatorValueResolvent_fixed_iff_constant hn _).mp hi
    refine ⟨⟨a, b⟩,?_⟩
    have hd := ginibreFullComplex_decomposition n u
    have hc := ginibreFullComplex_decomposition n (ginibreFullConstant n hn ⟨a, b⟩).val
    rw [ha, hb] at hd
    have hre : ginibreFullComplexRe n (ginibreFullConstant n hn ⟨a, b⟩).val=
        ginibreRealConstantL2 n hn a := ginibreFullConstant_re n hn ⟨a, b⟩
    have him : ginibreFullComplexIm n (ginibreFullConstant n hn ⟨a, b⟩).val=
        ginibreRealConstantL2 n hn b := ginibreFullConstant_im n hn ⟨a, b⟩
    rw [hre, him] at hc
    exact hd.symm.trans hc
  · rintro ⟨c, rfl⟩
    exact correspondenceOperatorComplexResolvent_constant n hn c
end
end GinibrePoincare

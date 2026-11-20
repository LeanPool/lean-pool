/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorConservation.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorEvolution
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupConservation
/-!
# Correspondence operator conservation

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperatorEvolution_constant`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- The unrestricted resolvent fixes every genuine equilibrium constant. -/
theorem correspondenceOperatorValueResolvent_constant (n : ℕ) (hn : 0 < n) (c : ℝ) :
    correspondenceOperatorValueResolvent n hn (ginibreRealConstantL2 n hn c)=
      ginibreRealConstantL2 n hn c := by
  have he := correspondenceOperatorGenerator_resolvent_unique n hn
    (ginibreRealConstantL2 n hn c) (ginibreRealConstantL2 n hn c) 0
    (ginibreRealConstantL2_weak n hn c) (by intro v h hv; simp)
  exact he.1.symm

theorem correspondenceOperatorComplexResolvent_constant (n : ℕ) (hn : 0 < n) (c : ℂ) :
    correspondenceOperatorComplexResolvent n hn (ginibreFullConstant n hn c).val =
      (ginibreFullConstant n hn c).val := by
  have hr : ginibreFullComplexRe n (ginibreFullConstant n hn c).val =
      ginibreRealConstantL2 n hn c.re := ginibreFullConstant_re n hn c
  have hi : ginibreFullComplexIm n (ginibreFullConstant n hn c).val =
      ginibreRealConstantL2 n hn c.im := ginibreFullConstant_im n hn c
  have hd := ginibreFullComplex_decomposition n
    (correspondenceOperatorComplexResolvent n hn (ginibreFullConstant n hn c).val)
  rw [correspondenceOperatorComplexResolvent_re, correspondenceOperatorComplexResolvent_im,
    hr, hi, correspondenceOperatorValueResolvent_constant,
        correspondenceOperatorValueResolvent_constant] at hd
  have hc := ginibreFullComplex_decomposition n (ginibreFullConstant n hn c).val
  rw [hr, hi] at hc
  exact hd.symm.trans hc

/-- Every constant belongs to the unrestricted generator kernel. -/
theorem correspondenceOperatorGenerator_constant (n : ℕ) (hn : 0 < n) (c : ℂ) :
    ((ginibreFullConstant n hn c).val, 0) ∈ (correspondenceOperatorGenerator n hn).graph := by
  rw [correspondenceOperatorGenerator_graph_iff, sub_zero]
  exact correspondenceOperatorComplexResolvent_constant n hn c

/-- The unrestricted diffusion is conservative, preserving the literal
constant one (indeed every complex constant) at every nonnegative time. -/
theorem correspondenceOperatorEvolution_constant (n : ℕ) (hn : 0 < n) (t : ℝ≥0) (c : ℂ) :
    correspondenceOperatorEvolution n hn t (ginibreFullConstant n hn c).val =
      (ginibreFullConstant n hn c).val :=
  resolventCfcEvolution_fixes_kernel _ (correspondenceOperatorComplexResolvent_isSelfAdjoint n hn)
    (correspondenceOperatorComplexResolvent_injective n hn) t _
    (correspondenceOperatorGenerator_constant n hn c)

end
end GinibrePoincare

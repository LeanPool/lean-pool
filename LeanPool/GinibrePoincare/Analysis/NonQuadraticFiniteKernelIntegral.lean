/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticFiniteKernelIntegral.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticL2KernelIntegral
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Non quadratic finite kernel integral

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main result: `piSeparatedKernel_hasCompactSupport`. The finite-dimensional kernel-integral
representative `finiteDimensionalL2_kernel_integral_ae` and
`finiteTranslatedKernel_hasCompactSupport` live in `NonQuadraticL2KernelIntegral`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped Topology ContDiff InnerProductSpace Pointwise
namespace GinibrePoincare
noncomputable section

theorem piSeparatedKernel_hasCompactSupport {d : ℕ} (φ : Fin d → ℂ → ℂ)
    (hc : ∀ i, HasCompactSupport (φ i)) :
    HasCompactSupport (fun x : Fin d → ℂ => ∏ i, φ i (x i)) := by
  have hs : IsCompact {x : Fin d → ℂ | ∀ i, x i ∈ tsupport (φ i)} :=
    isCompact_pi_infinite hc
  apply hs.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hs.isClosed
  intro x hx i
  apply subset_closure
  intro hz
  exact hx (Finset.prod_eq_zero (Finset.mem_univ i) hz)

end
end GinibrePoincare

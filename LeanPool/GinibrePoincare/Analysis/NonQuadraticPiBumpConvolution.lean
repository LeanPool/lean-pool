/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticPiBumpConvolution.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticPiBumpAverage
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticFiniteKernelIntegral
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Non quadratic pi bump convolution

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `piL2BumpAverage_convolution_ae`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace GinibrePoincare
noncomputable section
attribute [local irreducible] piPlanarBump
/-- A continuous compactly supported function on `ℂ^d`, as an element of `L²` of Lebesgue
measure. -/
def piCompactFunctionL2 (d : ℕ) (f : Configuration d → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) : Lp ℂ 2 (volume : Measure (Configuration d)) :=
  (hf.memLp_of_hasCompactSupport hc).toLp f

theorem piTranslate_compact_smul_ae (d : ℕ) (c : ℝ) (a : Configuration d)
    (f : Configuration d → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    ((c • lebesgueL2Translate d a (piCompactFunctionL2 d f hf hc) :
      Lp ℂ 2 (volume : Measure (Configuration d))) : Configuration d → ℂ)
      =ᵐ[(volume : Measure (Configuration d))] (fun x => (c : ℂ) * f (x-a)) := by
  let u := piCompactFunctionL2 d f hf hc
  have hu : (u : Configuration d → ℂ) =ᵐ[(volume : Measure (Configuration d))] f :=
    (hf.memLp_of_hasCompactSupport hc).coeFn_toLp
  have he := (eventually_add_right_iff (volume : Measure (Configuration d)) (-a)).mpr hu
  filter_upwards [Lp.coeFn_smul c (lebesgueL2Translate d a u), lebesgueL2Translate_ae d a u, he]
    with x hs ht he
  rw [hs]
  change c • (lebesgueL2Translate d a u) x = _
  rw [Complex.real_smul, ht]
  change u (x-a) = f (x-a) at he
  rw [he]

theorem piL2BumpAverage_convolution_ae
    (d : ℕ) (φ : ContDiffBump (0 : ℂ)) (f : Configuration d → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) :
    ((piL2BumpAverage d φ (piCompactFunctionL2 d f hf hc) :
      Lp ℂ 2 (volume : Measure (Configuration d))) : Configuration d → ℂ)
      =ᵐ[(volume : Measure (Configuration d))]
      (fun x => ∫ a, (piPlanarBump d φ a : ℂ) * f (x - a)
        ∂(volume : Measure (Configuration d))) := by
  let u := piCompactFunctionL2 d f hf hc
  unfold piL2BumpAverage
  have hk : Continuous (fun a => (piPlanarBump d φ a : ℂ)) :=
    Complex.continuous_ofReal.comp (piPlanarBump_continuous d φ)
  have hkc : HasCompactSupport (fun a => (piPlanarBump d φ a : ℂ)) :=
    (piPlanarBump_compact d φ).comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hker := finiteDimensionalL2_kernel_integral_ae (volume : Measure (Configuration d))
    (fun p => (piPlanarBump d φ p.1 : ℂ) * f (p.2 - p.1))
    ((hk.comp continuous_fst).mul (hf.comp (continuous_snd.sub continuous_fst)))
    (finiteTranslatedKernel_hasCompactSupport (fun a => (piPlanarBump d φ a : ℂ)) f hkc hc)
    (fun a => piPlanarBump d φ a • lebesgueL2Translate d a u)
    (integrable_piL2BumpIntegrand d φ u)
    (fun a => piTranslate_compact_smul_ae d (piPlanarBump d φ a) a f hf hc)
  exact hker

end
end GinibrePoincare

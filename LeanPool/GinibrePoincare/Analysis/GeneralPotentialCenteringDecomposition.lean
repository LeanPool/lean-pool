/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralPotentialCenteringDecomposition.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialCenteredMean

/-!
# General potential centering decomposition

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `potentialCenteredL2_eq_sub_constant`.
-/

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section

theorem potentialCenteredL2_eq_sub_constant (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (f : Configuration n → ℝ) (hf : MemLp f 2 (potentialMeasure n V)) :
    potentialCenteredL2 n hn hV hfin f hf =
      hf.ofReal.toLp (fun z => (f z : ℂ)) -
        potentialConstantL2 n hn hV hfin ((∫ z, f z ∂potentialMeasure n V : ℝ) : ℂ) := by
  have hm : MemLp (fun z => (f z : ℂ)) 2 (potentialMeasure n V) := hf.ofReal
  apply Lp.ext
  filter_upwards [potentialCenteredL2_coeFn n hn hV hfin f hf,
    hm.coeFn_toLp, potentialConstantL2_coeFn n hn hV hfin ((∫ z, f z ∂potentialMeasure n V : ℝ) :
        ℂ),
    Lp.coeFn_sub (hf.ofReal.toLp (fun z => (f z : ℂ)))
      (potentialConstantL2 n hn hV hfin ((∫ z, f z ∂potentialMeasure n V : ℝ) : ℂ))] with z hc hf hk
          hs
  rw [hc, hs]
  simp only [Pi.sub_apply]
  rw [hf, hk, Complex.ofReal_sub]

end
end GinibrePoincare

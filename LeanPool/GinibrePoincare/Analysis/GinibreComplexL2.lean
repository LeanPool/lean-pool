/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreFullGeneratorComplexification.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorWeakSpace

/-! # Real and imaginary parts of complex Ginibre L² -/

@[expose] public section

noncomputable section
namespace GinibrePoincare
open MeasureTheory
open scoped Topology ContDiff

/-- Complex-valued L² classes for the normalized Ginibre measure. -/
abbrev GinibreFullComplexL2 (n : ℕ) := Lp ℂ 2 (ginibreMeasure n)

/-- Take the real part of a complex Ginibre L² class as a continuous real-linear map. -/
def ginibreFullComplexRe (n : ℕ) : GinibreFullComplexL2 n →L[ℝ] GinibreFullValueL2 n :=
  Complex.reCLM.compLpL 2 (ginibreMeasure n)

/-- Take the imaginary part of a complex Ginibre L² class as a continuous real-linear map. -/
def ginibreFullComplexIm (n : ℕ) : GinibreFullComplexL2 n →L[ℝ] GinibreFullValueL2 n :=
  Complex.imCLM.compLpL 2 (ginibreMeasure n)

/-- Embed a real Ginibre L² class into complex Ginibre L². -/
def ginibreFullComplexOfReal (n : ℕ) : GinibreFullValueL2 n →L[ℝ] GinibreFullComplexL2 n :=
  Complex.ofRealCLM.compLpL 2 (ginibreMeasure n)

theorem ginibreFullComplexRe_ae (n : ℕ) (f : GinibreFullComplexL2 n) :
    (ginibreFullComplexRe n f : Configuration n → ℝ) =ᵐ[ginibreMeasure n] fun z => (f z).re :=
  Complex.reCLM.coeFn_compLpL f

theorem ginibreFullComplexIm_ae (n : ℕ) (f : GinibreFullComplexL2 n) :
    (ginibreFullComplexIm n f : Configuration n → ℝ) =ᵐ[ginibreMeasure n] fun z => (f z).im :=
  Complex.imCLM.coeFn_compLpL f

theorem ginibreFullComplexOfReal_ae (n : ℕ) (f : GinibreFullValueL2 n) :
    (ginibreFullComplexOfReal n f : Configuration n → ℂ) =ᵐ[ginibreMeasure n] fun z => (f z : ℂ) :=
  Complex.ofRealCLM.coeFn_compLpL f

@[simp] theorem ginibreFullComplexRe_ofReal (n : ℕ) (f : GinibreFullValueL2 n) :
    ginibreFullComplexRe n (ginibreFullComplexOfReal n f) = f := by
  apply Lp.ext
  filter_upwards [ginibreFullComplexRe_ae n (ginibreFullComplexOfReal n f),
    ginibreFullComplexOfReal_ae n f] with z hr hc
  simp [hr, hc]

@[simp] theorem ginibreFullComplexIm_ofReal (n : ℕ) (f : GinibreFullValueL2 n) :
    ginibreFullComplexIm n (ginibreFullComplexOfReal n f) = 0 := by
  apply Lp.ext
  filter_upwards [ginibreFullComplexIm_ae n (ginibreFullComplexOfReal n f),
    ginibreFullComplexOfReal_ae n f, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := ginibreMeasure n)] with
      z hr hc hz
  rw [hr, hc]
  change 0 = (0 : GinibreFullValueL2 n) z
  simpa only [Pi.zero_apply] using hz.symm

/-- Every actual complex Ginibre L² class is reconstructed from its actual
real and imaginary L² parts. -/
theorem ginibreFullComplex_decomposition (n : ℕ) (f : GinibreFullComplexL2 n) :
    ginibreFullComplexOfReal n (ginibreFullComplexRe n f) +
      Complex.I • ginibreFullComplexOfReal n (ginibreFullComplexIm n f) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (ginibreFullComplexOfReal n (ginibreFullComplexRe n f))
      (Complex.I • ginibreFullComplexOfReal n (ginibreFullComplexIm n f)),
    Lp.coeFn_smul Complex.I (ginibreFullComplexOfReal n (ginibreFullComplexIm n f)),
    ginibreFullComplexOfReal_ae n (ginibreFullComplexRe n f),
    ginibreFullComplexOfReal_ae n (ginibreFullComplexIm n f),
    ginibreFullComplexRe_ae n f, ginibreFullComplexIm_ae n f] with z hadd hs hr hi hfr hfi
  rw [hadd]
  change (ginibreFullComplexOfReal n (ginibreFullComplexRe n f)) z +
    (Complex.I • ginibreFullComplexOfReal n (ginibreFullComplexIm n f)) z = f z
  rw [hs]
  change (ginibreFullComplexOfReal n (ginibreFullComplexRe n f)) z +
    Complex.I * (ginibreFullComplexOfReal n (ginibreFullComplexIm n f)) z = f z
  rw [hr, hi, hfr, hfi]
  simpa [mul_comm] using Complex.re_add_im (f z)

end GinibrePoincare

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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorDensity
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorSpectrum
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Ginibre Full Generator Complexification
-/


@[expose] public section

namespace GinibrePoincare
noncomputable section
open MeasureTheory
open scoped Topology

abbrev GinibreFullComplexL2 (n : ℕ) := Lp ℂ 2 (ginibreMeasure n)

def ginibreFullComplexRe (n : ℕ) : GinibreFullComplexL2 n →L[ℝ] GinibreFullValueL2 n :=
  Complex.reCLM.compLpL 2 (ginibreMeasure n)

def ginibreFullComplexIm (n : ℕ) : GinibreFullComplexL2 n →L[ℝ] GinibreFullValueL2 n :=
  Complex.imCLM.compLpL 2 (ginibreMeasure n)

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


/-- Pointwise continuous linear maps commute with actual particle pullbacks. -/
theorem ginibreFullComplex_map_permute {n : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (σ : ParticlePermutation n) (f : Lp E 2 (ginibreMeasure n)) :
    L.compLpL 2 (ginibreMeasure n)
      (Lp.compMeasurePreserving (permute σ) (ginibre_measurePreserving_permute σ) f) =
      Lp.compMeasurePreserving (permute σ) (ginibre_measurePreserving_permute σ)
        (L.compLpL 2 (ginibreMeasure n) f) := by
  apply Lp.ext
  have hc := (ginibre_measurePreserving_permute σ).quasiMeasurePreserving.ae_eq_comp
    (L.coeFn_compLpL f)
  filter_upwards [L.coeFn_compLpL
      (Lp.compMeasurePreserving (permute σ) (ginibre_measurePreserving_permute σ) f),
    Lp.coeFn_compMeasurePreserving f (ginibre_measurePreserving_permute σ),
    Lp.coeFn_compMeasurePreserving (L.compLpL 2 (ginibreMeasure n) f)
      (ginibre_measurePreserving_permute σ), hc] with z hl hp hr hc
  simp only [Function.comp_apply] at hc hp hr
  rw [hl, hp, hr, hc]

/-- Real part on the actual complex symmetric Hilbert subspace. -/
def ginibreFullSymmetricRe (n : ℕ) : ginibreSymmetricL2 n →L[ℝ] ginibreFullSymmetricValues n :=
  ((ginibreFullComplexRe n).comp ((ginibreSymmetricL2 n).subtypeL.restrictScalars ℝ)).codRestrict
    (ginibreFullSymmetricValues n) (by
      intro f σ
      have h := ginibreFullComplex_map_permute Complex.reCLM σ f.val
      change ginibreFullComplexRe n (ginibrePermutationL2 σ f.val) =
        ginibreRealPermutationL2 σ (ginibreFullComplexRe n f.val) at h
      rw [f.property σ] at h
      exact h.symm)

/-- Imaginary part on the actual complex symmetric Hilbert subspace. -/
def ginibreFullSymmetricIm (n : ℕ) : ginibreSymmetricL2 n →L[ℝ] ginibreFullSymmetricValues n :=
  ((ginibreFullComplexIm n).comp ((ginibreSymmetricL2 n).subtypeL.restrictScalars ℝ)).codRestrict
    (ginibreFullSymmetricValues n) (by
      intro f σ
      have h := ginibreFullComplex_map_permute Complex.imCLM σ f.val
      change ginibreFullComplexIm n (ginibrePermutationL2 σ f.val) =
        ginibreRealPermutationL2 σ (ginibreFullComplexIm n f.val) at h
      rw [f.property σ] at h
      exact h.symm)

/-- Embed actual real symmetric L² values into actual complex symmetric L². -/
def ginibreFullSymmetricOfReal (n : ℕ) : ginibreFullSymmetricValues n →L[ℝ] ginibreSymmetricL2 n :=
  ((ginibreFullComplexOfReal n).comp (ginibreFullSymmetricValues n).subtypeL).codRestrict
    ((ginibreSymmetricL2 n).restrictScalars ℝ) (by
      intro f σ
      have h := ginibreFullComplex_map_permute Complex.ofRealCLM σ f.val
      change ginibreFullComplexOfReal n (ginibreRealPermutationL2 σ f.val) =
        ginibrePermutationL2 σ (ginibreFullComplexOfReal n f.val) at h
      rw [f.property σ] at h
      exact h.symm)

/-- Complexification of the actual full symmetric weak resolvent, initially
bundled over the reals. -/
def ginibreFullComplexResolventReal (n : ℕ) (hn : 0 < n) :
    ginibreSymmetricL2 n →L[ℝ] ginibreSymmetricL2 n :=
  (ginibreFullSymmetricOfReal n).comp ((ginibreFullSymmetricResolvent n hn).comp
    (ginibreFullSymmetricRe n)) + Complex.I •
      (ginibreFullSymmetricOfReal n).comp ((ginibreFullSymmetricResolvent n hn).comp
        (ginibreFullSymmetricIm n))


@[simp] theorem ginibreFullComplexRe_I (n : ℕ) (f : GinibreFullComplexL2 n) :
    ginibreFullComplexRe n (Complex.I • f) = -ginibreFullComplexIm n f := by
  apply Lp.ext
  filter_upwards [ginibreFullComplexRe_ae n (Complex.I • f), Lp.coeFn_smul Complex.I f,
    Lp.coeFn_neg (ginibreFullComplexIm n f), ginibreFullComplexIm_ae n f] with z hr hs hn hi
  rw [hr, hs, hn]
  change (Complex.I * f z).re = -(ginibreFullComplexIm n f) z
  rw [hi]
  simp

@[simp] theorem ginibreFullComplexIm_I (n : ℕ) (f : GinibreFullComplexL2 n) :
    ginibreFullComplexIm n (Complex.I • f) = ginibreFullComplexRe n f := by
  apply Lp.ext
  filter_upwards [ginibreFullComplexIm_ae n (Complex.I • f), Lp.coeFn_smul Complex.I f,
    ginibreFullComplexRe_ae n f] with z hi hs hr
  rw [hi, hs, hr]
  change (Complex.I * f z).im = (f z).re
  simp

@[simp] theorem ginibreFullSymmetricRe_I (n : ℕ) (f : ginibreSymmetricL2 n) :
    ginibreFullSymmetricRe n (Complex.I • f) = -ginibreFullSymmetricIm n f := by
  apply Subtype.ext
  exact ginibreFullComplexRe_I n f.val

@[simp] theorem ginibreFullSymmetricIm_I (n : ℕ) (f : ginibreSymmetricL2 n) :
    ginibreFullSymmetricIm n (Complex.I • f) = ginibreFullSymmetricRe n f := by
  apply Subtype.ext
  exact ginibreFullComplexIm_I n f.val

/-- The actual complexification commutes with multiplication by `I`. -/
theorem ginibreFullComplexResolventReal_I (n : ℕ) (hn : 0 < n) (f : ginibreSymmetricL2 n) :
    ginibreFullComplexResolventReal n hn (Complex.I • f) =
      Complex.I • ginibreFullComplexResolventReal n hn f := by
  simp only [ginibreFullComplexResolventReal, add_apply,
    ContinuousLinearMap.comp_apply, smul_apply, ginibreFullSymmetricRe_I,
    ginibreFullSymmetricIm_I, map_neg, smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]
  abel

/-- Complex scalar multiplication splits into the two real scalar actions. -/
theorem ginibreFullComplex_scalar_decomposition (n : ℕ) (c : ℂ) (f : ginibreSymmetricL2 n) :
    c • f = c.re • f + c.im • (Complex.I • f) := by
  apply Subtype.ext
  change c • f.val = c.re • f.val + c.im • (Complex.I • f.val)
  conv_lhs => rw [← Complex.re_add_im c, add_smul, mul_smul]
  simp only [Complex.coe_smul]
  rfl

/-- The actual full symmetric weak resolvent is complex-linear. -/
def ginibreFullComplexResolventLinear (n : ℕ) (hn : 0 < n) :
    ginibreSymmetricL2 n →ₗ[ℂ] ginibreSymmetricL2 n where
  toFun := ginibreFullComplexResolventReal n hn
  map_add' := (ginibreFullComplexResolventReal n hn).map_add
  map_smul' := by
    intro c f
    rw [ginibreFullComplex_scalar_decomposition, map_add, map_smul, map_smul,
      ginibreFullComplexResolventReal_I]
    exact (ginibreFullComplex_scalar_decomposition n c _).symm

/-- The complex-linear full symmetric resolvent is continuous on actual L². -/
def ginibreFullComplexResolvent (n : ℕ) (hn : 0 < n) :
    ginibreSymmetricL2 n →L[ℂ] ginibreSymmetricL2 n :=
  { ginibreFullComplexResolventLinear n hn with
    cont := (ginibreFullComplexResolventReal n hn).continuous }


/-- Splitting into real and imaginary parts preserves the actual L² norm
by the exact sum-of-squares formula. -/
theorem ginibreFullComplex_norm_sq (n : ℕ) (f : GinibreFullComplexL2 n) :
    ‖f‖ ^ 2 = ‖ginibreFullComplexRe n f‖ ^ 2 + ‖ginibreFullComplexIm n f‖ ^ 2 := by
  let r := ginibreFullComplexRe n f
  let i := ginibreFullComplexIm n f
  have hr : Integrable (fun z => ‖r z‖ ^ 2) (ginibreMeasure n) := by
    have ht : Integrable (fun z => r z ^ 2) (ginibreMeasure n) := by
      convert (Lp.memLp r).integrable_mul (Lp.memLp r) using 1
      funext z
      simp [pow_two]
    simpa only [Real.norm_eq_abs, sq_abs] using ht
  have hi : Integrable (fun z => ‖i z‖ ^ 2) (ginibreMeasure n) := by
    have ht : Integrable (fun z => i z ^ 2) (ginibreMeasure n) := by
      convert (Lp.memLp i).integrable_mul (Lp.memLp i) using 1
      funext z
      simp [pow_two]
    simpa only [Real.norm_eq_abs, sq_abs] using ht
  rw [← integral_norm_sq_eq_L2_norm_sq (ginibreMeasure n) f,
    ← integral_norm_sq_eq_L2_norm_sq (ginibreMeasure n) r,
    ← integral_norm_sq_eq_L2_norm_sq (ginibreMeasure n) i, ← integral_add hr hi]
  apply integral_congr_ae
  filter_upwards [ginibreFullComplexRe_ae n f, ginibreFullComplexIm_ae n f] with z hzR hzI
  change ‖f z‖ ^ 2 = ‖r z‖ ^ 2 + ‖i z‖ ^ 2
  change r z = (f z).re at hzR
  change i z = (f z).im at hzI
  rw [hzR, hzI, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [Real.norm_eq_abs, pow_two]

/-- Real part of the complex inner product, in actual real L² coordinates. -/
theorem ginibreFullComplex_inner_re (n : ℕ) (f h : GinibreFullComplexL2 n) :
    (inner ℂ f h).re = inner ℝ (ginibreFullComplexRe n f) (ginibreFullComplexRe n h) +
      inner ℝ (ginibreFullComplexIm n f) (ginibreFullComplexIm n h) := by
  have hnorm := norm_add_sq (𝕜 := ℂ) f h
  rw [ginibreFullComplex_norm_sq n (f + h), ginibreFullComplex_norm_sq n f,
    ginibreFullComplex_norm_sq n h, map_add, map_add] at hnorm
  have hr := norm_add_sq_real (ginibreFullComplexRe n f) (ginibreFullComplexRe n h)
  have hi := norm_add_sq_real (ginibreFullComplexIm n f) (ginibreFullComplexIm n h)
  change _ = _ + 2 * (inner ℂ f h).re + _ at hnorm
  linarith

/-- Imaginary part of the complex inner product, in actual real L² coordinates. -/
theorem ginibreFullComplex_inner_im (n : ℕ) (f h : GinibreFullComplexL2 n) :
    (inner ℂ f h).im = inner ℝ (ginibreFullComplexRe n f) (ginibreFullComplexIm n h) -
      inner ℝ (ginibreFullComplexIm n f) (ginibreFullComplexRe n h) := by
  have hi := ginibreFullComplex_inner_re n (Complex.I • f) h
  rw [ginibreFullComplexRe_I, ginibreFullComplexIm_I, inner_neg_left] at hi
  have hI : (inner ℂ (Complex.I • f) h).re = (inner ℂ f h).im := by
    rw [inner_smul_left, Complex.conj_I]
    simp [Complex.mul_re]
  rw [hI] at hi
  linarith


@[simp] theorem ginibreFullSymmetricRe_ofReal (n : ℕ) (f : ginibreFullSymmetricValues n) :
    ginibreFullSymmetricRe n (ginibreFullSymmetricOfReal n f) = f := by
  apply Subtype.ext
  exact ginibreFullComplexRe_ofReal n f.val

@[simp] theorem ginibreFullSymmetricIm_ofReal (n : ℕ) (f : ginibreFullSymmetricValues n) :
    ginibreFullSymmetricIm n (ginibreFullSymmetricOfReal n f) = 0 := by
  apply Subtype.ext
  exact ginibreFullComplexIm_ofReal n f.val

@[simp] theorem ginibreFullComplexResolvent_re (n : ℕ) (hn : 0 < n)
    (f : ginibreSymmetricL2 n) :
    ginibreFullSymmetricRe n (ginibreFullComplexResolvent n hn f) =
      ginibreFullSymmetricResolvent n hn (ginibreFullSymmetricRe n f) := by
  change ginibreFullSymmetricRe n (ginibreFullComplexResolventReal n hn f) = _
  simp [ginibreFullComplexResolventReal, map_add]

@[simp] theorem ginibreFullComplexResolvent_im (n : ℕ) (hn : 0 < n)
    (f : ginibreSymmetricL2 n) :
    ginibreFullSymmetricIm n (ginibreFullComplexResolvent n hn f) =
      ginibreFullSymmetricResolvent n hn (ginibreFullSymmetricIm n f) := by
  change ginibreFullSymmetricIm n (ginibreFullComplexResolventReal n hn f) = _
  simp [ginibreFullComplexResolventReal, map_add]

/-- Actual self-adjointness of the complexified full symmetric weak resolvent. -/
theorem ginibreFullComplexResolvent_symmetric (n : ℕ) (hn : 0 < n)
    (f h : ginibreSymmetricL2 n) :
    inner ℂ (ginibreFullComplexResolvent n hn f) h =
      inner ℂ f (ginibreFullComplexResolvent n hn h) := by
  apply Complex.ext
  · have hleft := ginibreFullComplex_inner_re n (ginibreFullComplexResolvent n hn f).val h.val
    have hright := ginibreFullComplex_inner_re n f.val (ginibreFullComplexResolvent n hn h).val
    change (inner ℂ (ginibreFullComplexResolvent n hn f) h).re =
      inner ℝ (ginibreFullSymmetricRe n (ginibreFullComplexResolvent n hn f))
        (ginibreFullSymmetricRe n h) +
        inner ℝ (ginibreFullSymmetricIm n (ginibreFullComplexResolvent n hn f))
          (ginibreFullSymmetricIm n h) at hleft
    change (inner ℂ f (ginibreFullComplexResolvent n hn h)).re =
      inner ℝ (ginibreFullSymmetricRe n f) (ginibreFullSymmetricRe n (ginibreFullComplexResolvent
        n hn h)) +
        inner ℝ (ginibreFullSymmetricIm n f) (ginibreFullSymmetricIm n
          (ginibreFullComplexResolvent n hn h)) at hright
    rw [hleft, hright, ginibreFullComplexResolvent_re, ginibreFullComplexResolvent_im,
      ginibreFullComplexResolvent_re, ginibreFullComplexResolvent_im,
      ginibreFullSymmetricResolvent_symmetric, ginibreFullSymmetricResolvent_symmetric]
  · have hleft := ginibreFullComplex_inner_im n (ginibreFullComplexResolvent n hn f).val h.val
    have hright := ginibreFullComplex_inner_im n f.val (ginibreFullComplexResolvent n hn h).val
    change (inner ℂ (ginibreFullComplexResolvent n hn f) h).im =
      inner ℝ (ginibreFullSymmetricRe n (ginibreFullComplexResolvent n hn f))
        (ginibreFullSymmetricIm n h) -
        inner ℝ (ginibreFullSymmetricIm n (ginibreFullComplexResolvent n hn f))
          (ginibreFullSymmetricRe n h) at hleft
    change (inner ℂ f (ginibreFullComplexResolvent n hn h)).im =
      inner ℝ (ginibreFullSymmetricRe n f) (ginibreFullSymmetricIm n (ginibreFullComplexResolvent
        n hn h)) -
        inner ℝ (ginibreFullSymmetricIm n f) (ginibreFullSymmetricRe n
          (ginibreFullComplexResolvent n hn h)) at hright
    rw [hleft, hright, ginibreFullComplexResolvent_re, ginibreFullComplexResolvent_im,
      ginibreFullComplexResolvent_re, ginibreFullComplexResolvent_im,
      ginibreFullSymmetricResolvent_symmetric, ginibreFullSymmetricResolvent_symmetric]


instance ginibreFullComplexSymmetric_complete (n : ℕ) : CompleteSpace (ginibreSymmetricL2 n) :=
  (isClosed_ginibreSymmetricL2 n).completeSpace_coe

theorem ginibreFullComplexResolvent_isSelfAdjoint (n : ℕ) (hn : 0 < n) :
    IsSelfAdjoint (ginibreFullComplexResolvent n hn) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (ginibreFullComplexResolvent_symmetric n hn)

/-- The actual full symmetric resolvent contracts the original real L² norm. -/
theorem ginibreFullSymmetricResolvent_norm_le (n : ℕ) (hn : 0 < n)
    (f : ginibreFullSymmetricValues n) : ‖ginibreFullSymmetricResolvent n hn f‖ ≤ ‖f‖ :=
  (WithLp.norm_fst_le (α := GinibreFullValueL2 n) (β := GinibreFullGradientL2 n)
    (ginibreFullFormResolvent n hn f.val).val).trans (ginibreFullFormResolvent_norm_le n hn f.val)

/-- The complex extension contracts the original complex Ginibre L² norm. -/
theorem ginibreFullComplexResolvent_norm_le (n : ℕ) (hn : 0 < n)
    (f : ginibreSymmetricL2 n) : ‖ginibreFullComplexResolvent n hn f‖ ≤ ‖f‖ := by
  have hr := ginibreFullComplex_norm_sq n (ginibreFullComplexResolvent n hn f).val
  have hf := ginibreFullComplex_norm_sq n f.val
  change ‖ginibreFullComplexResolvent n hn f‖ ^ 2 =
    ‖ginibreFullSymmetricRe n (ginibreFullComplexResolvent n hn f)‖ ^ 2 +
      ‖ginibreFullSymmetricIm n (ginibreFullComplexResolvent n hn f)‖ ^ 2 at hr
  change ‖f‖ ^ 2 = ‖ginibreFullSymmetricRe n f‖ ^ 2 + ‖ginibreFullSymmetricIm n f‖ ^ 2 at hf
  rw [ginibreFullComplexResolvent_re, ginibreFullComplexResolvent_im] at hr
  have hRe := ginibreFullSymmetricResolvent_norm_le n hn (ginibreFullSymmetricRe n f)
  have hIm := ginibreFullSymmetricResolvent_norm_le n hn (ginibreFullSymmetricIm n f)
  have hReSq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hRe
  have hImSq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hIm
  nlinarith [norm_nonneg f, norm_nonneg (ginibreFullComplexResolvent n hn f)]

theorem ginibreFullComplexResolvent_opNorm_le (n : ℕ) (hn : 0 < n) :
    ‖ginibreFullComplexResolvent n hn‖ ≤ 1 :=
  (ginibreFullComplexResolvent n hn).opNorm_le_bound (by norm_num) (by
    intro f
    simpa using ginibreFullComplexResolvent_norm_le n hn f)

/-- Positivity is inherited from the two genuine real Dirichlet resolvents. -/
theorem ginibreFullComplexResolvent_inner_nonneg (n : ℕ) (hn : 0 < n)
    (f : ginibreSymmetricL2 n) : 0 ≤ (inner ℂ f (ginibreFullComplexResolvent n hn f)).re := by
  have h := ginibreFullComplex_inner_re n f.val (ginibreFullComplexResolvent n hn f).val
  change (inner ℂ f (ginibreFullComplexResolvent n hn f)).re =
    inner ℝ (ginibreFullSymmetricRe n f) (ginibreFullSymmetricRe n (ginibreFullComplexResolvent n
      hn f)) +
      inner ℝ (ginibreFullSymmetricIm n f) (ginibreFullSymmetricIm n (ginibreFullComplexResolvent
        n hn f)) at h
  rw [ginibreFullComplexResolvent_re, ginibreFullComplexResolvent_im] at h
  have hR := ginibreFullValueResolvent_positive n hn (ginibreFullSymmetricRe n f).val
  have hI := ginibreFullValueResolvent_positive n hn (ginibreFullSymmetricIm n f).val
  rw [h]
  change 0 ≤ inner ℝ (ginibreFullSymmetricRe n f).val
      (ginibreFullValueResolvent n hn (ginibreFullSymmetricRe n f).val) +
    inner ℝ (ginibreFullSymmetricIm n f).val
      (ginibreFullValueResolvent n hn (ginibreFullSymmetricIm n f).val)
  rw [hR, hI]
  positivity

theorem ginibreFullComplexResolvent_isPositive (n : ℕ) (hn : 0 < n) :
    (ginibreFullComplexResolvent n hn).IsPositive := by
  refine ⟨ginibreFullComplexResolvent_symmetric n hn, ?_⟩
  intro f
  change 0 ≤ (inner ℂ (ginibreFullComplexResolvent n hn f) f).re
  have h := inner_re_symm (𝕜 := ℂ) (ginibreFullComplexResolvent n hn f) f
  change (inner ℂ (ginibreFullComplexResolvent n hn f) f).re =
    (inner ℂ f (ginibreFullComplexResolvent n hn f)).re at h
  rw [h]
  exact ginibreFullComplexResolvent_inner_nonneg n hn f

/-- The complexified full symmetric resolvent has no kernel. -/
theorem ginibreFullComplexResolvent_eq_zero_iff (n : ℕ) (hn : 0 < n)
    (f : ginibreSymmetricL2 n) : ginibreFullComplexResolvent n hn f = 0 ↔ f = 0 := by
  constructor
  · intro hz
    have hr := congrArg (ginibreFullSymmetricRe n) hz
    have hi := congrArg (ginibreFullSymmetricIm n) hz
    simp only [ginibreFullComplexResolvent_re, map_zero] at hr
    simp only [ginibreFullComplexResolvent_im, map_zero] at hi
    have hRe := (ginibreFullSymmetricResolvent_eq_zero_iff n hn _).mp hr
    have hIm := (ginibreFullSymmetricResolvent_eq_zero_iff n hn _).mp hi
    apply Subtype.ext
    have hdec := ginibreFullComplex_decomposition n f.val
    have hrval : ginibreFullComplexRe n f.val = 0 := congrArg Subtype.val hRe
    have hival : ginibreFullComplexIm n f.val = 0 := congrArg Subtype.val hIm
    rw [hrval, hival, map_zero, smul_zero, zero_add] at hdec
    exact hdec.symm
  · intro hz
    simp [hz]

theorem ginibreFullComplexResolvent_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (ginibreFullComplexResolvent n hn) := by
  intro f h heq
  have hz : ginibreFullComplexResolvent n hn (f - h) = 0 := by
    rw [map_sub, heq, sub_self]
  exact sub_eq_zero.mp ((ginibreFullComplexResolvent_eq_zero_iff n hn (f - h)).mp hz)

/-- Dense range in the actual complex symmetric Ginibre Hilbert space. -/
theorem ginibreFullComplexResolvent_denseRange (n : ℕ) (hn : 0 < n) :
    DenseRange (ginibreFullComplexResolvent n hn) := by
  let K := (ginibreFullComplexResolvent n hn).toLinearMap.range.topologicalClosure
  let : CompleteSpace K := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have horth : Kᗮ = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro a ha
    change a = 0
    have hRa : ginibreFullComplexResolvent n hn a = 0 := by
      apply ext_inner_right ℂ
      intro f
      have hmem : ginibreFullComplexResolvent n hn f ∈ K :=
        Submodule.le_topologicalClosure _ ⟨f, rfl⟩
      have hzero := (Submodule.mem_orthogonal' K a).mp ha _ hmem
      rw [ginibreFullComplexResolvent_symmetric]
      simpa using hzero
    exact (ginibreFullComplexResolvent_eq_zero_iff n hn a).mp hRa
  have hK : K = ⊤ := Submodule.orthogonal_eq_bot_iff.mp horth
  change Dense (Set.range (ginibreFullComplexResolvent n hn))
  rw [dense_iff_closure_eq]
  change closure ((ginibreFullComplexResolvent n hn).toLinearMap.range : Set (ginibreSymmetricL2
    n)) = Set.univ
  rw [← Submodule.topologicalClosure_coe]
  change (K : Set (ginibreSymmetricL2 n)) = Set.univ
  rw [hK]
  rfl


/-- The spectrum of the actual full symmetric resolvent lies in `[0,1]`. -/
theorem ginibreFullComplexResolvent_spectrum (n : ℕ) (hn : 0 < n) :
    spectrum ℝ (ginibreFullComplexResolvent n hn) ⊆ Set.Icc 0 1 :=
  ginibreFull_positive_contraction_spectrum (ginibreFullComplexResolvent n hn)
    (ginibreFullComplexResolvent_isPositive n hn) (ginibreFullComplexResolvent_opNorm_le n hn)

end
end GinibrePoincare

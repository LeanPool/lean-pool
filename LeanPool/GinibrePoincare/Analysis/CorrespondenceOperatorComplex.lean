/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorComplex.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorResolvent
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorComplexification
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupGenerator
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorSpectrum
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupCFC
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
/-!
# Correspondence operator complex

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperatorComplexResolvent_spectrum`,
`correspondenceOperatorGenerator_graph_iff`, `correspondenceOperatorGenerator_dense_domain`,
`correspondenceOperatorGenerator_isClosed`.
-/

@[expose] public section
namespace GinibrePoincare
noncomputable section
open MeasureTheory
open scoped Topology
/-- The complexified value resolvent: `correspondenceOperatorValueResolvent n hn` applied
separately to the real and imaginary parts, as a real-linear operator on
`GinibreFullComplexL2 n`. -/
def correspondenceOperatorComplexResolventReal (n : ℕ) (hn : 0 < n) :
    GinibreFullComplexL2 n →L[ℝ] GinibreFullComplexL2 n :=
  (ginibreFullComplexOfReal n).comp ((correspondenceOperatorValueResolvent n hn).comp
    (ginibreFullComplexRe n)) + Complex.I •
      (ginibreFullComplexOfReal n).comp ((correspondenceOperatorValueResolvent n hn).comp
        (ginibreFullComplexIm n))

theorem correspondenceOperatorComplexResolventReal_I (n : ℕ) (hn : 0 < n) (f : GinibreFullComplexL2
    n) :
    correspondenceOperatorComplexResolventReal n hn (Complex.I • f) =
      Complex.I • correspondenceOperatorComplexResolventReal n hn f := by
  simp only [correspondenceOperatorComplexResolventReal, add_apply,
    ContinuousLinearMap.comp_apply, smul_apply, ginibreFullComplexRe_I,
    ginibreFullComplexIm_I, map_neg, smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]
  abel

/-- Complex scalar multiplication splits into the two real scalar actions. -/
theorem correspondenceOperatorComplex_scalar_decomposition (n : ℕ) (c : ℂ)
    (f : GinibreFullComplexL2 n) :
    c • f = c.re • f + c.im • (Complex.I • f) := by
  conv_lhs => rw [← Complex.re_add_im c, add_smul, mul_smul]
  simp only [Complex.coe_smul]
  rfl

/-- The actual unrestricted weak resolvent is complex-linear. -/
def correspondenceOperatorComplexResolventLinear (n : ℕ) (hn : 0 < n) :
    GinibreFullComplexL2 n →ₗ[ℂ] GinibreFullComplexL2 n where
  toFun := correspondenceOperatorComplexResolventReal n hn
  map_add' := (correspondenceOperatorComplexResolventReal n hn).map_add
  map_smul' := by
    intro c f
    rw [correspondenceOperatorComplex_scalar_decomposition, map_add, map_smul, map_smul,
      correspondenceOperatorComplexResolventReal_I]
    exact (correspondenceOperatorComplex_scalar_decomposition n c _).symm

/-- The complex-linear unrestricted resolvent is continuous on actual L². -/
def correspondenceOperatorComplexResolvent (n : ℕ) (hn : 0 < n) :
    GinibreFullComplexL2 n →L[ℂ] GinibreFullComplexL2 n :=
  { correspondenceOperatorComplexResolventLinear n hn with
    cont := (correspondenceOperatorComplexResolventReal n hn).continuous }

@[simp] theorem correspondenceOperatorComplexResolvent_re (n : ℕ) (hn : 0 < n)
    (f : GinibreFullComplexL2 n) :
    ginibreFullComplexRe n (correspondenceOperatorComplexResolvent n hn f) =
      correspondenceOperatorValueResolvent n hn (ginibreFullComplexRe n f) := by
  change ginibreFullComplexRe n (correspondenceOperatorComplexResolventReal n hn f) = _
  simp [correspondenceOperatorComplexResolventReal, map_add]

@[simp] theorem correspondenceOperatorComplexResolvent_im (n : ℕ) (hn : 0 < n)
    (f : GinibreFullComplexL2 n) :
    ginibreFullComplexIm n (correspondenceOperatorComplexResolvent n hn f) =
      correspondenceOperatorValueResolvent n hn (ginibreFullComplexIm n f) := by
  change ginibreFullComplexIm n (correspondenceOperatorComplexResolventReal n hn f) = _
  simp [correspondenceOperatorComplexResolventReal, map_add]

@[simp] theorem correspondenceOperatorComplexResolvent_ofReal (n : ℕ) (hn : 0 < n)
    (u : GinibreFullValueL2 n) :
    correspondenceOperatorComplexResolvent n hn (ginibreFullComplexOfReal n u) =
      ginibreFullComplexOfReal n (correspondenceOperatorValueResolvent n hn u) := by
  change correspondenceOperatorComplexResolventReal n hn (ginibreFullComplexOfReal n u)=_
  simp [correspondenceOperatorComplexResolventReal]

/-- Actual self-adjointness of the complexified unrestricted weak resolvent. -/
theorem correspondenceOperatorComplexResolvent_symmetric (n : ℕ) (hn : 0 < n)
    (f h : GinibreFullComplexL2 n) :
    inner ℂ (correspondenceOperatorComplexResolvent n hn f) h =
      inner ℂ f (correspondenceOperatorComplexResolvent n hn h) := by
  apply Complex.ext
  · have hleft := ginibreFullComplex_inner_re n (correspondenceOperatorComplexResolvent n hn f) h
    have hright := ginibreFullComplex_inner_re n f (correspondenceOperatorComplexResolvent n hn h)
    change (inner ℂ (correspondenceOperatorComplexResolvent n hn f) h).re =
      inner ℝ (ginibreFullComplexRe n (correspondenceOperatorComplexResolvent n hn f))
          (ginibreFullComplexRe n h) +
        inner ℝ (ginibreFullComplexIm n (correspondenceOperatorComplexResolvent n hn f))
            (ginibreFullComplexIm n h) at hleft
    change (inner ℂ f (correspondenceOperatorComplexResolvent n hn h)).re =
      inner ℝ (ginibreFullComplexRe n f) (ginibreFullComplexRe n
          (correspondenceOperatorComplexResolvent n hn h)) +
        inner ℝ (ginibreFullComplexIm n f) (ginibreFullComplexIm n
            (correspondenceOperatorComplexResolvent n hn h)) at hright
    rw [hleft, hright, correspondenceOperatorComplexResolvent_re,
        correspondenceOperatorComplexResolvent_im,
      correspondenceOperatorComplexResolvent_re, correspondenceOperatorComplexResolvent_im,
      correspondenceOperatorValueResolvent_symmetric,
          correspondenceOperatorValueResolvent_symmetric]
  · have hleft := ginibreFullComplex_inner_im n (correspondenceOperatorComplexResolvent n hn f) h
    have hright := ginibreFullComplex_inner_im n f (correspondenceOperatorComplexResolvent n hn h)
    change (inner ℂ (correspondenceOperatorComplexResolvent n hn f) h).im =
      inner ℝ (ginibreFullComplexRe n (correspondenceOperatorComplexResolvent n hn f))
          (ginibreFullComplexIm n h) -
        inner ℝ (ginibreFullComplexIm n (correspondenceOperatorComplexResolvent n hn f))
            (ginibreFullComplexRe n h) at hleft
    change (inner ℂ f (correspondenceOperatorComplexResolvent n hn h)).im =
      inner ℝ (ginibreFullComplexRe n f) (ginibreFullComplexIm n
          (correspondenceOperatorComplexResolvent n hn h)) -
        inner ℝ (ginibreFullComplexIm n f) (ginibreFullComplexRe n
            (correspondenceOperatorComplexResolvent n hn h)) at hright
    rw [hleft, hright, correspondenceOperatorComplexResolvent_re,
        correspondenceOperatorComplexResolvent_im,
      correspondenceOperatorComplexResolvent_re, correspondenceOperatorComplexResolvent_im,
      correspondenceOperatorValueResolvent_symmetric,
          correspondenceOperatorValueResolvent_symmetric]

theorem correspondenceOperatorComplexResolvent_isSelfAdjoint (n : ℕ) (hn : 0 < n) :
    IsSelfAdjoint (correspondenceOperatorComplexResolvent n hn) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (correspondenceOperatorComplexResolvent_symmetric n hn)

/-- The actual unrestricted resolvent contracts the original real L² norm. -/
theorem correspondenceOperatorValueResolvent_norm_le (n : ℕ) (hn : 0 < n)
    (f : GinibreFullValueL2 n) : ‖correspondenceOperatorValueResolvent n hn f‖ ≤ ‖f‖ :=
  (WithLp.norm_fst_le (α := GinibreFullValueL2 n) (β := GinibreFullGradientL2 n)
    (correspondenceOperatorFormResolvent n hn f).val).trans
      (correspondenceOperatorFormResolvent_norm_le n hn f)

/-- The complex extension contracts the original complex Ginibre L² norm. -/
theorem correspondenceOperatorComplexResolvent_norm_le (n : ℕ) (hn : 0 < n)
    (f : GinibreFullComplexL2 n) : ‖correspondenceOperatorComplexResolvent n hn f‖ ≤ ‖f‖ := by
  have hr := ginibreFullComplex_norm_sq n (correspondenceOperatorComplexResolvent n hn f)
  have hf := ginibreFullComplex_norm_sq n f
  change ‖correspondenceOperatorComplexResolvent n hn f‖ ^ 2 =
    ‖ginibreFullComplexRe n (correspondenceOperatorComplexResolvent n hn f)‖ ^ 2 +
      ‖ginibreFullComplexIm n (correspondenceOperatorComplexResolvent n hn f)‖ ^ 2 at hr
  change ‖f‖ ^ 2 = ‖ginibreFullComplexRe n f‖ ^ 2 + ‖ginibreFullComplexIm n f‖ ^ 2 at hf
  rw [correspondenceOperatorComplexResolvent_re, correspondenceOperatorComplexResolvent_im] at hr
  have hRe := correspondenceOperatorValueResolvent_norm_le n hn (ginibreFullComplexRe n f)
  have hIm := correspondenceOperatorValueResolvent_norm_le n hn (ginibreFullComplexIm n f)
  have hReSq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hRe
  have hImSq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hIm
  nlinarith [norm_nonneg f, norm_nonneg (correspondenceOperatorComplexResolvent n hn f)]

theorem correspondenceOperatorComplexResolvent_opNorm_le (n : ℕ) (hn : 0 < n) :
    ‖correspondenceOperatorComplexResolvent n hn‖ ≤ 1 :=
  (correspondenceOperatorComplexResolvent n hn).opNorm_le_bound (by norm_num) (by
    intro f
    simpa using correspondenceOperatorComplexResolvent_norm_le n hn f)

/-- Positivity is inherited from the two genuine real Dirichlet resolvents. -/
theorem correspondenceOperatorComplexResolvent_inner_nonneg (n : ℕ) (hn : 0 < n)
    (f : GinibreFullComplexL2 n) : 0 ≤ (inner ℂ f (correspondenceOperatorComplexResolvent n hn
        f)).re := by
  have h := ginibreFullComplex_inner_re n f (correspondenceOperatorComplexResolvent n hn f)
  change (inner ℂ f (correspondenceOperatorComplexResolvent n hn f)).re =
    inner ℝ (ginibreFullComplexRe n f) (ginibreFullComplexRe n
        (correspondenceOperatorComplexResolvent n hn f)) +
      inner ℝ (ginibreFullComplexIm n f) (ginibreFullComplexIm n
          (correspondenceOperatorComplexResolvent n hn f)) at h
  rw [correspondenceOperatorComplexResolvent_re, correspondenceOperatorComplexResolvent_im] at h
  have hR := correspondenceOperatorValueResolvent_positive n hn (ginibreFullComplexRe n f)
  have hI := correspondenceOperatorValueResolvent_positive n hn (ginibreFullComplexIm n f)
  rw [h]
  change 0 ≤ inner ℝ (ginibreFullComplexRe n f)
      (correspondenceOperatorValueResolvent n hn (ginibreFullComplexRe n f)) +
    inner ℝ (ginibreFullComplexIm n f)
      (correspondenceOperatorValueResolvent n hn (ginibreFullComplexIm n f))
  rw [hR, hI]
  positivity

theorem correspondenceOperatorComplexResolvent_isPositive (n : ℕ) (hn : 0 < n) :
    (correspondenceOperatorComplexResolvent n hn).IsPositive := by
  refine ⟨correspondenceOperatorComplexResolvent_symmetric n hn, ?_⟩
  intro f
  change 0 ≤ (inner ℂ (correspondenceOperatorComplexResolvent n hn f) f).re
  have h := inner_re_symm (𝕜 := ℂ) (correspondenceOperatorComplexResolvent n hn f) f
  change (inner ℂ (correspondenceOperatorComplexResolvent n hn f) f).re =
    (inner ℂ f (correspondenceOperatorComplexResolvent n hn f)).re at h
  rw [h]
  exact correspondenceOperatorComplexResolvent_inner_nonneg n hn f

/-- The complexified unrestricted resolvent has no kernel. -/
theorem correspondenceOperatorComplexResolvent_eq_zero_iff (n : ℕ) (hn : 0 < n)
    (f : GinibreFullComplexL2 n) : correspondenceOperatorComplexResolvent n hn f = 0 ↔ f = 0 := by
  constructor
  · intro hz
    have hr := congrArg (ginibreFullComplexRe n) hz
    have hi := congrArg (ginibreFullComplexIm n) hz
    simp only [correspondenceOperatorComplexResolvent_re, map_zero] at hr
    simp only [correspondenceOperatorComplexResolvent_im, map_zero] at hi
    have hRe := (correspondenceOperatorValueResolvent_eq_zero_iff n hn _).mp hr
    have hIm := (correspondenceOperatorValueResolvent_eq_zero_iff n hn _).mp hi
    have hdec := ginibreFullComplex_decomposition n f
    have hrval : ginibreFullComplexRe n f = 0 := hRe
    have hival : ginibreFullComplexIm n f = 0 := hIm
    rw [hrval, hival, map_zero, smul_zero, zero_add] at hdec
    exact hdec.symm
  · intro hz
    simp [hz]

theorem correspondenceOperatorComplexResolvent_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (correspondenceOperatorComplexResolvent n hn) := by
  intro f h heq
  have hz : correspondenceOperatorComplexResolvent n hn (f - h) = 0 := by
    rw [map_sub, heq, sub_self]
  exact sub_eq_zero.mp ((correspondenceOperatorComplexResolvent_eq_zero_iff n hn (f - h)).mp hz)

/-- Dense range in the actual unrestricted complex Ginibre Hilbert space. -/
theorem correspondenceOperatorComplexResolvent_denseRange (n : ℕ) (hn : 0 < n) :
    DenseRange (correspondenceOperatorComplexResolvent n hn) := by
  let K := (correspondenceOperatorComplexResolvent n hn).toLinearMap.range.topologicalClosure
  let : CompleteSpace K := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have horth : Kᗮ = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro a ha
    change a = 0
    have hRa : correspondenceOperatorComplexResolvent n hn a = 0 := by
      apply ext_inner_right ℂ
      intro f
      have hmem : correspondenceOperatorComplexResolvent n hn f ∈ K :=
        Submodule.le_topologicalClosure _ ⟨f, rfl⟩
      have hzero := (Submodule.mem_orthogonal' K a).mp ha _ hmem
      rw [correspondenceOperatorComplexResolvent_symmetric]
      simpa using hzero
    exact (correspondenceOperatorComplexResolvent_eq_zero_iff n hn a).mp hRa
  have hK : K = ⊤ := Submodule.orthogonal_eq_bot_iff.mp horth
  change Dense (Set.range (correspondenceOperatorComplexResolvent n hn))
  rw [dense_iff_closure_eq]
  change closure ((correspondenceOperatorComplexResolvent n hn).toLinearMap.range : Set
      (GinibreFullComplexL2 n)) = Set.univ
  rw [← Submodule.topologicalClosure_coe]
  change (K : Set (GinibreFullComplexL2 n)) = Set.univ
  rw [hK]
  rfl

/-- The spectrum of the actual unrestricted resolvent lies in `[0,1]`. -/
theorem correspondenceOperatorComplexResolvent_spectrum (n : ℕ) (hn : 0 < n) :
    spectrum ℝ (correspondenceOperatorComplexResolvent n hn) ⊆ Set.Icc 0 1 :=
  ginibreFull_positive_contraction_spectrum (correspondenceOperatorComplexResolvent n hn)
    (correspondenceOperatorComplexResolvent_isPositive n hn)
        (correspondenceOperatorComplexResolvent_opNorm_le n hn)

/-- Maximal unrestricted complex L² operator associated with the concrete
ordinary weighted weak Dirichlet form. -/
def correspondenceOperatorGenerator (n : ℕ) (hn : 0 < n) :
    GinibreFullComplexL2 n →ₗ.[ℂ] GinibreFullComplexL2 n :=
  resolventGenerator (correspondenceOperatorComplexResolvent n hn)
    (correspondenceOperatorComplexResolvent_injective n hn)

theorem correspondenceOperatorGenerator_graph_iff (n : ℕ) (hn : 0 < n)
    (u v : GinibreFullComplexL2 n) :
    (u, v) ∈ (correspondenceOperatorGenerator n hn).graph ↔
      correspondenceOperatorComplexResolvent n hn (u-v)=u := by
  rw [correspondenceOperatorGenerator, resolventGenerator_graph _
    (correspondenceOperatorComplexResolvent_injective n hn)]
  rfl

theorem correspondenceOperatorGenerator_dense_domain (n : ℕ) (hn : 0 < n) :
    Dense ((correspondenceOperatorGenerator n hn).domain : Set (GinibreFullComplexL2 n)) :=
  resolventGenerator_dense_domain _ (correspondenceOperatorComplexResolvent_injective n hn)
    (correspondenceOperatorComplexResolvent_denseRange n hn)

theorem correspondenceOperatorGenerator_selfAdjoint (n : ℕ) (hn : 0 < n) :
    IsSelfAdjoint (correspondenceOperatorGenerator n hn) :=
  resolventGenerator_selfAdjoint _ (correspondenceOperatorComplexResolvent_isSelfAdjoint n hn)
    (correspondenceOperatorComplexResolvent_injective n hn)
    (correspondenceOperatorComplexResolvent_denseRange n hn)

theorem correspondenceOperatorGenerator_isClosed (n : ℕ) (hn : 0 < n) :
    (correspondenceOperatorGenerator n hn).IsClosed :=
  (correspondenceOperatorGenerator_selfAdjoint n hn).isClosed

end
end GinibrePoincare

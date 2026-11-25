/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Distribution.Distribution

/-! # Commutation of distribution derivatives -/

@[expose] public section

open TopologicalSpace
open scoped Distributions

namespace SGPT.Foundations.Analysis

/-- Mixed distribution derivatives commute by transposing the symmetry of the
second Fréchet derivative of every smooth compactly supported test function. -/
theorem distribution_derivatives_commute
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Opens E) (T : 𝓓'(Ω, ℝ)) (v w : E) :
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) v
        (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) w T) =
      Distribution.lineDerivCLM (n := ⊤) (k := ⊤) w
        (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) v T) := by
  ext φ
  simp only [Distribution.lineDerivCLM_apply, neg_neg]
  congr 1
  ext x
  simp only [TestFunction.lineDerivCLM_apply, le_top, ↓reduceIte]
  have hφdiff : Differentiable ℝ (φ : E → ℝ) :=
    φ.contDiff.differentiable (by simp)
  have htest (a : E) :
      (fun y => (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ a φ) y) =
        fun y => fderiv ℝ (φ : E → ℝ) y a := by
    funext y
    rw [TestFunction.lineDerivCLM_apply]
    simp only [le_top, ↓reduceIte]
    exact (hφdiff y).lineDeriv_eq_fderiv
  have horder : (1 : WithTop ℕ∞) + 1 ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
    norm_num
  have hc : DifferentiableAt ℝ (fderiv ℝ (φ : E → ℝ)) x :=
    (φ.contDiff.contDiffAt.fderiv_right horder).differentiableAt one_ne_zero
  have happ (a : E) :
      DifferentiableAt ℝ (fun y => fderiv ℝ (φ : E → ℝ) y a) x :=
    hc.clm_apply (differentiableAt_const a)
  have hcomp (a b : E) :
      fderiv ℝ (fun y => fderiv ℝ (φ : E → ℝ) y a) x b =
        fderiv ℝ (fderiv ℝ (φ : E → ℝ)) x b a := by
    have h := congrArg (fun L : E →L[ℝ] ℝ => L b)
      (fderiv_clm_apply hc (differentiableAt_const a))
    simpa using h
  change lineDeriv ℝ
      (fun y => (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v φ) y) x w =
    lineDeriv ℝ
      (fun y => (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ w φ) y) x v
  rw [htest v, htest w, (happ v).lineDeriv_eq_fderiv,
    (happ w).lineDeriv_eq_fderiv, hcomp v w, hcomp w v]
  apply φ.contDiff.contDiffAt.isSymmSndFDerivAt
  rw [minSmoothness_of_isRCLikeNormedField]
  exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)

end SGPT.Foundations.Analysis

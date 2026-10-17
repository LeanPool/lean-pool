/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Lambda.PathGronwall

/-!
# PathDerivative

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The response derivative along the whole perturbation path

The provider `Provider.Path.responseJ_derivative` differentiates the scalar
response `t ↦ J(U, a + t h, p, q)` only at the *base* point `t = 0`.  The `J`
sensitivity proof needs the derivative at *every* point of the segment `[0,1]`.
As in `Provider.Lambda.PathGronwall` (which does this for the pure-flux loading
`p = 0`), the path semigroup `(a + t h) + s h = a + (t + s) h` transports the
base-point statement to an arbitrary base point; the present module records the
general `(p, q)` version.

The second declaration is the elementary "mean-value" step used to integrate
the resulting differential inequality: a uniform bound on the derivative over
`[0,1]` bounds the increment.

Every declaration is an internal helper for the Section 2.4 sensitivity
providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Response

open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section24.Sensitivity.Provider.Lambda
open Algsuperdiff.Section24.Sensitivity.Provider.Path
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Differentiability at every point of the path -/

/-- **The scalar response is differentiable at every point of the perturbation
path**, with derivative one half of the `D_h` quadratic form at the current base
point tested against `(p, -q)`.

This is the derivative theorem `Provider.Path.responseJ_derivative` transported
along the path semigroup, exactly as in
`Provider.Lambda.PathGronwall.hasDerivAt_responseJ_perturbCoeffOn`, but for a
general loading `(p, q)` rather than the pure-flux loading `p = 0`. -/
theorem hasDerivAt_responseJ_perturbCoeffOn_pair (dimension : 2 ≤ d) (U : Domain d)
    (a : CoeffOn U) (h : LInfSkewMatrixFieldOn U) (p q : Vec d) (t : ℝ) :
    HasDerivAt (fun τ => responseJ U (perturbCoeffOn U a h τ) p q)
      ((1 / 2 : ℝ) * blockVecDot (p, -q)
        (blockMatVecMul
          (coarseMatrixDerivative U (perturbCoeffOn U a h t) h.1) (p, -q))) t := by
  have hbase := responseJ_derivative dimension U (perturbCoeffOn U a h t) h p q
  have hcongr : (fun s => responseJ U
        (perturbCoeffOn U (perturbCoeffOn U a h t) h s) p q) =
      fun s => responseJ U (perturbCoeffOn U a h (t + s)) p q := by
    funext s
    exact responseJ_perturbCoeffOn_add U a h t s p q
  rw [hcongr] at hbase
  have hbase' : HasDerivAt (fun s => responseJ U (perturbCoeffOn U a h (t + s)) p q)
      ((1 / 2 : ℝ) * blockVecDot (p, -q)
        (blockMatVecMul (coarseMatrixDerivative U (perturbCoeffOn U a h t) h.1)
          (p, -q))) (-t + t) := by
    simpa using hbase
  have hcomp := hbase'.comp_const_add (-t) t
  have hfun : (fun x : ℝ => responseJ U (perturbCoeffOn U a h (t + (-t + x))) p q) =
      fun τ => responseJ U (perturbCoeffOn U a h τ) p q := by
    funext τ
    simp
  rw [hfun] at hcomp
  exact hcomp

/-! ## Integrating a uniform derivative bound -/

/-- **The increment of a differentiable function is controlled by a uniform
bound on its derivative.**  This is the elementary integration step behind the
source's passage from the pointwise derivative bound to the self-referential
inequality for the maximum of `J` along the segment. -/
theorem le_add_of_hasDerivAt_le {y y' : ℝ → ℝ} {B t₁ t₂ : ℝ}
    (hderiv : ∀ τ, HasDerivAt y (y' τ) τ)
    (hbound : ∀ τ, t₁ ≤ τ → τ ≤ t₂ → y' τ ≤ B) (ht : t₁ ≤ t₂) :
    y t₂ ≤ y t₁ + B * (t₂ - t₁) := by
  set z : ℝ → ℝ := fun τ => y τ - B * τ with hz
  have hzderiv : ∀ τ, HasDerivAt z (y' τ - B) τ := by
    intro τ
    have hlin : HasDerivAt (fun σ : ℝ => B * σ) B τ := by
      simpa using (hasDerivAt_id τ).const_mul B
    exact (hderiv τ).sub hlin
  have hanti : AntitoneOn z (Set.Icc t₁ t₂) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc t₁ t₂) ?_ ?_ ?_
    · exact fun τ _ => ((hzderiv τ).continuousAt).continuousWithinAt
    · exact fun τ _ => (hzderiv τ).differentiableAt.differentiableWithinAt
    · intro τ hτ
      rw [interior_Icc] at hτ
      have hmem : τ ∈ Set.Ioo t₁ t₂ := hτ
      rw [(hzderiv τ).deriv]
      have hb := hbound τ hmem.1.le hmem.2.le
      linarith
  have hle : z t₂ ≤ z t₁ :=
    hanti (Set.left_mem_Icc.2 ht) (Set.right_mem_Icc.2 ht) ht
  have hz₁ : z t₁ = y t₁ - B * t₁ := rfl
  have hz₂ : z t₂ = y t₂ - B * t₂ := rfl
  rw [hz₁, hz₂] at hle
  linarith [hle]

end

end Algsuperdiff.Section24.Sensitivity.Provider.Response

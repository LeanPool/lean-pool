/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Path.Closure

/-!
# PathGronwall

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The pure-flux response along the canonical perturbation path

Source: ABK26.  The conditional `lambda_{s,q}` sensitivity estimate compounds a
per-cube estimate along the segment `a + t h`, `t ∈ [0,1]`.  This module
supplies the two facts about that segment that the compounding needs, at a
*general* Chapter 2 domain and for the pure-flux loading `p = 0`:

* the perturbation path is a one-parameter semigroup, `(a + t h) + s h = a + (t
  + s) h`, so the derivative theorem `Provider.Path.responseJ_derivative` —
  which differentiates only at the base point — yields differentiability of `t
  ↦ J(U, a + t h, 0, q)` at *every* `t`, with derivative the `D_h` flux form at
  the current base point;
* a Grönwall step: a pointwise bound `|y'| ≤ K y` on an interval turns into the
  multiplicative bound `y t₂ ≤ exp (K (t₂ - t₁)) * y t₁`.

Nothing in this module asserts differentiability of any multiscale aggregate;
only the single-cube scalar response is differentiated, exactly as required by
the aggregation argument.

Every declaration is an internal helper for the Section 2.4 sensitivity
providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Lambda

open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section24.Sensitivity.Provider.Path
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The perturbation path is a semigroup -/

/-- The canonical perturbation path is additive in its parameter. -/
theorem perturbCoeffOn_perturbCoeffOn (U : Domain d) (a : CoeffOn U)
    (h : LInfSkewMatrixFieldOn U) (t s : ℝ) :
    CoeffOn.AEEq (perturbCoeffOn U (perturbCoeffOn U a h t) h s)
      (perturbCoeffOn U a h (t + s)) := by
  refine Filter.Eventually.of_forall fun x => ?_
  change (a.toCoeffField x + t • h.1.1 x) + s • h.1.1 x =
    a.toCoeffField x + (t + s) • h.1.1 x
  rw [add_smul, add_assoc]

/-- The pure-flux response along the path is unchanged by reparametrizing the
base point. -/
theorem responseJ_perturbCoeffOn_add (U : Domain d) (a : CoeffOn U)
    (h : LInfSkewMatrixFieldOn U) (t s : ℝ) (p q : Vec d) :
    responseJ U (perturbCoeffOn U (perturbCoeffOn U a h t) h s) p q =
      responseJ U (perturbCoeffOn U a h (t + s)) p q :=
  responseJ_eq_ofAEEq (perturbCoeffOn_perturbCoeffOn U a h t s) p q

/-! ## The `D_h` flux form -/

/-- The `D_h` quadratic form at the pure-flux loading `P = (0, -q)`.  This is
the bottom-right entry of `D_h` tested against `q`, i.e. the slope of the
pure-flux response along the perturbation path. -/
def dhFluxForm (U : Domain d) (a : CoeffOn U) (h : LInfSkewMatrixFieldOn U)
    (q : Vec d) : ℝ :=
  blockVecDot ((0 : Vec d), -q)
    (blockMatVecMul (coarseMatrixDerivative U a h.1) ((0 : Vec d), -q))

/-! ## Differentiability of the pure-flux response along the whole path -/

/-- **The pure-flux response is differentiable at every point of the perturbation
path**, with derivative one half of the `D_h` flux form at the current base
point.  This is the derivative theorem transported along the path semigroup. -/
theorem hasDerivAt_responseJ_perturbCoeffOn (dimension : 2 ≤ d) (U : Domain d)
    (a : CoeffOn U) (h : LInfSkewMatrixFieldOn U) (q : Vec d) (t : ℝ) :
    HasDerivAt (fun τ => responseJ U (perturbCoeffOn U a h τ) 0 q)
      ((1 / 2 : ℝ) * dhFluxForm U (perturbCoeffOn U a h t) h q) t := by
  have hbase := responseJ_derivative dimension U (perturbCoeffOn U a h t) h 0 q
  have hcongr : (fun s => responseJ U
        (perturbCoeffOn U (perturbCoeffOn U a h t) h s) 0 q) =
      fun s => responseJ U (perturbCoeffOn U a h (t + s)) 0 q := by
    funext s
    exact responseJ_perturbCoeffOn_add U a h t s 0 q
  rw [hcongr] at hbase
  have hbase' : HasDerivAt (fun s => responseJ U (perturbCoeffOn U a h (t + s)) 0 q)
      ((1 / 2 : ℝ) * blockVecDot ((0 : Vec d), -q)
        (blockMatVecMul (coarseMatrixDerivative U (perturbCoeffOn U a h t) h.1)
          ((0 : Vec d), -q))) (-t + t) := by
    simpa using hbase
  have hcomp := hbase'.comp_const_add (-t) t
  have hfun : (fun x : ℝ => responseJ U (perturbCoeffOn U a h (t + (-t + x))) 0 q) =
      fun τ => responseJ U (perturbCoeffOn U a h τ) 0 q := by
    funext τ
    simp
  rw [hfun] at hcomp
  simpa [dhFluxForm] using hcomp

/-! ## The Grönwall step -/

/-- **Grönwall on an interval.**  A nonnegative differentiable function whose
derivative is bounded by `K` times its value grows at most exponentially. -/
theorem le_exp_mul_of_hasDerivAt_le {y y' : ℝ → ℝ} {K t₁ t₂ : ℝ}
    (hderiv : ∀ τ, HasDerivAt y (y' τ) τ)
    (hbound : ∀ τ, t₁ ≤ τ → τ ≤ t₂ → y' τ ≤ K * y τ) (ht : t₁ ≤ t₂) :
    y t₂ ≤ Real.exp (K * (t₂ - t₁)) * y t₁ := by
  set z : ℝ → ℝ := fun τ => Real.exp (-(K * τ)) * y τ with hz
  have hzderiv : ∀ τ, HasDerivAt z
      (Real.exp (-(K * τ)) * (y' τ - K * y τ)) τ := by
    intro τ
    have hexp : HasDerivAt (fun σ : ℝ => Real.exp (-(K * σ)))
        (Real.exp (-(K * τ)) * (-K)) τ := by
      have h1 : HasDerivAt (fun σ : ℝ => -(K * σ)) (-K) τ := by
        simpa using! ((hasDerivAt_id τ).const_mul K).neg
      simpa using h1.exp
    have := hexp.mul (hderiv τ)
    convert this using 1
    all_goals first | rfl | ring
  have hanti : AntitoneOn z (Set.Icc t₁ t₂) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc t₁ t₂) ?_ ?_ ?_
    · exact fun τ _ => ((hzderiv τ).continuousAt).continuousWithinAt
    · exact fun τ _ => (hzderiv τ).differentiableAt.differentiableWithinAt
    · intro τ hτ
      rw [interior_Icc] at hτ
      have hmem : τ ∈ Set.Ioo t₁ t₂ := hτ
      rw [(hzderiv τ).deriv]
      have hb := hbound τ hmem.1.le hmem.2.le
      have hexp : 0 < Real.exp (-(K * τ)) := Real.exp_pos _
      nlinarith [hb, hexp]
  have hle : z t₂ ≤ z t₁ :=
    hanti (Set.left_mem_Icc.2 ht) (Set.right_mem_Icc.2 ht) ht
  have hexp₂ : 0 < Real.exp (K * t₂) := Real.exp_pos _
  have hstep : Real.exp (-(K * t₂)) * y t₂ ≤ Real.exp (-(K * t₁)) * y t₁ := hle
  have := mul_le_mul_of_nonneg_left hstep hexp₂.le
  calc y t₂ = Real.exp (K * t₂) * (Real.exp (-(K * t₂)) * y t₂) := by
        rw [← mul_assoc, ← Real.exp_add]
        simp
    _ ≤ Real.exp (K * t₂) * (Real.exp (-(K * t₁)) * y t₁) := this
    _ = Real.exp (K * (t₂ - t₁)) * y t₁ := by
        rw [← mul_assoc, ← Real.exp_add]
        ring_nf

end

end Algsuperdiff.Section24.Sensitivity.Provider.Lambda

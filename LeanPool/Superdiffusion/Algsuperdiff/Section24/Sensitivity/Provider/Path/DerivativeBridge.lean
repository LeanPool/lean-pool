/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Path.DhIdentification
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.DeterministicIdentities

/-!
# DerivativeBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Difference-quotient bridge toward `responseJ_derivative`

Source: (`e.derivative.J`, with the corrected factor `1/2` frozen in
`responseJ_derivative`).

This module provides the increment calculus that turns the two-sided
second-difference expansion into a genuine `HasDerivAt`, the reduction of the
scalar response path to the doubled-`mu` path via the deterministic identity
`J(U,p,q;a) = mu(U,(-p,q);a) - p·q`, and the nonnegativity of the quadratic
path term of an admissible field.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Path

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory
open scoped Topology

noncomputable section

variable {d : ℕ}

/-! ## Increment calculus -/

/-- **Second-order increment bridge.**  A one-variable function whose
increment matches a linear slope up to `K t² + |t| e(t)` with `e → 0` at `0`
is differentiable at `0` with that slope.  This is the exact difference
quotient shape produced by the two-sided coarse-matrix expansion. -/
theorem hasDerivAt_of_second_order_bounds {F : ℝ → ℝ} {L K : ℝ} {e : ℝ → ℝ}
    (he : Filter.Tendsto e (𝓝 0) (𝓝 0))
    (hbound : ∀ t : ℝ, |F t - F 0 - t * L| ≤ K * t ^ 2 + |t| * e t) :
    HasDerivAt F L 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hsub : Filter.Tendsto (fun t : ℝ => slope F 0 t - L)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun t : ℝ => K * |t| + e t) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : (t : ℝ) ≠ 0 := ht
      have habs : (0 : ℝ) < |t| := abs_pos.2 ht'
      have hslope : slope F 0 t - L = (F t - F 0 - t * L) / t := by
        rw [slope_def_field, sub_zero]
        field_simp
      rw [Real.norm_eq_abs, hslope, abs_div]
      rw [div_le_iff₀ habs]
      calc
        |F t - F 0 - t * L| ≤ K * t ^ 2 + |t| * e t := hbound t
        _ = (K * |t| + e t) * |t| := by
          rw [← sq_abs]
          ring
    · have h1 : Filter.Tendsto (fun t : ℝ => K * |t|) (𝓝 0) (𝓝 0) := by
        have hc : Continuous fun t : ℝ => K * |t| :=
          continuous_const.mul continuous_abs
        have := hc.tendsto (0 : ℝ)
        simpa using this
      have h2 : Filter.Tendsto (fun t : ℝ => K * |t| + e t) (𝓝 0) (𝓝 0) := by
        simpa using h1.add he
      exact h2.mono_left nhdsWithin_le_nhds
  have := hsub.add_const L
  simpa using this

/-! ## Nonnegativity of the quadratic path term -/

/-- The inverse of the symmetric part of an elliptic matrix has a nonnegative
quadratic form. -/
theorem vecDot_matVecMul_symmPartInv_nonneg {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (ξ : Vec d) :
    0 ≤ vecDot ξ (matVecMul (symmPart A)⁻¹ ξ) := by
  have hdet : IsUnit (symmPart A).det :=
    isUnit_det_symmPart_of_isEllipticMatrix hA
  set z : Vec d := matVecMul (symmPart A)⁻¹ ξ with hz
  have hsz : matVecMul (symmPart A) z = ξ := by
    rw [hz, matVecMul_mul, Matrix.mul_nonsing_inv _ hdet]
    exact Matrix.one_mulVec ξ
  have hcoercive : 0 ≤ vecDot z (matVecMul (symmPart A) z) := by
    rw [vecDot_matVecMul_symmPart]
    calc
      (0 : ℝ) ≤ lam * vecNormSq z :=
        mul_nonneg (le_of_lt hA.1) (vecNormSq_nonneg z)
      _ ≤ vecDot z (matVecMul A z) := hA.2.2.1 z
  calc
    (0 : ℝ) ≤ vecDot z (matVecMul (symmPart A) z) := hcoercive
    _ = vecDot (matVecMul (symmPart A) z) z := vecDot_comm _ _
    _ = vecDot ξ z := by rw [hsz]
    _ = vecDot ξ (matVecMul (symmPart A)⁻¹ ξ) := by rw [hz]

/-- The quadratic path term of any doubled field is nonnegative. -/
theorem pathQuadraticTerm_nonneg {U : Domain d} (a : CoeffOn U)
    (hField : CoeffField d) (X : DoubledField d) :
    0 ≤ pathQuadraticTerm a hField X := by
  change 0 ≤ volumeAverage (U : Set (Vec d)) (pathQuadraticDensity a hField X)
  unfold volumeAverage
  refine mul_nonneg (by positivity) ?_
  refine integral_nonneg_of_ae ?_
  have hae := a.aeElliptic
  filter_upwards [hae] with x hx
  unfold pathQuadraticDensity
  have := vecDot_matVecMul_symmPartInv_nonneg hx
    (matVecMul (hField x) (X.potential x))
  positivity

/-! ## Reduction of the scalar response path to the doubled-`mu` path -/

/-- The scalar response along the canonical path, written through the
deterministic identity `J(U,p,q;a) = mu(U,(-p,q);a) - p·q`. -/
theorem responseJ_perturbCoeffOn_eq_doubledMu_sub {U : Domain d}
    (a : CoeffOn U) (h : LInfSkewMatrixFieldOn U) (t : ℝ) (p q : Vec d) :
    responseJ U (perturbCoeffOn U a h t) p q =
      doubledMu U (perturbCoeffOn U a h t) (-p, q) - vecDot p q :=
  responseJ_eq_doubledMu_neg_left_sub_vecDot U (perturbCoeffOn U a h t) p q

/-- Differentiability of the doubled-`mu` path at `0` transfers to the scalar
response path, with the same slope. -/
theorem hasDerivAt_responseJ_of_hasDerivAt_doubledMu {U : Domain d}
    (a : CoeffOn U) (h : LInfSkewMatrixFieldOn U) (p q : Vec d) {L : ℝ}
    (hmu : HasDerivAt
      (fun t => doubledMu U (perturbCoeffOn U a h t) (-p, q)) L 0) :
    HasDerivAt (fun t => responseJ U (perturbCoeffOn U a h t) p q) L 0 := by
  have hfun : (fun t => responseJ U (perturbCoeffOn U a h t) p q)
      = fun t => doubledMu U (perturbCoeffOn U a h t) (-p, q) - vecDot p q := by
    funext t
    exact responseJ_perturbCoeffOn_eq_doubledMu_sub a h t p q
  rw [hfun]
  simpa using hmu.sub_const (vecDot p q)

/-- The doubled-`mu` value of the path at `t = 0` is the base value. -/
theorem doubledMu_perturbCoeffOn_zero {U : Domain d} (a : CoeffOn U)
    (h : LInfSkewMatrixFieldOn U) (P : BlockVec d) :
    doubledMu U (perturbCoeffOn U a h 0) P = doubledMu U a P :=
  doubledMu_eq_ofAEEq (perturbCoeffOn_zero_aeeq U a h) P

end

end Algsuperdiff.Section24.Sensitivity.Provider.Path

/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Path.Continuity

/-!
# Closure

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The response derivative along the canonical perturbation path

This module assembles the provider theorem `responseJ_derivative`:

* the deterministic identity `J(U,p,q;a) = mu(U,(-p,q);a) - p·q` reduces the
  scalar response path to the doubled-`mu` path;
* the upper second-difference expansion at the base minimizer gives the
  `O(t²)` one-sided bound with slope `ℓ(X₀)`;
* the lower expansion at the perturbed minimizer gives the opposite bound
  with slope `ℓ(X_t)`, and minimizer continuity turns the discrepancy into
  `|t| · O(√|t|)`;
* the `D_h` identification `ℓ(X₀) = ½ (p,-q)·D_h(U;a)(p,-q)` identifies the
  slope with the frozen value.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Path

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory
open scoped Topology

noncomputable section

variable {d : ℕ}

/-- **Differentiability of the doubled-`mu` path at the base point.**  The
slope is the linear response term of any base minimizer. -/
theorem hasDerivAt_doubledMu_perturbCoeffOn {U : Domain d} (a : CoeffOn U)
    (h : LInfSkewMatrixFieldOn U) (p q : Vec d) {X0 : DoubledField d}
    (hX0 : IsDoubledMuMinimizer U a (-p, q) X0) :
    HasDerivAt (fun t => doubledMu U (perturbCoeffOn U a h t) (-p, q))
      (pathLinearTerm a h.1.1 X0) 0 := by
  set F : ℝ → ℝ := fun t => doubledMu U (perturbCoeffOn U a h t) (-p, q) with hF
  set L : ℝ := pathLinearTerm a h.1.1 X0 with hL
  set K : ℝ := pathQuadraticTerm a h.1.1 X0 with hK
  set t0 : ℝ := pathSmallParam a h.1 with ht0def
  set C : ℝ := pathContConst a h.1 (-p, q) with hCdef
  have hKnonneg : 0 ≤ K := pathQuadraticTerm_nonneg a h.1.1 X0
  have hCnonneg : 0 ≤ C := pathContConst_nonneg a h.1 (-p, q)
  have ht0pos : 0 < t0 := pathSmallParam_pos a h.1
  have hF0 : F 0 = doubledMu U a (-p, q) := doubledMu_perturbCoeffOn_zero a h (-p, q)
  set e : ℝ → ℝ := fun t =>
    if |t| ≤ t0 then C * Real.sqrt |t| else |F t - F 0 - t * L| / |t| with hedef
  -- the error function tends to zero
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), |t| ≤ t0 := by
    rw [Metric.eventually_nhds_iff]
    refine ⟨t0, ht0pos, ?_⟩
    intro y hy
    have : |y - 0| < t0 := by simpa [Real.dist_eq] using hy
    simpa using this.le
  have hsqrt : Filter.Tendsto (fun t : ℝ => C * Real.sqrt |t|) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous fun t : ℝ => C * Real.sqrt |t| :=
      continuous_const.mul (Real.continuous_sqrt.comp continuous_abs)
    simpa using hcont.tendsto (0 : ℝ)
  have he : Filter.Tendsto e (𝓝 0) (𝓝 0) := by
    refine hsqrt.congr' ?_
    filter_upwards [hsmall] with t ht
    rw [hedef]
    simp only [ite_eq_left ht]
  -- the second-order bound
  have hbound : ∀ t : ℝ, |F t - F 0 - t * L| ≤ K * t ^ 2 + |t| * e t := by
    intro t
    by_cases hcase : |t| ≤ t0
    · have hval : e t = C * Real.sqrt |t| := by
        rw [hedef]; simp only [ite_eq_left hcase]
      by_cases htz : t = 0
      · subst htz
        simp
      · obtain ⟨Xt, hXt⟩ :=
          (doubledMuTheory U (perturbCoeffOn U a h t)).minimizer_exists (-p, q)
        have hupper := doubledMu_perturbCoeffOn_expansion_upper a h t (-p, q) hX0
        have hlower := doubledMu_perturbCoeffOn_expansion_lower a h t (-p, q) hXt
        have hqt : 0 ≤ pathQuadraticTerm a h.1.1 Xt :=
          pathQuadraticTerm_nonneg a h.1.1 Xt
        have hcont := abs_pathLinearTerm_sub_le a h (-p, q) hcase htz hX0 hXt
        have hsq : 0 ≤ Real.sqrt |t| := Real.sqrt_nonneg _
        have habs : 0 ≤ |t| := abs_nonneg t
        have hprod : -(|t| * (C * Real.sqrt |t|)) ≤
            t * (pathLinearTerm a h.1.1 Xt - L) := by
          have h1 : -(|t * (pathLinearTerm a h.1.1 Xt - L)|) ≤
              t * (pathLinearTerm a h.1.1 Xt - L) := neg_abs_le _
          have h2 : |t * (pathLinearTerm a h.1.1 Xt - L)| =
              |t| * |pathLinearTerm a h.1.1 Xt - L| := abs_mul _ _
          have h3 : |t| * |pathLinearTerm a h.1.1 Xt - L| ≤
              |t| * (C * Real.sqrt |t|) :=
            mul_le_mul_of_nonneg_left hcont habs
          linarith
        have hKt : 0 ≤ K * t ^ 2 := by positivity
        have hCt : 0 ≤ |t| * (C * Real.sqrt |t|) := by positivity
        rw [hval, hF0]
        refine abs_le.2 ⟨?_, ?_⟩
        · nlinarith [hlower, hprod, hqt, hKt]
        · nlinarith [hupper, hCt]
    · have hval : e t = |F t - F 0 - t * L| / |t| := by
        rw [hedef]; simp only [ite_eq_right hcase]
      have htpos : 0 < |t| := lt_of_lt_of_le ht0pos (le_of_not_ge hcase)
      have hKt : 0 ≤ K * t ^ 2 := by positivity
      rw [hval, mul_div_cancel₀ _ htpos.ne']
      linarith
  exact hasDerivAt_of_second_order_bounds he hbound

/-- **Provider theorem: the response derivative along the canonical
perturbation path.**  The scalar response functional is differentiable at the
base coefficient in the direction of any bounded skew perturbation, with
derivative `½ (p,-q) · D_h(U;a) (p,-q)`. -/
theorem responseJ_derivative {d : ℕ} (_dimension : 2 ≤ d) (U : Domain d)
    (a : CoeffOn U) (h : LInfSkewMatrixFieldOn U) (p q : Vec d) :
    HasDerivAt
      (fun t => responseJ U (perturbCoeffOn U a h t) p q)
      ((1 / 2 : ℝ) * blockVecDot (p, -q)
        (blockMatVecMul (coarseMatrixDerivative U a h.1) (p, -q))) 0 := by
  obtain ⟨X0, hX0⟩ := (doubledMuTheory U a).minimizer_exists (-p, q)
  have hslope : pathLinearTerm a h.1.1 X0 =
      (1 / 2 : ℝ) * blockVecDot (p, -q)
        (blockMatVecMul (coarseMatrixDerivative U a h.1) (p, -q)) :=
    pathLinearTerm_isDoubledMuMinimizer_eq a h p q hX0
  have hmu := hasDerivAt_doubledMu_perturbCoeffOn a h p q hX0
  rw [hslope] at hmu
  exact hasDerivAt_responseJ_of_hasDerivAt_doubledMu a h p q hmu

end

end Algsuperdiff.Section24.Sensitivity.Provider.Path

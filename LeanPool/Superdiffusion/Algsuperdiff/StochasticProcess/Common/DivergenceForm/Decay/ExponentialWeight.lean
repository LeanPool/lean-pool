/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.WeightedEnergy

/-!
# ExponentialWeight

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Exponentially weighted mass estimate

The weight of the Agmon-type estimate is a localized exponential
`eta * chi`, where `eta` is a smooth compactly supported localization inside
the domain and `chi` is a smooth positive factor obeying the logarithmic
gradient bound `|grad chi| <= kappa * chi`.  The exponential
`chi = exp (kappa * psi)` of a smooth function with `|grad psi| <= 1` is the
model case.

The mass form of the weighted energy inequality then absorbs the exponential
contribution as soon as `8 * Lam ^ 2 * kappa ^ 2 <= lam * mass`, leaving only
the contribution of the localization gradient.  This is the quantitative
statement behind the exponential decay of a solution away from the region
where the localization is not yet constant.

## Main results

- `DivergenceFormProcess.Decay.exponentialWeight_gradient_le`
-/

noncomputable section

namespace DivergenceFormProcess.Decay

open HCPolySupport MeasureTheory
open DivergenceFormProcess.Form
open scoped ENNReal

variable {d : ℕ} {U : Set (Vec d)}

/-- The coordinate gradient of a smooth compactly supported function has
compact support, and so does its squared norm. -/
theorem hasCompactSupport_gradSq {f : Vec d → ℝ}
    (hf : HasCompactSupport f) :
    HasCompactSupport
      (fun x => vecNormSq (fun i => (fderiv ℝ f x) (basisVec i))) := by
  refine HasCompactSupport.intro hf.isCompact ?_
  intro x hx
  rw [fderiv_of_notMem_tsupport ℝ hx]
  simp only [zero_apply, vecNormSq, vecDot, mul_zero,
    Finset.sum_const_zero]

/-- The squared coordinate gradient of a smooth function is continuous. -/
theorem continuous_gradSq {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (fun x => vecNormSq (fun i => (fderiv ℝ f x) (basisVec i))) := by
  have hcoord : ∀ i : Fin d,
      Continuous (fun x => (fderiv ℝ f x) (basisVec i)) := by
    intro i
    exact (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  simp only [vecNormSq, vecDot]
  exact continuous_finsetSum _ fun i _ => (hcoord i).mul (hcoord i)

section Localized

variable {eta chi : Vec d → ℝ}

/-- Multiplying by a second factor does not enlarge the topological support. -/
theorem tsupport_mul_subset {V : Set (Vec d)} (hetaU : tsupport eta ⊆ V) :
    tsupport (fun x => eta x * chi x) ⊆ V := by
  refine (closure_mono ?_).trans hetaU
  intro x hx
  simp only [Function.mem_support, ne_eq] at hx ⊢
  intro h
  exact hx (by rw [h]; ring)

/-- The localized weight is admissible when the localization is supported in
the domain. -/
theorem isAdmissibleMultiplier_localized_of_tsupport_subset
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U)
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta) (hetaCompact : HasCompactSupport eta)
    (hetaU : tsupport eta ⊆ U) (hchi : ContDiff ℝ (⊤ : ℕ∞) chi) :
    IsAdmissibleMultiplier U u (fun x => (eta x * chi x) ^ 2) :=
  isAdmissibleMultiplier_sq_of_tsupport_subset hU u (heta.mul hchi)
    hetaCompact.mul_right (tsupport_mul_subset hetaU)

end Localized

section Exponential

variable {eta psi : Vec d → ℝ}

/-- The exponential of a smooth function is smooth. -/
theorem contDiff_exponentialWeight (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi)
    (kappa : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => Real.exp (kappa * psi x)) :=
  (contDiff_const.mul hpsi).exp

/-- The exponential weight of a smooth function obeys the logarithmic
gradient bound with constant `kappa` at every point where the phase has unit
gradient. -/
theorem exponentialWeight_gradient_le (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi)
    {x : Vec d}
    (hpsiGrad : vecNormSq (fun i => (fderiv ℝ psi x) (basisVec i)) ≤ 1)
    (kappa : ℝ) :
    vecNormSq (fun i =>
        (fderiv ℝ (fun y => Real.exp (kappa * psi y)) x) (basisVec i)) ≤
      kappa ^ 2 * Real.exp (kappa * psi x) ^ 2 := by
  have hd : HasFDerivAt psi (fderiv ℝ psi x) x :=
    (hpsi.differentiable (by simp) x).hasFDerivAt
  have hp : HasFDerivAt (fun y => kappa * psi y) (kappa • fderiv ℝ psi x) x := by
    simpa using hd.const_mul kappa
  have hfd : fderiv ℝ (fun y => Real.exp (kappa * psi y)) x =
      Real.exp (kappa * psi x) • (kappa • fderiv ℝ psi x) := hp.exp.fderiv
  have hshape : (fun i =>
        (fderiv ℝ (fun y => Real.exp (kappa * psi y)) x) (basisVec i)) =
      (Real.exp (kappa * psi x) * kappa) •
        fun i => (fderiv ℝ psi x) (basisVec i) := by
    funext i
    rw [hfd]
    simp only [smul_apply, smul_eq_mul, Pi.smul_apply]
    ring
  rw [hshape, vecNormSq_smul]
  have hnn : (0 : ℝ) ≤ (Real.exp (kappa * psi x) * kappa) ^ 2 := sq_nonneg _
  calc
    (Real.exp (kappa * psi x) * kappa) ^ 2 *
        vecNormSq (fun i => (fderiv ℝ psi x) (basisVec i)) ≤
        (Real.exp (kappa * psi x) * kappa) ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hpsiGrad hnn
    _ = kappa ^ 2 * Real.exp (kappa * psi x) ^ 2 := by ring

/-- The canonical admissible rate.  The Agmon rate
`sqrt (lam * mass) / (2 * sqrt 2 * Lam)` saturates the absorption
condition. -/
theorem agmonRate_admissible {lam Lam mass : ℝ} (hlam : 0 ≤ lam)
    (hmass : 0 ≤ mass) (hLam : 0 < Lam) :
    8 * Lam ^ 2 *
        (Real.sqrt (lam * mass) / (2 * Real.sqrt 2 * Lam)) ^ 2 ≤ lam * mass := by
  have hprod : (0 : ℝ) ≤ lam * mass := mul_nonneg hlam hmass
  have hden : (2 * Real.sqrt 2 * Lam) ^ 2 = 8 * Lam ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [div_pow, Real.sq_sqrt hprod, hden]
  have hLam2 : (0 : ℝ) < 8 * Lam ^ 2 := by positivity
  rw [mul_div_cancel₀ _ hLam2.ne']

end Exponential

end DivergenceFormProcess.Decay

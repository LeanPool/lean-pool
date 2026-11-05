/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.LinftyResolventBound
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.ResolventH10Representative
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.ScalarWeakSolution

/-!
# ShiftedResidualBound

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Bounded scalar residuals for the shifted resolvent

This file removes the zeroth-order term from the shifted weak resolvent
equation. If the scalar forcing is almost everywhere bounded by `C`, then its
unshifted residual is almost everywhere bounded by `2 * C`.

The conclusions concern the chosen Sobolev representative only almost
everywhere. No pointwise measurability or continuity is asserted.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory

variable {d : ℕ} {U : Set (Vec d)}

/-- The scalar residual of an `H¹₀` representative of the shifted resolvent
is almost everywhere bounded by twice the forcing bound. -/
theorem abs_sub_alpha_mul_toFun_le_two_mul_ae (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    {alpha lam Lam C : ℝ} (hAlpha : 0 < alpha) (hLam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a) (f : ScalarL2 U)
    (hC : 0 ≤ C) (hf : ∀ᵐ x ∂volumeMeasureOn U, |f x| ≤ C)
    (u : H10Function U)
    (hu : u.toH1Function.toScalarL2 =
      alphaShiftedResolvent a hAlpha hLam hEll f) :
    ∀ᵐ x ∂volumeMeasureOn U,
      |f x - alpha * u.toH1Function.toFun x| ≤ 2 * C := by
  have hres := abs_alpha_mul_alphaShiftedResolvent_le_ae
    a hU hAlpha hLam hEll f C hC hf
  have huAe : ∀ᵐ x ∂volumeMeasureOn U,
      u.toH1Function.toFun x = alphaShiftedResolvent a hAlpha hLam hEll f x := by
    filter_upwards [u.toH1Function.coeFn_toScalarL2] with x hx
    exact hx.symm.trans (congrArg (fun g : ScalarL2 U => g x) hu)
  filter_upwards [hf, hres, huAe] with x hfx hresx hux
  rw [hux]
  calc
    |f x - alpha * alphaShiftedResolvent a hAlpha hLam hEll f x| ≤
        |f x| + |alpha * alphaShiftedResolvent a hAlpha hLam hEll f x| :=
      abs_sub _ _
    _ ≤ C + C := add_le_add hfx hresx
    _ = 2 * C := by ring

/-- A bounded forcing admits an `H¹₀` representative of its shifted
resolvent which solves the unshifted scalar equation with almost everywhere
bounded residual. -/
theorem exists_h10Function_scalarForced_residual_bound
    (hU : IsOpenBoundedConvexDomain U) (a : CoeffField d)
    {alpha lam Lam C : ℝ} (hAlpha : 0 < alpha) (hLam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a) (f : ScalarL2 U)
    (hC : 0 ≤ C) (hf : ∀ᵐ x ∂volumeMeasureOn U, |f x| ≤ C) :
    ∃ u : H10Function U,
      u.toH1Function.toScalarL2 =
          alphaShiftedResolvent a hAlpha hLam hEll f ∧
        IsAlphaShiftedWeakSolution a U alpha f
          (ZeroTraceSobolev.ofH10Function u) ∧
        IsScalarForcedWeakSolution a U
          (fun x => f x - alpha * u.toH1Function.toFun x)
          u.toH1Function ∧
        ∀ᵐ x ∂volumeMeasureOn U,
          |f x - alpha * u.toH1Function.toFun x| ≤ 2 * C := by
  obtain ⟨u, -, hweak, hu⟩ :=
    exists_h10Function_alphaShiftedResolvent hU a hAlpha hLam hEll f
  refine ⟨u, hu, hweak, ?_, ?_⟩
  · exact isScalarForcedWeakSolution_sub_alpha_mul_of_isAlphaShiftedWeakSolution
      u hweak
  · exact abs_sub_alpha_mul_toFun_le_two_mul_ae
      a hU hAlpha hLam hEll f hC hf u hu

end DivergenceFormProcess.Form

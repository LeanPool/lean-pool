/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Assembly.EnergyBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.UnitCubeMultiscale.Lambda.UnitCubeLambdaCharacterization
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.UnitCubeMultiscale.CompatibleFamily
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Public
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Localization
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.CoarsePoincare

/-!
# GaugeBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Coarse Poincaré at the sensitivity gauge `(s, q) = (3/8, 2)`

Two layers are proved:

* the **general layer**, at an arbitrary triadic cube `Q` and an arbitrary
  CoarseGraining coefficient family `F`, in CoarseGraining gauge vocabulary
  (`Ch02.lambdaSq Q s q F`);
* the **frozen unit-cube layer**, obtained from the general layer by choosing a
  compatible family (`exists_compatibleTriadicCoeffFamily`) and rewriting the
  gauge with `unitCubeLambda_characterization`.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Assembly

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- CoarseGraining writes coarse-gauge powers with explicit `Real.rpow`; Mathlib's
`^`-notation lemmas do not rewrite against it.  This definitional bridge lets
`simp only` move between the two. -/
private theorem rpow_eq_pow (x y : ℝ) : Real.rpow x y = x ^ y := rfl

/-- `x ^ (-(1/2))` is `√(x⁻¹)` for nonnegative `x`, including at `x = 0`. -/
theorem rpow_neg_half_eq_sqrt_inv {x : ℝ} (hx : 0 ≤ x) :
    Real.rpow x (-(1 / 2 : ℝ)) = Real.sqrt x⁻¹ := by
  simp only [rpow_eq_pow]
  rw [Real.rpow_neg hx, Real.sqrt_inv, ← Real.sqrt_eq_rpow]

/-- The gauge exponent pair used by the frozen sensitivity statements. -/
theorem sensitivityExponent_isAdmissible :
    (Ch02.MultiscaleExponent.finite 2).IsAdmissible := by
  simp [Ch02.MultiscaleExponent.IsAdmissible]

/-- The scale-free discount factor of the coarse Poincaré right-hand side at the
sensitivity gauge is positive. -/
theorem poincareDiscountFactor_sensitivity_pos :
    0 < Ch03.poincareDiscountFactor (3 / 8) (.finite 2) := by
  have hbase : 0 < Ch02.geometricDiscount (3 / 8 : ℝ) 2 := by
    have h3 : Real.rpow (3 : ℝ) (-(3 / 8 : ℝ) * 2) < 1 := by
      simp only [rpow_eq_pow]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    simpa [Ch02.geometricDiscount] using sub_pos.2 h3
  simpa [Ch03.poincareDiscountFactor, rpow_eq_pow] using
    Real.rpow_pos_of_pos hbase (-(1 / 2 : ℝ))

/-- **General coarse Poincaré at the sensitivity gauge.**  At an arbitrary
triadic cube and an arbitrary coefficient family, the concrete negative Besov
norm of the gradient of a response maximizer is controlled by
`λ_{3/8,2}^{-1/2} √J`, up to the scale-free discount constant. -/
theorem scaleNormalizedNegativeBesovVectorNorm_solutionGradient_le
    [NeZero d] (Q : TriadicCube d) (F : Ch03.CoeffFamily d) {p q : Vec d}
    {v : Ch03.CubeSolution Q F}
    (hv : IsResponseMaximizer (cubeDomain Q) (F.coeffOn Q) p q v) :
    Ch03.scaleNormalizedNegativeBesovVectorNorm Q (3 / 8) (.finite 2)
        (Ch03.solutionGradientField v) ≤
      Ch03.poincareDiscountFactor (3 / 8) (.finite 2) *
        Real.sqrt ((Ch02.lambdaSq Q (3 / 8) (.finite 2) F)⁻¹) *
        (2 * Real.sqrt (responseJ (cubeDomain Q) (F.coeffOn Q) p q)) := by
  have hpoincare :=
    Ch03.coarsePoincareGradient_negativeBesov_le (Q := Q) (a := F)
      (s := (3 / 8 : ℝ)) (q := .finite 2) v (by norm_num)
      sensitivityExponent_isAdmissible
  have hlam : 0 ≤ Ch02.lambdaSq Q (3 / 8) (.finite 2) F :=
    Ch02.lambdaSq_nonneg Q F (by norm_num) sensitivityExponent_isAdmissible
  have hfactor :
      Ch03.poincareLowerEllipticityFactor Q F (3 / 8) (.finite 2) =
        Real.sqrt ((Ch02.lambdaSq Q (3 / 8) (.finite 2) F)⁻¹) := by
    simpa [Ch03.poincareLowerEllipticityFactor] using rpow_neg_half_eq_sqrt_inv hlam
  refine hpoincare.trans ?_
  rw [Ch03.coarsePoincareGradientRHS, hfactor]
  refine mul_le_mul_of_nonneg_left
    (solutionEnergyNorm_le_two_mul_sqrt_responseJ Q F hv) ?_
  exact mul_nonneg poincareDiscountFactor_sensitivity_pos.le (Real.sqrt_nonneg _)

/-- **Frozen unit-cube coarse Poincaré at the sensitivity gauge.**  The same
estimate with the frozen gauge `unitCubeLambda (3/8) (.finite 2) a`, for a
coefficient given directly on the origin cube. -/
theorem scaleNormalizedNegativeBesovVectorNorm_solutionGradient_unitCube_le
    [NeZero d] (a : CoeffOn (cubeDomain (originCube d 0))) {p q : Vec d}
    (F : Ch03.CoeffFamily d) (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    {v : Ch03.CubeSolution (originCube d 0) F}
    (hv : IsResponseMaximizer (cubeDomain (originCube d 0)) (F.coeffOn (originCube d 0)) p q v) :
    Ch03.scaleNormalizedNegativeBesovVectorNorm (originCube d 0) (3 / 8) (.finite 2)
        (Ch03.solutionGradientField v) ≤
      Ch03.poincareDiscountFactor (3 / 8) (.finite 2) *
        Real.sqrt ((unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
        (2 * Real.sqrt (responseJ (cubeDomain (originCube d 0)) a p q)) := by
  have hgauge := unitCubeLambda_characterization (3 / 8 : ℝ) (.finite 2) a F hF
  have hJ : responseJ (cubeDomain (originCube d 0)) (F.coeffOn (originCube d 0)) p q =
      responseJ (cubeDomain (originCube d 0)) a p q := responseJ_eq_ofAEEq hF p q
  have hmain :=
    scaleNormalizedNegativeBesovVectorNorm_solutionGradient_le
      (originCube d 0) F hv
  rw [hgauge, ← hJ]
  exact hmain

end

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Assembly

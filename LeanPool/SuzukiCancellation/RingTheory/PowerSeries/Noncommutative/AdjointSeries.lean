/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.SeriesAction
public import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.ExponentialDerivative
public import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.BernoulliSeries

/-!
# Scalar functions of the graded adjoint

The coefficientwise adjoint of a positive series is itself a positive operator
series. Scalar functional calculus and the Cauchy action therefore give an
associative calculus for its locally degree-raising adjoint action.
-/

@[expose] public noncomputable section

namespace FQFP

open Finset PowerSeries

variable {A : Type*} [Ring A] [Algebra ℚ A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The operator series whose coefficients are the adjoints of the input coefficients. -/
def adjointSeries (W : PowerSeries A) : PowerSeries (Module.End ℚ A) :=
  mapSeriesLinear (LieAlgebra.ad ℚ A).toLinearMap W

@[simp]
theorem coeff_adjointSeries (W : PowerSeries A) (n : ℕ) :
    coeff n (adjointSeries W) = LieAlgebra.ad ℚ A (coeff n W) := by
  simp [adjointSeries]

theorem constantCoeff_adjointSeries (W : PowerSeries A) (hW : constantCoeff W = 0) :
    constantCoeff (adjointSeries W) = 0 := by
  simp [adjointSeries, hW]

/-- Operator Cauchy action is the adjoint action in the noncommutative series algebra. -/
theorem seriesLinearAction_adjointSeries (W V : PowerSeries A) :
    seriesLinearAction (adjointSeries W) V = LieAlgebra.ad ℚ (PowerSeries A) W V := by
  ext n
  simp only [coeff_seriesLinearAction, coeff_adjointSeries, LieAlgebra.ad,
    LieModule.toEnd_apply_apply, Ring.lie_def, map_sub, coeff_mul, sum_sub_distrib]
  congr 1
  exact Finset.Nat.sum_antidiagonal_swap
    (f := fun ij : ℕ × ℕ ↦ coeff ij.1 V * coeff ij.2 W) (n := n)

/-- Operator powers act as iterated adjoints of the whole formal series. -/
theorem seriesLinearAction_adjointSeries_pow (W V : PowerSeries A) (j : ℕ) :
    seriesLinearAction (adjointSeries W ^ j) V = (LieAlgebra.ad ℚ (PowerSeries A) W ^ j) V := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', seriesLinearAction_mul, ih, seriesLinearAction_adjointSeries,
      pow_succ', mul_apply_eq_comp]

/-- Applying a scalar formal function of the positive graded adjoint. -/
def adjointSeriesApply (c : PowerSeries ℚ) (W V : PowerSeries A) : PowerSeries A :=
  seriesLinearAction (scalarSeriesApply c (fun k ↦ coeff k (adjointSeries W))) V

/-- Scalar products act as compositions of graded adjoint functions. -/
theorem adjointSeriesApply_mul (c d : PowerSeries ℚ) (W V : PowerSeries A) :
    adjointSeriesApply (c * d) W V = adjointSeriesApply c W (adjointSeriesApply d W V) := by
  simp only [adjointSeriesApply, scalarSeriesApply_mul, seriesLinearAction_mul]

@[simp]
theorem adjointSeriesApply_one (W V : PowerSeries A) : adjointSeriesApply 1 W V = V := by
  unfold adjointSeriesApply
  rw [← scalarSeriesApplyHom_apply, map_one, seriesLinearAction_one]

/-- Each coefficient is a finite sum of iterated adjoints. -/
theorem coeff_adjointSeriesApply (c : PowerSeries ℚ) (W V : PowerSeries A)
    (hW : constantCoeff W = 0) (n : ℕ) :
    coeff n (adjointSeriesApply c W V) = ∑ j ∈ range (n + 1), coeff j c •
      coeff n ((LieAlgebra.ad ℚ (PowerSeries A) W ^ j) V) := by
  rw [adjointSeriesApply,
    coeff_seriesLinearAction_scalarSeriesApply c _ (constantCoeff_adjointSeries W hW)]
  simp only [seriesLinearAction_adjointSeries_pow]

/-- The Bernoulli function inverts the divided exponential of the graded adjoint. -/
theorem adjointSeriesApply_bernoulli_exponentialDivX (W V : PowerSeries A) :
    adjointSeriesApply (bernoulliPowerSeries ℚ) W (adjointSeriesApply exponentialDivX W V) = V := by
  rw [← adjointSeriesApply_mul, bernoulliPowerSeries_mul_exponentialDivX,
    adjointSeriesApply_one]

/-- Iterated adjoints of positive inputs have minimum degree one greater than their depth. -/
theorem coeff_ad_pow_eq_zero_of_le (W V : PowerSeries A)
    (hW : constantCoeff W = 0) (hV : constantCoeff V = 0) (j n : ℕ) (hn : n ≤ j) :
    coeff n ((LieAlgebra.ad ℚ (PowerSeries A) W ^ j) V) = 0 := by
  rw [← seriesLinearAction_adjointSeries_pow, coeff_seriesLinearAction]
  apply sum_eq_zero
  intro ij hij
  have hij' := mem_antidiagonal.mp hij
  by_cases hi : ij.1 < j
  · have hz : coeff ij.1 (adjointSeries W ^ j) = 0 := by
      rw [← positiveSeries_coeff _ (constantCoeff_adjointSeries W hW)]
      exact coeff_positiveSeries_pow_eq_zero_of_lt _ _ _ hi
    rw [hz, LinearMap.zero_apply]
  · rw [show ij.2 = 0 by lia, coeff_zero_eq_constantCoeff_apply, hV, map_zero]

/-- The divided exponential of the adjoint is the right differential exponential. -/
theorem adjointSeriesApply_exponentialDivX (D : A →ₗ[ℚ] A)
    (hD : ∀ a b, D (a * b) = D a * b + a * D b)
    (W : PowerSeries A) (hW : constantCoeff W = 0) :
    adjointSeriesApply exponentialDivX W (mapSeriesLinear D W) =
      mapSeriesLinear D (formalExp W) * formalExp (-W) := by
  ext n
  rw [coeff_adjointSeriesApply _ _ _ hW, sum_range_succ,
    coeff_rightLogarithmicDerivative_formalExp D hD W hW n]
  simp only [exponentialDivX, coeff_mk]
  rw [coeff_ad_pow_eq_zero_of_le W (mapSeriesLinear D W) hW
    (by simp [hW]) n n le_rfl, smul_zero, add_zero]

/-- Exponential adjoint action is formal conjugation. -/
theorem adjointSeriesApply_exp (W V : PowerSeries A) (hW : constantCoeff W = 0) :
    adjointSeriesApply (exp ℚ) W V = formalExp W * V * formalExp (-W) := by
  ext n
  rw [coeff_adjointSeriesApply _ _ _ hW, coeff_formalExp_conjugate W V hW n]
  simp only [coeff_exp, Algebra.algebraMap_self, RingHom.id_apply, one_div]

theorem adjointSeriesApply_add (c d : PowerSeries ℚ) (W V : PowerSeries A) :
    adjointSeriesApply (c + d) W V = adjointSeriesApply c W V + adjointSeriesApply d W V := by
  simp only [adjointSeriesApply, ← scalarSeriesApplyHom_apply, map_add, seriesLinearAction_add]

theorem adjointSeriesApply_smul (r : ℚ) (c : PowerSeries ℚ) (W V : PowerSeries A) :
    adjointSeriesApply (r • c) W V = r • adjointSeriesApply c W V := by
  simp only [adjointSeriesApply, scalarSeriesApply_smul, seriesLinearAction_smul]

/-- The symmetric product differential equation gives the Bernoulli adjoint equation for its log. -/
theorem mapSeriesLinear_formalLog_eq_adjointSeriesApply (D : A →ₗ[ℚ] A)
    (hD : ∀ a b, D (a * b) = D a * b + a * D b)
    (E X₁ : PowerSeries A) (hE : constantCoeff E = 1)
    (hd : mapSeriesLinear D E = (2 : ℚ)⁻¹ • (X₁ * E + E * X₁)) :
    mapSeriesLinear D (formalLog E) =
      adjointSeriesApply (bernoulliPowerSeries ℚ + (2 : ℚ)⁻¹ • X) (formalLog E) X₁ := by
  have hW : constantCoeff (formalLog E) = 0 := constantCoeff_formalLog E
  have he : formalExp (formalLog E) = E := formalExp_formalLog E hE
  have hei : E * formalExp (-formalLog E) = 1 := by
    calc
      _ = formalExp (formalLog E) * formalExp (-formalLog E) :=
        congrArg (· * formalExp (-formalLog E)) he.symm
      _ = 1 := formalExp_mul_neg _ hW
  have hphi : adjointSeriesApply exponentialDivX (formalLog E) (mapSeriesLinear D (formalLog E)) =
      adjointSeriesApply ((2 : ℚ)⁻¹ • (1 + exp ℚ)) (formalLog E) X₁ := by
    rw [adjointSeriesApply_exponentialDivX D hD _ hW, he, hd,
      adjointSeriesApply_smul, adjointSeriesApply_add, adjointSeriesApply_one,
      adjointSeriesApply_exp _ _ hW]
    rw [smul_mul_assoc, add_mul, mul_assoc, hei, mul_one, he]
  calc
    _ = adjointSeriesApply (bernoulliPowerSeries ℚ) (formalLog E)
        (adjointSeriesApply exponentialDivX (formalLog E) (mapSeriesLinear D (formalLog E))) :=
      (adjointSeriesApply_bernoulli_exponentialDivX _ _).symm
    _ = _ := by
      rw [hphi, ← adjointSeriesApply_mul, bernoulliPowerSeries_mul_half_exp_add_one]

end FQFP

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.ScalarWeakSolution
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.EquationRestrictionZeroExtension

/-!
# ScalarWeakSolutionRestriction

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Restriction and differences of scalar-forced weak solutions

Two structural operations on the pointwise weak equation `-div (a grad u) = g` are recorded.

*Restriction to an open subset.*  A test function of the subset extends by zero to a test
function of the ambient domain, so the equation on the larger set implies the equation on the
smaller one for the restricted `H¹` function.  The zero extension is the `p = 2` construction of
`EquationRestrictionZeroExtension.lean`.

*Differences.*  The equation is affine in the pair (forcing, solution), so the difference of two
solutions solves the equation with the difference of the forcings.  Splitting the integrals uses
the `L²` control of the fluxes, which is where the ellipticity certificate enters.

Both are needed to compare the Dirichlet resolvents of two exhaustion cubes on a common smaller
cube: their difference solves the homogeneous shifted equation there.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## Zero-extended tests -/

/-- Pairing a field against the gradient of a zero-extended test function on the larger set is
pairing it against the original gradient on the smaller set. -/
private theorem setIntegral_vecDot_h10Extend {V W : Set (Vec d)}
    (hV : MeasurableSet V) (hVW : V ⊆ W) (F : Vec d → Vec d) (phi : H10Function V) :
    ∫ x in W, vecDot (F x)
        ((h10ExtendToSuperset phi hV hVW).toH1Function.grad x) ∂volume =
      ∫ x in V, vecDot (F x) (phi.toH1Function.grad x) ∂volume := by
  have hindicator :
      (fun x ↦ vecDot (F x) ((h10ExtendToSuperset phi hV hVW).toH1Function.grad x)) =
        V.indicator (fun x ↦ vecDot (F x) (phi.toH1Function.grad x)) := by
    funext x
    rw [h10ExtendToSuperset_grad phi hV hVW]
    by_cases hx : x ∈ V
    · simp only [h10ZeroExtensionGrad_of_mem phi hx, Set.indicator_of_mem hx]
    · simp only [h10ZeroExtensionGrad_of_not_mem phi hx, Set.indicator_of_notMem hx,
        vecDot_zero_right]
  rw [hindicator, integral_indicator hV, Measure.restrict_restrict hV,
    Set.inter_eq_left.mpr hVW]

/-- Pairing a scalar against the value of a zero-extended test function on the larger set is
pairing it against the original value on the smaller set. -/
private theorem setIntegral_mul_h10Extend {V W : Set (Vec d)}
    (hV : MeasurableSet V) (hVW : V ⊆ W) (g : Vec d → ℝ) (phi : H10Function V) :
    ∫ x in W, g x * (h10ExtendToSuperset phi hV hVW).toH1Function.toFun x ∂volume =
      ∫ x in V, g x * phi.toH1Function.toFun x ∂volume := by
  have hindicator :
      (fun x ↦ g x * (h10ExtendToSuperset phi hV hVW).toH1Function.toFun x) =
        V.indicator (fun x ↦ g x * phi.toH1Function.toFun x) := by
    funext x
    rw [h10ExtendToSuperset_toFun phi hV hVW]
    by_cases hx : x ∈ V
    · simp only [h10ZeroExtension_of_mem phi hx, Set.indicator_of_mem hx]
    · simp only [h10ZeroExtension_of_not_mem phi hx, Set.indicator_of_notMem hx, mul_zero]
  rw [hindicator, integral_indicator hV, Measure.restrict_restrict hV,
    Set.inter_eq_left.mpr hVW]

/-! ## The two operations -/

/-- **The scalar-forced weak equation restricts to every open subset.** -/
theorem IsScalarForcedWeakSolution.restrictSubset {W V : Set (Vec d)} (hV : IsOpen V)
    (hVW : V ⊆ W) {a : CoeffField d} {g : Vec d → ℝ} {u : H1Function W}
    (h : IsScalarForcedWeakSolution a W g u) :
    IsScalarForcedWeakSolution a V g (u.restrict hV hVW) := by
  refine ⟨memL2On_mono hVW h.1, fun phi ↦ ?_⟩
  have hflux := setIntegral_vecDot_h10Extend hV.measurableSet hVW
    (fun x ↦ matVecMul (a x) (u.grad x)) phi
  have hforcing := setIntegral_mul_h10Extend hV.measurableSet hVW g phi
  have hgradEq : (u.restrict hV hVW).grad = u.grad := rfl
  calc
    ∫ x in V, vecDot (matVecMul (a x) ((u.restrict hV hVW).grad x))
        (phi.toH1Function.grad x) ∂volume =
        ∫ x in W, vecDot (matVecMul (a x) (u.grad x))
          ((h10ExtendToSuperset phi hV.measurableSet hVW).toH1Function.grad x) ∂volume := by
      rw [hgradEq, hflux]
    _ = ∫ x in W, g x *
          (h10ExtendToSuperset phi hV.measurableSet hVW).toH1Function.toFun x ∂volume :=
      h.2 (h10ExtendToSuperset phi hV.measurableSet hVW)
    _ = ∫ x in V, g x * phi.toH1Function.toFun x ∂volume := hforcing

/-- **The difference of two scalar-forced weak solutions solves the equation with the difference
of the forcings.** -/
theorem IsScalarForcedWeakSolution.sub {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a) {g₁ g₂ : Vec d → ℝ} {u₁ u₂ : H1Function U}
    (h₁ : IsScalarForcedWeakSolution a U g₁ u₁)
    (h₂ : IsScalarForcedWeakSolution a U g₂ u₂) :
    IsScalarForcedWeakSolution a U (fun x ↦ g₁ x - g₂ x) (u₁ - u₂) := by
  refine ⟨h₁.1.sub h₂.1, fun phi ↦ ?_⟩
  have hflux₁ : MemVectorL2 U (fun x ↦ matVecMul (a x) (u₁.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u₁.grad_memVectorL2
  have hflux₂ : MemVectorL2 U (fun x ↦ matVecMul (a x) (u₂.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u₂.grad_memVectorL2
  have hint₁ : Integrable (fun x ↦ vecDot (matVecMul (a x) (u₁.grad x))
      (phi.toH1Function.grad x)) (volumeMeasureOn U) :=
    integrableOn_vecDot_of_memVectorL2 hflux₁ phi.toH1Function.grad_memVectorL2
  have hint₂ : Integrable (fun x ↦ vecDot (matVecMul (a x) (u₂.grad x))
      (phi.toH1Function.grad x)) (volumeMeasureOn U) :=
    integrableOn_vecDot_of_memVectorL2 hflux₂ phi.toH1Function.grad_memVectorL2
  have hg₁ : Integrable (fun x ↦ g₁ x * phi.toH1Function.toFun x) (volumeMeasureOn U) :=
    h₁.1.integrable_mul phi.toH1Function.memL2
  have hg₂ : Integrable (fun x ↦ g₂ x * phi.toH1Function.toFun x) (volumeMeasureOn U) :=
    h₂.1.integrable_mul phi.toH1Function.memL2
  calc
    ∫ x in U, vecDot (matVecMul (a x) ((u₁ - u₂).grad x))
        (phi.toH1Function.grad x) ∂volume =
        ∫ x in U, (vecDot (matVecMul (a x) (u₁.grad x)) (phi.toH1Function.grad x) -
          vecDot (matVecMul (a x) (u₂.grad x)) (phi.toH1Function.grad x)) ∂volume := by
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [H1Function.sub_grad]
      simp only [vecDot, matVecMul, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, sub_mul]
    _ = (∫ x in U, vecDot (matVecMul (a x) (u₁.grad x))
          (phi.toH1Function.grad x) ∂volume) -
        ∫ x in U, vecDot (matVecMul (a x) (u₂.grad x))
          (phi.toH1Function.grad x) ∂volume := integral_sub hint₁ hint₂
    _ = (∫ x in U, g₁ x * phi.toH1Function.toFun x ∂volume) -
        ∫ x in U, g₂ x * phi.toH1Function.toFun x ∂volume := by
      rw [h₁.2 phi, h₂.2 phi]
    _ = ∫ x in U, (g₁ x - g₂ x) * phi.toH1Function.toFun x ∂volume := by
      rw [← integral_sub hg₁ hg₂]
      refine integral_congr_ae ?_
      filter_upwards with x
      ring

end

end DivergenceFormProcess.Form

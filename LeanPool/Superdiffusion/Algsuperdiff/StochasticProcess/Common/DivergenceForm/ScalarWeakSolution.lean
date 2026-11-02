/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.AlphaShiftedWeakSolution

/-!
# ScalarWeakSolution

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Pointwise scalar-forced divergence-form weak solutions

This file exposes the variational equation needed by scalar De Giorgi arguments.
Our sign convention is

`-div (a grad u) = g`,

so testing against `v` gives `integral (a grad u) dot grad v = integral g * v`.
The forcing is an honest pointwise scalar field with an explicit local `L^2` witness.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory
open scoped RealInnerProductSpace

variable {d : ℕ} {U : Set (Vec d)}

/-- The pointwise weak equation `-div (a grad u) = g` on `U`.

The test space is the existing `H10Function U` carrier. The first conjunct keeps
the pointwise forcing available to subsequent truncation and level-set estimates.
-/
def IsScalarForcedWeakSolution (a : CoeffField d) (U : Set (Vec d))
    (g : Vec d → ℝ) (u : H1Function U) : Prop :=
  MemScalarL2 U g ∧
    ∀ v : H10Function U,
      (∫ x in U, vecDot (matVecMul (a x) (u.grad x))
          (v.toH1Function.grad x) ∂MeasureTheory.volume) =
        ∫ x in U, g x * v.toH1Function.toFun x ∂MeasureTheory.volume

/-- Scaling the coefficient and scalar forcing by the same real constant preserves the equation. -/
theorem IsScalarForcedWeakSolution.const_smul_coefficient
    {W : Set (Vec d)} {c : ℝ} {a : CoeffField d}
    {u : H1Function W} {g : Vec d → ℝ}
    (hu : IsScalarForcedWeakSolution a W g u) :
    IsScalarForcedWeakSolution (fun x => c • a x) W (fun x => c * g x) u := by
  refine ⟨?_, fun phi => ?_⟩
  · have h := hu.1.const_smul c
    simpa only [Pi.smul_apply, smul_eq_mul] using! h
  · have h := hu.2 phi
    have hleft :
        (∫ x in W, vecDot (matVecMul (c • a x) (u.grad x))
            (phi.toH1Function.grad x) ∂volume) =
          c * ∫ x in W, vecDot (matVecMul (a x) (u.grad x))
            (phi.toH1Function.grad x) ∂volume := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      simp only [smul_matVecMul, vecDot_smul_left]
    have hright :
        (∫ x in W, (c * g x) * phi.toH1Function.toFun x ∂volume) =
          c * ∫ x in W, g x * phi.toH1Function.toFun x ∂volume := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring
    rw [hleft, hright, h]

/-- The alpha-shifted graph-carrier equation gives the pointwise equation
`-div (a grad u) = f - alpha * u` for every honest `H10Function` representative.
-/
theorem isScalarForcedWeakSolution_sub_alpha_mul_of_isAlphaShiftedWeakSolution
    {a : CoeffField d} {alpha : ℝ} {f : ScalarL2 U} (u : H10Function U)
    (hweak : IsAlphaShiftedWeakSolution a U alpha f
      (ZeroTraceSobolev.ofH10Function u)) :
    IsScalarForcedWeakSolution a U
      (fun x => f x - alpha * u.toH1Function.toFun x) u.toH1Function := by
  constructor
  · exact (MeasureTheory.Lp.memLp f).sub (u.toH1Function.memL2.const_smul alpha)
  · intro v
    have h := hweak (ZeroTraceSobolev.ofH10Function v)
    rw [ZeroTraceSobolev.toL2_ofH10Function,
      ZeroTraceSobolev.gradient_ofH10Function,
      ZeroTraceSobolev.toL2_ofH10Function,
      ZeroTraceSobolev.gradient_ofH10Function] at h
    have hcoefficient :
        coefficientPairing a U u.toH1Function.gradToHilbertVectorL2
            v.toH1Function.gradToHilbertVectorL2 =
          ∫ x in U, vecDot (matVecMul (a x) (u.toH1Function.grad x))
            (v.toH1Function.grad x) ∂MeasureTheory.volume := by
      rw [coefficientPairing]
      apply MeasureTheory.integral_congr_ae
      filter_upwards
        [u.toH1Function.coeFn_gradToHilbertVectorL2,
          v.toH1Function.coeFn_gradToHilbertVectorL2,
          coeFn_hilbertVectorL2ToVectorL2
            (U := U) u.toH1Function.gradToHilbertVectorL2,
          coeFn_hilbertVectorL2ToVectorL2
            (U := U) v.toH1Function.gradToHilbertVectorL2]
        with x hu hv hu' hv'
      rw [hu', hv', hu, hv]
      rfl
    have hmass :
        inner ℝ u.toH1Function.toScalarL2 v.toH1Function.toScalarL2 =
          ∫ x in U, u.toH1Function.toFun x * v.toH1Function.toFun x
            ∂MeasureTheory.volume := by
      rw [scalarInner_eq_integral]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [u.toH1Function.coeFn_toScalarL2,
        v.toH1Function.coeFn_toScalarL2] with x hu hv
      rw [hu, hv]
    have hforcing :
        inner ℝ f v.toH1Function.toScalarL2 =
          ∫ x in U, f x * v.toH1Function.toFun x ∂MeasureTheory.volume := by
      rw [scalarInner_eq_integral]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [v.toH1Function.coeFn_toScalarL2] with x hv
      rw [hv]
    rw [hcoefficient, hmass, hforcing] at h
    have hfInt : MeasureTheory.Integrable
        (fun x => f x * v.toH1Function.toFun x) (volumeMeasureOn U) :=
      (MeasureTheory.Lp.memLp f).integrable_mul v.toH1Function.memL2
    have huInt : MeasureTheory.Integrable
        (fun x => alpha *
          (u.toH1Function.toFun x * v.toH1Function.toFun x))
        (volumeMeasureOn U) :=
      (u.toH1Function.memL2.integrable_mul v.toH1Function.memL2).const_mul alpha
    calc
      (∫ x in U, vecDot (matVecMul (a x) (u.toH1Function.grad x))
          (v.toH1Function.grad x) ∂MeasureTheory.volume) =
          (∫ x in U, f x * v.toH1Function.toFun x ∂MeasureTheory.volume) -
            alpha * ∫ x in U,
              u.toH1Function.toFun x * v.toH1Function.toFun x
              ∂MeasureTheory.volume := by
        apply eq_sub_of_add_eq
        rw [add_comm]
        exact h
      _ = ∫ x in U, f x * v.toH1Function.toFun x -
            alpha * (u.toH1Function.toFun x * v.toH1Function.toFun x)
            ∂MeasureTheory.volume := by
        rw [← MeasureTheory.integral_const_mul]
        exact (MeasureTheory.integral_sub hfInt huInt).symm
      _ = ∫ x in U,
            (f x - alpha * u.toH1Function.toFun x) * v.toH1Function.toFun x
            ∂MeasureTheory.volume := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        ring

end DivergenceFormProcess.Form

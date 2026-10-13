/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.InteriorEquationBridge
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.ScalarWeakSolution

/-!
# PotentialBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# A scalar-forcing bridge for potential weak solutions

This file translates the zero-trace potential weak formulation into the
pointwise scalar-forcing carrier used by the Agmon decay applications.  It is
kept in the whole-space layer because that is its first consumer.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open scoped RealInnerProductSpace

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

/-- A potential weak solution represented by an `H¹₀` function solves the
pointwise scalar-forced equation obtained by moving both zeroth-order terms
to the right-hand side. -/
theorem isScalarForcedWeakSolution_of_isPotentialWeakSolution [NeZero d]
    {a : CoeffField d} {alpha C : ℝ} {q : Vec d → ℝ} {f : ScalarL2 U}
    (u : H10Function U) (hq : IsBoundedNonnegativePotential U q C)
    (hweak : IsPotentialWeakSolution a alpha q U
      (ZeroTraceSobolev.ofH10Function u) f) :
    IsScalarForcedWeakSolution a U
      (fun x => f x - (alpha + q x) * u.toH1Function.toFun x)
      u.toH1Function := by
  let z : ZeroTraceSobolev U := ZeroTraceSobolev.ofH10Function u
  let g : Vec d → ℝ :=
    fun x => f x - (alpha + q x) * u.toH1Function.toFun x
  have hsource : (interiorScalarSource alpha q hq f z : Vec d → ℝ) =ᵐ[
      volumeMeasureOn U] g := by
    filter_upwards [interiorScalarSource_coeFn alpha q hq f z,
      u.toH1Function.coeFn_toScalarL2] with x hx hu
    rw [hx]
    change f x - alpha * u.toH1Function.toScalarL2 x -
        q x * u.toH1Function.toScalarL2 x = g x
    rw [hu]
    dsimp only [g]
    ring
  have hmatrix :=
    isMatrixDivFormWeakSolutionZerothOrderOn_domain_of_isPotentialWeakSolution
      a q hq f hweak u (ZeroTraceSobolev.gradient_ofH10Function u)
  constructor
  · exact (Lp.memLp (interiorScalarSource alpha q hq f z)).ae_eq hsource
  · intro phi
    have hbase :
        (∫ x in U, vecDot (matVecMul (a x) (u.toH1Function.grad x))
            (phi.toH1Function.grad x) ∂volume) =
          ∫ x in U, interiorScalarSource alpha q hq f z x *
            phi.toH1Function.toFun x ∂volume := by
      simpa only [Pi.zero_apply, vecDot_zero_left, integral_zero, sub_zero]
        using hmatrix phi
    calc
      (∫ x in U, vecDot (matVecMul (a x) (u.toH1Function.grad x))
          (phi.toH1Function.grad x) ∂volume) =
          ∫ x in U, interiorScalarSource alpha q hq f z x *
            phi.toH1Function.toFun x ∂volume := hbase
      _ = ∫ x in U, g x * phi.toH1Function.toFun x ∂volume := by
        refine integral_congr_ae ?_
        filter_upwards [hsource] with x hx
        rw [hx]

end

end DivergenceFormProcess.Form

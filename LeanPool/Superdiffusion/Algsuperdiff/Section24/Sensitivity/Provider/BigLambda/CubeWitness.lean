/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Lambda.WitnessBudget
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.BigLambda.BMatrix
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.BigLambda.CubeEllipticity

/-!
# CubeWitness

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The zero-trace witness budget at the pure-potential loading

Source: ABK26 (`e.split.besov.stuff.begin`), specialized to the
**pure-potential** loading `q = 0` and stated at an arbitrary triadic cube `R`.

At `q = 0` the source combination is

```
∇u = ½ (∇v(·,R,p,0;a) + ∇v(·,R,p,0;aᵗ)) + p ,
```

so there are three summands.  The two maximizer gradients are handled by the
general-cube budget of `Provider.Lambda.WitnessBudget`; because the
pure-potential response is transpose invariant
(`BigLambda.responseJ_potential_transpose`) the adjoint half carries **no**
`|p·q|` shift.  The affine summand `p` is a constant field, whose negative
Besov seminorm is `≤ C |p|` (`Discharge.ConstantBesov`), and `|p|` is absorbed
by the general-cube ellipticity chain
(`BigLambda.vecNorm_le_sqrt_two_mul_sqrt_lambdaSq_inv_mul_sqrt_responseJ`).

The resulting budget is a clean multiple of `λ_{3/8,2}^{-1/2}(R) J(R,p,0)^{1/2}`.

Every declaration in this module is an internal helper for the Section 2.4
sensitivity providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.BigLambda

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Assembly
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge
open Algsuperdiff.Section24.Sensitivity.Provider.Lambda
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The adjoint budget at the pure-potential loading -/

/-- The adjoint budget at the **pure-potential** loading.  At `q = 0` the
transposed response equals the primal one, so there is no `|p·q|` shift. -/
theorem cubeBesovNegativeVectorSeminormTwo_cubeAdjointGrad_potential_le [NeZero d]
    (Q : TriadicCube d) (F : Ch02.TriadicCoeffFamily d) {p : Vec d}
    {vAdj : Solution (cubeDomain Q) (F.coeffOn Q).transpose}
    (hvAdj : IsResponseMaximizer (cubeDomain Q) (F.coeffOn Q).transpose p
      (-(0 : Vec d)) vAdj) :
    cubeBesovNegativeVectorSeminormTwo Q (3 / 8) (fun x => vAdj.toH1.grad x) ≤
      Ch03.poincareDiscountFactor (3 / 8) (.finite 2) *
        Real.sqrt ((Ch02.lambdaSq Q (3 / 8) (.finite 2) F)⁻¹) *
        (2 * Real.sqrt (responseJ (cubeDomain Q) (F.coeffOn Q) p 0)) := by
  have hbase := cubeBesovNegativeVectorSeminormTwo_cubeMaximizerGrad_le Q
    (transposeCoeffFamily F) (v := vAdj) hvAdj
  rw [lambdaSq_transposeCoeffFamily] at hbase
  have hJ : responseJ (cubeDomain Q) ((transposeCoeffFamily F).coeffOn Q) p
      (-(0 : Vec d)) = responseJ (cubeDomain Q) (F.coeffOn Q) p 0 := by
    rw [transposeCoeffFamily_coeffOn, neg_zero]
    exact responseJ_potential_transpose (cubeDomain Q) (F.coeffOn Q) p
  rwa [hJ] at hbase

/-! ## The pure-potential witness budget -/

/-- The explicit constant of the pure-potential witness-gradient negative Besov
budget. -/
def potWitnessConst : ℝ :=
  Real.sqrt 2 *
    (2⁻¹ * Real.sqrt 2 *
        (2 * Ch03.poincareDiscountFactor (3 / 8) (.finite 2) +
          2 * Ch03.poincareDiscountFactor (3 / 8) (.finite 2)) +
      constantFieldBesovConst (3 / 8) * Real.sqrt 2)

theorem potWitnessConst_nonneg : 0 ≤ potWitnessConst := by
  have := poincareDiscountFactor_sensitivity_pos.le
  have := constantFieldBesovConst_nonneg (3 / 8 : ℝ)
  have h2 := Real.sqrt_nonneg (2 : ℝ)
  unfold potWitnessConst
  positivity

/-- **The pure-potential negative Besov budget of the zero-trace witness
gradient at an arbitrary triadic cube.** -/
theorem cubeBesovNegativeVectorSeminormTwo_potWitnessGrad_le [NeZero d]
    (Q : TriadicCube d) (F : Ch02.TriadicCoeffFamily d) (p : Vec d)
    {vAdj : Solution (cubeDomain Q) (F.coeffOn Q).transpose}
    {v : Ch03.CubeSolution Q F}
    (hvAdj : IsResponseMaximizer (cubeDomain Q) (F.coeffOn Q).transpose p
      (-(0 : Vec d)) vAdj)
    (hv : IsResponseMaximizer (cubeDomain Q) (F.coeffOn Q) p 0 v)
    (u : H10Function ((cubeDomain Q : Domain d) : Set (Vec d)))
    (hu : ∀ᵐ x ∂volumeMeasureOn ((cubeDomain Q : Domain d) : Set (Vec d)),
      u.toH1Function.grad x =
        (2 : ℝ)⁻¹ • (vAdj.toH1.grad x + v.toH1.grad x) + p) :
    cubeBesovNegativeVectorSeminormTwo Q (3 / 8) (fun x => u.toH1Function.grad x) ≤
      potWitnessConst *
        (Real.sqrt ((Ch02.lambdaSq Q (3 / 8) (.finite 2) F)⁻¹) *
          Real.sqrt (responseJ (cubeDomain Q) (F.coeffOn Q) p 0)) := by
  classical
  set PD : ℝ := Ch03.poincareDiscountFactor (3 / 8) (.finite 2) with hPD
  set X : ℝ := Real.sqrt ((Ch02.lambdaSq Q (3 / 8) (.finite 2) F)⁻¹) *
    Real.sqrt (responseJ (cubeDomain Q) (F.coeffOn Q) p 0) with hX
  have hAdj : cubeBesovNegativeVectorSeminormTwo Q (3 / 8)
      (fun x => vAdj.toH1.grad x) ≤ (2 * PD) * X := by
    refine (cubeBesovNegativeVectorSeminormTwo_cubeAdjointGrad_potential_le Q F
      hvAdj).trans (le_of_eq ?_)
    rw [hX, hPD]; ring
  have hPrimal : cubeBesovNegativeVectorSeminormTwo Q (3 / 8)
      (fun x => v.toH1.grad x) ≤ (2 * PD) * X := by
    refine (cubeBesovNegativeVectorSeminormTwo_cubeMaximizerGrad_le Q F hv).trans
      (le_of_eq ?_)
    rw [hX, hPD]; ring
  have hConst : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminormTwo Q (3 / 8) N (fun _ => p) ≤
        (constantFieldBesovConst (3 / 8) * Real.sqrt 2) * X := by
    intro N
    refine (cubeBesovNegativeVectorPartialSeminormTwo_const_le Q
      (by norm_num) N p).trans ?_
    have hp := vecNorm_le_sqrt_two_mul_sqrt_lambdaSq_inv_mul_sqrt_responseJ Q F
      (F.coeffOn Q) (CoeffOn.AEEq.refl _) p
    have hstep := mul_le_mul_of_nonneg_left hp
      (constantFieldBesovConst_nonneg (3 / 8 : ℝ))
    refine hstep.trans (le_of_eq ?_)
    rw [hX]; ring
  have hae : (fun x => u.toH1Function.grad x)
      =ᵐ[normalizedCubeMeasure Q]
      fun x => ((2 : ℝ)⁻¹ • (vAdj.toH1.grad x + v.toH1.grad x)) + (fun _ => p) x := by
    refine ae_cubeDomain_iff_normalizedCubeMeasure Q ?_
    filter_upwards [hu] with x hx using hx
  have hL2Adj : MemVectorL2 (cubeSet Q) (fun x => vAdj.toH1.grad x) :=
    memVectorL2_cubeSet_grad vAdj.toH1
  have hL2v : MemVectorL2 (cubeSet Q) (fun x => v.toH1.grad x) :=
    memVectorL2_cubeSet_grad v.toH1
  have hBddAdj := bddAbove_cubeBesovNegativeVectorPartialSeminormTwo_h1Grad
    Q vAdj.toH1
  have hBddv := bddAbove_cubeBesovNegativeVectorPartialSeminormTwo_h1Grad
    Q v.toH1
  have hleft := cubeBesovNegativeVectorPartialSeminormTwo_smul_add_le
    Q (3 / 8) ((2 : ℝ)⁻¹) _ _ hL2Adj hL2v hBddAdj hBddv hAdj hPrimal
  have hbound := cubeBesovNegativeVectorSeminormTwo_add_const_le
    Q (3 / 8) _ _ p ((hL2Adj.add hL2v).const_smul ((2 : ℝ)⁻¹))
    hae hleft hConst
  refine hbound.trans_eq ?_
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)]
  unfold potWitnessConst
  rw [hPD]; ring

end

end Algsuperdiff.Section24.Sensitivity.Provider.BigLambda

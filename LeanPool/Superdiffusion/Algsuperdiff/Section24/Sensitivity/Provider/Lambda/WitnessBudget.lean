/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge.GradientSplit
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Adjoint.H10Witness

/-!
# WitnessBudget

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The pure-flux zero-trace witness budget at a general triadic cube

Source: ABK26 (`e.split.besov.stuff.begin`) specialized to the **pure-flux
loading** `p = 0` and stated at an *arbitrary* triadic cube.

At `p = 0` the source combination degenerates:

```
∇u = ∇w + ∇w^* = ½ (∇v(·,Q,0,q;a) + ∇v(·,Q,0,-q;aᵗ)) ,
```

with **no** affine summand.  Consequently the budget is a clean multiple of
`λ_{3/8,2}^{-1/2} J^{1/2}` with no `|p·q|` term, and neither
`Discharge.ConstantBesov` nor `Discharge.EllipticityOrdered` is needed.

Two general-cube inputs make this work at a descendant cube:

* the coarse Poincaré estimate of `Assembly.GaugeBridge`, which is already
  stated at an arbitrary triadic cube and an arbitrary CoarseGraining family;
* the transpose invariance of the multiscale gauge
  (`Discharge.TransposeGauge.lambdaSq_transposeCoeffFamily`) together with the
  pure-flux adjoint identity `J(Q, aᵗ, 0, -q) = J(Q, a, 0, q)`, which at `p = 0`
  carries no shift.

Every declaration is an internal helper for the Section 2.4 sensitivity
providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Lambda

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Assembly
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Measure bridges at a general triadic cube -/

/-- The Chapter 2 carrier of `cubeDomain Q` is the open cube. -/
theorem cubeDomain_coe_openCubeSet (Q : TriadicCube d) :
    ((cubeDomain Q : Domain d) : Set (Vec d)) = openCubeSet Q :=
  Ch02.cubeDomain_coe Q

/-- `L^p` membership on the open-cube carrier transfers to the normalized cube
measure, at an arbitrary triadic cube. -/
theorem memLp_normalizedCubeMeasure_of_memLp_cubeDomain {E : Type*}
    [NormedAddCommGroup E] {r : ℝ≥0∞} {f : Vec d → E} (Q : TriadicCube d)
    (hf : MemLp f r (volumeMeasureOn ((cubeDomain Q : Domain d) : Set (Vec d)))) :
    MemLp f r (normalizedCubeMeasure Q) := by
  rw [cubeDomain_coe_openCubeSet] at hf
  have hcube : MemLp f r (cubeMeasure Q) := by
    rw [cubeMeasure, HCPolySupport.volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    exact hf
  rw [normalizedCubeMeasure]
  exact hcube.smul_measure ENNReal.ofReal_ne_top

/-- Any a.e. property on the open-cube carrier holds a.e. for the normalized
cube measure, at an arbitrary triadic cube. -/
theorem ae_normalizedCubeMeasure_of_ae_cubeDomain {P : Vec d → Prop}
    (Q : TriadicCube d)
    (h : ∀ᵐ x ∂volumeMeasureOn ((cubeDomain Q : Domain d) : Set (Vec d)), P x) :
    ∀ᵐ x ∂ normalizedCubeMeasure Q, P x := by
  rw [cubeDomain_coe_openCubeSet] at h
  have hcube : ∀ᵐ x ∂ cubeMeasure Q, P x := by
    rw [cubeMeasure, HCPolySupport.volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    exact h
  rw [normalizedCubeMeasure]
  exact MeasureTheory.Measure.ae_smul_measure hcube _

/-- A.e. equality on the open-cube carrier transfers to the normalized cube
measure, at an arbitrary triadic cube. -/
theorem ae_cubeDomain_iff_normalizedCubeMeasure {E : Type*}
    {f g : Vec d → E} (Q : TriadicCube d)
    (h : f =ᵐ[volumeMeasureOn ((cubeDomain Q : Domain d) : Set (Vec d))] g) :
    f =ᵐ[normalizedCubeMeasure Q] g :=
  ae_normalizedCubeMeasure_of_ae_cubeDomain (P := fun x => f x = g x) Q h

/-! ## The two maximizer-gradient budgets at a general cube -/

/-- The negative Besov budget of a response-maximizer gradient at an arbitrary
triadic cube, in the concrete `q = 2` spelling. -/
theorem cubeBesovNegativeVectorSeminormTwo_cubeMaximizerGrad_le [NeZero d]
    (Q : TriadicCube d) (F : Ch03.CoeffFamily d) {p q : Vec d}
    {v : Ch03.CubeSolution Q F}
    (hv : IsResponseMaximizer (cubeDomain Q) (F.coeffOn Q) p q v) :
    cubeBesovNegativeVectorSeminormTwo Q (3 / 8) (fun x => v.toH1.grad x) ≤
      Ch03.poincareDiscountFactor (3 / 8) (.finite 2) *
        Real.sqrt ((Ch02.lambdaSq Q (3 / 8) (.finite 2) F)⁻¹) *
        (2 * Real.sqrt (responseJ (cubeDomain Q) (F.coeffOn Q) p q)) := by
  have hmain := scaleNormalizedNegativeBesovVectorNorm_solutionGradient_le Q F hv
  rwa [Ch03.solutionGradientField,
    Ch03.scaleNegativeBesovVectorNorm_finiteTwo_eq_cubeNegativeSeminorm]
    at hmain

/-- The adjoint budget at the **pure-flux** loading.  At `p = 0` the transposed
response equals the primal one, so there is no `|p·q|` shift. -/
theorem cubeBesovNegativeVectorSeminormTwo_cubeAdjointGrad_flux_le [NeZero d]
    (Q : TriadicCube d) (F : Ch03.CoeffFamily d) {w : Vec d}
    {vAdj : Solution (cubeDomain Q) (F.coeffOn Q).transpose}
    (hvAdj : IsResponseMaximizer (cubeDomain Q) (F.coeffOn Q).transpose 0 (-w) vAdj) :
    cubeBesovNegativeVectorSeminormTwo Q (3 / 8) (fun x => vAdj.toH1.grad x) ≤
      Ch03.poincareDiscountFactor (3 / 8) (.finite 2) *
        Real.sqrt ((Ch02.lambdaSq Q (3 / 8) (.finite 2) F)⁻¹) *
        (2 * Real.sqrt (responseJ (cubeDomain Q) (F.coeffOn Q) 0 w)) := by
  have hbase := cubeBesovNegativeVectorSeminormTwo_cubeMaximizerGrad_le Q
    (transposeCoeffFamily F) (v := vAdj) hvAdj
  rw [lambdaSq_transposeCoeffFamily] at hbase
  have hJ : responseJ (cubeDomain Q) ((transposeCoeffFamily F).coeffOn Q) 0 (-w) =
      responseJ (cubeDomain Q) (F.coeffOn Q) 0 w := by
    rw [transposeCoeffFamily_coeffOn,
      responseJ_transpose_neg_right (cubeDomain Q) (F.coeffOn Q) 0 w]
    have : vecDot (0 : Vec d) w = 0 := by simp [vecDot]
    rw [this]; ring
  rwa [hJ] at hbase

/-! ## The pure-flux witness-gradient budget -/

/-- The explicit constant of the pure-flux witness-gradient negative Besov
budget. -/
def fluxWitnessConst : ℝ :=
  2 * Real.sqrt 2 * Ch03.poincareDiscountFactor (3 / 8) (.finite 2)

theorem fluxWitnessConst_nonneg : 0 ≤ fluxWitnessConst := by
  have := poincareDiscountFactor_sensitivity_pos.le
  have h2 := Real.sqrt_nonneg (2 : ℝ)
  unfold fluxWitnessConst
  positivity

/-- **The pure-flux negative Besov budget of the zero-trace witness gradient at
an arbitrary triadic cube.**

At `p = 0` there is no affine summand, so the budget is a pure multiple of
`λ_{3/8,2}^{-1/2} J^{1/2}`. -/
theorem cubeBesovNegativeVectorSeminormTwo_fluxWitnessGrad_le [NeZero d]
    (Q : TriadicCube d) (F : Ch03.CoeffFamily d) (w : Vec d)
    {vAdj : Solution (cubeDomain Q) (F.coeffOn Q).transpose}
    {v : Ch03.CubeSolution Q F}
    (hvAdj : IsResponseMaximizer (cubeDomain Q) (F.coeffOn Q).transpose 0 (-w) vAdj)
    (hv : IsResponseMaximizer (cubeDomain Q) (F.coeffOn Q) 0 w v)
    (u : H10Function ((cubeDomain Q : Domain d) : Set (Vec d)))
    (hu : ∀ᵐ x ∂volumeMeasureOn ((cubeDomain Q : Domain d) : Set (Vec d)),
      u.toH1Function.grad x =
        (2 : ℝ)⁻¹ • (vAdj.toH1.grad x + v.toH1.grad x) + (0 : Vec d)) :
    cubeBesovNegativeVectorSeminormTwo Q (3 / 8) (fun x => u.toH1Function.grad x) ≤
      fluxWitnessConst *
        (Real.sqrt ((Ch02.lambdaSq Q (3 / 8) (.finite 2) F)⁻¹) *
          Real.sqrt (responseJ (cubeDomain Q) (F.coeffOn Q) 0 w)) := by
  classical
  set PD : ℝ := Ch03.poincareDiscountFactor (3 / 8) (.finite 2) with hPD
  have hPDnn : 0 ≤ PD := poincareDiscountFactor_sensitivity_pos.le
  set X : ℝ := Real.sqrt ((Ch02.lambdaSq Q (3 / 8) (.finite 2) F)⁻¹) *
    Real.sqrt (responseJ (cubeDomain Q) (F.coeffOn Q) 0 w) with hX
  have hXnn : 0 ≤ X := by
    rw [hX]; exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hAdj : cubeBesovNegativeVectorSeminormTwo Q (3 / 8)
      (fun x => vAdj.toH1.grad x) ≤ (2 * PD) * X := by
    refine (cubeBesovNegativeVectorSeminormTwo_cubeAdjointGrad_flux_le Q F hvAdj).trans
      (le_of_eq ?_)
    rw [hX, hPD]; ring
  have hPrimal : cubeBesovNegativeVectorSeminormTwo Q (3 / 8)
      (fun x => v.toH1.grad x) ≤ (2 * PD) * X := by
    refine (cubeBesovNegativeVectorSeminormTwo_cubeMaximizerGrad_le Q F hv).trans
      (le_of_eq ?_)
    rw [hX, hPD]; ring
  -- the a.e. identification of the witness gradient
  have hae : (fun x => u.toH1Function.grad x)
      =ᵐ[normalizedCubeMeasure Q]
      fun x => (2 : ℝ)⁻¹ • (vAdj.toH1.grad x + v.toH1.grad x) := by
    refine ae_cubeDomain_iff_normalizedCubeMeasure Q ?_
    filter_upwards [hu] with x hx
    simpa using hx
  -- `L²` data
  have hL2Adj : MemVectorL2 (cubeSet Q) (fun x => vAdj.toH1.grad x) :=
    memVectorL2_cubeSet_grad vAdj.toH1
  have hL2v : MemVectorL2 (cubeSet Q) (fun x => v.toH1.grad x) :=
    memVectorL2_cubeSet_grad v.toH1
  have hBddAdj := bddAbove_cubeBesovNegativeVectorPartialSeminormTwo_h1Grad Q vAdj.toH1
  have hBddv := bddAbove_cubeBesovNegativeVectorPartialSeminormTwo_h1Grad Q v.toH1
  refine cubeBesovNegativeVectorSeminormTwo_le_of_partialBound _ _ _ ?_
  intro N
  rw [cubeBesovNegativeVectorPartialSeminormTwo_congr_ae Q (3 / 8) N hae]
  have hsmul := cubeBesovNegativeVectorPartialSeminormTwo_const_smul Q (3 / 8) N
    ((2 : ℝ)⁻¹) (fun x => vAdj.toH1.grad x + v.toH1.grad x)
  have habs2 : |((2 : ℝ)⁻¹)| = (2 : ℝ)⁻¹ := by norm_num
  rw [habs2] at hsmul
  have hinner := cubeBesovNegativeVectorPartialSeminormTwo_add_le_sqrtTwo_mul_add
    Q (3 / 8) (fun x => vAdj.toH1.grad x) (fun x => v.toH1.grad x) hL2Adj hL2v N
  have hAdjN : cubeBesovNegativeVectorPartialSeminormTwo Q (3 / 8) N
      (fun x => vAdj.toH1.grad x) ≤ (2 * PD) * X := by
    refine le_trans ?_ hAdj
    unfold cubeBesovNegativeVectorSeminormTwo
    exact le_csSup hBddAdj ⟨N, rfl⟩
  have hvN : cubeBesovNegativeVectorPartialSeminormTwo Q (3 / 8) N
      (fun x => v.toH1.grad x) ≤ (2 * PD) * X := by
    refine le_trans ?_ hPrimal
    unfold cubeBesovNegativeVectorSeminormTwo
    exact le_csSup hBddv ⟨N, rfl⟩
  have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  rw [hsmul]
  have hstep := hinner.trans (mul_le_mul_of_nonneg_left (add_le_add hAdjN hvN) hs2)
  have hgoal : (2 : ℝ)⁻¹ * (Real.sqrt 2 * ((2 * PD) * X + (2 * PD) * X)) =
      fluxWitnessConst * X := by
    unfold fluxWitnessConst
    rw [hPD]; ring
  calc (2 : ℝ)⁻¹ * cubeBesovNegativeVectorPartialSeminormTwo Q (3 / 8) N
        (fun x => vAdj.toH1.grad x + v.toH1.grad x)
      ≤ (2 : ℝ)⁻¹ * (Real.sqrt 2 * ((2 * PD) * X + (2 * PD) * X)) :=
        mul_le_mul_of_nonneg_left hstep (by norm_num)
    _ = fluxWitnessConst * X := hgoal

end

end Algsuperdiff.Section24.Sensitivity.Provider.Lambda

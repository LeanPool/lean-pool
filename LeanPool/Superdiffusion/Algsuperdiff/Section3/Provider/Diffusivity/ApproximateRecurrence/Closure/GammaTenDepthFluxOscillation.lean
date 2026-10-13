/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenInteriorArithmetic
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenInteriorMinkowski
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.Step5DefectGauge
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationOscillationFullMesh
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationSelectionFamily

/-!
# GammaTenDepthFluxOscillation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The depth oscillation root of the **flux leg**, on the cutoff-sample carrier

ABK26, `e.lower.bound.oscillations`, `e.nablaw.oscillations`, `e.Fz.def`.

## The two gaps this module closes

The depth-indexed interior endpoints
`Closure.GammaTenDepthOscillation.exists_gamma0_freshShell{Dirichlet,Neumann}_meshOscillationDepth_le_gamma_pow_sixteen`
bound the oscillation of the corrector **gradient**, on `M.P.toMeasure`.  The
Besov tower of Step 2 is read

* at the Neumann leg not of `grad w_N` but of
  `PrincipalResponsePz.neumannFluxField = grad w_N + streamForcing`, and
* on `(cutoffSampleLaw M).toMeasure`, the closure's own carrier.

Both transports are performed here, in one statement, at an arbitrary depth ---
the depth index rides the mesh scale `nn` and the cube family, not the carrier,
so nothing in either transport is depth-specific.

## How the flux leg is paid for

`Closure.GammaTenInteriorMinkowski.meshOscillationCell_neumannFluxField_le` splits
the cell into `osc(grad w_N)` plus the deterministic forcing term
`3^{nn} shom^{-1} d |e'| shellDerivNormSum`, and
`LocalizationOscillationGridMoment.gridFourthMomentRoot_le_add_of_le` turns the
cellwise split into the grid root at the elementary cost `8^{1/4} <= 2`.  The
forcing term's own grid root is the single-base-point root at a maximizing cube
(`Closure.Step5DefectGauge.gridFourthMomentRoot_shellDerivNormSum_le_of_base_point`),
which is exactly the additive term the depth endpoints already carry --- so the
hypothesis `hend` is used at that maximizing base point and the whole forcing
budget is absorbed into it, at the price of the factor `d |e'| <= d`.

The conclusion is therefore `2 d` times the endpoint's own bound `Bd`: no new
analytic input, one explicit dimensional constant.

## What is proved

* `gridFourthMomentRoot_meshOscillationCell_neumannFluxField_cutoffSample_le` ---
  **the flux-leg depth root**: on the cutoff-sample carrier, the grid
  fourth-moment root of the flux field's oscillation cells over an interior mesh
  is at most `2 d Bd`, where `Bd` is any bound on the endpoint's own left-hand
  side (the gradient root plus the forcing gauge) at *every* base point.

## Binders

The scale gate `nn <= lowScale` (which is what makes the shell-derivative gauge a
majorant on the oscillation cube), `lowScale < highScale` (the forcing gauge's
fourth-power integrability), `1 <= d`, `|e'| <= 1`, the window containment `hwin`
of the mesh cells in the localization cube, the fourth-power integrability
`hoscInt` of the gradient oscillation cells in the sample, and the endpoint
hypothesis `hend`.  No smallness gate on `cgamma`, no model estimate and no
measurability of the flux oscillation cell is assumed.

## Scope

Internal Provider infrastructure for the Step-2 fluctuation estimate.  There is
no `sorry`, no `admit`, no custom axiom and no `set_option maxHeartbeats`.

## References

* ABK26, `e.lower.bound.oscillations`, `e.nablaw.oscillations`, `e.Fz.def`,
  `e.def.w`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 HCPolySupport.Book.Ch03
open MeasureTheory
open Algsuperdiff.Section3.Cutoff Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The flux leg -/

/-- **The depth oscillation root of the flux leg, on the cutoff-sample
carrier.**

`Bd` is any bound on the depth endpoints' own left-hand side --- the gradient
oscillation root plus the forcing gauge --- valid at **every** base point `z0`;
the depth endpoints of `Closure.GammaTenDepthOscillation` deliver exactly that,
their base point being universally quantified.  The conclusion is the same
quantity read at `neumannFluxField` instead of `grad w_N`, on
`(cutoffSampleLaw M).toMeasure` instead of `M.P.toMeasure`, at the explicit cost
`2 d`.

on `hnn`, `hlt`, `hd1`, `he'`, `hwin`, `hoscInt` and `hend`. -/
theorem gridFourthMomentRoot_meshOscillationCell_neumannFluxField_cutoffSample_le
    (M : ABKModel d) (hd1 : 1 ≤ d) (sigma : PositiveScalar) {lowScale highScale : ℤ}
    (hlt : lowScale < highScale) (e' : Vec d) (he' : vecNorm e' ≤ 1)
    {K nn outer : ℤ}
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d K)))
    (hnn : nn ≤ lowScale)
    (hwin : ∀ R' ∈ interiorMesoCubeGrid d K nn outer,
      openCubeSet R' ⊆ openCubeSet (originCube d K))
    (hoscInt : ∀ R' ∈ interiorMesoCubeGrid d K nn outer,
      Integrable (fun omega : CutoffSample d =>
        meshOscillationCell nn (wN omega.val).toH1Function.grad R' ^ (4 : ℝ))
        (cutoffSampleLaw M).toMeasure)
    {Bd : ℝ}
    (hend : ∀ z0 : Vec d,
      gridFourthMomentRoot M.P.toMeasure (interiorMesoCubeGrid d K nn outer)
          (fun R' omega => meshOscillationCell nn (wN omega).toH1Function.grad R') +
        ((sigma : ℝ))⁻¹ * ((3 : ℝ) ^ ((nn : ℤ) : ℝ) *
          (∫ omega : ShellSeq d,
            shellDerivNormSum lowScale highScale z0 omega ^ (4 : ℝ) ∂M.P.toMeasure) ^
              ((4 : ℝ)⁻¹)) ≤ Bd) :
    gridFourthMomentRoot (cutoffSampleLaw M).toMeasure
        (interiorMesoCubeGrid d K nn outer)
        (fun R' omega => meshOscillationCell nn
          (neumannFluxField sigma omega.val lowScale highScale e' (wN omega.val)) R') ≤
      2 * (d : ℝ) * Bd := by
  classical
  set I : Finset (TriadicCube d) := interiorMesoCubeGrid d K nn outer with hIdef
  set mu : Measure (CutoffSample d) := (cutoffSampleLaw M).toMeasure with hmu
  set sinv : ℝ := ((sigma : ℝ))⁻¹ with hsinv
  have hsinv0 : (0 : ℝ) ≤ sinv := (inv_pos.2 sigma.2).le
  have hd1R : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hd0R : (0 : ℝ) ≤ (d : ℝ) := by linarith
  have he'0 : (0 : ℝ) ≤ vecNorm e' := vecNorm_nonneg e'
  have h3nn : (0 : ℝ) < (3 : ℝ) ^ nn := zpow_pos (by norm_num) nn
  have h3eq : (3 : ℝ) ^ ((nn : ℤ) : ℝ) = (3 : ℝ) ^ nn := Real.rpow_intCast 3 nn
  -- the maximizing base point of the finite grid
  obtain ⟨z0, hz0⟩ :=
    gridFourthMomentRoot_shellDerivNormSum_le_of_base_point M lowScale highScale I
  set Sroot : ℝ := (∫ omega : ShellSeq d,
    shellDerivNormSum lowScale highScale z0 omega ^ (4 : ℝ) ∂M.P.toMeasure) ^ ((4 : ℝ)⁻¹)
    with hSroot
  have hzint : (∫ omega : CutoffSample d,
      shellDerivNormSum lowScale highScale z0 omega.val ^ (4 : ℝ) ∂mu) =
      ∫ omega : ShellSeq d,
        shellDerivNormSum lowScale highScale z0 omega ^ (4 : ℝ) ∂M.P.toMeasure :=
    integral_cutoffSampleLaw_val M
      (fun omega => shellDerivNormSum lowScale highScale z0 omega ^ (4 : ℝ))
  rw [hzint] at hz0
  have hSroot0 : (0 : ℝ) ≤ Sroot := by
    rw [hSroot]
    exact Real.rpow_nonneg (integral_nonneg fun omega =>
      Real.rpow_nonneg (shellDerivNormSum_nonneg _ _ _ _) _) _
  -- the gradient root, on the closure's carrier
  set rootG : ℝ := gridFourthMomentRoot mu I
    (fun R' omega => meshOscillationCell nn (wN omega.val).toH1Function.grad R')
    with hrootG
  have hrootG0 : (0 : ℝ) ≤ rootG := by
    rw [hrootG]
    exact Real.rpow_nonneg (gridFourthMoment_nonneg _ _ _) _
  have hrootEq : rootG = gridFourthMomentRoot M.P.toMeasure I
      (fun R' omega => meshOscillationCell nn (wN omega).toH1Function.grad R') := by
    rw [hrootG, hmu]
    exact gridFourthMomentRoot_val_cutoffSampleLaw M I
      (fun R' omega => meshOscillationCell nn (wN omega).toH1Function.grad R')
  have hendz : rootG + sinv * ((3 : ℝ) ^ nn * Sroot) ≤ Bd := by
    have hbase := hend z0
    rw [h3eq] at hbase
    rw [hrootEq]
    exact hbase
  have hBd0 : (0 : ℝ) ≤ Bd := by
    have hterm : (0 : ℝ) ≤ sinv * ((3 : ℝ) ^ nn * Sroot) := by positivity
    linarith
  -- the deterministic forcing majorant
  set cst : ℝ := (3 : ℝ) ^ nn * (sinv * (d : ℝ) * vecNorm e') with hcst
  have hcst0 : (0 : ℝ) ≤ cst := by
    rw [hcst]
    exact mul_nonneg h3nn.le (mul_nonneg (mul_nonneg hsinv0 hd0R) he'0)
  set H : TriadicCube d → CutoffSample d → ℝ := fun R' omega =>
    cst * shellDerivNormSum lowScale highScale (triadicCubeShift R') omega.val with hH
  -- the cellwise split
  have hle : ∀ R' ∈ I, ∀ omega : CutoffSample d,
      meshOscillationCell nn
          (neumannFluxField sigma omega.val lowScale highScale e' (wN omega.val)) R' ≤
        meshOscillationCell nn (wN omega.val).toH1Function.grad R' + H R' omega := by
    intro R' hR' omega
    have hscale : R'.scale = nn :=
      scale_eq_of_mem_mesoCubeGrid (interiorMesoCubeGrid_subset hR')
    have hwindow : openCubeAtScale (triadicCubeShift R') nn = openCubeSet R' := by
      rw [← hscale]
      exact openCubeAtScale_triadicCubeShift_eq_openCubeSet R'
    have hgrad : MemVectorL2 (openCubeAtScale (triadicCubeShift R') nn)
        (wN omega.val).toH1Function.grad := by
      rw [hwindow]
      exact memVectorL2_of_subset (hwin R' hR') (wN omega.val).toH1Function.grad_memVectorL2
    have hforce : MemVectorL2 (openCubeAtScale (triadicCubeShift R') nn)
        (streamForcing ((sigma : ℝ))⁻¹ omega.val lowScale highScale e') := by
      rw [hwindow]
      exact memVectorL2_openCubeSet_of_continuous R'
        (continuous_streamForcing ((sigma : ℝ))⁻¹ omega.val lowScale highScale e')
    have hsplit := meshOscillationCell_neumannFluxField_le (sigma := sigma) omega.val
      lowScale highScale e' (wN omega.val) nn hnn R' hgrad hforce
    refine hsplit.trans (le_of_eq ?_)
    rw [hH, hcst, hsinv]
    ring
  -- the two moment bounds
  have hGmom : gridFourthMoment mu I
      (fun R' omega => meshOscillationCell nn (wN omega.val).toH1Function.grad R') ≤
      rootG ^ (4 : ℕ) :=
    gridFourthMoment_le_pow_four_of_root_le mu I _ (le_of_eq hrootG)
  have hHroot : gridFourthMomentRoot mu I H ≤ cst * Sroot := by
    have hconst := gridFourthMomentRoot_const_mul' (d := d) mu I hcst0
      (fun (R' : TriadicCube d) (omega : CutoffSample d) =>
        shellDerivNormSum lowScale highScale (triadicCubeShift R') omega.val)
    rw [hH, hconst]
    exact mul_le_mul_of_nonneg_left hz0 hcst0
  have hHmom : gridFourthMoment mu I H ≤ (cst * Sroot) ^ (4 : ℕ) :=
    gridFourthMoment_le_pow_four_of_root_le mu I H hHroot
  -- the two integrabilities
  have hHint : ∀ R' ∈ I, Integrable (fun omega => H R' omega ^ (4 : ℝ)) mu := by
    intro R' _
    have hbase : Integrable (fun omega : CutoffSample d =>
        shellDerivNormSum lowScale highScale (triadicCubeShift R') omega.val ^ (4 : ℝ))
        mu := by
      rw [hmu]
      exact integrable_comp_val_cutoffSampleLaw M
        (integrable_shellDerivNormSum_rpow_four M hlt (triadicCubeShift R'))
    have hfun : (fun omega : CutoffSample d => H R' omega ^ (4 : ℝ)) =
        fun omega : CutoffSample d => cst ^ (4 : ℕ) *
          (shellDerivNormSum lowScale highScale (triadicCubeShift R') omega.val ^
            (4 : ℝ)) := by
      funext omega
      rw [hH, rpow_four_eq_pow_four, rpow_four_eq_pow_four, mul_pow]
    rw [hfun]
    exact hbase.const_mul _
  -- the grid Minkowski step
  have hsum := gridFourthMomentRoot_le_add_of_le mu I
    (fun R' omega => meshOscillationCell nn
      (neumannFluxField sigma omega.val lowScale highScale e' (wN omega.val)) R')
    (fun R' omega => meshOscillationCell nn (wN omega.val).toH1Function.grad R') H
    hrootG0 (mul_nonneg hcst0 hSroot0)
    (fun R' _ omega => meshOscillationCell_nonneg _ _ _) hle hoscInt hHint hGmom hHmom
  refine hsum.trans ?_
  -- the numerical closing step
  have h8 : (8 : ℝ) ^ ((4 : ℝ)⁻¹) ≤ 2 := by
    have hmono : (8 : ℝ) ^ ((4 : ℝ)⁻¹) ≤ (16 : ℝ) ^ ((4 : ℝ)⁻¹) :=
      Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
    have hval : (16 : ℝ) ^ ((4 : ℝ)⁻¹) = 2 := by
      have h16 : (16 : ℝ) = (2 : ℝ) ^ ((4 : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]; norm_num
      rw [h16, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    linarith [hmono, hval.le, hval.ge]
  have hcS : cst * Sroot ≤ (d : ℝ) * (sinv * ((3 : ℝ) ^ nn * Sroot)) := by
    have hstep : cst * Sroot =
        (d : ℝ) * vecNorm e' * (sinv * ((3 : ℝ) ^ nn * Sroot)) := by
      rw [hcst]; ring
    have hbase : (0 : ℝ) ≤ sinv * ((3 : ℝ) ^ nn * Sroot) := by positivity
    have hfac : (d : ℝ) * vecNorm e' ≤ (d : ℝ) := by
      calc (d : ℝ) * vecNorm e' ≤ (d : ℝ) * 1 := mul_le_mul_of_nonneg_left he' hd0R
        _ = (d : ℝ) := mul_one _
    rw [hstep]
    exact mul_le_mul_of_nonneg_right hfac hbase
  have hinner : rootG + cst * Sroot ≤ (d : ℝ) * Bd := by
    have hgd : rootG ≤ (d : ℝ) * rootG := le_mul_of_one_le_left hrootG0 hd1R
    have hmul : (d : ℝ) * (rootG + sinv * ((3 : ℝ) ^ nn * Sroot)) ≤ (d : ℝ) * Bd :=
      mul_le_mul_of_nonneg_left hendz hd0R
    have hexp : (d : ℝ) * (rootG + sinv * ((3 : ℝ) ^ nn * Sroot)) =
        (d : ℝ) * rootG + (d : ℝ) * (sinv * ((3 : ℝ) ^ nn * Sroot)) := by ring
    rw [hexp] at hmul
    linarith [hcS, hgd, hmul]
  have hpos : (0 : ℝ) ≤ rootG + cst * Sroot := by
    have := mul_nonneg hcst0 hSroot0
    linarith
  calc (8 : ℝ) ^ ((4 : ℝ)⁻¹) * (rootG + cst * Sroot)
      ≤ 2 * (rootG + cst * Sroot) := mul_le_mul_of_nonneg_right h8 hpos
    _ ≤ 2 * ((d : ℝ) * Bd) := by linarith [hinner]
    _ = 2 * (d : ℝ) * Bd := by ring

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

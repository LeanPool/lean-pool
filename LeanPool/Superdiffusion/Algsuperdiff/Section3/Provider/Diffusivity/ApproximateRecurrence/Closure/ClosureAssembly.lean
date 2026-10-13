/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.AnnealedLimitJunction
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.JunctionDischargePrincipalSwitch
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.JunctionDischargeStepFiveDisplay
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.JunctionDischargeStepFour
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.NodeContract
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.ShellSumEnergyDisplay

/-!
# ClosureAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The closure assembly: the two displays at one explicit pair of correctors

`Closure.Junctions` names the four junctions of the closure node and proves two
`private` assembly skeletons from them.  This module carries the assembly as
far as the proved producers allow: it **chooses** the corrector families,
discharges Junction 4 at them for every large localization cube, reduces the
drift limit to two typing binders, and states the two printed displays
conditionally on what is genuinely still in flight.

## Two shape deltas against `Closure.Junctions`' skeletons, and what replaces
them

The skeletons `upperDisplay_of_junctions` / `lowerDisplay_of_junctions` of
`Closure.Junctions` cannot be used here, for two independent reasons.

1. **They are `private`.**  A `private` declaration is visible only inside its
   own module, so no other file can instantiate them.  They are therefore
   re-proved here, from the *public*
   `Closure.StepSixClosure.upperDisplay_of_annealedBlockBound` and
   `..._lowerDisplay_of_annealedBlockBound`, with the same proof.

2. **Their quantification over the localization cube does not match the
   producers.**  The skeletons consume the junctions as

   ```
     {j : ℕ}   and   (hswitch : ∀ K : ℕ, PrincipalSwitchEndpoint M n h (K : ℤ) j ...)
   ```

   i.e. at *one fixed descendant depth `j`* and at *every* cube scale `K`.
   Both producers of `hswitch` and `hsplit` --- the proved principal-response
   terminal
`exists_const_descendantsAverage_integral_principalEnergy_le_annealedLimit`
   and the proved structural split
`LocalizationRecurrenceMesh.exists_localizationRecurrenceMeshSplit_le_descendantsAverage_expanded`
   --- carry the depth-naming identity

   ```
     ((originCube d Kc).scale : ℤ) - (j : ℤ)
       = recurrenceMesoScale recurrenceGapMultiplier M.gamma m (hgap : ℤ)
   ```

   and `(originCube d Kc).scale = Kc`, so at a fixed `j` that identity pins `Kc`
   to the single value `j + recurrenceMesoScale ...`.  Both producers also carry
   the localization gap `10^10 cgamma^{-1} <= Kc - m`, which fails for small
   `Kc`.  A `∀ K` premise at fixed `j` is therefore not obtainable from them.

   Exactly two changes are needed, both harmless for the limit passage: the depth
   becomes a **family** `jf : ℕ → ℕ` (one depth per cube scale), and the junctions are
   consumed **eventually** in `K` rather than for all `K` (`ge_of_tendsto` in place of
   `ge_of_tendsto'`).  `upperDisplay_of_junctionFamilies` and
   `lowerDisplay_of_junctionFamilies` below are the skeletons in that shape;
   `closureMeshDepth` is the depth family the producers name.

## What is supplied

* `upperDisplay_of_junctionFamilies`, `lowerDisplay_of_junctionFamilies` --- the
  two assembly skeletons in the corrected shape.
* `closureDirichletFamily`, `closureNeumannFamily` --- the two corrector
  families of `e.def.w`, indexed by the increment path exactly as
  `Closure.alongIncrementPath` and the fresh-shell energy display require, built
  from `Corrector.exists_isZeroTraceDirichletRhsWeakSolution_openCubeSet_of_continuous`
  and its Neumann mirror.  Their two weak formulations are proved at every
  `(K, f)`, and transported to the `streamForcing` shape the terminal, Step 4
  and Step 5 read, by `Corrector.toVec_realize_valuePathForcing_shellSumValuePath`.
* `closureMeshDepth`, `eventually_closureMeshDepth_scale` --- the depth family
  and its depth-naming identity, valid for every large cube scale.
* `eventually_principalSwitchEndpoint_closureFamilies` --- **Junction 4 at the
  chosen families**, for every large cube scale, from
  `Closure.JunctionDischargePrincipalSwitch.principalSwitchEndpoint_of_terminal`.
* `tendsto_neumannCubeEnergy_closureNeumannFamily`,
  `tendsto_dirichletCubeEnergy_closureDirichletFamily` --- the drift limit `hlimit` of
  both skeletons, reduced to the *two `AEStronglyMeasurable` typing binders* the proved
  display
  `Corrector.ShellSumEnergyDisplay.tendsto_integral_cutoffSample_cubeAverage_display`
  already carries; the two weak formulations it asks for are discharged by the
  construction, and the limit value is matched to `Closure.shellDrift` through
  `Closure.shellDrift_eq_shellSum`.
* `exists_const_recurrenceUpperDisplay_of_inflight`,
  `exists_const_recurrenceLowerDisplay_of_inflight` --- the two printed displays
  of `e.what.do.we.have`, conditional on the premises listed below and on
  nothing else.

## The premises that remain, and their producers

Neither conditional assembly assumes any estimate of the manuscript beyond the
following, each of which is a *named producer's* output:

| premise | content | producer |
|---|---|---|
| `hsplit` | Junction 3, `e.lower.bound.basic.split` + `e.lower.bound.localization.terms` at the
`cgamma^10` endpoint | **IN**, lane `gamma10-fold`; reduce to one finite grid first with
`Closure.AnnealedLimitJunction.annealedSplitEndpoint_of_integral_ch02CoarseBlockMatrix_le` |
| `hstep4` | Junction 1 at the chosen families |
`Closure.JunctionDischargeStepFour.step4GaugeEndpoint_of_correctors`, whose `hD` binder is
`isZeroTraceDirichletRhsWeakSolution_alongIncrementPath` below and whose four remaining binders are
the analytic side conditions its own docstring table charges to
`Corrector.CorrectorMeasurableGradient` and `Corrector.CorrectorLimitNode` |
| `hstep5` | Junction 2 at the chosen families |
`Closure.JunctionDischargeStepFiveDisplay.step5GaugeEndpoint_of_correctors_gauge` (per-cube gauge),
whose `hosc` binder is supplied by `Closure.Step5DefectGauge`'s re-sited full-mesh producer and
whose remaining binders are that module's own table |
| `hDm`, `hNm` | `AEStronglyMeasurable` of the two cube energies along the increment path | the
path-carrier analogue of `Corrector.CorrectorMeasurableForcing.continuous_contMatrixFieldL2`
composed with `Corrector.MeasurablePrereqSolutionOperator`'s continuous solution operators; not
built here |

`hgamma`, `hcap`, `hsmall` are the parameter-regime facts the manuscript grants
(`e.cgamma.constraints`, `Closure.shellDrift_le_cap`); they are carried as
binders, not assumed away.

## References

* ABK26, `l.approximate.recurrence.formula`, Steps 4--6.
* ABK26, `e.def.w`; `e.perturb.assumption`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector

noncomputable section

variable {d : ℕ}

private theorem switchBudget_nonneg' (M : ABKModel d) (Ec : {E : ℝ // 1 ≤ E}) :
    0 ≤ 3 * principalResponseSwitchBudget M Ec 64 := by
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  rw [principalResponseSwitchBudget_eq]
  have h1 : (0 : ℝ) ≤ principalResponseBudgetConst :=
    principalResponseBudgetConst_pos.le
  have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ (128 : ℕ) := by positivity
  have h3 : (0 : ℝ) ≤ (Ec : ℝ) ^ 2 * Real.log M.gamma ^ 2 * M.gamma := by positivity
  have h4 := mul_nonneg (mul_nonneg h1 h2) h3
  linarith

theorem upperDisplay_of_junctionFamilies (M : ABKModel d) {n : ℤ} {h : ℕ}
    {jf : ℕ → ℕ} {Ec : {E : ℝ // 1 ≤ E}} {e' : Vec d}
    {wD : ∀ K : ℕ, C(Vec d, Mat d) → H10Function (openCubeSet (originCube d (K : ℤ)))}
    {wN : ∀ K : ℕ,
      C(Vec d, Mat d) → H1MeanZeroFunction (openCubeSet (originCube d (K : ℤ)))}
    (he' : vecNormSq e' = 1)
    (hgamma : M.gamma ≤ Real.exp (-1))
    (hcap : shellDrift M n h ≤ shellIncrementCap)
    (hsplit : ∀ᶠ K : ℕ in Filter.atTop,
      AnnealedSplitEndpoint M n h (K : ℤ) (jf K) 0 e'
        (alongIncrementPath n h (wD K)) (alongIncrementPath n h (wN K)))
    (hswitch : ∀ᶠ K : ℕ in Filter.atTop,
      PrincipalSwitchEndpoint M n h (K : ℤ) (jf K) Ec 0 e'
        (alongIncrementPath n h (wD K)) (alongIncrementPath n h (wN K)))
    (hstep4 : ∀ᶠ K : ℕ in Filter.atTop,
      Step4GaugeEndpoint M n h K (jf K) e' (wD K) (wN K))
    (hlimit : Filter.Tendsto (fun K : ℕ => neumannCubeEnergy M n h K (wN K))
      Filter.atTop (nhds (shellDrift M n h))) :
    RecurrenceUpperDisplay M closureConstant (Ec : ℝ) n h := by
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hbud0 : 0 ≤ 3 * principalResponseSwitchBudget M Ec 64 :=
    switchBudget_nonneg' M Ec
  have hchain : ∀ᶠ K : ℕ in Filter.atTop,
      blockVecDot (recurrenceP (Annealed.sigmaBar M n) 0 e')
          (blockMatVecMul (annealedLimitBlock (Annealed.sigmaBar M (n + (h : ℤ))))
            (recurrenceP (Annealed.sigmaBar M n) 0 e')) ≤
        (1 + 3 * principalResponseSwitchBudget M Ec 64) *
            (1 + neumannCubeEnergy M n h K (wN K)) +
          (M.gamma ^ (6 : ℕ) + M.gamma ^ (10 : ℕ)) := by
    filter_upwards [hsplit, hswitch, hstep4] with K hs hw h4
    unfold AnnealedSplitEndpoint at hs
    unfold PrincipalSwitchEndpoint at hw
    unfold Step4GaugeEndpoint at h4
    have hmono := mul_le_mul_of_nonneg_left h4 (by linarith : (0 : ℝ) ≤
      1 + 3 * principalResponseSwitchBudget M Ec 64)
    linarith [hs, hw, hmono]
  have htend : Filter.Tendsto
      (fun K : ℕ => (1 + 3 * principalResponseSwitchBudget M Ec 64) *
          (1 + neumannCubeEnergy M n h K (wN K)) +
        (M.gamma ^ (6 : ℕ) + M.gamma ^ (10 : ℕ))) Filter.atTop
      (nhds ((1 + 3 * principalResponseSwitchBudget M Ec 64) *
          (1 + shellDrift M n h) + (M.gamma ^ (6 : ℕ) + M.gamma ^ (10 : ℕ)))) :=
    ((hlimit.const_add 1).const_mul
      (1 + 3 * principalResponseSwitchBudget M Ec 64)).add_const _
  refine upperDisplay_of_annealedBlockBound
    (gauge := 1 + shellDrift M n h)
    (rem := M.gamma ^ (6 : ℕ) + M.gamma ^ (10 : ℕ)) M he' hbud0 hcap ?_ le_rfl ?_
  · exact ge_of_tendsto htend hchain
  · have hstep := switch_and_remainders_le_flatError M Ec hgamma
    have h15 : (0 : ℝ) ≤ 2 * M.gamma ^ (15 : ℕ) := by positivity
    linarith [hstep, h15]

theorem lowerDisplay_of_junctionFamilies (M : ABKModel d) {n : ℤ} {h : ℕ}
    {jf : ℕ → ℕ} {Ec : {E : ℝ // 1 ≤ E}} {e : Vec d} {Fend : ℝ}
    {wD : ∀ K : ℕ, C(Vec d, Mat d) → H10Function (openCubeSet (originCube d (K : ℤ)))}
    {wN : ∀ K : ℕ,
      C(Vec d, Mat d) → H1MeanZeroFunction (openCubeSet (originCube d (K : ℤ)))}
    (he : vecNormSq e = 1) (hFend : 0 ≤ Fend)
    (hgamma : M.gamma ≤ Real.exp (-1))
    (hsmall : 3 * principalResponseSwitchBudget M Ec 64 ≤ 1)
    (hsplit : ∀ᶠ K : ℕ in Filter.atTop,
      AnnealedSplitEndpoint M n h (K : ℤ) (jf K) e 0
        (alongIncrementPath n h (wD K)) (alongIncrementPath n h (wN K)))
    (hswitch : ∀ᶠ K : ℕ in Filter.atTop,
      PrincipalSwitchEndpoint M n h (K : ℤ) (jf K) Ec e 0
        (alongIncrementPath n h (wD K)) (alongIncrementPath n h (wN K)))
    (hstep5 : ∀ᶠ K : ℕ in Filter.atTop,
      Step5GaugeEndpoint M n h K (jf K) e Fend (wD K) (wN K))
    (hlimit : Filter.Tendsto (fun K : ℕ => dirichletCubeEnergy M n h K (wD K))
      Filter.atTop (nhds (shellDrift M n h))) :
    RecurrenceLowerDisplay M (max closureConstant (2 * Fend)) (Ec : ℝ) n h := by
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hbud0 : 0 ≤ 3 * principalResponseSwitchBudget M Ec 64 :=
    switchBudget_nonneg' M Ec
  have hcross0 : (0 : ℝ) ≤ Fend * ((h : ℝ)) ^ 2 *
      (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ *
      (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)) := by
    have hr := Real.rpow_pos_of_pos (show (0 : ℝ) < 3 by norm_num)
      (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ))
    have hs : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
    positivity
  have hosc0 : (0 : ℝ) ≤ M.gamma ^ (15 : ℕ) := by positivity
  have hchain : ∀ᶠ K : ℕ in Filter.atTop,
      blockVecDot (recurrenceP (Annealed.sigmaBar M n) e 0)
          (blockMatVecMul (annealedLimitBlock (Annealed.sigmaBar M (n + (h : ℤ))))
            (recurrenceP (Annealed.sigmaBar M n) e 0)) ≤
        (1 + 3 * principalResponseSwitchBudget M Ec 64) *
            (1 - dirichletCubeEnergy M n h K (wD K) +
              Fend * ((h : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ *
                (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)) +
              M.gamma ^ (15 : ℕ)) +
          (M.gamma ^ (6 : ℕ) + M.gamma ^ (10 : ℕ)) := by
    filter_upwards [hsplit, hswitch, hstep5] with K hs hw h5
    unfold AnnealedSplitEndpoint at hs
    unfold PrincipalSwitchEndpoint at hw
    unfold Step5GaugeEndpoint at h5
    have hmono := mul_le_mul_of_nonneg_left h5 (by linarith : (0 : ℝ) ≤
      1 + 3 * principalResponseSwitchBudget M Ec 64)
    linarith [hs, hw, hmono]
  have htend : Filter.Tendsto
      (fun K : ℕ => (1 + 3 * principalResponseSwitchBudget M Ec 64) *
          (1 - dirichletCubeEnergy M n h K (wD K) +
            Fend * ((h : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ *
              (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)) +
            M.gamma ^ (15 : ℕ)) +
        (M.gamma ^ (6 : ℕ) + M.gamma ^ (10 : ℕ))) Filter.atTop
      (nhds ((1 + 3 * principalResponseSwitchBudget M Ec 64) *
          (1 - shellDrift M n h +
            Fend * ((h : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ *
              (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)) +
            M.gamma ^ (15 : ℕ)) + (M.gamma ^ (6 : ℕ) + M.gamma ^ (10 : ℕ)))) :=
    (((((hlimit.const_sub 1).add_const _).add_const _).const_mul
      (1 + 3 * principalResponseSwitchBudget M Ec 64)).add_const _)
  refine lowerDisplay_of_annealedBlockBound
    (gauge := 1 - shellDrift M n h +
      Fend * ((h : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ *
        (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)) + M.gamma ^ (15 : ℕ))
    (rem := M.gamma ^ (6 : ℕ) + M.gamma ^ (10 : ℕ))
    (cross := Fend * ((h : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ *
      (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)))
    (osc := M.gamma ^ (15 : ℕ))
    M he hbud0 hsmall hcross0 hosc0 ?_ le_rfl ?_ ?_
  · exact ge_of_tendsto htend hchain
  · have hC : 2 * Fend ≤ max closureConstant (2 * Fend) := le_max_right _ _
    have hr := Real.rpow_pos_of_pos (show (0 : ℝ) < 3 by norm_num)
      (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ))
    have hs : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
    have hbase : (0 : ℝ) ≤ ((h : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ *
        (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)) := by positivity
    calc 2 * (Fend * ((h : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ *
          (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)))
        = (2 * Fend) * (((h : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ *
            (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ))) := by ring
      _ ≤ max closureConstant (2 * Fend) *
            (((h : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ *
              (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ))) :=
          mul_le_mul_of_nonneg_right hC hbase
      _ = max closureConstant (2 * Fend) * ((h : ℝ)) ^ 2 *
            (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ *
            (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)) := by ring
  · have hstep := switch_and_remainders_le_flatError M Ec hgamma
    have hCle : closureConstant ≤ max closureConstant (2 * Fend) := le_max_left _ _
    have hbase : (0 : ℝ) ≤ (Ec : ℝ) ^ 2 * Real.log M.gamma ^ 2 * M.gamma := by
      positivity
    have hmono : recurrenceFlatError M closureConstant (Ec : ℝ) ≤
        recurrenceFlatError M (max closureConstant (2 * Fend)) (Ec : ℝ) := by
      unfold recurrenceFlatError
      calc closureConstant * (Ec : ℝ) ^ 2 * Real.log M.gamma ^ 2 * M.gamma
          = closureConstant * ((Ec : ℝ) ^ 2 * Real.log M.gamma ^ 2 * M.gamma) := by
            ring
        _ ≤ max closureConstant (2 * Fend) *
              ((Ec : ℝ) ^ 2 * Real.log M.gamma ^ 2 * M.gamma) :=
            mul_le_mul_of_nonneg_right hCle hbase
        _ = max closureConstant (2 * Fend) * (Ec : ℝ) ^ 2 * Real.log M.gamma ^ 2 *
              M.gamma := by ring
    have hcapnn : (0 : ℝ) ≤ shellIncrementCap := shellIncrementCap_pos.le
    have hdrop : 3 * principalResponseSwitchBudget M Ec 64 ≤
        (1 + shellIncrementCap) * (3 * principalResponseSwitchBudget M Ec 64) := by
      nlinarith [hbud0, hcapnn]
    linarith [hstep, hmono, hdrop]

/-! ## The corrector families -/

open Algsuperdiff.Section3.Provider.Corrector (realize valuePathForcing
  shellSumValuePath toVec_realize_valuePathForcing_shellSumValuePath
  continuous_toVec_realize_valuePathForcing) in
/-- The Dirichlet corrector of `e.def.w` at the gauged direction `c • e`, on the
localization cube `cu_K`, indexed by the increment path. -/
def closureDirichletFamily [NeZero d] (c : ℝ) (e : Vec d) (K : ℕ)
    (f : C(Vec d, Mat d)) : H10Function (openCubeSet (originCube d (K : ℤ))) :=
  Classical.choose
    (exists_isZeroTraceDirichletRhsWeakSolution_openCubeSet_of_continuous
      (originCube d (K : ℤ))
      (g := fun x => -(realize (valuePathForcing (c • e)) f x).toVec)
      (continuous_toVec_realize_valuePathForcing (c • e) f).neg)

open Algsuperdiff.Section3.Provider.Corrector (realize valuePathForcing
  continuous_toVec_realize_valuePathForcing) in
/-- The Neumann corrector of `e.def.w`, likewise. -/
def closureNeumannFamily (c : ℝ) (e : Vec d) (K : ℕ)
    (f : C(Vec d, Mat d)) : H1MeanZeroFunction (openCubeSet (originCube d (K : ℤ))) :=
  Classical.choose
    (exists_isMeanZeroNeumannRhsWeakSolution_openCubeSet_of_continuous
      (originCube d (K : ℤ))
      (g := fun x => -(realize (valuePathForcing (c • e)) f x).toVec)
      (continuous_toVec_realize_valuePathForcing (c • e) f).neg)

open Algsuperdiff.Section3.Provider.Corrector (realize valuePathForcing
  continuous_toVec_realize_valuePathForcing) in
theorem isZeroTraceDirichletRhsWeakSolution_closureDirichletFamily [NeZero d]
    (c : ℝ) (e : Vec d) (K : ℕ) (f : C(Vec d, Mat d)) :
    IsZeroTraceDirichletRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
      (openCubeSet (originCube d (K : ℤ))) (closureDirichletFamily c e K f)
      (fun x => -(realize (valuePathForcing (c • e)) f x).toVec) :=
  Classical.choose_spec
    (exists_isZeroTraceDirichletRhsWeakSolution_openCubeSet_of_continuous
      (originCube d (K : ℤ))
      (g := fun x => -(realize (valuePathForcing (c • e)) f x).toVec)
      (continuous_toVec_realize_valuePathForcing (c • e) f).neg)

open Algsuperdiff.Section3.Provider.Corrector (realize valuePathForcing
  continuous_toVec_realize_valuePathForcing) in
theorem isMeanZeroNeumannRhsWeakSolution_closureNeumannFamily
    (c : ℝ) (e : Vec d) (K : ℕ) (f : C(Vec d, Mat d)) :
    IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
      (openCubeSet (originCube d (K : ℤ))) (closureNeumannFamily c e K f)
      (fun x => -(realize (valuePathForcing (c • e)) f x).toVec) :=
  Classical.choose_spec
    (exists_isMeanZeroNeumannRhsWeakSolution_openCubeSet_of_continuous
      (originCube d (K : ℤ))
      (g := fun x => -(realize (valuePathForcing (c • e)) f x).toVec)
      (continuous_toVec_realize_valuePathForcing (c • e) f).neg)

open Algsuperdiff.Section3.Provider.Corrector (realize valuePathForcing
  shellSumValuePath toVec_realize_valuePathForcing_shellSumValuePath) in
theorem isZeroTraceDirichletRhsWeakSolution_alongIncrementPath [NeZero d]
    (c : ℝ) (e : Vec d) (K : ℕ) (n : ℤ) (h : ℕ) (omega : ShellSeq d) :
    IsZeroTraceDirichletRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
      (openCubeSet (originCube d (K : ℤ)))
      (alongIncrementPath n h (closureDirichletFamily c e K) omega)
      (fun x => -streamForcing c omega n (n + (h : ℤ)) e x) := by
  have hforce : (fun x => -(realize (valuePathForcing (c • e))
      (shellSumValuePath n (n + (h : ℤ)) omega) x).toVec) =
      fun x => -streamForcing c omega n (n + (h : ℤ)) e x := by
    funext x
    rw [toVec_realize_valuePathForcing_shellSumValuePath c e n (n + (h : ℤ)) omega x]
  have h0 := isZeroTraceDirichletRhsWeakSolution_closureDirichletFamily c e K
    (shellSumValuePath n (n + (h : ℤ)) omega)
  rw [hforce] at h0
  exact h0

open Algsuperdiff.Section3.Provider.Corrector (realize valuePathForcing
  shellSumValuePath toVec_realize_valuePathForcing_shellSumValuePath) in
theorem isMeanZeroNeumannRhsWeakSolution_alongIncrementPath
    (c : ℝ) (e : Vec d) (K : ℕ) (n : ℤ) (h : ℕ) (omega : ShellSeq d) :
    IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
      (openCubeSet (originCube d (K : ℤ)))
      (alongIncrementPath n h (closureNeumannFamily c e K) omega)
      (fun x => -streamForcing c omega n (n + (h : ℤ)) e x) := by
  have hforce : (fun x => -(realize (valuePathForcing (c • e))
      (shellSumValuePath n (n + (h : ℤ)) omega) x).toVec) =
      fun x => -streamForcing c omega n (n + (h : ℤ)) e x := by
    funext x
    rw [toVec_realize_valuePathForcing_shellSumValuePath c e n (n + (h : ℤ)) omega x]
  have h0 := isMeanZeroNeumannRhsWeakSolution_closureNeumannFamily c e K
    (shellSumValuePath n (n + (h : ℤ)) omega)
  rw [hforce] at h0
  exact h0

/-! ## The mesh depth attached to a localization scale -/

/-- The descendant depth the terminal and the structural split both name at the
localization scale `K`: the unique `j` with `K - j = recurrenceMesoScale`. -/
def closureMeshDepth (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℕ) : ℕ :=
  ((K : ℤ) - recurrenceMesoScale recurrenceGapMultiplier M.gamma
    (n + (h : ℤ)) (h : ℤ)).toNat

theorem eventually_closureMeshDepth_scale (M : ABKModel d) (n : ℤ) (h : ℕ) :
    ∀ᶠ K : ℕ in Filter.atTop,
      ((originCube d (K : ℤ)).scale : ℤ) - ((closureMeshDepth M n h K : ℕ) : ℤ) =
        recurrenceMesoScale recurrenceGapMultiplier M.gamma (n + (h : ℤ)) (h : ℤ) := by
  filter_upwards [Filter.eventually_ge_atTop
    (recurrenceMesoScale recurrenceGapMultiplier M.gamma (n + (h : ℤ)) (h : ℤ)).toNat]
    with K hK
  have hle : recurrenceMesoScale recurrenceGapMultiplier M.gamma
      (n + (h : ℤ)) (h : ℤ) ≤ (K : ℤ) :=
    le_trans (Int.self_le_toNat _) (by exact_mod_cast hK)
  change ((K : ℤ)) - ((closureMeshDepth M n h K : ℕ) : ℤ) = _
  rw [closureMeshDepth, Int.toNat_of_nonneg (by omega)]
  ring

theorem vecNorm_eq_one_of_vecNormSq_eq_one {e : Vec d} (he : vecNormSq e = 1) :
    Ch02.vecNorm e = 1 := by
  rw [vecNorm_eq_sqrt_vecNormSq, he, Real.sqrt_one]

/-! ## The drift limit at the constructed families -/

open Algsuperdiff.Section3.Provider.Corrector (realize valuePathForcing
  shellSumValuePath tendsto_integral_cutoffSample_cubeAverage_display
  shellSumValuePathLaw) in
/-- **The Neumann half of `e.perturb.assumption` at the closure's own corrector family.**
The only remaining binders are the two `AEStronglyMeasurable` typing conditions the proved
display carries; the two weak formulations are discharged by the construction. -/
theorem tendsto_neumannCubeEnergy_closureNeumannFamily [NeZero d] (M : ABKModel d)
    (n : ℤ) (h : ℕ) {e : Vec d} (he : Ch02.vecNorm e = 1)
    (hDm : ∀ K : ℕ, AEStronglyMeasurable
      (fun f => cubeAverage (originCube d (K : ℤ))
        fun x => vecDot
          ((closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K f).toH1Function.grad x)
          ((closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K f).toH1Function.grad x))
      (shellSumValuePathLaw M.P n (n + (h : ℤ))).toMeasure)
    (hNm : ∀ K : ℕ, AEStronglyMeasurable
      (fun f => cubeAverage (originCube d (K : ℤ))
        fun x => vecDot
          ((closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K f).toH1Function.grad x)
          ((closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K f).toH1Function.grad x))
      (shellSumValuePathLaw M.P n (n + (h : ℤ))).toMeasure) :
    Filter.Tendsto
      (fun K : ℕ => neumannCubeEnergy M n h K
        (closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K))
      Filter.atTop (nhds (shellDrift M n h)) := by
  have hdisp := (tendsto_integral_cutoffSample_cubeAverage_display M
    ((Annealed.sigmaBar M n : ℝ))⁻¹ he n (n + (h : ℤ))
    (fun K => closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
    (fun K => closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
    hDm hNm
    (fun K f => isZeroTraceDirichletRhsWeakSolution_closureDirichletFamily _ e K f)
    (fun K f => isMeanZeroNeumannRhsWeakSolution_closureNeumannFamily _ e K f)).2
  have hval : ((Annealed.sigmaBar M n : ℝ))⁻¹ ^ 2 *
      (Disorder.cstar M * Real.log 3 *
        ∑ k ∈ Finset.Ioc n (n + (h : ℤ)), (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) =
      shellDrift M n h := by
    rw [shellDrift_eq_shellSum, inv_pow]
  rwa [hval] at hdisp

open Algsuperdiff.Section3.Provider.Corrector (realize valuePathForcing
  shellSumValuePath tendsto_integral_cutoffSample_cubeAverage_display
  shellSumValuePathLaw) in
/-- **The Dirichlet half**, the Step-5 mirror of the previous statement. -/
theorem tendsto_dirichletCubeEnergy_closureDirichletFamily [NeZero d] (M : ABKModel d)
    (n : ℤ) (h : ℕ) {e : Vec d} (he : Ch02.vecNorm e = 1)
    (hDm : ∀ K : ℕ, AEStronglyMeasurable
      (fun f => cubeAverage (originCube d (K : ℤ))
        fun x => vecDot
          ((closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K f).toH1Function.grad x)
          ((closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K f).toH1Function.grad x))
      (shellSumValuePathLaw M.P n (n + (h : ℤ))).toMeasure)
    (hNm : ∀ K : ℕ, AEStronglyMeasurable
      (fun f => cubeAverage (originCube d (K : ℤ))
        fun x => vecDot
          ((closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K f).toH1Function.grad x)
          ((closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K f).toH1Function.grad x))
      (shellSumValuePathLaw M.P n (n + (h : ℤ))).toMeasure) :
    Filter.Tendsto
      (fun K : ℕ => dirichletCubeEnergy M n h K
        (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K))
      Filter.atTop (nhds (shellDrift M n h)) := by
  have hdisp := (tendsto_integral_cutoffSample_cubeAverage_display M
    ((Annealed.sigmaBar M n : ℝ))⁻¹ he n (n + (h : ℤ))
    (fun K => closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
    (fun K => closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
    hDm hNm
    (fun K f => isZeroTraceDirichletRhsWeakSolution_closureDirichletFamily _ e K f)
    (fun K f => isMeanZeroNeumannRhsWeakSolution_closureNeumannFamily _ e K f)).1
  have hval : ((Annealed.sigmaBar M n : ℝ))⁻¹ ^ 2 *
      (Disorder.cstar M * Real.log 3 *
        ∑ k ∈ Finset.Ioc n (n + (h : ℤ)), (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) =
      shellDrift M n h := by
    rw [shellDrift_eq_shellSum, inv_pow]
  rwa [hval] at hdisp

/-! ## Junction 4 at the constructed families, for every large localization cube -/

theorem eventually_principalSwitchEndpoint_closureFamilies (d : ℕ) [NeZero d]
    (hd : 2 ≤ d) :
    ∃ Cterm : ℝ, 0 < Cterm ∧
      ∀ (M : ABKModel d) (n : ℤ) (h : ℕ) (Ec : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (n + (h : ℤ) - 1) Ec →
        0 < h →
        Cterm * (Disorder.cstar M)⁻¹ ≤ (Ec : ℝ) →
        M.gamma ≤ (Ec : ℝ) ^ (-5 : ℤ) →
        (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
        ∀ e e' : Vec d, Ch02.vecNorm e ≤ 1 → Ch02.vecNorm e' ≤ 1 →
          ∀ᶠ K : ℕ in Filter.atTop,
            PrincipalSwitchEndpoint M n h (K : ℤ) (closureMeshDepth M n h K) Ec e e'
              (alongIncrementPath n h
                (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K))
              (alongIncrementPath n h
                (closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e' K)) := by
  obtain ⟨Cterm, hCterm, hmain⟩ := principalSwitchEndpoint_of_terminal d hd
  refine ⟨Cterm, hCterm, ?_⟩
  intro M n h Ec hstate hh hCE hgammaE hhcap e e' he he'
  have hbig : ∀ᶠ K : ℕ in Filter.atTop,
      (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (((K : ℤ)) : ℝ) - ((n + (h : ℤ) : ℤ) : ℝ) := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
      ((10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ + ((n + (h : ℤ) : ℤ) : ℝ))] with K hK
    push_cast at hK ⊢
    linarith
  filter_upwards [eventually_closureMeshDepth_scale M n h, hbig] with K hscale hK
  refine hmain M n (K : ℤ) h Ec hstate hh hCE hgammaE hhcap hK e e' he he'
    (closureMeshDepth M n h K) hscale _ _
    (fun omega => isZeroTraceDirichletRhsWeakSolution_alongIncrementPath _ e K n h omega)
    (fun omega => isMeanZeroNeumannRhsWeakSolution_alongIncrementPath _ e' K n h omega)

/-! ## The conditional assembly -/

open Algsuperdiff.Section3.Provider.Corrector (shellSumValuePathLaw) in
theorem exists_const_recurrenceUpperDisplay_of_inflight (d : ℕ) [NeZero d]
    (hd : 2 ≤ d) :
    ∃ Cterm : ℝ, 0 < Cterm ∧
      ∀ (M : ABKModel d) (n : ℤ) (h : ℕ) (Ec : {E : ℝ // 1 ≤ E}) (e' : Vec d),
        vecNormSq e' = 1 →
        Algsuperdiff.Frozen.Section3.inductionState M (n + (h : ℤ) - 1) Ec →
        0 < h →
        Cterm * (Disorder.cstar M)⁻¹ ≤ (Ec : ℝ) →
        M.gamma ≤ (Ec : ℝ) ^ (-5 : ℤ) →
        (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
        M.gamma ≤ Real.exp (-1) →
        shellDrift M n h ≤ shellIncrementCap →
        (∀ᶠ K : ℕ in Filter.atTop,
          AnnealedSplitEndpoint M n h (K : ℤ) (closureMeshDepth M n h K) 0 e'
            (alongIncrementPath n h
              (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ 0 K))
            (alongIncrementPath n h
              (closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e' K))) →
        (∀ᶠ K : ℕ in Filter.atTop,
          Step4GaugeEndpoint M n h K (closureMeshDepth M n h K) e'
            (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ 0 K)
            (closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e' K)) →
        (∀ K : ℕ, AEStronglyMeasurable
          (fun f => cubeAverage (originCube d (K : ℤ))
            fun x => vecDot
              ((closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e' K f).toH1Function.grad x)
              ((closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e' K f).toH1Function.grad x))
          (shellSumValuePathLaw M.P n (n + (h : ℤ))).toMeasure) →
        (∀ K : ℕ, AEStronglyMeasurable
          (fun f => cubeAverage (originCube d (K : ℤ))
            fun x => vecDot
              ((closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e' K f).toH1Function.grad x)
              ((closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e' K f).toH1Function.grad x))
          (shellSumValuePathLaw M.P n (n + (h : ℤ))).toMeasure) →
        RecurrenceUpperDisplay M closureConstant (Ec : ℝ) n h := by
  obtain ⟨Cterm, hCterm, hswitch⟩ :=
    eventually_principalSwitchEndpoint_closureFamilies d hd
  refine ⟨Cterm, hCterm, ?_⟩
  intro M n h Ec e' he' hstate hh hCE hgammaE hhcap hgamma hcap hsplit hstep4 hDm hNm
  have hzero : Ch02.vecNorm (0 : Vec d) ≤ 1 := by
    have h0 : vecNormSq (0 : Vec d) = 0 := by simp [vecNormSq, vecDot]
    rw [vecNorm_eq_sqrt_vecNormSq, h0, Real.sqrt_zero]
    norm_num
  have he1 : Ch02.vecNorm e' = 1 := vecNorm_eq_one_of_vecNormSq_eq_one he'
  exact upperDisplay_of_junctionFamilies M he' hgamma hcap hsplit
    (hswitch M n h Ec hstate hh hCE hgammaE hhcap 0 e' hzero (le_of_eq he1))
    hstep4
    (tendsto_neumannCubeEnergy_closureNeumannFamily M n h he1 hDm hNm)

open Algsuperdiff.Section3.Provider.Corrector (shellSumValuePathLaw) in
theorem exists_const_recurrenceLowerDisplay_of_inflight (d : ℕ) [NeZero d]
    (hd : 2 ≤ d) :
    ∃ Cterm : ℝ, 0 < Cterm ∧
      ∀ (M : ABKModel d) (n : ℤ) (h : ℕ) (Ec : {E : ℝ // 1 ≤ E}) (e : Vec d)
        (Fend : ℝ),
        vecNormSq e = 1 → 0 ≤ Fend →
        Algsuperdiff.Frozen.Section3.inductionState M (n + (h : ℤ) - 1) Ec →
        0 < h →
        Cterm * (Disorder.cstar M)⁻¹ ≤ (Ec : ℝ) →
        M.gamma ≤ (Ec : ℝ) ^ (-5 : ℤ) →
        (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
        M.gamma ≤ Real.exp (-1) →
        3 * principalResponseSwitchBudget M Ec 64 ≤ 1 →
        (∀ᶠ K : ℕ in Filter.atTop,
          AnnealedSplitEndpoint M n h (K : ℤ) (closureMeshDepth M n h K) e 0
            (alongIncrementPath n h
              (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K))
            (alongIncrementPath n h
              (closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ 0 K))) →
        (∀ᶠ K : ℕ in Filter.atTop,
          Step5GaugeEndpoint M n h K (closureMeshDepth M n h K) e Fend
            (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
            (closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ 0 K)) →
        (∀ K : ℕ, AEStronglyMeasurable
          (fun f => cubeAverage (originCube d (K : ℤ))
            fun x => vecDot
              ((closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K f).toH1Function.grad x)
              ((closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K f).toH1Function.grad x))
          (shellSumValuePathLaw M.P n (n + (h : ℤ))).toMeasure) →
        (∀ K : ℕ, AEStronglyMeasurable
          (fun f => cubeAverage (originCube d (K : ℤ))
            fun x => vecDot
              ((closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K f).toH1Function.grad x)
              ((closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K f).toH1Function.grad x))
          (shellSumValuePathLaw M.P n (n + (h : ℤ))).toMeasure) →
        RecurrenceLowerDisplay M (max closureConstant (2 * Fend)) (Ec : ℝ) n h := by
  obtain ⟨Cterm, hCterm, hswitch⟩ :=
    eventually_principalSwitchEndpoint_closureFamilies d hd
  refine ⟨Cterm, hCterm, ?_⟩
  intro M n h Ec e Fend he hFend hstate hh hCE hgammaE hhcap hgamma hsmall hsplit
    hstep5 hDm hNm
  have hzero : Ch02.vecNorm (0 : Vec d) ≤ 1 := by
    have h0 : vecNormSq (0 : Vec d) = 0 := by simp [vecNormSq, vecDot]
    rw [vecNorm_eq_sqrt_vecNormSq, h0, Real.sqrt_zero]
    norm_num
  have he1 : Ch02.vecNorm e = 1 := vecNorm_eq_one_of_vecNormSq_eq_one he
  exact lowerDisplay_of_junctionFamilies M he hFend hgamma hsmall hsplit
    (hswitch M n h Ec hstate hh hCE hgammaE hhcap e 0 (le_of_eq he1) hzero)
    hstep5
    (tendsto_dirichletCubeEnergy_closureDirichletFamily M n h he1 hDm hNm)

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.ClosureFinal
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.SplitProducerLoad
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationBackgroundClass

/-!
# SplitProducerFold

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `ClosureSplitInput` reduced to three named residual obligations

ABK26, `l.approximate.recurrence.formula`, Steps 1--3,
`e.lower.bound.basic.split`, `e.lower.bound.localization.terms`.

## What this module does

`Closure.ClosureFinal.ClosureSplitInput` is the finite-grid half of Steps 1--3
at the `cgamma^10` endpoint, read at the closure's own corrector families.  The
proved structural endpoint
`integral_blockVecDot_recurrenceP_le_principalSwitchEnergyAverage_add`
already delivers

```
  E[ P . bfA_{n+h}(cu_K) P ]  <=  principalSwitchEnergyAverage + fluctuationEnergyAverage ,
```

and `principalSwitchEnergyAverage` is *definitionally* the closure's own
`Closure.principalEnergyAverage` (checked: the `rfl` below).  This module
performs the whole remaining assembly --- the eventual large-cube gate, the
eventual depth-naming identity, the weak-solution properties of the closure
families, the `hintLHS` producer, and both direction pairs --- and isolates
exactly what is *not* proved anywhere in the repository as of writing:

`SplitScaleObligations`, three propositions at one localization scale and one
direction pair.

| obligation | content | status |
|---|---|---|
| (1) | per-cell sample integrability of the switch energy at `P_z` | **produced** (see the audit
correction below):
`exists_const_eventually_integrable_switchCubeEnergy_closureFamilies`;
its *measurability* half is `Closure.SplitProducerLoad.measurable_principalPz_cutoffSample` |
| (2) | per-cell sample integrability of the background energy `mu(a_omega; P_z + bfF_z)` |
**produced** (see the audit correction below):
`Closure.SplitObligationsBackground.integrable_doubledMuValue_meshCellBackground_of_cellMoments`,
fed by the cell moments of `Closure.SplitFoldCellMoments`; its *measurability* half is
`LocalizationFluctuationBackgroundClass.measurable_doubledMuValue_meshCellBackground` |
| (3) | `fluctuationEnergyAverage <= cgamma^10` | open: Step 2 itself  |

Both are **obsolete**: the two dominations have since proved, and the two
obligations are now produced unconditionally at the closure's own families and
inside the closure's own regime by `Closure.SplitObligationsRegime` and
`Closure.SplitObligationsBackground`, assembled in
`Closure.SplitObligations.splitScaleObligations_integrability_of_regime` and
(with the cell moments discharged) in
`Closure.SplitFoldIntegrability.splitScaleObligations_integrability_closureFamilies`.
`Closure.SplitFoldIntegrability.closureSplitInput_of_gammaTenBound` consumes
exactly that, leaving conjunct (3) --- Step 2 --- as the sole residual
obligation of `Closure.ClosureFinal.ClosureSplitInput`.  Nothing in *this* file
changed; only the status column was stale.

Everything else the split input needs is discharged below.  In particular the
two typing binders `hpot`, `hflux` and the whole `hcomp` front are supplied by
`LocalizationFluctuationBackgroundClass`, so no measurability proposition
survives in `SplitScaleObligations`.

## Scope

There is no `sorry`, no `admit`, no custom axiom and no `set_option
maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula`,
  `e.lower.bound.basic.split`, Step 2,
  `e.lower.bound.localization.terms`, `e.recurrence.params`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

noncomputable section

variable {d : ℕ}

/-! ## The closure's corrector families, named -/

/-- The Dirichlet corrector of `e.def.w` the closure reads at direction `e`, on
`cu_K`, along the increment path.  A name for the term `ClosureSplitInput`
prints. -/
def closureDirichletAlong [NeZero d] (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℕ)
    (e : Vec d) : ShellSeq d → H10Function (openCubeSet (originCube d (K : ℤ))) :=
  alongIncrementPath n h (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)

/-- The mean-zero Neumann mirror. -/
def closureNeumannAlong (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℕ) (e' : Vec d) :
    ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d (K : ℤ))) :=
  alongIncrementPath n h (closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e' K)

theorem isZeroTraceDirichletRhsWeakSolution_closureDirichletAlong [NeZero d]
    (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℕ) (e : Vec d) (omega : ShellSeq d) :
    IsZeroTraceDirichletRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
      (openCubeSet (originCube d (K : ℤ))) (closureDirichletAlong M n h K e omega)
      (fun x => -Corrector.streamForcing ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n
        (n + (h : ℤ)) e x) :=
  isZeroTraceDirichletRhsWeakSolution_alongIncrementPath _ e K n h omega

theorem isMeanZeroNeumannRhsWeakSolution_closureNeumannAlong [NeZero d]
    (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℕ) (e' : Vec d) (omega : ShellSeq d) :
    IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
      (openCubeSet (originCube d (K : ℤ))) (closureNeumannAlong M n h K e' omega)
      (fun x => -Corrector.streamForcing ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n
        (n + (h : ℤ)) e' x) :=
  isMeanZeroNeumannRhsWeakSolution_alongIncrementPath _ e' K n h omega

/-! ## The residual obligations -/

/-- **The three residual obligations of the finite-grid half of Steps 1--3**, at
one localization scale `K` and one direction pair.

Two integrability statements in the sample, per mesoscopic cell, and the Step-2
estimate itself.  No measurability proposition occurs: the measurability halves
of the first two are proved
(`Closure.SplitProducerLoad.measurable_principalPz_cutoffSample` and
`LocalizationFluctuationBackgroundClass.measurable_doubledMuValue_meshCellBackground`),
and the whole `hcomp` front is proved as well. -/
def SplitScaleObligations [NeZero d] (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℕ)
    (e e' : Vec d) : Prop :=
  (∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) (closureMeshDepth M n h K),
      Integrable (fun omega : CutoffSample d =>
        switchCubeEnergy M (n + (h : ℤ)) R
          (principalPz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e e' R
            (closureDirichletAlong M n h K e omega.val)
            (closureNeumannAlong M n h K e' omega.val)) omega)
        (cutoffSampleLaw M).toMeasure) ∧
    (∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) (closureMeshDepth M n h K),
      Integrable (fun omega : CutoffSample d =>
        Ch02.doubledMuValue (Ch02.cubeDomain R) (meshCellCoeff M (n + (h : ℤ)) R omega)
          (meshCellBackground M n h (K : ℤ) e e' (closureDirichletAlong M n h K e)
            (closureNeumannAlong M n h K e') R omega))
        (cutoffSampleLaw M).toMeasure) ∧
    fluctuationEnergyAverage M n h (K : ℤ) (closureMeshDepth M n h K) e e'
        (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e') ≤
      M.gamma ^ (10 : ℕ)

/-! ## The reduction at one direction pair -/

/-- **The Step-1--3 display at one direction pair, from the three residual
obligations.**

exactly on `SplitScaleObligations` holding for all sufficiently large
localization cubes.  Everything else --- the large-cube gate, the depth-naming
identity, the weak-solution properties of the closure families, the
unconditional `hintLHS` producer, the typing binders and the whole `hcomp`
measurability front --- is discharged here. -/
theorem eventually_integral_le_principalEnergyAverage_add [NeZero d]
    (M : ABKModel d) (n : ℤ) (h : ℕ) (e e' : Vec d)
    (hobl : ∀ᶠ K : ℕ in Filter.atTop, SplitScaleObligations M n h K e e') :
    ∀ᶠ K : ℕ in Filter.atTop,
      ∫ omega : CutoffSample d,
          blockVecDot (recurrenceP (Annealed.sigmaBar M n) e e')
            (blockMatVecMul
              (Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube d (K : ℤ)))
                ((coefficientCutoffTriadicCoeffFamily M (n + (h : ℤ)) omega).coeffOn
                  (originCube d (K : ℤ))))
              (recurrenceP (Annealed.sigmaBar M n) e e'))
          ∂(cutoffSampleLaw M).toMeasure ≤
        principalEnergyAverage M n h (K : ℤ) (closureMeshDepth M n h K) e e'
            (alongIncrementPath n h
              (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K))
            (alongIncrementPath n h
              (closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e' K)) +
          M.gamma ^ (10 : ℕ) := by
  classical
  have hbig : ∀ᶠ K : ℕ in Filter.atTop,
      (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (((K : ℤ)) : ℝ) - ((n + (h : ℤ) : ℤ) : ℝ) := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
      ((10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ + ((n + (h : ℤ) : ℤ) : ℝ))] with K hK
    push_cast at hK ⊢
    linarith
  filter_upwards [hobl, eventually_closureMeshDepth_scale M n h, hbig]
    with K hobligations hscale hK
  obtain ⟨hprin, hbg, hfluct⟩ := hobligations
  let : MeasurableSpace (HilbertBlockL2 (openCubeSet (originCube d (K : ℤ)))) :=
    borel _
  have : BorelSpace (HilbertBlockL2 (openCubeSet (originCube d (K : ℤ)))) := ⟨rfl⟩
  set wD := closureDirichletAlong M n h K e with hwDdef
  set wN := closureNeumannAlong M n h K e' with hwNdef
  have hwD : ∀ omega : ShellSeq d, IsZeroTraceDirichletRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
      (openCubeSet (originCube d (K : ℤ))) (wD omega)
      (fun x => -Corrector.streamForcing ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n
        (n + (h : ℤ)) e x) :=
    isZeroTraceDirichletRhsWeakSolution_closureDirichletAlong M n h K e
  have hwN : ∀ omega : ShellSeq d, IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
      (openCubeSet (originCube d (K : ℤ))) (wN omega)
      (fun x => -Corrector.streamForcing ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n
        (n + (h : ℤ)) e' x) :=
    isMeanZeroNeumannRhsWeakSolution_closureNeumannAlong M n h K e'
  -- the fluctuation cell integrability, from the two residual integrabilities
  have hintFluct : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ))
      (closureMeshDepth M n h K),
      Integrable (fun omega : CutoffSample d =>
        meshFluctuationCellIntegrand M n h (K : ℤ) e e' wD wN R omega)
        (cutoffSampleLaw M).toMeasure := by
    intro R hR
    let : MeasurableSpace (HilbertBlockL2
        ((Ch02.cubeDomain R : Ch02.Domain d) : Set (Vec d))) := borel _
    have : BorelSpace (HilbertBlockL2
        ((Ch02.cubeDomain R : Ch02.Domain d) : Set (Vec d))) := ⟨rfl⟩
    exact integrable_meshFluctuationCellIntegrand' M n h (K : ℤ) e e' wD wN R
      (memVectorL2_meshCellBackground_potential M n h (K : ℤ) e e' wD wN hR)
      (memVectorL2_meshCellBackground_flux M n h (K : ℤ) e e' wD wN hR)
      (aemeasurable_doubledMuValue_meshCellBackground_add_testField M n h (K : ℤ) e e'
        wD wN hwD hwN hR (cutoffSampleLaw M).toMeasure)
      (hbg R hR) (hprin R hR)
  have hmain := integral_blockVecDot_recurrenceP_le_principalSwitchEnergyAverage_add
    M n (K : ℤ) h hK e e' (closureMeshDepth M n h K) hscale wD wN
    (fun omega : CutoffSample d => hwD omega.val)
    (fun omega : CutoffSample d => hwN omega.val)
    (integrable_recurrenceP_coarseBlockMatrix M n (K : ℤ) h e e')
    hprin hintFluct
  refine hmain.trans ?_
  have hpe : principalSwitchEnergyAverage M n h (K : ℤ) (closureMeshDepth M n h K) e e'
      wD wN =
      principalEnergyAverage M n h (K : ℤ) (closureMeshDepth M n h K) e e'
        (alongIncrementPath n h
          (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K))
        (alongIncrementPath n h
          (closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e' K)) := rfl
  rw [← hpe]
  linarith [hfluct]

/-! ## The split input -/

/-- **`Closure.ClosureSplitInput` from the residual obligations at both gauge
branches.**

on `hobl`; nothing else is assumed.  This module does **not** prove
`ClosureSplitInput`. -/
theorem closureSplitInput_of_obligations (d : ℕ) [NeZero d] {Csplit : ℝ}
    (hCsplit : 0 < Csplit)
    (hobl : ∀ (M : ABKModel d) (n : ℤ) (h : ℕ) (Ec : {E : ℝ // 1 ≤ E}) (e : Vec d),
      vecNormSq e = 1 → ClosureRegime Csplit M n h Ec →
      (∀ᶠ K : ℕ in Filter.atTop, SplitScaleObligations M n h K 0 e) ∧
        (∀ᶠ K : ℕ in Filter.atTop, SplitScaleObligations M n h K e 0)) :
    ClosureSplitInput d := by
  intro _hd
  refine ⟨Csplit, hCsplit, ?_⟩
  intro M n h Ec e he hreg
  obtain ⟨hup, hlo⟩ := hobl M n h Ec e he hreg
  exact ⟨eventually_integral_le_principalEnergyAverage_add M n h 0 e hup,
    eventually_integral_le_principalEnergyAverage_add M n h e 0 hlo⟩

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

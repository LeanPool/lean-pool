/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationSelectValue
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationRecurrenceMesh
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseSwitchActualPerCube

/-!
# LocalizationFluctuationSelectEndpoint

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Step-2 endpoint integrand: well-posed, de-existentialized, consumer-shaped

ABK26, `l.approximate.recurrence.formula`, Steps 1--2, read at the recurrence
pair `(n, n+h)` of the closure junctions.

## What this module does

The proved structural split
`LocalizationRecurrenceMesh.exists_localizationRecurrenceMeshSplit_le_descendantsAverage_expanded`
holds **one sample at a time** and delivers the two cell fields `S_z`, `tilde
S_z` through an existential.  The Step-3 consumer
`Closure.AnnealedLimitJunction.annealedSplitEndpoint_of_integral_ch02CoarseBlockMatrix_le`
needs the *sample integral* of that split's left-hand side, so its right-hand
side has to be an honest function of the sample.  Three things are supplied
here.

1. **De-existentialization** (`blockVecDot_recurrenceP_le_descendantsAverage_switch_add_fluctuation`).
   The split's right-hand side is rewritten, at each cell, as
   `switchCubeEnergy` plus the canonical number
   `LocalizationFluctuationSelectValue.localizationFluctuationValue`, which is
   a function of the cell datum only.  The existential quantifiers vanish from
   the statement: **no minimizer is chosen, and no measurable selection of the
   minimizer family is needed**, because the two printed fluctuation summands
   only ever enter through their sum, and that sum is a difference of two
   variational minima.  See the `LocalizationFluctuationSelectValue` header for
   why this is the form the no-choice-without-uniqueness rule demands: the
   field-slope minimizer is unique only a.e., so a chosen witness would carry no
   information, while the *number* is choice-free.

2. **The interchange** (`integral_descendantsAverage`,
   `integrable_descendantsAverage`, `descendantsAverage_add`).
   `descendantsAverage` is a normalized sum over the finite `Finset`
   `descendantsAtDepth (cu_{Kc}) j`, so the sample integral passes through it as
   soon as each cell integrand is sample-integrable.  Both directions are
   proved, with the per-cell integrability as an explicit binder.

3. **The carrier identification**
   (`switchCubeEnergy_eq_blockVecDot_coarseBlockMatrix`,
   `principalPz_shell_normalize`, `localizationFz_shell_normalize`).  The
   principal summand of the split is the Chapter 2 coarse pairing `P_z.
   bfA(z+cu_n) P_z`, and `switchCubeEnergy` is *by definition* that pairing
   (`PrincipalResponseSwitchActualPerCube.switchCubeEnergy`); the
   identification therefore already exists in the cone and is `rfl`.  The only
   genuinely missing piece was the shell-index normalization `(n + h) - h = n`
   between the split's `(m, h)` indexing and the junctions' `(n, n+h)`
   indexing; it is proved here.  The neighbouring identification of the
   *annealed* layer's cube matrix with the Chapter 2 one is the proved
   `Closure.AnnealedLimitPassage.coarseBlockMatrix_cubeSet_coefficientCutoff_eq_ch02`
   and is not restated.

## The endpoint

`integral_blockVecDot_recurrenceP_le_principalSwitchEnergyAverage_add` packages
1--3: it produces

```
  E[ P . bfA_{n+h}(cu_{Kc}) P ]
    <=  principalSwitchEnergyAverage  +  fluctuationEnergyAverage ,
```

whose first summand is, *verbatim*, `Closure.Junctions.principalEnergyAverage M
n h Kc j e e' wD wN` with its definition unfolded (that module is a live lane
and is deliberately not imported here; the two terms are syntactically equal
after `unfold`).  A fold lane that proves

```
  fluctuationEnergyAverage M n h Kc j e e' wD wN  <=  M.gamma ^ 10
```

--- which is Step 2, --- therefore closes the hypothesis `hfinite` of
`annealedSplitEndpoint_of_integral_ch02CoarseBlockMatrix_le` by one `le_trans`.

That composition was **checked**, in an untracked probe that additionally
imports `Closure.AnnealedLimitJunction` (not imported here: `Closure` is a live
lane).  Both halves elaborate:

```
  example ... : principalSwitchEnergyAverage M n h Kc j e e' wD wN
                  = Closure.principalEnergyAverage M n h Kc j e e' wD wN := rfl

  example ... (hstep2 : fluctuationEnergyAverage M n h Kc j e e' wD wN
                          <= M.gamma ^ (10 : Nat)) :
      Closure.AnnealedSplitEndpoint M n h Kc j e e' wD wN :=
    Closure.annealedSplitEndpoint_of_integral_ch02CoarseBlockMatrix_le M n h Kc j Kc
      e e' wD wN
      (le_trans
        (integral_blockVecDot_recurrenceP_le_principalSwitchEnergyAverage_add M n Kc h
          hK e e' j hscale wD wN hwD hwN hintLHS hintPrincipal hintFluctuation)
        (by ... linarith))
```

The junction is instantiated at the cube scale `K := Kc`, i.e. at the *same*
large cube the split localizes inside; no second scale is introduced.

## The surviving obligations, stated exactly

The endpoint carries three integrability binders and no other analytic
hypothesis:

* `hintLHS` --- sample-integrability of the coarse quadratic form on `cu_{Kc}`;
* `hintPrincipal` --- sample-integrability of `switchCubeEnergy` at `P_z`, per
  cell.  A producer of the a.e.-strong measurability half is proved
  (`PrincipalResponseGoodEnergy.aestronglyMeasurable_switchCubeEnergy`, which
  consumes a measurable `P_z` family); the domination half is the
  good-event/bad-event budget of Step 3.
* `hintFluctuation` --- sample-integrability of the canonical fluctuation
  number, per cell.  The fluctuation number is instead a variational minimum in
  which the sample enters through **both** the coefficient `a_omega` and the
  slope field `bfF_z(omega)`, and no proved statement asserts that `omega |->
  mu_field(U, a_omega; F_omega)` is measurable.  The exact missing statement
  is recorded in the docstring of `fluctuationEnergyAverage`.

## References

* ABK26, `l.approximate.recurrence.formula`,
  `e.lower.bound.basic.split`, Step 2,
  `e.lower.bound.localization.terms`, `e.Pz.def`, `e.Fz.def`, the switch
  display.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## `descendantsAverage` is a finite normalized sum -/

/-- Two cell functions that agree on the grid have the same descendant
average. -/
theorem descendantsAverage_congr (Q : TriadicCube d) (j : ℕ)
    {F G : TriadicCube d → ℝ} (h : ∀ R ∈ descendantsAtDepth Q j, F R = G R) :
    descendantsAverage Q j F = descendantsAverage Q j G := by
  show ((descendantsAtDepth Q j).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q j, F R =
    ((descendantsAtDepth Q j).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q j, G R
  rw [Finset.sum_congr rfl h]

/-- The descendant average is additive. -/
theorem descendantsAverage_add (Q : TriadicCube d) (j : ℕ)
    (F G : TriadicCube d → ℝ) :
    descendantsAverage Q j (fun R => F R + G R) =
      descendantsAverage Q j F + descendantsAverage Q j G := by
  show ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
      ∑ R ∈ descendantsAtDepth Q j, (F R + G R) =
    ((descendantsAtDepth Q j).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q j, F R +
      ((descendantsAtDepth Q j).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q j, G R
  rw [Finset.sum_add_distrib]
  ring

/-! ## The interchange of the sample integral with the cell average -/

/-- **Sample integrability of the cell average from per-cell integrability.**
The grid is a `Finset`, so this is a finite sum of integrable functions. -/
theorem integrable_descendantsAverage {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} (Q : TriadicCube d) (j : ℕ)
    (f : Omega → TriadicCube d → ℝ)
    (hint : ∀ R ∈ descendantsAtDepth Q j, Integrable (fun omega => f omega R) mu) :
    Integrable (fun omega => descendantsAverage Q j (f omega)) mu := by
  have hrw : (fun omega => descendantsAverage Q j (f omega)) =
      fun omega => ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j, f omega R := rfl
  rw [hrw]
  exact (integrable_finsetSum _ hint).const_mul _

/-- **The interchange `int_omega avsum_z = avsum_z int_omega`.**  The cell
average is a normalized finite sum, so the sample integral passes through it as
soon as every cell integrand is sample-integrable.  This is item (b) of the
`gamma^{10}` endpoint chain. -/
theorem integral_descendantsAverage {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} (Q : TriadicCube d) (j : ℕ)
    (f : Omega → TriadicCube d → ℝ)
    (hint : ∀ R ∈ descendantsAtDepth Q j, Integrable (fun omega => f omega R) mu) :
    ∫ omega, descendantsAverage Q j (f omega) ∂mu =
      descendantsAverage Q j (fun R => ∫ omega, f omega R ∂mu) := by
  show ∫ omega, ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
      ∑ R ∈ descendantsAtDepth Q j, f omega R ∂mu = _
  rw [integral_const_mul, integral_finsetSum _ hint]
  rfl

/-! ## The de-existentialized split at the recurrence pair -/

/-- **The localized variational test, with the existential removed** (at the
recurrence pair `(n, n+h)`).

```
P . bfA_{n+h}(cu_{Kc}) P
  <= avsum_z ( switchCubeEnergy(P_z)  +  fluct(z+cu_n; P_z, bfF_z) ) ,
```

with `P = recurrenceP (shom_n) e e'` and `fluct` the canonical fluctuation
number of `LocalizationFluctuationSelectValue`.  **The right-hand side mentions
no minimizer**: it is a function of the sample, the two correctors and the
geometry only, so it can be integrated in the sample without any selection.

exactly on the binders of the proved split it is derived from --- the
large-cube gate, the depth-naming identity, and the two weak formulations of
`e.def.w`.  No measurability, integrability or smallness proposition occurs. -/
theorem blockVecDot_recurrenceP_le_descendantsAverage_switch_add_fluctuation
    (M : ABKModel d) (omega : CutoffSample d) (n Kc : ℤ) (h : ℕ)
    (hK : (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (Kc : ℝ) - ((n + (h : ℤ) : ℤ) : ℝ))
    (e e' : Vec d) (j : ℕ)
    (hscale : ((originCube d Kc).scale : ℤ) - (j : ℤ) =
      recurrenceMesoScale recurrenceGapMultiplier M.gamma (n + (h : ℤ)) (h : ℤ))
    (wD : H10Function (openCubeSet (originCube d Kc)))
    (wN : H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (hwD : IsZeroTraceDirichletRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
      (openCubeSet (originCube d Kc)) wD
      (fun x => -Corrector.streamForcing
        ((Annealed.sigmaBar M n : ℝ))⁻¹ omega.val n (n + (h : ℤ)) e x))
    (hwN : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
      (openCubeSet (originCube d Kc)) wN
      (fun x => -Corrector.streamForcing
        ((Annealed.sigmaBar M n : ℝ))⁻¹ omega.val n (n + (h : ℤ)) e' x)) :
    blockVecDot (recurrenceP (Annealed.sigmaBar M n) e e')
        (blockMatVecMul
          (Book.Ch02.coarseBlockMatrix (cubeDomain (originCube d Kc))
            ((coefficientCutoffTriadicCoeffFamily M (n + (h : ℤ)) omega).coeffOn
              (originCube d Kc)))
          (recurrenceP (Annealed.sigmaBar M n) e e')) ≤
      descendantsAverage (originCube d Kc) j
        (fun R =>
          switchCubeEnergy M (n + (h : ℤ)) R
              (principalPz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e e' R wD wN)
              omega +
            localizationFluctuationValue (cubeDomain R)
              ((coefficientCutoffTriadicCoeffFamily M (n + (h : ℤ)) omega).coeffOn R)
              (principalPz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e e' R wD wN)
              (localizationFz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e' R
                wD wN)) := by
  have hm : n + (h : ℤ) - (h : ℤ) = n := by omega
  obtain ⟨S, T, hS, hT, hresp, hle⟩ :=
    exists_localizationRecurrenceMeshSplit_le_descendantsAverage_expanded M omega
      (n + (h : ℤ)) Kc h hK e e' j hscale wD wN (by rw [hm]; exact hwD)
      (by rw [hm]; exact hwN)
  rw [hm] at hS hT hle
  refine hle.trans (le_of_eq (descendantsAverage_congr _ _ fun R hR => ?_))
  rw [localizationFluctuationValue_eq_of_isDoubledMuMinimizerField (hS R hR) (hT R hR)
    (hresp R hR)]
  simp only [switchCubeEnergy, cubeDomain_coe]
  ring

/-! ## The endpoint carriers -/

/-- **The per-cell Step-2 integrand.**  The canonical fluctuation number at the
recurrence carriers, as a function of the sample.  Both correctors are read
along the sample, exactly as `Closure.Junctions.principalEnergyAverage` reads
them. -/
def meshFluctuationCellIntegrand (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ)
    (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (R : TriadicCube d) (omega : CutoffSample d) : ℝ :=
  localizationFluctuationValue (cubeDomain R)
    ((coefficientCutoffTriadicCoeffFamily M (n + (h : ℤ)) omega).coeffOn R)
    (principalPz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e e' R
      (wD omega.val) (wN omega.val))
    (localizationFz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e' R
      (wD omega.val) (wN omega.val))

/-- **The principal half of the endpoint, at the terminal's carrier.**  This is
`Closure.Junctions.principalEnergyAverage M n h Kc j e e' wD wN` with its
definition unfolded; that module is a live lane and is deliberately not imported
here, so the equality is left as a syntactic one for the consumer. -/
def principalSwitchEnergyAverage (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ) (j : ℕ)
    (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc))) : ℝ :=
  descendantsAverage (originCube d Kc) j
    (fun R => ∫ omega : CutoffSample d,
      switchCubeEnergy M (n + (h : ℤ)) R
        (principalPz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e e' R
          (wD omega.val) (wN omega.val)) omega
      ∂(cutoffSampleLaw M).toMeasure)

/-- **The fluctuation half of the endpoint: the quantity Step 2 must bound by
`cgamma^{10}`** (target `e.lower.bound.localization.terms`).

The missing producer, stated exactly, is sample-integrability of the cell
integrand: for each `R` in `descendantsAtDepth (cu_{Kc}) j`,

```
  Integrable (fun omega => meshFluctuationCellIntegrand M n h Kc e e' wD wN R omega)
             ((cutoffSampleLaw M).toMeasure) .
```

The proved measurability statements
(`Provider.Diffusivity.Corrector.CorrectorMeasurable{Forcing,Gradient,Consumer,
Quartic}`, and `LocalizationFluctuationCellIntegrable.measurable_volumeAverage_
vecNormSq_freshShell{Dirichlet,Neumann}Grad`) all factor through *continuous or
Borel functionals of the `L^2` class of `grad w_omega`* at a fixed coefficient.

```
  omega |-> doubledMuField (cubeDomain R) (a_omega) (F_omega)
```

in either argument.  Producing it is a separate, self-contained task. -/
def fluctuationEnergyAverage (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ) (j : ℕ)
    (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc))) : ℝ :=
  descendantsAverage (originCube d Kc) j
    (fun R => ∫ omega : CutoffSample d,
      meshFluctuationCellIntegrand M n h Kc e e' wD wN R omega
      ∂(cutoffSampleLaw M).toMeasure)

/-! ## The endpoint -/

/-- **The Step-1/2 endpoint, well-posed and consumer-shaped.**

```
  E[ P . bfA_{n+h}(cu_{Kc}) P ]
    <=  principalSwitchEnergyAverage  +  fluctuationEnergyAverage .
```

The left-hand side is *verbatim* the left-hand side of the hypothesis `hfinite`
of `Closure.AnnealedLimitJunction.annealedSplitEndpoint_of_integral_ch02CoarseBlockMatrix_le`
at `K := Kc`, and the first summand on the right is *verbatim*
`Closure.Junctions.principalEnergyAverage M n h Kc j e e' wD wN` unfolded.  A
fold lane that proves `fluctuationEnergyAverage <= M.gamma ^ 10` therefore
closes Junction 3 with `le_trans` and `add_le_add_left`.

No estimate on anything is assumed. -/
theorem integral_blockVecDot_recurrenceP_le_principalSwitchEnergyAverage_add
    (M : ABKModel d) (n Kc : ℤ) (h : ℕ)
    (hK : (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (Kc : ℝ) - ((n + (h : ℤ) : ℤ) : ℝ))
    (e e' : Vec d) (j : ℕ)
    (hscale : ((originCube d Kc).scale : ℤ) - (j : ℤ) =
      recurrenceMesoScale recurrenceGapMultiplier M.gamma (n + (h : ℤ)) (h : ℤ))
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (hwD : ∀ omega : CutoffSample d, IsZeroTraceDirichletRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
      (openCubeSet (originCube d Kc)) (wD omega.val)
      (fun x => -Corrector.streamForcing
        ((Annealed.sigmaBar M n : ℝ))⁻¹ omega.val n (n + (h : ℤ)) e x))
    (hwN : ∀ omega : CutoffSample d, IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
      (openCubeSet (originCube d Kc)) (wN omega.val)
      (fun x => -Corrector.streamForcing
        ((Annealed.sigmaBar M n : ℝ))⁻¹ omega.val n (n + (h : ℤ)) e' x))
    (hintLHS : Integrable (fun omega : CutoffSample d =>
      blockVecDot (recurrenceP (Annealed.sigmaBar M n) e e')
        (blockMatVecMul
          (Book.Ch02.coarseBlockMatrix (cubeDomain (originCube d Kc))
            ((coefficientCutoffTriadicCoeffFamily M (n + (h : ℤ)) omega).coeffOn
              (originCube d Kc)))
          (recurrenceP (Annealed.sigmaBar M n) e e')))
      (cutoffSampleLaw M).toMeasure)
    (hintPrincipal : ∀ R ∈ descendantsAtDepth (originCube d Kc) j,
      Integrable (fun omega : CutoffSample d =>
        switchCubeEnergy M (n + (h : ℤ)) R
          (principalPz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e e' R
            (wD omega.val) (wN omega.val)) omega)
        (cutoffSampleLaw M).toMeasure)
    (hintFluctuation : ∀ R ∈ descendantsAtDepth (originCube d Kc) j,
      Integrable (fun omega : CutoffSample d =>
        meshFluctuationCellIntegrand M n h Kc e e' wD wN R omega)
        (cutoffSampleLaw M).toMeasure) :
    ∫ omega : CutoffSample d,
        blockVecDot (recurrenceP (Annealed.sigmaBar M n) e e')
          (blockMatVecMul
            (Book.Ch02.coarseBlockMatrix (cubeDomain (originCube d Kc))
              ((coefficientCutoffTriadicCoeffFamily M (n + (h : ℤ)) omega).coeffOn
                (originCube d Kc)))
            (recurrenceP (Annealed.sigmaBar M n) e e'))
        ∂(cutoffSampleLaw M).toMeasure ≤
      principalSwitchEnergyAverage M n h Kc j e e' wD wN +
        fluctuationEnergyAverage M n h Kc j e e' wD wN := by
  classical
  set cell : CutoffSample d → TriadicCube d → ℝ := fun omega R =>
    switchCubeEnergy M (n + (h : ℤ)) R
        (principalPz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e e' R
          (wD omega.val) (wN omega.val)) omega +
      meshFluctuationCellIntegrand M n h Kc e e' wD wN R omega with hcell
  have hcellint : ∀ R ∈ descendantsAtDepth (originCube d Kc) j,
      Integrable (fun omega => cell omega R) (cutoffSampleLaw M).toMeasure := by
    intro R hR
    exact (hintPrincipal R hR).add (hintFluctuation R hR)
  have hpt : ∀ omega : CutoffSample d,
      blockVecDot (recurrenceP (Annealed.sigmaBar M n) e e')
          (blockMatVecMul
            (Book.Ch02.coarseBlockMatrix (cubeDomain (originCube d Kc))
              ((coefficientCutoffTriadicCoeffFamily M (n + (h : ℤ)) omega).coeffOn
                (originCube d Kc)))
            (recurrenceP (Annealed.sigmaBar M n) e e')) ≤
        descendantsAverage (originCube d Kc) j (cell omega) := fun omega =>
    blockVecDot_recurrenceP_le_descendantsAverage_switch_add_fluctuation M omega n Kc h
      hK e e' j hscale (wD omega.val) (wN omega.val) (hwD omega) (hwN omega)
  calc ∫ omega : CutoffSample d,
        blockVecDot (recurrenceP (Annealed.sigmaBar M n) e e')
          (blockMatVecMul
            (Book.Ch02.coarseBlockMatrix (cubeDomain (originCube d Kc))
              ((coefficientCutoffTriadicCoeffFamily M (n + (h : ℤ)) omega).coeffOn
                (originCube d Kc)))
            (recurrenceP (Annealed.sigmaBar M n) e e'))
        ∂(cutoffSampleLaw M).toMeasure
      ≤ ∫ omega : CutoffSample d, descendantsAverage (originCube d Kc) j (cell omega)
          ∂(cutoffSampleLaw M).toMeasure :=
        integral_mono hintLHS
          (integrable_descendantsAverage (originCube d Kc) j cell hcellint) hpt
    _ = descendantsAverage (originCube d Kc) j
          (fun R => ∫ omega : CutoffSample d, cell omega R
            ∂(cutoffSampleLaw M).toMeasure) :=
        integral_descendantsAverage (originCube d Kc) j cell hcellint
    _ = principalSwitchEnergyAverage M n h Kc j e e' wD wN +
          fluctuationEnergyAverage M n h Kc j e e' wD wN := by
        unfold principalSwitchEnergyAverage fluctuationEnergyAverage
        rw [← descendantsAverage_add]
        refine descendantsAverage_congr _ _ fun R hR => ?_
        exact integral_add (hintPrincipal R hR) (hintFluctuation R hR)

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationJointField

/-!
# LocalizationFluctuationJointBackground

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `hcomp` and the measurability half of `hbg`, from one class hypothesis

ABK26, `l.approximate.recurrence.formula`, Step 2.

## What this module does

`LocalizationFluctuationMuMeasCell.integrable_meshFluctuationCellIntegrand'`
carries two hypotheses whose content is measurability in the sample:

* `hcomp`, for **every** test field `Y` on the cell, of
  `omega |-> mu(a_omega; background_omega + Y)`;
* the measurability half of `hbg`, i.e. the same statement at `Y = 0`.

This module reduces both, **simultaneously and for every `Y` at once**, to the
single statement

```
  omega |->  [ background_omega ]   is measurable into  L^2(cell; R^{2d}) ,
```

i.e. to measurability of the background field's `L^2` class.  Adding a fixed
test field is a translation of the `L^2` carrier, hence continuous, so the class
of `background + Y` is measurable as soon as the class of `background` is; and
`LocalizationFluctuationJointField.measurable_doubledMuValue_meshCellCoeff_of_measurable_class`
then converts a measurable class into a measurable energy.

## The remaining obligation, stated exactly

After this module the whole `hcomp`/`hbg`-measurability front is the single
proposition

```
  Measurable (fun omega : CutoffSample d =>
    toHilbertBlockL2OfBlockField
      (memBlockL2_blockField (hpot omega) (hflux omega)))
```

at `F = meshCellBackground M n h Kc e e' wD wN R`.  Its two legs are the
constant load `P_z` (whose sample measurability is proved at
`PrincipalResponseLoadMeas.measurable_shellIndexSigma_principalPz`) and
`bfF_z`, whose legs are the corrector gradients, proved *as `L^2` classes on
the localization cube* `cu_K` at
`Corrector.measurable_freshShell{Dirichlet,Neumann}GradL2`.  The one piece of
plumbing still missing between the two is the **restriction of an `L^2` class
from the localization cube to the mesoscopic cell**, which
`Corrector.CorrectorMeasurableGradient` explicitly records as not built.

## Binders

Beyond the typing binders: `[NeZero d]`; the vector-`L^2` membership of the two
legs of the background at every sample (a typing property of the corrector
data); and the class measurability.  No integrability, no estimate, no
smallness, and no selection of any minimizer occurs.

## Scope

There is no `sorry`, no `admit`, no custom axiom and no `set_option
maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula`, Step 2, `e.Pz.def`, `e.Fz.def`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open HCPolySupport.Internal.Ch02.BookCh02
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The class map is additive -/

/-- Adding a fixed test field translates the `L^2` class of the background by a
constant, hence preserves measurability of the class. -/
theorem measurable_toHilbertBlockL2OfBlockField_add_const {Omega : Type*}
    [MeasurableSpace Omega] (U : Domain d)
    [MeasurableSpace (HilbertBlockL2 ((U : Domain d) : Set (Vec d)))]
    [BorelSpace (HilbertBlockL2 ((U : Domain d) : Set (Vec d)))]
    {F : Omega → DoubledField d} {Y : DoubledField d}
    (hpot : ∀ omega, MemVectorL2 ((U : Domain d) : Set (Vec d)) (F omega).potential)
    (hflux : ∀ omega, MemVectorL2 ((U : Domain d) : Set (Vec d)) (F omega).flux)
    (hYpot : MemVectorL2 ((U : Domain d) : Set (Vec d)) Y.potential)
    (hYflux : MemVectorL2 ((U : Domain d) : Set (Vec d)) Y.flux)
    (hclass : Measurable fun omega =>
      toHilbertBlockL2OfBlockField (memBlockL2_blockField (hpot omega) (hflux omega))) :
    Measurable fun omega =>
      toHilbertBlockL2OfBlockField
        (memBlockL2_blockField ((hpot omega).add hYpot) ((hflux omega).add hYflux)) := by
  have hrw : (fun omega =>
      toHilbertBlockL2OfBlockField
        (memBlockL2_blockField ((hpot omega).add hYpot) ((hflux omega).add hYflux)))
      = fun omega =>
        toHilbertBlockL2OfBlockField (memBlockL2_blockField (hpot omega) (hflux omega))
          + toHilbertBlockL2OfBlockField (memBlockL2_blockField hYpot hYflux) := by
    funext omega
    exact toHilbertBlockL2OfBlockField_add (memBlockL2_blockField (hpot omega) (hflux omega))
      (memBlockL2_blockField hYpot hYflux)
      (memBlockL2_blockField ((hpot omega).add hYpot) ((hflux omega).add hYflux))
      (fun _ => rfl)
  rw [hrw]
  exact ((continuous_id.add continuous_const).measurable).comp hclass

/-! ## The reduction of `hcomp` and of the measurability half of `hbg` -/

/-- **The `hcomp`/`hbg` measurability front, reduced to one class hypothesis.**

At every fixed competitor `Y` --- in particular at `Y = 0`, which is `hbg` ---
the doubled energy value of the shifted background is measurable in the sample,
given only that the background's own `L^2` class is.

on `hpot`, `hflux` (typing), `hYpot`, `hYflux` (typing of the competitor) and
`hclass`.  No estimate, no integrability and no selection. -/
theorem measurable_doubledMuValue_meshCellCoeff_background_add [NeZero d]
    (M : ABKModel d) (m : ℤ) (R : TriadicCube d)
    [MeasurableSpace (HilbertBlockL2 ((cubeDomain R : Domain d) : Set (Vec d)))]
    [BorelSpace (HilbertBlockL2 ((cubeDomain R : Domain d) : Set (Vec d)))]
    {F : CutoffSample d → DoubledField d} {Y : DoubledField d}
    (hpot : ∀ omega, MemVectorL2 ((cubeDomain R : Domain d) : Set (Vec d))
      (F omega).potential)
    (hflux : ∀ omega, MemVectorL2 ((cubeDomain R : Domain d) : Set (Vec d))
      (F omega).flux)
    (hYpot : MemVectorL2 ((cubeDomain R : Domain d) : Set (Vec d)) Y.potential)
    (hYflux : MemVectorL2 ((cubeDomain R : Domain d) : Set (Vec d)) Y.flux)
    (hclass : Measurable fun omega =>
      toHilbertBlockL2OfBlockField (memBlockL2_blockField (hpot omega) (hflux omega))) :
    Measurable fun omega : CutoffSample d =>
      doubledMuValue (cubeDomain R) (meshCellCoeff M m R omega) (F omega + Y) :=
  measurable_doubledMuValue_meshCellCoeff_of_measurable_class M m R
    (fun omega => F omega + Y)
    (fun omega => memBlockL2_blockField ((hpot omega).add hYpot) ((hflux omega).add hYflux))
    (measurable_toHilbertBlockL2OfBlockField_add_const (cubeDomain R) hpot hflux hYpot hYflux
      hclass)

/-- **`hcomp` of
`LocalizationFluctuationMuMeasCell.integrable_meshFluctuationCellIntegrand'`, in
its own binder shape.**  Every test field on the cell is admissible at once. -/
theorem aemeasurable_doubledMuValue_meshCellCoeff_background_add_testField [NeZero d]
    (M : ABKModel d) (m : ℤ) (R : TriadicCube d)
    [MeasurableSpace (HilbertBlockL2 ((cubeDomain R : Domain d) : Set (Vec d)))]
    [BorelSpace (HilbertBlockL2 ((cubeDomain R : Domain d) : Set (Vec d)))]
    {F : CutoffSample d → DoubledField d}
    (hpot : ∀ omega, MemVectorL2 ((cubeDomain R : Domain d) : Set (Vec d))
      (F omega).potential)
    (hflux : ∀ omega, MemVectorL2 ((cubeDomain R : Domain d) : Set (Vec d))
      (F omega).flux)
    (hclass : Measurable fun omega =>
      toHilbertBlockL2OfBlockField (memBlockL2_blockField (hpot omega) (hflux omega)))
    (mu : Measure (CutoffSample d)) :
    ∀ Y : DoubledField d, IsDoubledTestField (cubeDomain R) Y → AEMeasurable
      (fun omega : CutoffSample d =>
        doubledMuValue (cubeDomain R) (meshCellCoeff M m R omega) (F omega + Y)) mu := by
  intro Y hY
  exact (measurable_doubledMuValue_meshCellCoeff_background_add M m R hpot hflux
    hY.1.1 hY.2.1 hclass).aemeasurable

/-- **The measurability half of `hbg`**: the background energy itself. -/
theorem measurable_doubledMuValue_meshCellCoeff_background [NeZero d]
    (M : ABKModel d) (m : ℤ) (R : TriadicCube d)
    [MeasurableSpace (HilbertBlockL2 ((cubeDomain R : Domain d) : Set (Vec d)))]
    [BorelSpace (HilbertBlockL2 ((cubeDomain R : Domain d) : Set (Vec d)))]
    {F : CutoffSample d → DoubledField d}
    (hpot : ∀ omega, MemVectorL2 ((cubeDomain R : Domain d) : Set (Vec d))
      (F omega).potential)
    (hflux : ∀ omega, MemVectorL2 ((cubeDomain R : Domain d) : Set (Vec d))
      (F omega).flux)
    (hclass : Measurable fun omega =>
      toHilbertBlockL2OfBlockField (memBlockL2_blockField (hpot omega) (hflux omega))) :
    Measurable fun omega : CutoffSample d =>
      doubledMuValue (cubeDomain R) (meshCellCoeff M m R omega) (F omega) :=
  measurable_doubledMuValue_meshCellCoeff_of_measurable_class M m R F
    (fun omega => memBlockL2_blockField (hpot omega) (hflux omega)) hclass

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

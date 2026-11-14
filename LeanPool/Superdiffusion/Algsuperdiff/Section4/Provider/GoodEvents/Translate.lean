/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Symmetry

/-!
# Translate

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The translation calculus of the cutoff sample carrier

Support layer for the Section 4 good-event A.  Every Section 4 event is built
from the frozen `Algsuperdiff.Frozen.Section4.goodEventAt`, which is a
`Cutoff.translateCutoffSample y` preimage (resolution A4: the *sample* is
translated, never the cube).  Reading such an event, comparing two of them, and
transferring its probability from a lattice point `z` to the origin all reduce
to three facts about `Cutoff.translateCutoffSample`:

* it is a group action of `Vec d` — `translate 0 = id` and
  `translate z ∘ translate w = translate (z + w)`;
* each `translate z` is a measurable equivalence of the carrier; and
* each `translate z` preserves the cutoff-sample law.

The third is **not** re-derived here.  It is the proved
`Algsuperdiff.Section3.Cutoff.map_translateCutoffSample_cutoffSampleLaw`
(`Section3/Cutoff/Symmetry.lean`), which holds for **every real** vector `z:
Vec d`, not merely for lattice shifts: it descends J1 stationarity of the
zero shell through the exact marginal scaling law and the independence of the
shell coordinates.  Section 4's lattice sums therefore need no additional
stationarity input; see the module note below.

## Stationarity strength available to Section 4

What the graph's stationarity gaps still require is *not* a stronger invariance
of the law: it is the (separate) claim that the observable being maximized is
the same function of the translated sample, i.e. the pointwise identities
`observable(z + □) (ω) = observable(□) (translate z ω)`.  Those identities are
per-observable statements and are proved in the individual Section 4 modules;
this module supplies only the law-level half.

## References

* ABK26, `d.good.event.for.lambda`, (the translate convention).
-/

namespace Algsuperdiff.Section4.Provider.GoodEvents

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The additive action -/

/-- **The zero translation is the identity.**  Pointwise form. -/
theorem translateCutoffSample_zero (omega : Cutoff.CutoffSample d) :
    Cutoff.translateCutoffSample (0 : Vec d) omega = omega := by
  apply Subtype.ext
  funext k
  apply Algsuperdiff.Frozen.Assumptions.ShellField.ext
  intro x
  simp only [Cutoff.translateCutoffSample_val,
    Algsuperdiff.Frozen.Assumptions.ShellField.translateSequence_apply,
    Algsuperdiff.Frozen.Assumptions.ShellField.translate_apply, add_zero]

/-- **The zero translation is the identity.**  Function form; this is the shape
consumed when a preimage is rewritten. -/
theorem translateCutoffSample_zero_eq_id :
    Cutoff.translateCutoffSample (0 : Vec d) = id :=
  funext fun omega => translateCutoffSample_zero omega

/-! ## 2. Preimage calculus -/

/-- The preimage form of `translate 0 = id`. -/
theorem preimage_translateCutoffSample_zero (t : Set (Cutoff.CutoffSample d)) :
    Cutoff.translateCutoffSample (0 : Vec d) ⁻¹' t = t := by
  rw [translateCutoffSample_zero_eq_id, Set.preimage_id]

/-! ## 3. The law-level statements -/

/-- **Every real translation preserves the cutoff-sample law.**

The bundled `MeasurePreserving` form of the proved
`Cutoff.map_translateCutoffSample_cutoffSampleLaw`; the translation vector is
an arbitrary real vector, in particular any triadic lattice point. -/
theorem measurePreserving_translateCutoffSample (M : ABKModel d) (z : Vec d) :
    MeasurePreserving (Cutoff.translateCutoffSample (d := d) z)
      (Cutoff.cutoffSampleLaw M).toMeasure (Cutoff.cutoffSampleLaw M).toMeasure :=
  ⟨Cutoff.measurable_translateCutoffSample z,
    Cutoff.map_translateCutoffSample_cutoffSampleLaw M z⟩

/-- **The per-`z` transfer of a probability.**  A measurable event and its
`z`-translate carry the same mass, for every real `z`. -/
theorem measure_preimage_translateCutoffSample (M : ABKModel d) (z : Vec d)
    {t : Set (Cutoff.CutoffSample d)} (ht : MeasurableSet t) :
    (Cutoff.cutoffSampleLaw M).toMeasure (Cutoff.translateCutoffSample z ⁻¹' t) =
      (Cutoff.cutoffSampleLaw M).toMeasure t :=
  (measurePreserving_translateCutoffSample M z).measure_preimage ht.nullMeasurableSet

end

end Algsuperdiff.Section4.Provider.GoodEvents

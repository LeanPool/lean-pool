/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Sum

/-!
# StepSevenAeMerge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The countable-`L` almost-everywhere merge

## The gap this module closes

flagged, for the future `hstep4` supplier, that the proved §4.3 producers put
the infrared-cutoff quantifier OUTSIDE the almost-everywhere quantifier.  For
instance the excess-decay lane's harmonic-approximation provider concludes

```text
  ∀ L m n : ℤ, m ≤ L → … → ∀ᵐ ω ∂(law M), P L m n ω ,
```

whereas the §4.4 consumer needs the SINGLE null set

```text
  ∀ᵐ ω ∂(law M), ∀ L : ℤ, m ≤ L → P L m n ω .
```

The exchange is legitimate because `ℤ` is countable, and it is exactly
Mathlib's `MeasureTheory.ae_all_iff` / `MeasureTheory.ae_ball_iff`.  The merge
is proved here as a standalone
measure-theoretic lemma: this module imports only Mathlib, in particular no
§4.3 file, so no §4.3 statement is touched or re-elaborated.

## What is provided

* `ae_forall_of_forall_ae_of_countable` — the plain countable-index exchange
  with a guard predicate: from `∀ i, Q i → ∀ᵐ a, P i a` conclude
  `∀ᵐ a, ∀ i, Q i → P i a`.  The guard `Q` is arbitrary; the guarded index need
  not range over a subtype.

No measurability hypothesis appears anywhere: the a.e. filter is a
`CountableInterFilter`, and the merge uses nothing else.

## References

* Mathlib, `MeasureTheory.ae_all_iff`, `MeasureTheory.ae_ball_iff`.
* The excess-decay seal-distance lane (the consumer whose quantifier order
  motivates this file; NOT imported).
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-! ## 1. The guarded countable exchange -/

/-- **The countable a.e. merge, with a guard.**

```text
  (∀ i, Q i → ∀ᵐ a ∂μ, P i a)   ⟹   ∀ᵐ a ∂μ, ∀ i, Q i → P i a .
```

The guarded indices form a countable subfamily of a countable family, so the
exceptional set is a countable union of null sets.  No measurability of `P` is
needed. -/
theorem ae_forall_of_forall_ae_of_countable {ι : Sort*} [Countable ι] {Q : ι → Prop}
    {P : ι → α → Prop} (h : ∀ i, Q i → ∀ᵐ a ∂μ, P i a) :
    ∀ᵐ a ∂μ, ∀ i, Q i → P i a := by
  classical
  have hstep : ∀ i : ι, ∀ᵐ a ∂μ, Q i → P i a := by
    intro i
    by_cases hi : Q i
    · exact (h i hi).mono fun a ha => fun _ => ha
    · exact Filter.Eventually.of_forall fun _ hQ => absurd hQ hi
  exact (ae_all_iff (p := fun a i => Q i → P i a)).2 hstep

end Algsuperdiff.Section4.Provider.Regularity

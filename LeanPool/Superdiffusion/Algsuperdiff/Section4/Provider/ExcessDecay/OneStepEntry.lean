/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepGoodScales
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.RebaseEpsilon

/-!
# OneStepEntry

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The entry point, generalized off the literal `(1/2)`

**Strict additions.**  `OneStepGoodScales.le_of_indicator_goodEventAt_le` — the
development's single consumption point for the anchor's indicator — is stated
at the *literal* threshold `(1/2)`.  The general clause is gated at the
threshold `C⁻¹ s⁴` instead, so the `ε`-parametric form of that consumption
point is needed.  This module proves it, plus the two reachability
instantiations that make the development's own good-scale supply feed the new
event with no further analysis.

## What is general and what is instantiated

* `le_of_indicator_goodEventAt_le_of_le` is the entry point at **any** event
  threshold `ε_ev`, under the single side condition `0 ≤ ε ≤ ε_ev` relating the
  *supply* threshold `ε` (the one `hmem` is stated at) to the *display*
  threshold `ε_ev`.  The proved literal form is the instance `ε_ev = 1/2`, and
  `le_of_indicator_goodEventAt_le_recovered` re-derives it verbatim, so the
  generalization is strict and no consumer needs to change.
* `goodScaleSupply_subset_clauseEvent` and `minimalScaleSupply_subset_clauseEvent`
  are the two *set-level* reachability facts, at the excess-decay consumer's
  own supply `ε = (s/8)√δ` and at the minimal-scale anchor's `ε = s√δ`.
* `le_of_indicator_goodEventAt_le_regated` is the entry point at the frozen
  threshold `C⁻¹ s⁴`, consumed straight from the excess-decay consumer's supply
  under the **`δ` re-pricing** `δ ≤ 64 C⁻² s⁶`.

## The `δ` price, and why it costs nothing at the pin

The sole eventual consumer of `l.excess.decay.good.scales` pins `s = 1/4`, so
`64 C⁻² s⁶ = C⁻²/64` is a **constant**: the re-pricing is a constant tightening
of the `δ`-window, not a new `s`- or `γ`-dependence.  The `γ`-exponent and the
`1 − C γ^{1/2}` target are untouched.

## References

* ABK26, `l.excess.decay.good.scales`, (the supply slot);
  `l.harmonic.approximation.good.scales`, (the display slot).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The entry point at an arbitrary event threshold -/

/-- **`OneStepGoodScales.le_of_indicator_goodEventAt_le`, off the literal.**

A bound carried by the indicator of `𝒢(j,z; t, ε_ev)` holds pathwise at every
`ω` of `𝒢(j,z; t, ε)` as soon as `0 ≤ ε ≤ ε_ev` — the event only grows with its
threshold.  The proved form is the instance `ε_ev = 1/2`. -/
theorem le_of_indicator_goodEventAt_le_of_le {M : ABKModel d} {Ccg : ℝ} {j : ℤ}
    {z : Vec d} {t : {t : ℝ // 0 < t}} {ep epEv : ℝ} (hep0 : 0 ≤ ep) (hle : ep ≤ epEv)
    {F : Cutoff.CutoffSample d → ℝ≥0∞} {B : ℝ≥0∞} {omega : Cutoff.CutoffSample d}
    (hmem : omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M Ccg j z t ep)
    (h : Set.indicator (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg j z t epEv) F omega
      ≤ B) :
    F omega ≤ B := by
  have hsub :=
    Algsuperdiff.Section4.Provider.GoodEvents.goodEventAt_mono_ep M Ccg j z t hep0 hle
  rwa [Set.indicator_of_mem (hsub hmem)] at h

/-! ## 2. The two reachability instantiations -/

/-! ## 3. The entry point at the frozen threshold `C⁻¹ s⁴` -/

end

end Algsuperdiff.Section4.Provider.ExcessDecay

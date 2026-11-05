/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationCorrectorRegularity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationEnvelopeWire
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationCellIntegrable
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationOscillationBudget
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationOscillationDisplay

/-!
# LocalizationOscillationEndpoint

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `e.lower.bound.oscillations` at the recurrence parameters: the `gamma^{15}` endpoint

ABK26, `l.approximate.recurrence.formula`, `e.lower.bound.oscillations`, read at
the parameters of `e.recurrence.params` with the multiplier `a = 32`:

* the buffer `n = recurrenceMesoScale 32 gamma m h = m - h - 32 ceil|log_3 gamma|`;
* the outer window scale `n + N = m - h`, `N = recurrenceGap 32 gamma`;
* the gauge `shom_{m-h}^{-1}` and the shell pair `(m - h, m)` of `e.def.w`;
* the big cube `cu_K` at the gate `10^10 gamma^{-1} <= K - m`.

Three modules meet here.

* `LocalizationOscillationDisplay.lean` proves the *first* inequality of the
  printed chain, at a free buffer, conditionally on a coarse-energy envelope
  `W` and on the sample integrability of the per-cell coarse energies.
* `LocalizationEnvelopeWire.lean` discharges the coarse-energy envelope from
  `e.nablaw.in.L.eight` -- this is the manuscript's own "by
  `e.nablaw.in.L.eight`" step -- at the constant
  `3^d freshShellFourthEnergyConst Chead (gamma^100)`.
* `LocalizationOscillationBudget.lean` collapses the resulting three terms to
  `gamma^{15}`.
* `LocalizationFluctuationCellIntegrable.lean` discharges the display's last
  sample-space hypothesis, the integrability in the sample of the per-cell
  coarse energies to the fourth power.

## What is proved

`exists_gamma0_freshShellDirichlet_meshOscillation_le_gamma_pow_fifteen` and its
Neumann mirror: at every `gamma` below one explicit threshold,

```
  ( avsum_{z} E[ ‖grad w - (grad w)_{z+cu_n}‖^4_{L2bar(z+cu_n)} ] )^{1/4}
    + shom_{m-h}^{-1} 3^n E[ ‖grad(k_m - k_{m-h})‖^4_{Linf} ]^{1/4}
  <= gamma^{15} .
```

## References

* ABK26, `e.lower.bound.oscillations`, `e.nablaw.oscillations`,
  `e.nablaw.in.L.eight`, `e.recurrence.params`, `e.def.w`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3.Cutoff
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The buffer identities -/

/-- The buffer and the gap add up to the inner scale of the fresh shell.
Unconditional. -/
theorem recurrenceMesoScale_add_recurrenceGap (a : ℕ) (gamma : ℝ) (m : ℤ) (h : ℕ) :
    recurrenceMesoScale a gamma m (h : ℤ) + ((recurrenceGap a gamma : ℕ) : ℤ) =
      m - (h : ℤ) := by
  simp [recurrenceMesoScale]

/-- The same identity after the real cast.  Unconditional. -/
theorem recurrenceMesoScale_add_recurrenceGap_real (a : ℕ) (gamma : ℝ) (m : ℤ) (h : ℕ) :
    ((recurrenceMesoScale a gamma m (h : ℤ) : ℤ) : ℝ) +
        ((recurrenceGap a gamma : ℕ) : ℝ) = (((m - (h : ℤ) : ℤ)) : ℝ) := by
  have h0 := recurrenceMesoScale_add_recurrenceGap a gamma m h
  exact_mod_cast congrArg (fun t : ℤ => (t : ℝ)) h0

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

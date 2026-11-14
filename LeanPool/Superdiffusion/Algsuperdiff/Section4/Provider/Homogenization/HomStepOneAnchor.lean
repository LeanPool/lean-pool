/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section4.BoundsMathcalEaL
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomStepOneArith

/-!
# HomStepOneAnchor

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5, Step 1: the constants of the parameter selection

## What this module is

Step 1 applies the eighth anchor

```
Algsuperdiff.Frozen.Section4.bounds_mathcal_E_aL
```

(`Algsuperdiff/Frozen/Section4/BoundsMathcalEaL.lean`, proved) once for each
`𝓔`-factor of `EthmB(m)`, at the §4.5 parameter selection

| factor of `EthmB(m)` | anchor exponent `s` | anchor gap `m − n` |
|---|---|---|
| `𝓔_{s₁,∞,2}(□_m, n; ·)`   | `s/2 = homS M / 2` | `k = homK M` |
| `𝓔_{1/4,∞,2}(□_m; ·)`     | `1/4`              | `0` (`n = m`) |
| `𝓔_{s₁/2,∞,2}(□_m, n; ·)` | `s/4 = homS M / 4` | `k = homK M` |

with `s = |log γ|⁻¹`, `k = ⌈10|log γ|⌉`, `n = m − k`.

This module fixes the constant that selection is priced at,

```text
  homConst C_A = 200 · max C_A 1,
```

with the two positivity facts it is used through, and records `3^0 = 1`, the
evaluation the middle row of the table needs.  The absence of a `|log γ|` in
that middle row is what makes the assembled Step-1 display carry `|log γ|²`
and not `|log γ|³`: the `|log γ|` of the `s⁻¹` prefactor of `EthmB(m)` and the
one of the `𝓔_{s₁}` factor are the only two in the product.
-/

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The produced constants -/

/-- The produced constant of the Step-1 factor bounds: `200 max(C_A, 1)`.  The
`200` is the product of the two evaluation losses `3³ = 27` and `6` of the
third slot (`162`), rounded up. -/
def homConst (CA : ℝ) : ℝ := 200 * max CA 1

theorem one_le_maxOne (CA : ℝ) : (1 : ℝ) ≤ max CA 1 := le_max_right _ _

theorem maxOne_pos (CA : ℝ) : (0 : ℝ) < max CA 1 :=
  lt_of_lt_of_le one_pos (one_le_maxOne CA)

theorem one_le_homConst (CA : ℝ) : 1 ≤ homConst CA := by
  have hK : (1 : ℝ) ≤ max CA 1 := one_le_maxOne CA
  rw [homConst]
  linarith only [hK]

/-! ## 2. `3^x ≤ 27` -/

theorem rpow_three_zero : Real.rpow (3 : ℝ) 0 = 1 := Real.rpow_zero 3

end

end Algsuperdiff.Section4.Provider.Homogenization

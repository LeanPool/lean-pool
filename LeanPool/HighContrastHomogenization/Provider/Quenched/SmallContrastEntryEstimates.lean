/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastHcoreEndpoint
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastHrecInstance
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakGroups

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastEntryEstimates

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The bootstrap entry is polynomial

The `hentry` clause of the endpoint asks for the entry generation to be bounded
by a fixed power of the law parameter
`Π = 2 + aspectRatio 𝐄 · K`.  With

```
N₁ = entryGeneration (s_K + 1 + gap) (entryDelay c_w C_src δ) n₀
```

the assembly is the entry-generation power bound; the per-constant core is
below.

**The core** is that every delay in the chain is a *ceiling of a base-3
logarithm*, and `3^{⌈log₃ x⌉₊} ≤ 3·max 1 x`: a delay defined that way is
automatically polynomial in whatever bounds `x`.  This applies unchanged to
`entryDelay c_w C_src δ = ⌈log₃(3 c_w C_src / δ)⌉₊` and, in the bootstrap
module's form, to `gap`.  The third estimate, `3^{n₀} ≤ Π^{C_delay}`, is
the account's own first clause and needs nothing.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix

noncomputable section

/-- **The delay core.**  A delay defined as a ceiling of a base-3 logarithm is
below `3·max 1 x` after exponentiation. -/
theorem three_pow_ceil_logb_le {x : ℝ} (hx : 0 < x) :
    (3 : ℝ) ^ (⌈Real.logb 3 x⌉₊) ≤ 3 * max 1 x := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  rcases le_or_gt (Real.logb 3 x) 0 with hle | hpos
  · have hzero : ⌈Real.logb 3 x⌉₊ = 0 := by
      simpa using Nat.ceil_eq_zero.mpr hle
    rw [hzero, pow_zero]
    have h1 : (1 : ℝ) ≤ max 1 x := le_max_left _ _
    linarith only [h1]
  · have hceil : ((⌈Real.logb 3 x⌉₊ : ℕ) : ℝ) ≤ Real.logb 3 x + 1 :=
      le_of_lt (Nat.ceil_lt_add_one (le_of_lt hpos))
    have hnat : (3 : ℝ) ^ (⌈Real.logb 3 x⌉₊) =
        (3 : ℝ) ^ ((⌈Real.logb 3 x⌉₊ : ℕ) : ℝ) :=
      (Real.rpow_natCast (3 : ℝ) _).symm
    rw [hnat]
    have hmono : (3 : ℝ) ^ ((⌈Real.logb 3 x⌉₊ : ℕ) : ℝ) ≤
        (3 : ℝ) ^ (Real.logb 3 x + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hceil
    have hval : (3 : ℝ) ^ (Real.logb 3 x + 1) = x * 3 := by
      rw [Real.rpow_add h3, Real.rpow_logb h3 (by norm_num) hx,
        Real.rpow_one]
    rw [hval] at hmono
    have hxmax : x ≤ max 1 x := le_max_right _ _
    have : x * 3 ≤ 3 * max 1 x := by linarith only [hxmax]
    linarith only [hmono, this]

end

end HCPolySupport.HighContrast.Quenched

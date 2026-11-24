/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.Actual214Window
public import LeanPool.ShellsortMean.RoughGapEndpointFrequency

/-! The retained Fourier modes after a nondividing gap followed by a dividing gap. -/

@[expose] public noncomputable section
namespace Shellsort.Actual214
open Finset RoughGapEndpoint

/-- Each nonzero mode of reduced denominator d dividing a genuine candidate
is controlled on the very same state following the two retained sorting passes.
The estimate charges the mass *before* those two passes. -/
theorem menu_mode_after_retained {n c h g₁ g₂ d : ℕ}
    (p : RankPlacement n) (T : ℕ) (hT : T ≤ n) (h₂ : 0 < g₂) (hle : g₂ ≤ g₁)
    (hh : h ∈ window c (Nat.gcd g₁ g₂)) (hdh : d ∣ h) (hd : 1 < d)
    (z : ℂ) (hz : ‖z‖ = 1) (hp : IsPrimitiveRoot z d) :
    ‖amplitude (gapSort (gapSort p g₁) g₂) T z‖ ^ 2 ≤
      (2 * (g₁ : ℝ) * d) * (∑ i, |(slotError p T i : ℝ)|) := by
  by_cases hdiv : d ∣ g₂
  · have off := (retained_breaks_divisor hh hdh hd).resolve_right (not_not_intro hdiv)
    exact nondividing_then_divisible_squared p T hT (lt_of_lt_of_le h₂ hle) (by omega) z hz hp off
      [g₂] (by simpa using hdiv)
  · have e := nondividing_then_divisible_squared (gapSort p g₁) T hT h₂ (by omega : 0 < d) z hz
      hp hdiv [] (by simp)
    have mass : (∑ i, |slotError (gapSort p g₁) T i|) ≤ ∑ i, |slotError p T i| := by
      rw [gapSort_abs_error_exact p T hT (lt_of_lt_of_le h₂ hle)]
      exact sum_abs_residueError_le p T hT (lt_of_lt_of_le h₂ hle)
    have massR : (∑ i, |(slotError (gapSort p g₁) T i : ℝ)|) ≤ ∑ i, |(slotError p T i : ℝ)| := by
      exact_mod_cast mass
    apply e.trans
    gcongr

end Shellsort.Actual214

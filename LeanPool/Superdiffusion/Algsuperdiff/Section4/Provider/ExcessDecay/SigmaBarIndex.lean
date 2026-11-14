/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.SigmaBarBudget
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.GoodEvents.InductionState

/-!
# SigmaBarIndex

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `σ` index conversion at a two-scale gap, binder-free

This module closes that conversion **inside the anchor's own regime**: the
induction-state binder that `Annular.SigmaBarBudget.sigmaBar_ratio_le_four`
carries is discharged internally by
`GoodEvents.exists_allScalesInductionState`, at the landmark `m₀ := n+2` (resp.
`m₀ := n`), so nothing beyond `γ ≤ C^{-1} c⋆^{10}` is asked of the caller.
This is the `B1` wrapper pattern of `Provider/BoundsEaL/StepFourSigmaBar.lean`,
re-derived here so that the `BoundsEaL` tree is not imported.

```text
   σ_{n+2}^{-1} ≤ 4 σ_n^{-1}        (the direction the anchor's display needs)
   σ_n^{-1}     ≤ 7 σ_{n+2}^{-1}    (the converse, at the same regime)
```

Both constants are absolute numerals: no `s`, no `γ`, no `c⋆`, no dimension.
The regime is written in the frozen theorem's own shape `γ ≤ C^{-1} c⋆^{10}`
(the induction-state producer's shape `γ ≤ (C₀^{-1})^{10} c⋆^{10}` is reached
by exporting `C := C₀^{10}`).

## Where the constants come from

`σ` is *almost monotone* in the scale, in both directions, because the
induction state pins `σ_m^2` inside a factor-`4` window around `max(c⋆ γ^{-1}
3^{2γm}, ν^2)`, and that window's own ratio across two scales is `3^{4γ} ≤ 3`
at the standing `γ ≤ 1/4`.  Upward: the window is monotone in `m`, so the two
factor-`4` branches give `σ_n ≤ 4 σ_{n+2}`.  Downward: the extra `3^{4γ} ≤ 3`
gives `σ_{n+2}^2 ≤ 48 σ_n^2`, i.e. `σ_{n+2} ≤ 7 σ_n`.

## References

* ABK26, `e.shom.h.bounds`; `p.induction.bounds` proof.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## 1. Two arithmetic helpers -/

/-- The regime bridge: the anchor prints `γ ≤ C^{-1} c⋆^{10}`, the induction
state producer asks for `γ ≤ (C₀^{-1})^{10} c⋆^{10}`. -/
private theorem regime_bridge {C0 gam c : ℝ} (h : gam ≤ (C0 ^ (10 : ℕ))⁻¹ * c) :
    gam ≤ (C0⁻¹) ^ (10 : ℕ) * c := by
  rwa [inv_pow]

/-! ## 2. The two ratio readings of the state -/

/-- **`σ` is almost increasing.**  From the induction state at the landmark
`n+2`: `σ_n ≤ 4 σ_{n+2}`, in the inverse form the force leg consumes. -/
theorem inv_sigmaBar_add_two_le_of_inductionState (M : ABKModel d) {m0 : ℤ}
    {E : {E : ℝ // 1 ≤ E}} (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E)
    {n : ℤ} (hn : n + 2 ≤ m0) :
    ((Annealed.sigmaBar M (n + 2) : ℝ))⁻¹ ≤ 4 * ((Annealed.sigmaBar M n : ℝ))⁻¹ := by
  have hidx : (n + 2 : ℤ) - 2 = n := by ring
  have hbase := Annular.sigmaBar_ratio_le_four M hS (m := n + 2) (n := n + 2)
    (by linarith only []) hn
  rw [hidx] at hbase
  have hB : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have hstep := mul_le_mul_of_nonneg_right hbase (inv_nonneg.2 hB.le)
  rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hB), mul_one] at hstep
  exact hstep

/-! ## 3. The binder-free exports -/

/-- **The `σ` index conversion the anchor's force leg needs, binder-free.**

In the frozen theorem's own regime alone, `σ_{n+2}^{-1} ≤ 4 σ_n^{-1}` at
every integer scale: the induction-state binder is discharged internally. -/
theorem exists_inv_sigmaBar_add_two_le (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d, M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        ∀ n : ℤ, ((Annealed.sigmaBar M (n + 2) : ℝ))⁻¹ ≤
          4 * ((Annealed.sigmaBar M n : ℝ))⁻¹ := by
  obtain ⟨C0, hC0, hC⟩ := GoodEvents.exists_allScalesInductionState d
  refine ⟨C0 ^ (10 : ℕ), by positivity, ?_⟩
  intro M hreg n
  obtain ⟨E, -, hall⟩ := hC M (regime_bridge hreg)
  exact inv_sigmaBar_add_two_le_of_inductionState M (E := E) (hall (n + 2)) le_rfl

end

end Algsuperdiff.Section4.Provider.ExcessDecay

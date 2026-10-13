/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFiveDeltaFamily

/-!
# StepFiveDeltaSum

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 5: `e.sum.delta.j.bound` at the concrete family

## The target

ABK26 `t.regularity` Step 5, (`e.sum.delta.j.bound`), at the `δ_j` of
`StepFiveDeltaFamily`:

```text
  ∑_{j=n}^{m-1} δ_j  ≤  C 3^{m/2} σ_m^{-1} [g]_{W^{1/2,∞}(□_m)}
      + C ( 3^{m/2} [∇h]_{W^{1/2,∞}(□_m)}
            + C₁^{-1}(1-α)(m-n) ‖∇h‖_{L^∞(□_m)} ) 1_{z ∉ □_{m-1}} .
```

```text
  r₁ := 3^{-(1/2-γ)} ,   r₂ := 3^{-1/2} ,
  K_g := C · 4 · 3^{m/2} σ_m^{-1} [g] ,   K_h := C · 3^{m/2} [∇h] ,
  Hinf := C ‖∇h‖_{L^∞(□_m)} ,   ind := 1_{z ∉ □_{m-1}} ,
```

## The two windows

`l.iteration.lemma` sums `δ` over `Finset.Icc n m`; the manuscript's display is
over `[n, m-1]` ('s deviation D1).

The abstract-real kit lemma for the anchor's window
(`sum_Icc_top_le_of_zpow_dominated`) is stated here rather than in the tracked
files pinned to the printed window; it is the same downward induction, re-used
through `sum_Icc_le_of_zpow_dominated` plus the single top term.

## References

* ABK26, `t.regularity` Step 5.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal
open scoped Classical

noncomputable section

/-! ## 1. The kit lemmas on the anchor's window `Icc n m` -/

/-- **The geometric tail on the anchor's window.**  For a nonnegative family
dominated from the top scale, `f j ≤ K r^{m-j}` with `0 < r < 1`,

```text
   ∑_{j=n}^{m} f j  ≤  K / (1 - r)          uniformly in n ≤ m .
```

One extra term over's printed-window `sum_Icc_le_of_zpow_dominated`, namely `f
m ≤ K`, turns its `K r/(1-r)` into `K/(1-r)`. -/
theorem sum_Icc_top_le_of_zpow_dominated {r K : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {f : ℤ → ℝ} {n m : ℤ} (hn : n ≤ m) (hf0 : 0 ≤ f m)
    (hdom : ∀ j : ℤ, j ≤ m → f j ≤ K * r ^ (m - j)) :
    ∑ j ∈ Finset.Icc n m, f j ≤ K / (1 - r) := by
  have h1r : (0 : ℝ) < 1 - r := by linarith only [hr1]
  have hsplit : Finset.Icc n m = insert m (Finset.Icc n (m - 1)) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : m ∉ Finset.Icc n (m - 1) := by
    simp only [Finset.mem_Icc]
    omega
  have htail := sum_Icc_le_of_zpow_dominated hr0 hr1 hn hf0 hdom
  have htail' : (∑ j ∈ Finset.Icc n (m - 1), f j) * (1 - r) ≤ K * r :=
    (le_div_iff₀ h1r).mp htail
  have hfm : f m ≤ K := by
    have hd := hdom m le_rfl
    have h0 : m - m = (0 : ℤ) := by omega
    rwa [h0, zpow_zero, mul_one] at hd
  have hfm' : f m * (1 - r) ≤ K * (1 - r) := mul_le_mul_of_nonneg_right hfm h1r.le
  rw [hsplit, Finset.sum_insert hnot, le_div_iff₀ h1r]
  linarith only [htail', hfm']

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end

end Algsuperdiff.Section4.Provider.Regularity

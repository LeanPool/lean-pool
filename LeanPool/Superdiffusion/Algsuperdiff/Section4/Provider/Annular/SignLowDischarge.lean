/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.ClauseOneFinal

/-!
# SignLowDischarge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The relaxed `σ` display, discharged, and the four-slot endpoint

ABK26, Section 4.1, `p.mathcalE.annular.decomp` Step 2.

The ugly chain reads the running-diffusivity lower bound at the *shifted* index
`n − 2` but writes it at the exponent `3^{γn}`:

```
½ κ 3^{γn} ≤ σ_{n−2} ,        κ = √c⋆ γ^{−1/2} .
```

That is not what the `Frozen.Section3.inductionState` delivers.  The state
gives `σ_k² ≥ ¼ max(c⋆ γ^{−1} 3^{2γk}, ν²)`, hence at `k = n − 2`

```
σ_{n−2} ≥ ½ κ 3^{γ(n−2)} = 3^{−2γ} · (½ κ 3^{γn}) ,
```

short of the printed display by exactly the factor `3^{2γ}` — which is at most
`3^{1/16} ≈ 1.072` on the printed window `8γ ≤ s ≤ 1/4`, and at most `2` under
the standing `γ ≤ 1/4` alone.

The chain's `hsignlow` binder has been relaxed to `¼` throughout
(`Ugly` → `UglyChain` → `GradNormalization` → `UglyLatticeChain` →
`FinalStitch` → `ClauseOneFinal`), at the cost of doubling two output-constant
coefficients and nothing else.  This module closes the loop:

`sigmaBar_sub_two_lower_quarter_of_inductionState` proves the relaxed display
outright from the induction state and the standing `γ ≤ 1/4`, so that a clause-(i)
endpoint can be run with the `hsignlow` binder discharged in place rather than
carried.  The two private `3^x` helpers are re-derived here because their
upstream twins are `private`.
-/

namespace Algsuperdiff.Section4.Provider.Annular

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Part A -- the index-shift cost `3^{2γ} ≤ 2` -/

private theorem three_rpow_mono₃ {x y : ℝ} (h : x ≤ y) : (3 : ℝ) ^ x ≤ (3 : ℝ) ^ y :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) h

/-- `3^{1/2} ≤ 2`, the only numeric fact the `3^{2γ}` index shift costs. -/
private theorem three_rpow_half_le_two' : (3 : ℝ) ^ ((1 : ℝ) / 2) ≤ 2 := by
  refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by norm_num) ?_
  have hsq : ((3 : ℝ) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = 3 := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ ((1 : ℝ) / 2)) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  rw [hsq]
  norm_num

/-! ## Part B -- the relaxed display, discharged -/

/-- **The relaxed `hsignlow` display, proved.**

On the Section 3 induction state, at the honest clause-(i) amplitude `κ = √c⋆
γ^{−1/2}` and at any index with `n − 2 ≤ m₀`,

```
¼ κ 3^{γn} ≤ σ_{n−2} .
```

The printed constant is `½`; the gap is the index shift `3^{2γ} ≤ 2`, which the
standing `γ ≤ 1/4` (`ABKModel.shellPrefix.gamma_le_quarter`) supplies with no
regime input.  This is the *exact* binder the relaxed ugly chain carries. -/
theorem sigmaBar_sub_two_lower_quarter_of_inductionState (M : ABKModel d) {m0 : ℤ}
    {E : {E : ℝ // 1 ≤ E}} (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E)
    {n : ℤ} (hn : n - 2 ≤ m0) :
    1 / 4 * ((Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹)
        * (3 : ℝ) ^ (M.gamma * (n : ℝ)))
      ≤ (Annealed.sigmaBar M (n - 2) : ℝ) := by
  have hkap0 := annularEventAmplitude_pos M
  have hg14 : M.gamma ≤ 1 / 4 := M.shellPrefix.gamma_le_quarter
  have hlow := sigmaBar_lower_of_inductionState M hS hn
  have hP0 : (0 : ℝ) < (3 : ℝ) ^ (M.gamma * (((n - 2 : ℤ)) : ℝ)) := by positivity
  have hsplit : (3 : ℝ) ^ (M.gamma * (n : ℝ))
      = (3 : ℝ) ^ (2 * M.gamma) * (3 : ℝ) ^ (M.gamma * (((n - 2 : ℤ)) : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  have h2g : (3 : ℝ) ^ (2 * M.gamma) ≤ 2 :=
    le_trans (three_rpow_mono₃ (by linarith only [hg14])) three_rpow_half_le_two'
  rw [hsplit]
  have hmul : (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) *
      ((3 : ℝ) ^ (2 * M.gamma) * (3 : ℝ) ^ (M.gamma * (((n - 2 : ℤ)) : ℝ)))
      ≤ (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) *
        (2 * (3 : ℝ) ^ (M.gamma * (((n - 2 : ℤ)) : ℝ))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2g hP0.le) hkap0.le
  linarith only [hmul, hlow]

end

end Algsuperdiff.Section4.Provider.Annular

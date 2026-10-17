/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.EnnrealShell
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepEntry
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepInterior
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ProviderEpsFree
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.RecutAtoms

/-!
# EdAssemblyOneStep

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Monotonicity of the interior one-step remainder slot

The interior one-step contraction carries its remainder as
`C_r(d,C,k) · 3^{-n} · √((3²)^d) · R`, with `R` the abstract real produced by
the harmonic-approximation anchor's `B.toReal` expansion.  Raising `R` raises
the remainder, which is what lets a caller substitute a larger bound for
`B.toReal` in a single `add_le_add`.  That monotonicity is this file.

## The `K_h` leg

The interior branch has **no** boundary-datum leg: the proved sibling's third
summand is `C_t (3^{n-k})^{1/2} · 0`, collapsed here.  That matches the printed
lemma, whose two `𝟙_{{(x+□_n)∩∂□_m ≠ ∅}}`-gated summands vanish on the interior
branch.

## References

* ABK26, `l.excess.decay.good.scales`, statement and proof;
  `l.harmonic.approximation.good.scales`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

/-! ## 1. The two abstract-real moves of the one-step conclusion -/

/-- **Monotonicity of the one-step remainder slot.**  The remainder is
`C_r(d,C,k) · 3^{-n} · √((3²)^d) · R`, increasing in `R` because
`triangleRemainderConst` is nonnegative. -/
theorem oneStepRemainder_mono (d : ℕ) {C : ℝ} (hC : 0 ≤ C) (k : ℕ) (n : ℤ)
    {R R' : ℝ} (hRR' : R ≤ R') :
    triangleRemainderConst d C k
        * ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * R)) ≤
      triangleRemainderConst d C k
        * ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * R')) :=
  mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hRR' (Real.sqrt_nonneg _))
      (zpow_pos (by norm_num) (-n)).le)
    (triangleRemainderConst_nonneg d hC k)

end

end Algsuperdiff.Section4.Provider.ExcessDecay

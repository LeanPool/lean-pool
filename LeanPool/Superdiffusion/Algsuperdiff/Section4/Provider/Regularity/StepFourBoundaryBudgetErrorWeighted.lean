/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourBoundaryBudget

/-!
# StepFourBoundaryBudgetErrorWeighted

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Step-4 boundary budget at the error-weighted anchor

Nothing here claims the anchor, and nothing here is a frozen statement.

## What the error-weighted recut buys, at the consumption side

`StepFourBoundaryBudget`'s `stepFourDeltaOut` carries FOUR boundary summands,
of which the fourth is `ε`-FREE:

```text
   stepFourDeltaOut = C_rem V_d ( C s^{-4} ε_j (s^{-3/2}/9) K_hinf     -- ε-FUNDED flat
                    + 8 C s^{-7} σ_n^{-1} 3^{n/2} K_g                  -- the g-leg
                    + C s^{-6} 3^{n/2} K_h                             -- the ∇h Gagliardo leg
                    + C s^{-6} (1/9) K_hinf )                          -- the ε-FREE flat leg
```

and that module proves the fourth leg's window sum is `(m-n)`-LINEAR against
the budget's `C₁^{-1}(1-α)(m-n)`, hence costs exactly
`Θ((1-α)^{-1}) = Θ(γ^{-1/2})` — sharp, and in contradiction with the printed
`α`-free constant.

Under the error-weighted anchor that fourth leg is produced `𝓔`-multiplied, and the
proved collapse `StepFourCollapseEps.ae_fluxCorrectedErrorRepresentative_le_
stepFiveEps` reads `𝓔 ≤ ε_j` at exactly this slot.  So the Step-4 output
becomes

```text
   stepFourDeltaOutErrorWeighted = C_rem V_d ( C s^{-4} ε_j (s^{-3/2}/9) K_hinf
                    + 8 C s^{-7} σ_n^{-1} 3^{n/2} K_g
                    + C s^{-6} 3^{n/2} K_h
                    + C s^{-6} ε_j (1/9) K_hinf )                      -- ε-FUNDED
```

— the SAME shape with `epsj` inserted on the fourth summand, and nothing else
moved.  Its boundary grouping therefore has

```text
   F = 0 ,      H = 2 · C_bd · K_hinf ,
```

the `ε_j·H` coefficient widened by exactly the factor `2` (the two `ε`-funded
flat summands sit at `s^{-4}s^{-3/2}/9` and `s^{-6}/9`, each below the single
constant `C_bd`), and the window sum loses its `W`-linear term outright:

```text
   ∑_{j=n}^{m} δ_j ≤ K_g/(1-r₁) + ( K_h/(1-r₂) + S_ε · (2 C_bd K_hinf) ) .
```

`S_ε` is bought by the `ε`-budget, so the proved flat-price absorption of
`StepBoundaryAbsorption` — which is ABSOLUTELY `α`-, `γ`- and `δ`-free, at
`8/(C₁ log 3) ≤ 4/log 3` — absorbs it.
The `γ^{-1/2}` price of `StepFourBoundaryBudget`'s honest stop is therefore
GONE, and Theorem C's boundary `∇h` leg closes at the printed `α`-free
constant.

## References

* ABK26, the Step-4/5 boundary budget.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3

noncomputable section

/-! ## 1. The error-weighted Step-4 boundary output -/

/-- **The Step-4 boundary output at the error-weighted anchor.**

`StepFourCollapseInterface.stepFourDeltaOut` with the FOURTH summand — the flat
`∇h` leg — carrying `ε_j`, which is what the error-weighted general clause's
`𝓔`-multiplied fifth leg delivers through the proved collapse `𝓔 ≤ ε_j`.  Every
other byte of the definition is unchanged. -/
def stepFourDeltaOutErrorWeighted (Crem Vd Cst s epsj Khinf SigInvN Kg Kh : ℝ) (n : ℤ) : ℝ :=
  Crem * Vd *
    (Cst * s ^ (-(4 : ℝ)) * epsj * (s ^ (-(3 / 2 : ℝ)) * (1 / 9) * Khinf) +
      (8 * (Cst * s ^ (-(7 : ℝ))) * (SigInvN * ((3 : ℝ) ^ ((n : ℝ) / 2) * Kg)) +
        (Cst * s ^ (-(6 : ℝ)) * ((3 : ℝ) ^ ((n : ℝ) / 2) * Kh) +
          Cst * s ^ (-(6 : ℝ)) * epsj * ((1 / 9) * Khinf))))

/-- **The error-weighted Step-4 output in the budget's own grouping, with
`F = 0`.**

```text
   stepFourDeltaOutErrorWeighted ≤ C_bd 3^{n/2} σ_n^{-1} K_g
                       + ( C_bd 3^{n/2} K_h + ε_j · (2 C_bd K_hinf) ) ,
```

i.e. `A^g_n + (A^h_n + ε_j H)` with `H = 2 C_bd K_hinf` and **no** `ε`-free
summand: the leg priced at `Θ(γ^{-1/2})` has been absorbed into the `ε`-budget
by the anchor recut. -/
theorem stepFourDeltaOutErrorWeighted_le_boundaryThreeLegs
    {Crem Vd Cst s epsj Khinf SigInvN Kg Kh : ℝ} {n : ℤ}
    (hCV : 0 ≤ Crem * Vd) (hCst : 0 ≤ Cst) (hs : 0 < s) (heps0 : 0 ≤ epsj)
    (hKhinf : 0 ≤ Khinf) (hSig0 : 0 ≤ SigInvN) (hKg0 : 0 ≤ Kg) (hKh0 : 0 ≤ Kh) :
    stepFourDeltaOutErrorWeighted Crem Vd Cst s epsj Khinf SigInvN Kg Kh n ≤
      stepFourBoundaryDeltaConst Crem Vd Cst s *
          ((3 : ℝ) ^ ((n : ℝ) / 2) * SigInvN * Kg) +
        (stepFourBoundaryDeltaConst Crem Vd Cst s * ((3 : ℝ) ^ ((n : ℝ) / 2) * Kh) +
          epsj * (2 * stepFourBoundaryDeltaConst Crem Vd Cst s * Khinf)) := by
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ ((n : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hX : (0 : ℝ) ≤ Cst * (s ^ (-(4 : ℝ)) * s ^ (-(3 / 2 : ℝ))) :=
    mul_nonneg hCst (mul_nonneg (Real.rpow_nonneg hs.le _) (Real.rpow_nonneg hs.le _))
  have hY : (0 : ℝ) ≤ Cst * s ^ (-(7 : ℝ)) := mul_nonneg hCst (Real.rpow_nonneg hs.le _)
  have hZ : (0 : ℝ) ≤ Cst * s ^ (-(6 : ℝ)) := mul_nonneg hCst (Real.rpow_nonneg hs.le _)
  -- the four coefficient comparisons, each against the single constant
  have hc1 : Cst * s ^ (-(4 : ℝ)) * (s ^ (-(3 / 2 : ℝ)) * (1 / 9))
      ≤ Cst * (s ^ (-(4 : ℝ)) * s ^ (-(3 / 2 : ℝ)) + 8 * s ^ (-(7 : ℝ)) + s ^ (-(6 : ℝ))) := by
    linarith only [hX, hY, hZ]
  have hc2 : 8 * (Cst * s ^ (-(7 : ℝ)))
      ≤ Cst * (s ^ (-(4 : ℝ)) * s ^ (-(3 / 2 : ℝ)) + 8 * s ^ (-(7 : ℝ)) + s ^ (-(6 : ℝ))) := by
    linarith only [hX, hY, hZ]
  have hc3 : Cst * s ^ (-(6 : ℝ))
      ≤ Cst * (s ^ (-(4 : ℝ)) * s ^ (-(3 / 2 : ℝ)) + 8 * s ^ (-(7 : ℝ)) + s ^ (-(6 : ℝ))) := by
    linarith only [hX, hY, hZ]
  have hc4 : Cst * s ^ (-(6 : ℝ)) * (1 / 9)
      ≤ Cst * (s ^ (-(4 : ℝ)) * s ^ (-(3 / 2 : ℝ)) + 8 * s ^ (-(7 : ℝ)) + s ^ (-(6 : ℝ))) := by
    linarith only [hX, hY, hZ]
  -- transport each comparison through `Crem V_d` and the nonnegative data factor
  have hf1 : 0 ≤ epsj * Khinf := mul_nonneg heps0 hKhinf
  have hf2 : 0 ≤ (3 : ℝ) ^ ((n : ℝ) / 2) * SigInvN * Kg :=
    mul_nonneg (mul_nonneg h3 hSig0) hKg0
  have hf3 : 0 ≤ (3 : ℝ) ^ ((n : ℝ) / 2) * Kh := mul_nonneg h3 hKh0
  have hm1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc1 hCV) hf1
  have hm2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc2 hCV) hf2
  have hm3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc3 hCV) hf3
  have hm4 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc4 hCV) hf1
  rw [stepFourDeltaOutErrorWeighted, stepFourBoundaryDeltaConst]
  linarith only [hm1, hm2, hm3, hm4]

end

end Algsuperdiff.Section4.Provider.Regularity

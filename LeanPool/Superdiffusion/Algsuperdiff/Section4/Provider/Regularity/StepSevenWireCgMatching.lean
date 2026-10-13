/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenEndPoincare
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenCaccMatching
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.CoarsePoincareRHS

/-!
# StepSevenWireCgMatching

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 7d: matching `l.coarse.graining.RHS` to the §4.4 data

## The gap this module closes

`e.cg.Poincare.with.rhs.grad.applied` is proved with its first conditional input
named `hcg`:

```text
  besov ≤ Ccg · (√lamInv · gradLoc) + Ccg · (lamInv · dataLoc) .
```

Here `exists_stepSevenCgPoincareInput` produces the `hcg` shape verbatim, and
composing it with `hlambda` gives the display's first inequality.  `hcg` is
therefore no longer a conditional input of the Step-7d chain.

## The carrier match, binder by binder

```text
  scaleNormalizedNegativeBesovVectorNorm Q s (.finite 2) (∇u)
    ≤ C s^{-3/2} λ_{s/2,2}^{-1/2}(Q;a) ‖∇u‖_{energy}
      + C s^{-3} λ_{s/2,2}^{-1}(Q;a) [𝐠]_{B^s_{2,2}(Q)} ,
```

which is the printed `e.cg.Poincare.with.rhs.grad` character for character: the
`s^{-3/2} λ^{-1/2}` / `s^{-3} λ^{-1}` pair, the note-normalized
`3^{-sm}‖∇u‖_{B^{-s}_{2,2}}` on the left, and `3^{sm}[𝐠]_{H^s}` on the right.

* **`besov`** ⇝ `scaleNormalizedNegativeBesovVectorNorm Q s (.finite 2) (∇u)`.
* **`lamInv`** ⇝ `stepSevenCgLamInv Q a s = λ_{s/2,2}^{-1}(Q;𝐚)`, defined here
  as the `rpow`-`(-1)` power of `Ch02.lambdaSq`, i.e. literally the second leg's
  own ellipticity factor.  `sqrt_stepSevenCgLamInv_eq` proves that its square
  root is literally the first leg's `poincareLowerEllipticityFactor`, so the two
  legs are weighted by one object — the object a future Step-7b theorem
  (`e.lambda.stability.applied`) must bound by `C σ_{m'}^{-1}`.  This is the
  carrier that the Step-7c and Step-7d `hlambda` slots both consume, so one
  Step-7b theorem discharges both.
* **`dataLoc`** ⇝ `scaleNormalizedPositiveBesovVectorSeminormTwo Q s g`.
* **`Ccg`** ⇝ `C · s^{-3}`: the two printed `s`-powers are collapsed to the
  larger one, which is legitimate exactly because `s ≤ 1`
  (`rpow_neg_three_halves_le_rpow_neg_three`).  Nothing else is enlarged.

## Off-grid: the §4.4 window `z'+□_{m'-1}`

`z'+□_{m'-1}` is not a `TriadicCube` — `z'` is the clamped, off-lattice centre.
The instantiation route is the convention *translate the sample, never the
cube*: the theorems below are applied at `Q := originCube d (m'-1)`, which is a
`TriadicCube`, with the translated sample

```text
  a ↦ 𝐚_{L,m'}(z'+·) ,   u ↦ u(z'+·) ,   g ↦ 𝐠(z'+·) ,
```

whose forced-equation binder is the
`isForcedEquation_fluxCorrectedCoeffFamily_of_isDirichletSolutionOn` route and
whose `L²` carriers transport by `normalizedL2SqOnSet_translateSet` /
`normalizedSetAverage_translateSet`.  No new analysis is used and no statement
is transported here: the §4.4 scalars are the translated-frame objects, exactly
as the Step-7c matching leaves its own carrier bridge to the caller.

## References

* ABK26, `l.coarse.graining.RHS`.
* ABK26, `e.cg.Poincare.with.rhs.grad.applied`.
* CoarseGraining, `Homogenization/Book/Ch03/Theorems/CoarsePoincare.lean`.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03

noncomputable section

variable {d : ℕ}

/-! ## 1. The ellipticity carrier shared by the two legs -/

/-- **The coarse-grained ellipticity weight of `l.coarse.graining.RHS`**:
`λ_{s/2,2}^{-1}(Q;𝐚)`, the object the printed display carries with a square
root on the gradient leg and in full on the data leg.  This is the `lamInv`
slot's `hcg`, and the object `e.lambda.stability.applied` must bound by `C
σ^{-1}`.  It is coarse-grained: no bare ellipticity of `𝐚` occurs. -/
noncomputable def stepSevenCgLamInv [NeZero d] (Q : TriadicCube d)
    (a : CoeffFamily d) (s : ℝ) : ℝ :=
  Real.rpow (Ch02.lambdaSq Q (s / 2) (Ch02.MultiscaleExponent.finite 2) a) (-1 : ℝ)

/-- **The two legs carry ONE ellipticity object.**  The gradient leg's
`poincareLowerEllipticityFactor Q a (s/2) (.finite 2) = λ_{s/2,2}^{-1/2}` is
the square root of the data leg's `stepSevenCgLamInv Q a s = λ_{s/2,2}^{-1}`.
This is what lets's `hlambda` be a SINGLE scalar inequality. -/
theorem sqrt_stepSevenCgLamInv_eq [NeZero d] (Q : TriadicCube d)
    (a : CoeffFamily d) {s : ℝ} (hs : 0 < s) :
    Real.sqrt (stepSevenCgLamInv Q a s) =
      poincareLowerEllipticityFactor Q a (s / 2) (Ch02.MultiscaleExponent.finite 2) := by
  have hL : 0 ≤ Ch02.lambdaSq Q (s / 2) (Ch02.MultiscaleExponent.finite 2) a :=
    Ch02.lambdaSq_finite_nonneg Q a (by linarith only [hs]) (by norm_num)
  have hmul :
      Real.rpow (Ch02.lambdaSq Q (s / 2) (Ch02.MultiscaleExponent.finite 2) a)
          ((-1 : ℝ) * (1 / 2 : ℝ)) =
        Real.rpow
          (Real.rpow (Ch02.lambdaSq Q (s / 2) (Ch02.MultiscaleExponent.finite 2) a) (-1 : ℝ))
          (1 / 2 : ℝ) :=
    Real.rpow_mul hL (-1 : ℝ) (1 / 2 : ℝ)
  have hsq : Real.sqrt (stepSevenCgLamInv Q a s) =
      Real.rpow (stepSevenCgLamInv Q a s) (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hexp : (-1 : ℝ) * (1 / 2 : ℝ) = -(1 / 2 : ℝ) := by norm_num
  rw [hsq, stepSevenCgLamInv, ← hmul, hexp, poincareLowerEllipticityFactor]

/-! ## 2. The `s`-power collapse -/

/-- `s^{-3/2} ≤ s^{-3}` for `0 < s ≤ 1`: the two printed prefactors of
`l.coarse.graining.RHS` collapse to the larger one, which is what lets the `hcg`
slot carry a single `Ccg`. -/
theorem rpow_neg_three_halves_le_rpow_neg_three {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    Real.rpow s (-(3 / 2 : ℝ)) ≤ Real.rpow s (-3 : ℝ) :=
  Real.rpow_le_rpow_of_exponent_ge hs hs1 (by norm_num)

/-- **`l.coarse.graining.RHS`, matched to the `hcg` slot.**

For every triadic cube `Q`, every coefficient family `𝐚`, every exponent
`s ∈ (0,1)`, every forcing `𝐠 ∈ H^s(Q)` and every `H¹(Q)` solution of
`-∇·𝐚∇u = ∇·𝐠`,

```text
  3^{-sm}‖∇u‖_{B^{-s}_{2,2}(Q)}
    ≤ (C s^{-3})·(√(λ_{s/2,2}^{-1})·‖∇u‖_{energy})
      + (C s^{-3})·(λ_{s/2,2}^{-1}·3^{sm}[𝐠]_{H^s(Q)}) ,
```

which is `stepSevenCgPoincareApplied`'s `hcg` hypothesis verbatim at
`Ccg = C s^{-3}` and `lamInv = stepSevenCgLamInv Q a s`.  Unconditional beyond
the printed lemma's own binders. -/
theorem exists_stepSevenCgPoincareInput (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ} {g : Vec d → Vec d}
        (u : ForcedCubeSolution Q a g),
        0 < s → s < 1 → ForceBesovRegularity Q s g →
          scaleNormalizedNegativeBesovVectorNorm Q s (Ch02.MultiscaleExponent.finite 2)
              (forcedSolutionGradientField u) ≤
            (C * Real.rpow s (-3 : ℝ)) *
                (Real.sqrt (stepSevenCgLamInv Q a s) * forcedSolutionEnergyNorm Q a u) +
              (C * Real.rpow s (-3 : ℝ)) *
                (stepSevenCgLamInv Q a s *
                  scaleNormalizedPositiveBesovVectorSeminormTwo Q s g) := by
  obtain ⟨C, hCpos, hgrad, _⟩ := (coarsePoincareRHSTheory (d := d)).exists_constant
  refine ⟨C, hCpos, ?_⟩
  intro Q a s g u hs hs1 hg
  have hmain := hgrad u hs hs1 hg
  rw [coarsePoincareWithRHSGradientRHS] at hmain
  -- the gradient leg: one ellipticity object, and the smaller `s`-power
  have hlam := sqrt_stepSevenCgLamInv_eq Q a hs
  have hE : (0 : ℝ) ≤ forcedSolutionEnergyNorm Q a u := by
    rw [forcedSolutionEnergyNorm, h1EnergyNormOnCube]
    exact Real.sqrt_nonneg _
  have hP : (0 : ℝ) ≤ Real.sqrt (stepSevenCgLamInv Q a s) * forcedSolutionEnergyNorm Q a u :=
    mul_nonneg (Real.sqrt_nonneg _) hE
  have hpow : Real.rpow s (-(3 / 2 : ℝ)) ≤ Real.rpow s (-3 : ℝ) :=
    rpow_neg_three_halves_le_rpow_neg_three hs hs1.le
  have hCmul : C * Real.rpow s (-(3 / 2 : ℝ)) ≤ C * Real.rpow s (-3 : ℝ) :=
    mul_le_mul_of_nonneg_left hpow hCpos.le
  have hleg1 :
      C * Real.rpow s (-(3 / 2 : ℝ)) *
          poincareLowerEllipticityFactor Q a (s / 2) (Ch02.MultiscaleExponent.finite 2) *
          forcedSolutionEnergyNorm Q a u ≤
        (C * Real.rpow s (-3 : ℝ)) *
          (Real.sqrt (stepSevenCgLamInv Q a s) * forcedSolutionEnergyNorm Q a u) := by
    rw [← hlam]
    have hshape :
        C * Real.rpow s (-(3 / 2 : ℝ)) * Real.sqrt (stepSevenCgLamInv Q a s) *
            forcedSolutionEnergyNorm Q a u =
          (C * Real.rpow s (-(3 / 2 : ℝ))) *
            (Real.sqrt (stepSevenCgLamInv Q a s) * forcedSolutionEnergyNorm Q a u) := by
      ring
    rw [hshape]
    exact mul_le_mul_of_nonneg_right hCmul hP
  -- the data leg: an identity
  have hleg2 :
      C * Real.rpow s (-3 : ℝ) *
          Real.rpow (Ch02.lambdaSq Q (s / 2) (Ch02.MultiscaleExponent.finite 2) a) (-1 : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q s g =
        (C * Real.rpow s (-3 : ℝ)) *
          (stepSevenCgLamInv Q a s *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q s g) := by
    rw [stepSevenCgLamInv]; ring
  linarith only [hmain, hleg1, hleg2.ge, hleg2.le]

noncomputable def stepSevenCgS : ℝ := stepOneS

@[simp] theorem stepSevenCgS_eq : stepSevenCgS = 1 / 4 := rfl

theorem stepSevenCgS_pos : 0 < stepSevenCgS := by rw [stepSevenCgS_eq]; norm_num

theorem stepSevenCgS_lt_one : stepSevenCgS < 1 := by rw [stepSevenCgS_eq]; norm_num

/-- **The pin makes the two `s`-prefactors absolute numerals**: `s₀^{-3} = 64` (and
`s₀^{-3/2} = 8`, dominated by it). -/
theorem stepSevenCgSPow_eq : Real.rpow stepSevenCgS (-3 : ℝ) = 64 := by
  have hcast : (-3 : ℝ) = (((-3 : ℤ)) : ℝ) := by norm_num
  have hz : Real.rpow ((1 : ℝ) / 4) (((-3 : ℤ)) : ℝ) = ((1 : ℝ) / 4) ^ (-3 : ℤ) :=
    Real.rpow_intCast _ _
  rw [stepSevenCgS_eq, hcast, hz]
  norm_num

/-- **`l.coarse.graining.RHS` at the §4.4 pin `s₀ = 1/4`.**  The `hcg` shape with the
prefactor an absolute numeral `64 C`. -/
theorem exists_stepSevenCgPoincareInput_pinned (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {g : Vec d → Vec d}
        (u : ForcedCubeSolution Q a g),
        ForceBesovRegularity Q stepSevenCgS g →
          scaleNormalizedNegativeBesovVectorNorm Q stepSevenCgS
              (Ch02.MultiscaleExponent.finite 2) (forcedSolutionGradientField u) ≤
            (C * 64) *
                (Real.sqrt (stepSevenCgLamInv Q a stepSevenCgS) *
                  forcedSolutionEnergyNorm Q a u) +
              (C * 64) *
                (stepSevenCgLamInv Q a stepSevenCgS *
                  scaleNormalizedPositiveBesovVectorSeminormTwo Q stepSevenCgS g) := by
  obtain ⟨C, hCpos, hC⟩ := exists_stepSevenCgPoincareInput d
  refine ⟨C, hCpos, ?_⟩
  intro Q a g u hg
  have h := hC (a := a) u stepSevenCgS_pos stepSevenCgS_lt_one hg
  rwa [stepSevenCgSPow_eq] at h

end

end Algsuperdiff.Section4.Provider.Regularity

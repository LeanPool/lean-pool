/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.LambdaIndexUpscale

/-!
# LambdaSlotConsumer

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Bullet (B5) at the `λ`-slot that Step 3's display actually reads

## The carrier gap this module closes

`MajorantSlots.step3DisplayAt` reads its `λ`-slot as

```
( unitCubeLambda (2γ) 2 ( unitRescaledCutoffCoeff M R (R.scale − 2) ω ) )^{-1} ,
```

the frozen Section-2.4 unit-cube gauge of the rescaled cutoff object at the
gapped gauge `s = 2γ`, whereas `LambdaIndexUpscale.lambdaPrintedAtom` is the
manuscript's `λ_{γ,2}^{-1}(z + □_j; 𝐚_{j−2})` at the printed gauge `γ`.  Two
proved identities and one antitonicity close the gap at constant `1`:

1. `BadEvents.unitCubeLambda_unitRescaledCutoffCoeff` — the unit-cube gauge of
   the rescaled object IS `Ch02.lambdaSq R s q (𝐚_{R.scale−2})`;
2. `Localize.inv_lambdaSq_two_antitone_gauge` — `λ^{-1}` is antitone in the
   gauge, so the `γ`-reading dominates the `2γ`-reading (this is the ONE
   available direction, and here it is the useful one);
3. `BadEvents.cubeLowerEllipticityInvLiteral_translateCutoffSample` together
   with `BadEvents.cubeLowerEllipticityInvLiteral_inv_eq_lambdaSq` — the cube
   `R` at the field `𝐚_{R.scale−2}` is the origin cube `□_{R.scale}` at the
   sample translated by `R`'s base point, which is exactly `lambdaPrintedAtom M
   R.scale (triadicCubeShift R)`.

Consequently the whole (B5) moment bound of `LambdaIndexUpscale` — printed cube
`□_j`, printed field `𝐚_{j−2}`, printed gauge `σ_{j−1}`, constant `64(1+9^d)` —
transfers verbatim to the slot Step 3 consumes.  No `γ`-exponent and no
`s`-power is moved.

## References

* ABK26, `l.bounds.mathcal.E.aL` bullet (B5); Step 3 display
  `e.apply.sensitivity.J.aL`.
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section4.Provider.Annular

noncomputable section

variable {d : ℕ}

/-- Local re-derivation (distinct name) of the `private neZero_of_model` of
the sibling modules. -/
private theorem neZeroFromModelSlot (M : ABKModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩

/-- Local re-derivation (distinct name) of `LambdaIndexUpscale.coarseTwoValue`
and `Annular.LambdaBudget.coarseTwo_val`. -/
private theorem coarseTwoSlot :
    Support.coarseEllipticityExponentTwo.1 = (Ch02.MultiscaleExponent.finite 2) := rfl

/-! ## 1. The pointwise carrier bridge -/

/-- **The `λ`-slot of Step 3's display is dominated by the printed (B5) atom.**

`(unitCubeLambda (2γ) 2 (unitRescaledCutoffCoeff M R (R.scale−2) ω))^{-1} ≤
λ_{γ,2}^{-1}(3^{R.scale}v + □_{R.scale}; 𝐚_{R.scale−2})`,

at constant `1`.  The inequality (rather than equality) is exactly the gauge
antitonicity `2γ ≥ γ`; the converse is NOT available (A9). -/
theorem inv_unitCubeLambda_twoGamma_le_lambdaPrintedAtom (M : ABKModel d)
    (R : TriadicCube d) (omega : Cutoff.CutoffSample d) :
    (Algsuperdiff.Frozen.Section24.unitCubeLambda (2 * M.gamma) (.finite 2)
        (unitRescaledCutoffCoeff M R (R.scale - 2) omega))⁻¹ ≤
      lambdaPrintedAtom M R.scale (triadicCubeShift R) omega := by
  have : NeZero d := neZeroFromModelSlot M
  have hg0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  set a := Cutoff.coefficientCutoffTriadicCoeffFamily M (R.scale - 2) omega with ha
  rw [unitCubeLambda_unitRescaledCutoffCoeff M R (R.scale - 2) (2 * M.gamma)
    (.finite 2) omega, ← ha]
  have hgauge : (Ch02.lambdaSq R (2 * M.gamma) (.finite 2) a)⁻¹ ≤
      (Ch02.lambdaSq R M.gamma (.finite 2) a)⁻¹ :=
    Localize.inv_lambdaSq_two_antitone_gauge R a hg0 (by linarith only [hg0])
  have hlit := cubeLowerEllipticityInvLiteral_inv_eq_lambdaSq M R (R.scale - 2) M.gamma
    Support.coarseEllipticityExponentTwo omega
  rw [coarseTwoSlot, ← ha] at hlit
  have hswap := cubeLowerEllipticityInvLiteral_translateCutoffSample M R (R.scale - 2)
    M.gamma Support.coarseEllipticityExponentTwo omega
  have hid : (Ch02.lambdaSq R M.gamma (.finite 2) a)⁻¹ =
      lambdaPrintedAtom M R.scale (triadicCubeShift R) omega := by
    rw [← hlit, inv_inv, hswap]
    rfl
  exact le_trans hgauge (le_of_eq hid)

/-! ## 2. The moment bound at the consumed slot -/

/-- **The consumed-slot bullet, packaged and unconditional in the printed
regime.**  The counterpart of
`LambdaIndexUpscale.exists_lintegral_rpow_lambdaPrintedAtom_le` at the slot
Step 3 reads. -/
theorem exists_lintegral_rpow_inv_unitCubeLambda_twoGamma_le (d : ℕ) :
    ∃ C : ℝ, 6 ≤ C ∧
      ∀ M : ABKModel d,
        M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        ∃ E : {E : ℝ // 1 ≤ E},
          (E : ℝ) = C * (Disorder.cstar M)⁻¹ ∧
            ∀ (R : TriadicCube d) (p : ℝ), 1 ≤ p →
              ∫⁻ omega : Cutoff.CutoffSample d,
                  ENNReal.ofReal
                    ((Algsuperdiff.Frozen.Section24.unitCubeLambda (2 * M.gamma) (.finite 2)
                      (unitRescaledCutoffCoeff M R (R.scale - 2) omega))⁻¹) ^ p
                  ∂(Cutoff.cutoffSampleLaw M).toMeasure
                ≤ ENNReal.ofReal
                    (lambdaUpscaleConst d * (((Annealed.sigmaBar M (R.scale - 1) : ℝ))⁻¹ *
                        Support.cgEllipLowerConstant d) +
                      gammaMomentBound (1 / 3) p
                        (lambdaUpscaleConst d * lambdaMaxOrliczConst d *
                          (((Annealed.sigmaBar M (R.scale - 1) : ℝ))⁻¹ *
                            Proportion.cgTailScale M (E : ℝ)))) ^ p := by
  obtain ⟨C, hC6, hall⟩ := exists_lintegral_rpow_lambdaPrintedAtom_le d
  refine ⟨C, hC6, fun M hreg => ?_⟩
  obtain ⟨E, hEval, hbound⟩ := hall M hreg
  refine ⟨E, hEval, fun R p hp => ?_⟩
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  refine le_trans (lintegral_mono fun omega => ?_)
    (hbound R.scale (triadicCubeShift R) p hp)
  exact ENNReal.rpow_le_rpow
    (ENNReal.ofReal_le_ofReal (inv_unitCubeLambda_twoGamma_le_lambdaPrintedAtom M R omega))
    hp0.le

end

end Algsuperdiff.Section4.Provider.BoundsEaL

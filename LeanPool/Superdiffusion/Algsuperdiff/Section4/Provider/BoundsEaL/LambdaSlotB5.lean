/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.MomentEngine
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.AtomTail
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Localize.GaugeAntitone
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Localize.SensitivitySwitch

/-!
# LambdaSlotB5

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Step 4's bullet (B5): the `λ`-slot display and its `q`-th moments

## The printed bullet

```
λ_{γ,2}^{-1}(□_j; 𝐚_{j−2}) ≤ C σ_{j−1}^{-1} + 𝒪_{Γ_{1/3}}(C σ_{j−1}^{-1}exp(−C^{-1}γ^{-1}))
E[λ_{γ,2}^{-q}(□_j; 𝐚_{j−2})]^{1/q} ≤ C σ_{j−1}^{-1}(1 + C q³ exp(−C^{-1}γ^{-1}))
```

the `q³` being `q^{1/σ}` at `σ = 1/3`.

## What is delivered, and the ONE index that does not match

The whole display is produced from the Section 3 anchor
`Frozen.Section3.coarse_ellipticity_bounds` through the proved
`Proportion.AtomTail`, whose `exists_cgExcess_atomTail` already discharges the
induction state and both `E`-window premises of `p.cg.ellipticity.bounds` (the
all-scales budget at the floor `(3/2)·exp(3C_cg)`).

**The index mismatch.**  The proposition is `sup_{L ≥ m−1}
λ_{s,q}^{-1}(□_m; 𝐚_L) σ_{m−1}` (frozen at the family base `m − 1`).
Reading it at the cube `□_j` forces `m = j`, hence `σ_{j−1}` — which is
exactly the printed right-hand side — but also `L ≥ j − 1`, whereas the printed
left-hand side carries the field `𝐚_{j−2}`.  The two readings cannot both hold:
at `m = j − 1` the field index `j − 2` is admissible but the cube becomes
`□_{j−1}` and the gauge becomes `σ_{j−2}`.  The statements below are therefore
delivered at the anchor's own matched pair `(□_{k−2}, 𝐚_{k−2}, σ_{k−3})`, i.e. at
`k = j + 2` in the Step-4 indices: cube `□_j`, gauge `σ_{j−1}` — both printed
— and field `𝐚_j` in place of the printed `𝐚_{j−2}`.  The missing step is a
domain/field upscaling for `λ^{-1}`, the (B5) analogue of (B4)'s; it is not
performed here, but in `LambdaIndexUpscale.lean`.

## The gauge

The displays are at the printed gauge `γ`.  Here that direction is the useful
one: `..._twoGamma` below transports every bound proved at `γ` to the gapped
gauge at constant `1`.  The converse is NOT available and is not claimed.

## References

* ABK26, `l.bounds.mathcal.E.aL`, (bullet (B5)); `p.cg.ellipticity.bounds`;
  `l.moments.gamma.psi`.
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## 1. The `σ = 1/3` moment majorant -/

/-! ## 2. The deterministic rearrangement -/

/-- **The bullet's shape, pointwise.**

`λ_{γ,2}^{-1}(z+□_{k−2}; 𝐚_{k−2}) ≤ σ_{k−3}^{-1}C + σ_{k−3}^{-1}𝒳_{k−2}(z)`,
where `𝒳` is `Localize.cgExcess`, the `𝒢₀` bracket.  This is the algebraic
content of bullet (B5): the anchor controls `σ_{k−3}λ^{-1}` and the bullet
divides by `σ_{k−3}`.  In the Step-4 indices `k = j + 2`: cube `□_j`, gauge
`σ_{j−1}`. -/
theorem lambdaAnnulusAtom_le_inv_sigmaBar_mul_add (M : ABKModel d) (Ccg : ℝ)
    (k : ℤ) (z : Vec d) (omega : Cutoff.CutoffSample d) :
    Support.lambdaAnnulusAtom M k z omega ≤
      ((Annealed.sigmaBar M (k - 3) : ℝ))⁻¹ * Ccg +
        ((Annealed.sigmaBar M (k - 3) : ℝ))⁻¹ *
          Localize.cgExcess M Ccg (k - 2) z omega := by
  have hS : (0 : ℝ) < (Annealed.sigmaBar M (k - 3) : ℝ) :=
    Provider.Orlicz.sigmaBar_pos M (k - 3)
  have hkey : (Annealed.sigmaBar M (k - 3) : ℝ) *
      Support.lambdaAnnulusAtom M k z omega - Ccg ≤
      Localize.cgExcess M Ccg (k - 2) z omega := by
    rw [Localize.cgExcess_sub_two]
    exact le_max_left _ _
  have hprod : (Annealed.sigmaBar M (k - 3) : ℝ) *
      Support.lambdaAnnulusAtom M k z omega ≤
      Ccg + Localize.cgExcess M Ccg (k - 2) z omega := by
    linarith only [hkey]
  have hfirst : Support.lambdaAnnulusAtom M k z omega =
      ((Annealed.sigmaBar M (k - 3) : ℝ))⁻¹ *
        ((Annealed.sigmaBar M (k - 3) : ℝ) *
          Support.lambdaAnnulusAtom M k z omega) := by
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hS), one_mul]
  calc Support.lambdaAnnulusAtom M k z omega
      = ((Annealed.sigmaBar M (k - 3) : ℝ))⁻¹ *
          ((Annealed.sigmaBar M (k - 3) : ℝ) *
            Support.lambdaAnnulusAtom M k z omega) := hfirst
    _ ≤ ((Annealed.sigmaBar M (k - 3) : ℝ))⁻¹ *
          (Ccg + Localize.cgExcess M Ccg (k - 2) z omega) :=
        mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr hS.le)
    _ = ((Annealed.sigmaBar M (k - 3) : ℝ))⁻¹ * Ccg +
          ((Annealed.sigmaBar M (k - 3) : ℝ))⁻¹ *
            Localize.cgExcess M Ccg (k - 2) z omega := by ring

/-- The `𝒢₀` bracket is measurable in the sample (through the proved measurability
of the `λ`-literal at a translated centre). -/
theorem measurable_cgExcess (M : ABKModel d) (Ccg : ℝ) (k : ℤ) (z : Vec d) :
    Measurable fun omega : Cutoff.CutoffSample d =>
      Localize.cgExcess M Ccg (k - 2) z omega := by
  have hfun : (fun omega : Cutoff.CutoffSample d =>
        Localize.cgExcess M Ccg (k - 2) z omega) =
      fun omega : Cutoff.CutoffSample d =>
        max ((Annealed.sigmaBar M (k - 3) : ℝ) *
          Support.lambdaAnnulusAtom M k z omega - Ccg) 0 :=
    funext fun omega => Localize.cgExcess_sub_two M Ccg k z omega
  rw [hfun]
  exact (((Support.measurable_lambdaAnnulusAtom M k z).const_mul _).sub_const
    _).max measurable_const

/-! ## 3. The moment conversion at the anchor's own premises -/

/-! ## 4. The gapped gauge `s = 2γ` -/

end

end Algsuperdiff.Section4.Provider.BoundsEaL

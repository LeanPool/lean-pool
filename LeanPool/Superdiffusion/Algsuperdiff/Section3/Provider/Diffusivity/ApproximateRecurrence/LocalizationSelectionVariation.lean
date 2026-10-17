/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationBasicSplit
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationSelectionExistence
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Whitney.ZeroExtension

/-!
# LocalizationSelectionVariation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the first variation of the field-slope localization minimizer

Source displays in ABK26:

* `e.Pz.def` and `e.Fz.def`;
* `e.lower.bound.basic.split`, whose quadratic expansion is the second line of
  the display and whose cross-term collapse is the third line, the cross summand
  itself sitting;

This module joins the existence layer of `LocalizationSelectionExistence.lean`
to the cell algebra of `LocalizationBasicSplit.lean`: it turns the *minimality*
of the field-slope minimizers into the *Euler--Lagrange* property that the cell
algebra consumes.

## What is proved

* `isDoubledTestField_add` -- the doubled test fields form an additive class
  (the two halves are `Whitney/ZeroExtension.lean`'s closure lemmas).
* `isDoubledAmbientField_of_isDoubledMuAdmissibleField` -- a competitor over an
  ambient slope field is ambient.
* `isDoubledResponseField_of_isDoubledMuMinimizerField` -- **the first
  variation**: a field-slope minimizer is a doubled response field.  This is
  what makes `LocalizationBasicSplit`'s cross-term collapse
  (`volumeAverage_doubledBlockPairingIntegrand_of_isDoubledResponseField`)
  applicable to `tilde S_z`, whose class is based at the field `bfF_z` rather
  than at a constant load.
* `two_mul_doubledMuValue_eq_volumeAverage_of_isDoubledMuMinimizerField` -- **
  with its correct justification**: `fint_U tilde S. bfA tilde S = fint_U bfF.
  bfA tilde S`.
* `isDoubledMuAdmissibleField_add_of_isDoubledMuAdmissible` -- the
  predicate-level companion of `X_z = S_z + tilde S_z`: a constant-load
  admissible field plus a field-slope admissible field is admissible for the
  shifted slope field.

## Divergences from the printed statement

* Mean-zeroness alone does not give the identity; the reason is the
  Euler--Lagrange equation of the minimizer.  Nor does mean-zeroness alone
  place `tilde S_z` in the class: ambient membership and integrability of
  `bfF_z` come from its gradient/solenoidal structure, and the actual-carrier
  consumer owes that derivation.
  `two_mul_doubledMuValue_eq_volumeAverage_of_isDoubledMuMinimizerField` below
  uses mean-zeroness nowhere.  In the pinned copy is the `Hminusul` factor of
  the *inequality that follows*; the justification sentence is and the identity
  itself is the first two lines of the display.
* **The factor two.**  As in `LocalizationBasicSplit.lean`, the manuscript's
  `fint_U X . bfA X` is twice CoarseGraining's `doubledMuValue`; the factor is
  carried explicitly rather than renormalizing either object.
* **.**  The carrier is Chapter 2's `DoubledField d` over `Domain d`; see
  `LocalizationSelectionExistence.lean`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-! ## Sums of test fields -/

/-- The doubled test fields form an additive class. -/
theorem isDoubledTestField_add {U : Domain d} {Y Z : DoubledField d}
    (hY : IsDoubledTestField U Y) (hZ : IsDoubledTestField U Z) :
    IsDoubledTestField U (Y + Z) := by
  constructor
  · exact potentialZeroTraceFieldOn_add hY.1 hZ.1
  · exact solenoidalZeroNormalTraceFieldOn_add hY.2 hZ.2

/-! ## The constant-slope special case -/

/-- **The predicate-level companion of `X_z = S_z + tilde S_z`.** A constant-load
admissible field plus a field-slope admissible field is admissible for the
shifted slope field.  At the manuscript's carriers, `S_z` is admissible at the
constant load `P_z` (`e.Pz.def`), `tilde S_z` is admissible for `bfF_z`
(`e.Fz.def`), and the shifted slope field `constantDoubledField P_z + bfF_z` is
exactly the background of the `X_z` display. -/
theorem isDoubledMuAdmissibleField_add_of_isDoubledMuAdmissible {U : Domain d}
    {P : BlockVec d} {F S T : DoubledField d}
    (hS : IsDoubledMuAdmissible U P S) (hT : IsDoubledMuAdmissibleField U F T) :
    IsDoubledMuAdmissibleField U (constantDoubledField P + F) (S + T) := by
  have hrw : (S + T) - (constantDoubledField P + F)
      = (S - constantDoubledField P) + (T - F) := by
    refine HCPolySupport.Internal.Ch02.BookCh02.doubledField_ext ?_ ?_
    · funext x
      change S.potential x + T.potential x - (P.1 + F.potential x)
        = (S.potential x - P.1) + (T.potential x - F.potential x)
      abel
    · funext x
      change S.flux x + T.flux x - (P.2 + F.flux x)
        = (S.flux x - P.2) + (T.flux x - F.flux x)
      abel
  have hT' : IsDoubledTestField U (T - F) := hT
  rw [isDoubledMuAdmissibleField_iff_isDoubledTestField_sub, hrw]
  exact isDoubledTestField_add (isDoubledTestField_sub_constantDoubledField hS) hT'

/-! ## Ambient membership of a competitor -/

/-- A competitor over an ambient slope field is itself ambient, i.e. lies in
`Lpot(U) x Lsol(U)`.  Both halves are the corresponding closure of the
Chapter-1 field spaces under adding a zero-trace element. -/
theorem isDoubledAmbientField_of_isDoubledMuAdmissibleField {U : Domain d}
    {F X : DoubledField d} (hF : IsDoubledAmbientField U F)
    (hX : IsDoubledMuAdmissibleField U F X) :
    IsDoubledAmbientField U X := by
  have hX' : IsDoubledTestField U (X - F) := hX
  obtain ⟨hFpL2, u, hu⟩ := hF.1
  obtain ⟨hFfL2, hFf⟩ := hF.2
  obtain ⟨hDpL2, v, hv⟩ := hX'.1
  obtain ⟨hDfL2, hDf⟩ := hX'.2
  have hXpot : MemVectorL2 (U : Set (Vec d)) X.potential :=
    memVectorL2_potential_of_isDoubledMuAdmissibleField hFpL2 hX
  have hXflux : MemVectorL2 (U : Set (Vec d)) X.flux :=
    memVectorL2_flux_of_isDoubledMuAdmissibleField hFfL2 hX
  constructor
  · refine ⟨hXpot, u + v.toH1Function, ?_⟩
    filter_upwards [hu, hv] with x hx hy
    have hdec : X.potential x = F.potential x + (X - F).potential x := by
      change X.potential x = F.potential x + (X.potential x - F.potential x)
      abel
    rw [hdec, hx, hy, H1Function.add_grad]
  · refine ⟨hXflux, fun phi => ?_⟩
    have hint1 := integrableOn_vecDot_of_memVectorL2 hFfL2 phi.toH1Function.grad_memVectorL2
    have hint2 := integrableOn_vecDot_of_memVectorL2 hDfL2 phi.toH1Function.grad_memVectorL2
    have hpt : ∀ x : Vec d,
        vecDot (X.flux x) (phi.toH1Function.grad x)
          = vecDot (F.flux x) (phi.toH1Function.grad x)
            + vecDot ((X - F).flux x) (phi.toH1Function.grad x) := by
      intro x
      have hdec : X.flux x = F.flux x + (X - F).flux x := by
        change X.flux x = F.flux x + (X.flux x - F.flux x)
        abel
      conv_lhs => rw [hdec]
      exact vecDot_add_left _ _ _
    calc
      ∫ x in (U : Set (Vec d)), vecDot (X.flux x) (phi.toH1Function.grad x) ∂volume
          = ∫ x in (U : Set (Vec d)),
              (vecDot (F.flux x) (phi.toH1Function.grad x)
                + vecDot ((X - F).flux x) (phi.toH1Function.grad x)) ∂volume :=
            integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = (∫ x in (U : Set (Vec d)), vecDot (F.flux x) (phi.toH1Function.grad x) ∂volume)
            + ∫ x in (U : Set (Vec d)),
                vecDot ((X - F).flux x) (phi.toH1Function.grad x) ∂volume :=
            integral_add hint1 hint2
      _ = 0 := by rw [hFf phi, hDf phi.toH1Function, add_zero]

/-! ## The first variation -/

/-- **The first variation of the field-slope minimizer.** A minimizer of the
doubled energy over the affine class `F + (L^2_{pot,0} x Lsolo)(U)` is a
doubled response field on `U`, i.e. it satisfies the Euler--Lagrange equation
against every test field.

At the manuscript's carriers this is the property of `tilde S_z` that
`LocalizationBasicSplit.volumeAverage_doubledBlockPairingIntegrand_of_isDoubledResponseField`
consumes for the cross-term collapse of `e.lower.bound.basic.split`, the third
line of that display it is also the correct justification of the identity. -/
theorem isDoubledResponseField_of_isDoubledMuMinimizerField {U : Domain d} {a : CoeffOn U}
    {F X : DoubledField d} (hF : IsDoubledAmbientField U F)
    (hX : IsDoubledMuMinimizerField U a F X) :
    IsDoubledResponseField U a X :=
  isDoubledResponseField_of_forall_le_add_isDoubledTestField
    (isDoubledAmbientField_of_isDoubledMuAdmissibleField hF hX.1)
    (fun Y hY => hX.2 (X + Y) (isDoubledMuAdmissibleField_add hX.1 hY))

/-! ## The energy comparison -/

/-- **ABK26's variation display, with the justification.**  For a field-slope
minimizer `X` over the slope field `F`,

```
fint_U X . bfA_m X = fint_U F . bfA_m X .
```

The manuscript justifies this by "since `bfF_z` has mean zero in `z+cu_n`";
mean-zeroness is used nowhere below.  The identity is the Euler--Lagrange
equation of `X` tested against the test field `X - F`.  Mean-zeroness alone
does not place `tilde S_z` in the class; membership needs the
gradient/solenoidal structure and integrability of `bfF_z`, which the
actual-carrier consumer must derive. -/
theorem two_mul_doubledMuValue_eq_volumeAverage_of_isDoubledMuMinimizerField
    {U : Domain d} {a : CoeffOn U} {F X : DoubledField d}
    (hF : IsDoubledAmbientField U F) (hX : IsDoubledMuMinimizerField U a F X) :
    2 * doubledMuValue U a X
      = volumeAverage (U : Set (Vec d)) (doubledBlockPairingIntegrand U a F X) := by
  have hresp : IsDoubledResponseField U a X :=
    isDoubledResponseField_of_isDoubledMuMinimizerField hF hX
  have hXpot : MemVectorL2 (U : Set (Vec d)) X.potential := hresp.1.1.1
  have hXflux : MemVectorL2 (U : Set (Vec d)) X.flux := hresp.1.2.1
  have hFpot : MemVectorL2 (U : Set (Vec d)) F.potential := hF.1.1
  have hFflux : MemVectorL2 (U : Set (Vec d)) F.flux := hF.2.1
  have hDpot : MemVectorL2 (U : Set (Vec d)) (X - F).potential := hX.1.1.1
  have hDflux : MemVectorL2 (U : Set (Vec d)) (X - F).flux := hX.1.2.1
  have hsplit : doubledBlockPairingIntegrand U a X X
      = doubledBlockPairingIntegrand U a F X
        + doubledBlockPairingIntegrand U a (X - F) X := by
    funext x
    change blockVecDot (X.eval x) (blockMatVecMul (blockMatrixField a x) (X.eval x))
      = blockVecDot (F.eval x) (blockMatVecMul (blockMatrixField a x) (X.eval x))
        + blockVecDot ((X - F).eval x) (blockMatVecMul (blockMatrixField a x) (X.eval x))
    have hdec : X.eval x = F.eval x + (X - F).eval x := by
      refine Prod.ext ?_ ?_
      · change X.potential x = F.potential x + (X.potential x - F.potential x)
        abel
      · change X.flux x = F.flux x + (X.flux x - F.flux x)
        abel
    conv_lhs => rw [hdec]
    rw [blockVecDot_add_left, ← hdec]
  have hintF := integrableOn_doubledBlockPairingIntegrand a hFpot hFflux hXpot hXflux
  have hintD := integrableOn_doubledBlockPairingIntegrand a hDpot hDflux hXpot hXflux
  have hzero : volumeAverage (U : Set (Vec d))
      (doubledBlockPairingIntegrand U a (X - F) X) = 0 :=
    volumeAverage_eq_zero_of_integral_eq_zero (hresp.2 (X - F) hX.1)
  have hval : 2 * doubledMuValue U a X
      = volumeAverage (U : Set (Vec d)) (doubledBlockPairingIntegrand U a X X) := by
    have hpt : (fun x => blockEnergyDensityAt a (X.eval x) x)
        = (1 / 2 : ℝ) • doubledBlockPairingIntegrand U a X X := by
      funext x
      change (1 / 2 : ℝ) * blockVecDot (X.eval x)
          (blockMatVecMul (blockMatrixField a x) (X.eval x)) = _
      rfl
    change 2 * volumeAverage (U : Set (Vec d))
      (fun x => blockEnergyDensityAt a (X.eval x) x) = _
    rw [hpt, volumeAverage_smul]
    ring
  rw [hval, hsplit, volumeAverage_add hintF hintD, hzero, add_zero]

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

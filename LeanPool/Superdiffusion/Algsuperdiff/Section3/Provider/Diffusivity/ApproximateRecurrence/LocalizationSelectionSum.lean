/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationBasicSplit
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationSelectionVariation

/-!
# LocalizationSelectionSum

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: `X_z = S_z + tilde S_z`

The two minimizers it relates are

* `S_z := S(., z+cu_n, -P_z, 0; a_m)`, the minimizer at the *constant* load
  `P_z` of `e.Pz.def`;
* `tilde S_z`, the minimizer over `bfF_z + (L^2_{pot,0} x Lsolo)(z+cu_n)` with
  `bfF_z` of `e.Fz.def`;

and the field they sum to is `X_z`, the minimizer over the class based at
`bfAhom_{m-h}^{-1/2}(e' + grad w_D^{(K)}, e + grad w_N^{(K)} + shom_{m-h}^{-1}
h e')`, which is exactly `constantDoubledField P_z + bfF_z`.

## What is proved

* `isDoubledTestField_sub` -- the doubled test fields are closed under
  differences.
* `isDoubledMuMinimizerField_add` -- ****: if `S` minimizes the doubled energy
  at the constant load `P` and `T` minimizes it over the field-slope class of
  `F`, then `S + T` minimizes it over the field-slope class of
  `constantDoubledField P + F`.

## Method

Purely variational, and it uses no positivity of `bfA` and no ambient-field
hypothesis.  For a competitor `W` of the sum class, `W - S` lies in the class of
`F`, so `E(T) <= E(W - S)`; the quadratic expansion
(`LocalizationBasicSplit.doubledMuValue_add`) then reduces the claim to the
vanishing of the cross pairing of `S` against the test field `W - S - T`, which
is upstream's `DoubledMuTheory.minimizer_first_variation` for `S` combined with
the a.e. symmetry of `bfA(x)`.  Only the *first variation* of `S` is used, not
its minimality.

## Divergences from the printed statement

* **.**  The carrier is Chapter 2's `DoubledField d` over `Domain d`; see
  `LocalizationSelectionExistence.lean`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.Path

noncomputable section

variable {d : ℕ}

/-- The doubled test fields are closed under differences. -/
theorem isDoubledTestField_sub {U : Domain d} {Y Z : DoubledField d}
    (hY : IsDoubledTestField U Y) (hZ : IsDoubledTestField U Z) :
    IsDoubledTestField U (Y - Z) := by
  have h := isDoubledTestField_add hY (isDoubledTestField_smul hZ (-1))
  have hrw : Y + (-1 : ℝ) • Z = Y - Z := by
    refine HCPolySupport.Internal.Ch02.BookCh02.doubledField_ext ?_ ?_
    · funext x
      show Y.potential x + (-1 : ℝ) • Z.potential x = Y.potential x - Z.potential x
      rw [neg_one_smul]
      abel
    · funext x
      show Y.flux x + (-1 : ℝ) • Z.flux x = Y.flux x - Z.flux x
      rw [neg_one_smul]
      abel
  rwa [hrw] at h

/-- The block pairing density is a.e. symmetric in its two fields, because
`bfA(x)` is a.e. a symmetric block matrix. -/
private theorem doubledBlockPairingIntegrand_symm_ae {U : Domain d} (a : CoeffOn U)
    (X Y : DoubledField d) :
    doubledBlockPairingIntegrand U a X Y
      =ᵐ[volumeMeasureOn (U : Set (Vec d))] doubledBlockPairingIntegrand U a Y X := by
  filter_upwards [(blockMatrixFieldAlgebraTheory U a).field_symmetric] with x hx
  exact blockVecDot_blockMatVecMul_comm_of_isSymmetricBlockMat hx (X.eval x) (Y.eval x)

/-- The pairing density is additive in its second field. -/
private theorem doubledBlockPairingIntegrand_add_right {U : Domain d} (a : CoeffOn U)
    (X Y Z : DoubledField d) :
    doubledBlockPairingIntegrand U a X (Y + Z)
      = doubledBlockPairingIntegrand U a X Y + doubledBlockPairingIntegrand U a X Z := by
  funext x
  show blockVecDot (X.eval x) (blockMatVecMul (blockMatrixField a x) ((Y + Z).eval x))
    = blockVecDot (X.eval x) (blockMatVecMul (blockMatrixField a x) (Y.eval x))
      + blockVecDot (X.eval x) (blockMatVecMul (blockMatrixField a x) (Z.eval x))
  have hev : (Y + Z).eval x = Y.eval x + Z.eval x := rfl
  rw [hev, blockMatVecMul_add, blockVecDot_add_right]

/-- **The first variation of the constant-load minimizer, in averaged form.**
The pairing of a constant-load minimizer against any test field has vanishing
normalized average.  Only upstream's `minimizer_first_variation` and the a.e.
symmetry of `bfA(x)` are used. -/
private theorem volumeAverage_doubledBlockPairingIntegrand_eq_zero_of_isDoubledMuMinimizer
    {U : Domain d} {a : CoeffOn U} {P : BlockVec d} {S : DoubledField d}
    (hS : IsDoubledMuMinimizer U a P S) {Y : DoubledField d}
    (hY : IsDoubledTestField U Y) :
    volumeAverage (U : Set (Vec d)) (doubledBlockPairingIntegrand U a S Y) = 0 := by
  have hEL := (doubledMuTheory U a).minimizer_first_variation P S hS Y hY
  rw [volumeAverage_congr_ae (doubledBlockPairingIntegrand_symm_ae a S Y)]
  exact volumeAverage_eq_zero_of_integral_eq_zero hEL

/-- **ABK26's selection split: `X_z = S_z + tilde S_z`.**

If `S` minimizes the doubled energy of `e.variational.mu.U.P` at the constant
load `P`, and `T` minimizes it over the field-slope class of `F`, then `S + T`
minimizes it over the field-slope class of `constantDoubledField P + F`.

At the manuscript's carriers `U = z + cu_n`, `P = P_z` (`e.Pz.def`), `F =
bfF_z` (`e.Fz.def`), `S = S_z`, `T = tilde S_z`, and `constantDoubledField P_z
+ bfF_z` is the background of the `X_z` display, so the conclusion is precisely
that `S_z + tilde S_z` realizes the `argmin` defining `X_z`.

Equality mode: if `X_z` is *defined* as `S_z + tilde S_z`, the identity is
literal.  If `X_z` is instead selected independently as the argmin of its own
display, this theorem combined with a.e. uniqueness
(`sameAE_of_isDoubledMuMinimizerField`) yields only `X_z = S_z + tilde S_z`
almost everywhere. -/
theorem isDoubledMuMinimizerField_add {U : Domain d} {a : CoeffOn U} {P : BlockVec d}
    {F S T : DoubledField d}
    (hFpot : MemVectorL2 (U : Set (Vec d)) F.potential)
    (hFflux : MemVectorL2 (U : Set (Vec d)) F.flux)
    (hS : IsDoubledMuMinimizer U a P S)
    (hT : IsDoubledMuMinimizerField U a F T) :
    IsDoubledMuMinimizerField U a (constantDoubledField P + F) (S + T) := by
  have hSpot := memVectorL2_potential_of_isDoubledMuAdmissible hS.1
  have hSflux := memVectorL2_flux_of_isDoubledMuAdmissible hS.1
  have hTpot := memVectorL2_potential_of_isDoubledMuAdmissibleField hFpot hT.1
  have hTflux := memVectorL2_flux_of_isDoubledMuAdmissibleField hFflux hT.1
  have hStest : IsDoubledTestField U (S - constantDoubledField P) :=
    isDoubledTestField_sub_constantDoubledField hS.1
  have hTtest : IsDoubledTestField U (T - F) := hT.1
  refine ⟨isDoubledMuAdmissibleField_add_of_isDoubledMuAdmissible hS.1 hT.1, ?_⟩
  intro W hW
  have hWtest : IsDoubledTestField U (W - (constantDoubledField P + F)) := hW
  -- `V := W - S` is a competitor for the class of `F`.
  have hVtest : IsDoubledTestField U ((W - S) - F) := by
    have h := isDoubledTestField_sub hWtest hStest
    have hrw : (W - (constantDoubledField P + F)) - (S - constantDoubledField P)
        = (W - S) - F := by
      refine HCPolySupport.Internal.Ch02.BookCh02.doubledField_ext ?_ ?_
      · funext x
        show W.potential x - (P.1 + F.potential x) - (S.potential x - P.1)
          = W.potential x - S.potential x - F.potential x
        abel
      · funext x
        show W.flux x - (P.2 + F.flux x) - (S.flux x - P.2)
          = W.flux x - S.flux x - F.flux x
        abel
    rwa [hrw] at h
  have hV : IsDoubledMuAdmissibleField U F (W - S) := hVtest
  have hVpot := memVectorL2_potential_of_isDoubledMuAdmissibleField hFpot hV
  have hVflux := memVectorL2_flux_of_isDoubledMuAdmissibleField hFflux hV
  -- The cross pairing of `S` against `V - T` vanishes.
  have hcross : volumeAverage (U : Set (Vec d))
      (doubledBlockPairingIntegrand U a S ((W - S) - T)) = 0 :=
    volumeAverage_doubledBlockPairingIntegrand_eq_zero_of_isDoubledMuMinimizer hS
      (by
        have h := isDoubledTestField_sub hVtest hTtest
        have hrw : ((W - S) - F) - (T - F) = (W - S) - T := by
          refine HCPolySupport.Internal.Ch02.BookCh02.doubledField_ext ?_ ?_
          · funext x
            show W.potential x - S.potential x - F.potential x
                - (T.potential x - F.potential x)
              = W.potential x - S.potential x - T.potential x
            abel
          · funext x
            show W.flux x - S.flux x - F.flux x - (T.flux x - F.flux x)
              = W.flux x - S.flux x - T.flux x
            abel
        rwa [hrw] at h)
  -- Split the pairing of `S` against `V` along `V = T + (V - T)`.
  have hVsplit : volumeAverage (U : Set (Vec d))
      (doubledBlockPairingIntegrand U a S (W - S))
      = volumeAverage (U : Set (Vec d)) (doubledBlockPairingIntegrand U a S T) := by
    have hdec : T + ((W - S) - T) = W - S := by
      refine HCPolySupport.Internal.Ch02.BookCh02.doubledField_ext ?_ ?_
      · funext x
        show T.potential x + (W.potential x - S.potential x - T.potential x)
          = W.potential x - S.potential x
        abel
      · funext x
        show T.flux x + (W.flux x - S.flux x - T.flux x) = W.flux x - S.flux x
        abel
    have hDpot : MemVectorL2 (U : Set (Vec d)) ((W - S) - T).potential := by
      have hfun : (W - S).potential - T.potential = ((W - S) - T).potential := rfl
      exact hfun ▸ hVpot.sub hTpot
    have hDflux : MemVectorL2 (U : Set (Vec d)) ((W - S) - T).flux := by
      have hfun : (W - S).flux - T.flux = ((W - S) - T).flux := rfl
      exact hfun ▸ hVflux.sub hTflux
    have hint1 := integrableOn_doubledBlockPairingIntegrand a hSpot hSflux hTpot hTflux
    have hint2 := integrableOn_doubledBlockPairingIntegrand a hSpot hSflux hDpot hDflux
    calc
      volumeAverage (U : Set (Vec d)) (doubledBlockPairingIntegrand U a S (W - S))
          = volumeAverage (U : Set (Vec d))
              (doubledBlockPairingIntegrand U a S (T + ((W - S) - T))) := by rw [hdec]
      _ = volumeAverage (U : Set (Vec d))
              (doubledBlockPairingIntegrand U a S T
                + doubledBlockPairingIntegrand U a S ((W - S) - T)) := by
            rw [doubledBlockPairingIntegrand_add_right]
      _ = volumeAverage (U : Set (Vec d)) (doubledBlockPairingIntegrand U a S T)
            + volumeAverage (U : Set (Vec d))
                (doubledBlockPairingIntegrand U a S ((W - S) - T)) :=
            volumeAverage_add hint1 hint2
      _ = volumeAverage (U : Set (Vec d)) (doubledBlockPairingIntegrand U a S T) := by
            rw [hcross, add_zero]
  -- Assemble.
  have hWsplit : S + (W - S) = W := by
    refine HCPolySupport.Internal.Ch02.BookCh02.doubledField_ext ?_ ?_
    · funext x
      show S.potential x + (W.potential x - S.potential x) = W.potential x
      abel
    · funext x
      show S.flux x + (W.flux x - S.flux x) = W.flux x
      abel
  have hEW : doubledMuValue U a W
      = doubledMuValue U a S + doubledMuValue U a (W - S)
        + volumeAverage (U : Set (Vec d))
            (doubledBlockPairingIntegrand U a S (W - S)) := by
    conv_lhs => rw [← hWsplit]
    exact doubledMuValue_add a hSpot hSflux hVpot hVflux
  have hEST := doubledMuValue_add a hSpot hSflux hTpot hTflux
  have hTle : doubledMuValue U a T ≤ doubledMuValue U a (W - S) := hT.2 (W - S) hV
  rw [hEST, hEW, hVsplit]
  linarith

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

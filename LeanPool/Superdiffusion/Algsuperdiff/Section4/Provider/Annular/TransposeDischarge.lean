/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.NegationSymmetry
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.SignLowDischarge

/-!
# TransposeDischarge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The transposed ugly estimate, discharged by the `(J3)` symmetry

ABK26, Section 4.1, `p.mathcalE.annular.decomp`: the manuscript runs
`e.ugly.estimate.for.J` a second time for the transposed field and asserts the
same right-hand side.

This module formalizes exactly that argument.  Write `N ω = −ω` for the proved
negation of the whole shell sequence on the genuine lower-tail carrier
(`Cutoff.negateCutoffSample`). Then:

1. `a_L(Nω) = a_L(ω)ᵀ` — the proved `(J3)` carrier identity
   `Cutoff.coefficientCutoff_negateCutoffSample_eq_adjoint`, itself a
   consequence of the proved skewness of the genuine lower-infinite cutoff;
2. the flux-correction constant `(k_L − k_m)_{□_m}` is linear in the shell
   fields, so it changes sign under `N` (`fluxIncrementAverage_negateCutoffSample`),
   and therefore `ã_{L,m}(Nω) = ã_{L,m}(ω)ᵀ` pointwise
   (`fluxCorrectedField_negateCutoffSample`);
3. every shell-norm-built slot is literally `N`-invariant, and the two
   variational slots (`λ_{γ,2}` and `𝓔_{s,2,2}`) are `N`-invariant because the
   skew part drops out of the coarse quadratic form
   (`NegationSymmetry.lean`, `TransposeError.lean`);
4. consequently the transposed `J`-leg at `ω` **is** the field `J`-leg at `Nω`
   (`jLegField_negateCutoffSample`), and the ugly estimate for the transposed
   field at `ω` **is** the proved field-side ugly estimate
   (`exists_uglyJEstimate_annulus_of_eventG1`) evaluated at `Nω`.

The ugly estimate itself is never re-proved: it is *transported*.  And the
transport is **deterministic** — the ruled "same law" is not consumed.  Every
step above is a pointwise identity on the carrier, so the transposed estimate
holds at each individual sample, not merely in law; the proved
`Cutoff.map_negateCutoffSample_cutoffSampleLaw` is not used.  The only
almost-sure input is the atom-versus-representative reconciliation
`annularErrorAtomMax_ae_le_annularErrorLatticeMax`, which the field-side leg
already consumes at the same place.

## The payoff

The transposed ugly estimate is thereby available at **every** sample, with the
transposed response family no longer a free variable: it is the concrete
`fun ω L ↦ annularResponseMax M L m (N ω)`.  A consumer of it is therefore a
transcription of the field-side leg, not a substitution.  Because the
atom-versus-representative reconciliation is only almost sure, the transposed
estimate has to be produced **inside** the `filter_upwards` of the display,
exactly where the field-side estimate already is.

## References

* ABK26, (`ã_{L,m}`), (the transposed ugly estimate).
-/

namespace Algsuperdiff.Section4.Provider.Annular

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.CoarseEllipticity
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Localization
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Part A -- the flux-corrected field transposes under `N` -/

/-- **The cube-averaged flux increment changes sign under `N`.**  It is linear in
the shell fields; equivalently, it is the transpose of itself at `ω`, and it is
antisymmetric. -/
theorem fluxIncrementAverage_negateCutoffSample (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) :
    Support.fluxIncrementAverage M L m Q (Cutoff.negateCutoffSample omega) =
      -Support.fluxIncrementAverage M L m Q omega := by
  funext i j
  have hentry : ∀ (k : ℤ) (x : Vec d),
      Cutoff.coefficientCutoff M.nu k (Cutoff.negateCutoffSample omega) x i j =
        Cutoff.coefficientCutoff M.nu k omega x j i := by
    intro k x
    have hx := congrArg (fun a : RegCoeffField d => a x)
      (Cutoff.coefficientCutoff_negateCutoffSample_eq_adjoint (d := d) M.nu k omega)
    change Cutoff.coefficientCutoff M.nu k (Cutoff.negateCutoffSample omega) x =
      adjointReg (Cutoff.coefficientCutoff M.nu k omega) x at hx
    rw [hx, adjointReg_apply]
    rfl
  have hfun : (fun x : Vec d =>
        Cutoff.coefficientCutoff M.nu L (Cutoff.negateCutoffSample omega) x i j -
          Cutoff.coefficientCutoff M.nu m (Cutoff.negateCutoffSample omega) x i j)
      = fun x : Vec d =>
        Cutoff.coefficientCutoff M.nu L omega x j i -
          Cutoff.coefficientCutoff M.nu m omega x j i := by
    funext x
    rw [hentry L x, hentry m x]
  have hstep : Support.fluxIncrementAverage M L m Q
      (Cutoff.negateCutoffSample omega) i j =
      Support.fluxIncrementAverage M L m Q omega j i := by
    rw [Support.fluxIncrementAverage_apply, Support.fluxIncrementAverage_apply, hfun]
  rw [hstep, Support.fluxIncrementAverage_skew]
  rfl

/-- **The flux-corrected coefficient transposes under `N`**, pointwise:
`ã_{L,m}(Nω)(x) = ã_{L,m}(ω)(x)ᵀ`.  The `a_L` leg transposes by the `(J3)`
carrier identity and the subtracted antisymmetric constant changes sign, which
is exactly what the transpose of the difference demands. -/
theorem fluxCorrectedField_negateCutoffSample (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) (x : Vec d) :
    Support.fluxCorrectedField M L m Q (Cutoff.negateCutoffSample omega) x =
      matTranspose (Support.fluxCorrectedField M L m Q omega x) := by
  have hx := congrArg (fun a : RegCoeffField d => a x)
    (Cutoff.coefficientCutoff_negateCutoffSample_eq_adjoint (d := d) M.nu L omega)
  have hx' : Cutoff.coefficientCutoff M.nu L (Cutoff.negateCutoffSample omega) x =
      matTranspose (Cutoff.coefficientCutoff M.nu L omega x) := by
    change Cutoff.coefficientCutoff M.nu L (Cutoff.negateCutoffSample omega) x =
      adjointReg (Cutoff.coefficientCutoff M.nu L omega) x at hx
    rw [hx, adjointReg_apply]
    rfl
  have hC := matTranspose_fluxIncrementAverage M L m Q omega
  have hT : ∀ A B : Mat d, matTranspose (A - B) = matTranspose A - matTranspose B := by
    intro A B
    funext i j
    simp [matTranspose, Matrix.sub_apply]
  rw [Support.fluxCorrectedField_apply, Support.fluxCorrectedField_apply,
    fluxIncrementAverage_negateCutoffSample, hx', hT, hC]

/-- The flux-corrected triadic family at `Nω` is the adjoint family at `ω`. -/
theorem fluxCorrectedCoeffFamily_negateCutoffSample_aeEq (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) :
    Ch02.TriadicCoeffFamily.AEEq
      (Support.fluxCorrectedCoeffFamily M L m Q (Cutoff.negateCutoffSample omega))
      (adjointFamily (Support.fluxCorrectedCoeffFamily M L m Q omega)) := by
  intro R
  refine Filter.Eventually.of_forall fun x => ?_
  change Support.fluxCorrectedRegField M L m Q (Cutoff.negateCutoffSample omega) x =
    matTranspose (Support.fluxCorrectedRegField M L m Q omega x)
  rw [Support.fluxCorrectedRegField_apply, Support.fluxCorrectedRegField_apply]
  exact fluxCorrectedField_negateCutoffSample M L m Q omega x

/-! ## Part B -- the two `J`-legs are exchanged by `N` -/

/-- The scalar response maximum depends on the coefficient object only through
its almost-everywhere class. -/
theorem scalarResponseMax_congr_aeeq {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) (sigma : Observable.PositiveScalar) :
    scalarResponseMax a sigma = scalarResponseMax b sigma := by
  unfold scalarResponseMax scalarResponseSet
  refine congrArg sSup (Set.ext fun x => ?_)
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, responseJ_eq_ofAEEq h _ _⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, responseJ_eq_ofAEEq h.symm _ _⟩

theorem jLegField_negateCutoffSample (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) (n : ℤ) :
    jLegField M L m (Cutoff.negateCutoffSample omega) n =
      jLegTranspose M L m omega n := by
  unfold jLegField jLegTranspose
  refine congrArg _ (funext fun v => ?_)
  exact scalarResponseMax_congr_aeeq
    (fluxCorrectedCoeffFamily_negateCutoffSample_aeEq M L m (originCube d m) omega
      (latticeCube n v))
    (Annealed.sigmaBar M m)

/-- Function form of `jLegField_negateCutoffSample`, as the `hpret` slot reads
it. -/
theorem jLegField_negateCutoffSample_funext (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) :
    jLegField M L m (Cutoff.negateCutoffSample omega) = jLegTranspose M L m omega :=
  funext (jLegField_negateCutoffSample M L m omega)

/-! ## Part B' -- the transposed annulus response family -/

/-- `ã_{L,m}` at `Nω` is `ã_{L,m}ᵀ` at `ω`, as a field identity. -/
theorem subConstCutoffField_negateCutoffSample (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) (x : Vec d) :
    subConstCutoffField M L
        (Support.fluxIncrementAverage M L m Q (Cutoff.negateCutoffSample omega))
        (Cutoff.negateCutoffSample omega) x =
      matTranspose (subConstCutoffField M L
        (Support.fluxIncrementAverage M L m Q omega) omega x) := by
  have hx := congrArg (fun a : RegCoeffField d => a x)
    (Cutoff.coefficientCutoff_negateCutoffSample_eq_adjoint (d := d) M.nu L omega)
  have hx' : Cutoff.coefficientCutoff M.nu L (Cutoff.negateCutoffSample omega) x =
      matTranspose (Cutoff.coefficientCutoff M.nu L omega x) := by
    change Cutoff.coefficientCutoff M.nu L (Cutoff.negateCutoffSample omega) x =
      adjointReg (Cutoff.coefficientCutoff M.nu L omega) x at hx
    rw [hx, adjointReg_apply]
    rfl
  have hC := matTranspose_fluxIncrementAverage M L m Q omega
  have hT : ∀ A B : Mat d, matTranspose (A - B) = matTranspose A - matTranspose B := by
    intro A B
    funext i j
    simp [matTranspose, Matrix.sub_apply]
  rw [subConstCutoffField_apply, subConstCutoffField_apply,
    fluxIncrementAverage_negateCutoffSample, hx', hT, hC]

end

end Algsuperdiff.Section4.Provider.Annular

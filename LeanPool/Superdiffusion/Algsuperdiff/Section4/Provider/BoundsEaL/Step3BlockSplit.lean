/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.FamilyBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.Step3HSlot
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.TransposeDischarge

/-!
# Step3BlockSplit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Step 3 at the *block* response maximum: the split applied, both legs supplied

Nothing here imports that file, and nothing here claims the anchor.

## What this module does

`Step3HSlot.exists_responseJ_step3_recentered` supplies the **field** leg of
the primal/adjoint split `e.bfJ.general`, proved here as
`Annular.normalizedBlockResponseMax_isotropicComparator_le` at constant `1`: an
`e`-free bound on `J(3^j v + □_j, σ_m^{-1/2} e, σ_m^{1/2} e; ã_{L,m})`.  The
split also needs the **transpose** leg, at `ã_{L,m}ᵗ`.

The transpose leg is supplied here by ONE per-cube specialization of the proved
lattice-level negation calculus of `Annular/TransposeDischarge.lean`: at the
negated sample `Nω = −ω` the coefficient field transposes,

```
ã_{L,m}(Nω)(x) = ã_{L,m}(ω)(x)ᵗ            (`subConstCutoffField_negateCutoffSample`)
```

This is the author's `(J3)` symmetry route, exactly as §4.1 discharges its
`hpret`/`huglyt` slots at the lattice level; nothing new is assumed, and NO
probabilistic input enters: the statements below are pointwise in `ω`.  (The
law-level invariance `Cutoff.map_negateCutoffSample_cutoffSampleLaw` is what a
later expectation step uses to make the `Nω` leg cost nothing; it is not used,
and not needed, here.)

Combining the two legs with the proved split, and rewriting the left-hand side
through the family bridge of `FamilyBridge.lean`, bounds the Step-1 endpoint's
per-cube object `Ch02.normalizedBlockResponseMax R (a_L − (k_L−k_m)_{□_m}) σ_m
Id` by the sum of Step 3's display at `ω` and at `Nω`.

`Annular.scalarResponseMax_le_normalizedBlockResponseMax` runs the W WAY for
this purpose (it bounds the scalar maximum by the block maximum); the split
above is the only proved route from scalar `J`-displays to the block maximum.

## Deviations, all inherited

Every deviation of `Step3HSlot.lean` is inherited verbatim -- in particular the
ruled gapped gauge `s = 2γ` (exponents `2s/(1−4γ)` and `4γ/(1−4γ)`, `λ`-slots
at `unitCubeLambda (2γ)`; A9 direction warning: the display can never be read
back at gauge `γ`) and the unit-cube gauges of the Section 2.4 anchor.  The `s
≤ 1/4` and `γ ≤ 1/8` binders are free at §4.5's own ranges.  Nothing new is
introduced here: `step3Display` is a *name* for the right-hand side of
`exists_responseJ_step3_recentered`, at the cube `R = ⟨R.scale, R.index⟩` and
the recentering index `m`.

## Main results

* `responseJ_subConstFlux_transpose_eq_negate` — the per-cube negation identity:
  the transposed response at `ω` is the field response at `Nω`.
* `normalizedBlockResponseMax_subConstFlux_le_of_bounds` — the proved split
  with its transpose leg pre-rewritten: two hypotheses (at `ω` and at `Nω`)
  bound the block maximum by `Jf + Jt`.
* `exists_normalizedBlockResponseMax_step3_split` — the two legs discharged by
  Step 3's display, with the left-hand side at the *endpoint's* carrier family.

## References

* ABK26, `l.bounds.mathcal.E.aL`, (Step 3); `e.bfJ.general`; (the transposed
  annulus maximum).
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section4.Provider.Annular

noncomputable section

variable {d : ℕ}

/-! ## The per-cube negation identity -/

/-- **`ã_{L,m}` at `Nω` is `ã_{L,m}ᵗ` at `ω`, at one cube.**  The a.e. field
identity behind the transpose leg; the proved field identity
`Annular.subConstCutoffField_negateCutoffSample` read through the definitional
`coeffOn`-characterization of the hand-built family. -/
theorem subConstFluxFamily_negate_coeffOn_aeEq_transpose (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) (R : TriadicCube d) :
    Ch02.CoeffOn.AEEq
      ((subConstFluxFamily M L m (Cutoff.negateCutoffSample omega)).coeffOn R)
      (((subConstFluxFamily M L m omega).coeffOn R).transpose) := by
  refine Filter.Eventually.of_forall fun x => ?_
  rw [Ch02.CoeffOn.transpose_apply]
  exact subConstCutoffField_negateCutoffSample M L m (originCube d m) omega x

/-- **The per-cube transpose leg.**  The transposed response functional at `ω` is
the untransposed response functional at the negated sample `Nω`, at every cube and
at every pair of loads. -/
theorem responseJ_subConstFlux_transpose_eq_negate (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) (R : TriadicCube d) (u w : Vec d) :
    Ch02.responseJ (cubeDomain R) ((subConstFluxFamily M L m omega).coeffOn R).transpose
        u w =
      Ch02.responseJ (cubeDomain R)
        ((subConstFluxFamily M L m (Cutoff.negateCutoffSample omega)).coeffOn R) u w :=
  (Ch02.responseJ_eq_ofAEEq
    (subConstFluxFamily_negate_coeffOn_aeEq_transpose M L m omega R) u w).symm

/-! ## The split, with the transpose leg pre-rewritten -/

/-- **The proved primal/adjoint split, at the development carrier, with the
transpose leg read at the negated sample.**

`Annular.normalizedBlockResponseMax_isotropicComparator_le` (`e.bfJ.general`,
constant `1`) asks for a bound on the field response and a bound on the
*transposed* field response.  By the per-cube negation identity the second is a
bound on the field response at `Nω`; so both hypotheses below are displays,
which is exactly what `Step3HSlot.lean` produces. -/
theorem normalizedBlockResponseMax_subConstFlux_le_of_bounds [NeZero d]
    (M : ABKModel d) (L m : ℤ) (omega : Cutoff.CutoffSample d) (R : TriadicCube d)
    {Jf Jt : ℝ}
    (hfld : ∀ e : Vec d, vecNorm e = 1 →
      Ch02.responseJ (cubeDomain R) ((subConstFluxFamily M L m omega).coeffOn R)
          (Observable.inverseSqrtLoad (Annealed.sigmaBar M m) e)
          (Observable.sqrtLoad (Annealed.sigmaBar M m) e) ≤ Jf)
    (hneg : ∀ e : Vec d, vecNorm e = 1 →
      Ch02.responseJ (cubeDomain R)
          ((subConstFluxFamily M L m (Cutoff.negateCutoffSample omega)).coeffOn R)
          (Observable.inverseSqrtLoad (Annealed.sigmaBar M m) e)
          (Observable.sqrtLoad (Annealed.sigmaBar M m) e) ≤ Jt) :
    Ch02.normalizedBlockResponseMax R (subConstFluxFamily M L m omega)
        (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) ≤ Jf + Jt := by
  refine normalizedBlockResponseMax_isotropicComparator_le _ R _ hfld ?_
  intro e he
  rw [responseJ_subConstFlux_transpose_eq_negate M L m omega R]
  exact hneg e he

/-! ## Step 3's display, named -/

/-- The recentered skew shell perturbation of Step 3: `h = k_L − k_{j−2} −
(k_L − k_m)_{□_m}` at the cube `R`, with the recentering constant folded into the
unit-cube perturbation.  A spelling abbreviation for the object appearing in
`Step3HSlot.exists_responseJ_step3_recentered`. -/
def step3Shell (M : ABKModel d) (L m : ℤ) (R : TriadicCube d) (hle : R.scale - 2 ≤ L)
    (omega : Cutoff.CutoffSample d) : UnitCubeSkewW2Infinity d :=
  centeredShellUnitCube M R hle omega
    (Support.fluxIncrementAverage M L m (originCube d m) omega)
    (matTranspose_fluxIncrementAverage M L m (originCube d m) omega)

/-- **Step 3's display, named.**  The right-hand side of
`Step3HSlot.exists_responseJ_step3_recentered` at the cube `R`: the three
printed summands of `e.apply.sensitivity.J.aL`, in the anchor's unit-cube
gauges and at the ruled gapped gauge `s = 2γ`.  It does not mention `e`. -/
def step3Display (C : ℝ) (M : ABKModel d) (L m : ℤ) (R : TriadicCube d)
    (hle : R.scale - 2 ≤ L) (omega : Cutoff.CutoffSample d) (s : ℝ) : ℝ :=
  C * ((Annealed.sigmaBar M m : ℝ)⁻¹ * (Annealed.sigmaBar M (R.scale - 2) : ℝ)) *
      Real.rpow (1 + (step3Shell M L m R hle omega).gradientW1Infinity *
          (unitCubeLambda (2 * M.gamma) (.finite 2)
            (unitRescaledCutoffCoeff M R (R.scale - 2) omega))⁻¹)
        (2 * s / (1 - 4 * M.gamma)) *
      unitCubeHomogenizationError s (.finite 2) (.finite 2)
        (unitRescaledCutoffCoeff M R (R.scale - 2) omega)
        (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M (R.scale - 2))) ^ 2 +
    C * ((Annealed.sigmaBar M m : ℝ)⁻¹ * (Annealed.sigmaBar M (R.scale - 2) : ℝ) ^ 2) *
      (unitCubeLambda (2 * M.gamma) (.finite 2)
        (unitRescaledCutoffCoeff M R (R.scale - 2) omega))⁻¹ *
      Real.rpow (1 + (step3Shell M L m R hle omega).gradientW1Infinity *
          (unitCubeLambda (2 * M.gamma) (.finite 2)
            (unitRescaledCutoffCoeff M R (R.scale - 2) omega))⁻¹)
        (4 * M.gamma / (1 - 4 * M.gamma)) *
      ((Annealed.sigmaBar M (R.scale - 2) : ℝ)⁻¹ ^ 2 *
          (step3Shell M L m R hle omega).valueL2 ^ 2 +
        ((Annealed.sigmaBar M m : ℝ) * (Annealed.sigmaBar M (R.scale - 2) : ℝ)⁻¹ - 1) ^ 2) +
    C * (((Annealed.sigmaBar M m : ℝ)⁻¹ +
        (unitCubeLambda (2 * M.gamma) (.finite 2)
          (unitRescaledCutoffCoeff M R (R.scale - 2) omega))⁻¹) *
      (step3Shell M L m R hle omega).gradientW1Infinity) ^ 2

/-! ## The two legs discharged -/

/-- The constant is the Section 2.4 anchor's own, taken from
`Step3HSlot.exists_responseJ_step3_recentered`; the field leg is that theorem
at `ω`, the transpose leg is that theorem at `Nω` composed with the per-cube
negation identity, and the left-hand side is moved to the endpoint's carrier by
the family bridge `FamilyBridge.normalizedBlockResponseMax_fluxCorrected_eq`.

Pointwise in `ω`: no event, no probability, no stationarity, no `z`-collapse. -/
theorem exists_normalizedBlockResponseMax_step3_split (d : ℕ) (dimension : 2 ≤ d) :
    letI : NeZero d := ⟨by omega⟩
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (L m : ℤ) (R : TriadicCube d) (hle : R.scale - 2 ≤ L)
        (omega : Cutoff.CutoffSample d) (s : ℝ),
        0 < s → s ≤ 1 / 4 → M.gamma ≤ 1 / 8 →
        Ch02.normalizedBlockResponseMax R
            (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
            (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) ≤
          step3Display C M L m R hle omega s +
            step3Display C M L m R hle (Cutoff.negateCutoffSample omega) s := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC, hstep3⟩ := exists_responseJ_step3_recentered d dimension
  refine ⟨C, hC, ?_⟩
  intro M L m R hle omega s hs0 hs1 hgam
  rw [normalizedBlockResponseMax_fluxCorrected_eq M L m omega R
    (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m))]
  refine normalizedBlockResponseMax_subConstFlux_le_of_bounds M L m omega R
    (fun e he => ?_) (fun e he => ?_)
  · exact hstep3 M m R.scale L hle R.index omega s e hs0 hs1 hgam he
  · exact hstep3 M m R.scale L hle R.index (Cutoff.negateCutoffSample omega) s e
      hs0 hs1 hgam he

end

end Algsuperdiff.Section4.Provider.BoundsEaL

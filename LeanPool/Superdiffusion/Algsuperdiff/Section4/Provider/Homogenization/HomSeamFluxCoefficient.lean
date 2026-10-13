/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.AntisymmetricShift
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamRepin

/-!
# HomSeamFluxCoefficient

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The COEFFICIENT half of the seam: the slots re-pinned at `ã_{L,m}`

## What this file settles

`HomSeamRepin` names, as an input, the domination

```text
  𝓔_{t,∞,2}(□_m, n; a_L, σ_m)  ≤  sup_{L' ≥ m} 𝓔_{t,∞,2}(□_m, n; ã_{L',m}, σ_m)
```

— the LEFT side at the UNCUT field `a_L`.  That statement is NOT the standing
`bounds_mathcal_E_aL` provider obligation, and it is not a consequence of it.
The obligation is an a.e. IDENTIFICATION *at the flux-corrected family*
(`Support/FluxCorrectedTwoScale.lean`, module docstring): both of its sides
carry `ã`.  The `a_L`-sided statement is a genuinely different — and much
stronger — inequality, for the following reason.

`𝓔` is built from `Ch02.doubledResponseJ`, whose block matrix
`blockMatrixOfCoeff A` reads the SKEW part of `A` explicitly
(`upperLeft = s + kᵀ s⁻¹ k`, `upperRight = -(kᵀ s⁻¹)`, …, with `k = skewPart A`).
Adding a constant skew matrix `K` to the coefficient therefore does not fix
`J`; in the classical variational form it shifts the second argument,

```text
  J(U, p, q; a + K)  =  J(U, p, q - Kᵀp; a)  =  J(U, p, q + Kp; a),
```

so at the normalized arguments `p = σ_m^{-1/2} e`, `q = σ_m^{1/2} e` the two
families are separated by exactly `σ_m^{-1/2} (k_L - k_m)_{□_m} e`.  That is
precisely the object the flux correction exists to REMOVE, and it is not bounded
uniformly in `L` (it is a stream-matrix increment across `L - m` scales).  No
constant — and no supremum over `L' ≥ m` on the right — restores the direction:
the right side vanishes on a configuration whose coarse-grained `ã` equals `σ_m
Id`, while the left side is then of size `|(k_L - k_m)_{□_m}|`.

## The print never asks for it

The manuscript's own route is the opposite one, and it is stated twice:

* (§4.5, the display feeding `EthmB(m)`): *"Note that the first
  equation in the Dirichlet-pair display is unchanged if we replace `a_L` by
  `ã_{L,m}:= a_L - (k_L - k_m)_{□_m}`"*, after which Step 3
  applies the coarse-graining proposition with `a = ã_{L,m}` — never with
  `a_L`;
* (§4.3): the same move, at `ã_{L,n+2}`.

So the coarse-graining bundle is to be INSTANTIATED at `ã_{L,m}`, and then the
seam's coefficient half is the already-named a.e. identification, with no new
estimate anywhere.  Sections 1--3 below are the machine content that makes the
re-instantiation free of charge:

* the constant increment is skew (`matTranspose_fluxIncrementAverage`);
* the §4.5 Dirichlet datum transports verbatim
  (`isDirichletSolutionOn_fluxCorrected_of_cutoff`'s own sentence);
* the bundle's energy slot `printedLocalEnergy` is LITERALLY EQUAL at the two
  fields (`printedLocalEnergy_fluxCorrected`), because it reads only `symmPart`.

Sections 4--6 carry the re-pinned slots `recutPinnedE1Flux`,
`recutPinnedE2Flux` and the two domination theorems, at the re-pinned base `s'
= s/8`, from the honest input `FluxCorrectedParentIdentification`.

## Scope

Proved outright: the skewness, the two transports, and the two domination
slots at the flux-corrected coefficient.

Still an input, and named as `FluxCorrectedParentIdentification`: the a.e.
identification of `CoarseGraining`'s literal `q = 2` truncated parent error of
`ã_{L,m}` with the measurable two-argument observable, at a fixed `ω` and in
the `≤` direction.  This IS the standing `bounds_mathcal_E_aL` provider
obligation (`Support/FluxCorrectedTwoScale.lean`), restricted to one sample;
nothing here asserts it.  Its ingredients are all but not composed:
`FluxCorrectedRepresentative.ae_forall_normalizedBlockResponseMax_fluxCorrected_eq_representative`
supplies the probability-one event, and what remains is the definitional
matching of `Ch02.parentTruncatedNormalizedBlockResponseScalarEMaxAtScale` (an
`ℝ≥0∞` `sSup` over descendants of the PARENT restriction) with
`Ch02.normalizedBlockResponseMax` (the real `sSup` at the FAMILY's own
`coeffOn`), plus the `ENNReal.ofReal`/`tsum`/`sqrt` commutations.
-/

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The constant flux increment is skew, in matrix form -/

/-- `(k_L - k_m)_Q(ω)` is antisymmetric as a matrix identity, which is the form
the shift API of `AntisymmetricShift` consumes. -/
theorem matTranspose_fluxIncrementAverage (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) :
    matTranspose (fluxIncrementAverage M L m Q omega) =
      -fluxIncrementAverage M L m Q omega := by
  ext i j
  have h := fluxIncrementAverage_skew M L m Q omega i j
  simpa only [Matrix.transpose_apply, Matrix.neg_apply] using! h

/-! ## 2. The Dirichlet datum transports -/

/-- **THE PRINT'S OWN MOVE** (and at §4.3): the
first equation of the Dirichlet pair is unchanged when `a_L` is replaced by
`ã_{L,m}`, because the two differ by a constant antisymmetric matrix.  The
boundary clause never sees the coefficient. -/
theorem isDirichletSolutionOn_fluxCorrected_of_cutoff (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d)
    {u h : H1Function (openCubeSet (originCube d m))} {g : Vec d → Vec d}
    (hsol : Support.IsDirichletSolutionOn
      (Cutoff.coefficientCutoffCoeffOn M L omega (originCube d m)).toCoeffField
      (originCube d m) u h g) :
    Support.IsDirichletSolutionOn
      (fluxCorrectedCoeffOn M L m (originCube d m) omega).toCoeffField
      (originCube d m) u h g :=
  isDirichletSolutionOn_sub_const_of_skew
    (matTranspose_fluxIncrementAverage M L m (originCube d m) omega) hsol

/-! ## 3. The energy slot is LITERALLY the same at the two fields -/

/-- The symmetric part is blind to the flux correction. -/
private theorem symmPart_fluxCorrectedCoeffOn (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) (x : Vec d) :
    symmPart ((fluxCorrectedCoeffOn M L m Q omega).toCoeffField x) =
      symmPart ((Cutoff.coefficientCutoffCoeffOn M L omega Q).toCoeffField x) :=
  symmPart_sub_const_of_skew (matTranspose_fluxIncrementAverage M L m Q omega) _

/-- **THE ENERGY SLOT IS FREE.**  `printedLocalEnergy` reads its coefficient
only through `symmPart`, so the bundle's `Gen` slot at `ã_{L,m}` is the SAME
function of cubes as at `a_L` — not merely dominated by it. -/
theorem printedLocalEnergy_fluxCorrected (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) (u : H1Function (openCubeSet (originCube d m)))
    (R : TriadicCube d) :
    printedLocalEnergy (fluxCorrectedCoeffOn M L m (originCube d m) omega) u R =
      printedLocalEnergy
        (Cutoff.coefficientCutoffCoeffOn M L omega (originCube d m)) u R := by
  unfold printedLocalEnergy
  by_cases hsub : openCubeSet R ⊆ openCubeSet (originCube d m)
  · rw [dite_eq_left hsub, dite_eq_left hsub]
    congr 1
    unfold localSymmetricEnergyENorm
    congr 1
    refine lintegral_congr fun x => ?_
    rw [Ch02.CoeffOn.restrictToSubcube_toCoeffField,
      Ch02.CoeffOn.restrictToSubcube_toCoeffField, symmPart_fluxCorrectedCoeffOn]
  · rw [dite_eq_right hsub, dite_eq_right hsub]

/-! ## 4. The print-accurate `𝓔` slots -/

/-- The `𝓔₁` slot at the PRINTED coefficient `ã_{L,m}` and the low order `s/8`.
The sibling of the pinned `𝓔₁` slot at the uncut `a_L`, with the print's own
coefficient in its place. -/
def recutPinnedE1Flux (M : ABKModel d) (L : ℤ) (omega : Cutoff.CutoffSample d)
    (m : ℤ) (jn : ℕ) {sigmaBarM : ℝ} (hsig : 0 < sigmaBarM) (s : FractionalOrder) : ℝ :=
  (Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar (originCube d m)
      ((originCube d m).scale - (jn : ℤ)) (recutParentScale m jn)
      (fluxCorrectedCoeffOn M L m (originCube d m) omega) sigmaBarM hsig
      (recutOrderLow s)).toReal

/-- The `𝓔₂` slot at the PRINTED coefficient `ã_{L,m}` and the half order
`s/16`. -/
def recutPinnedE2Flux (M : ABKModel d) (L : ℤ) (omega : Cutoff.CutoffSample d)
    (m : ℤ) (jn : ℕ) {sigmaBarM : ℝ} (hsig : 0 < sigmaBarM) (s : FractionalOrder) : ℝ :=
  (Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar (originCube d m)
      ((originCube d m).scale - (jn : ℤ)) (recutParentScale m jn)
      (fluxCorrectedCoeffOn M L m (originCube d m) omega) sigmaBarM hsig
      (fractionalOrderHalf (recutOrderLow s))).toReal

theorem recutPinnedE1Flux_nonneg [NeZero d] (M : ABKModel d) (L : ℤ)
    (omega : Cutoff.CutoffSample d) (m : ℤ) (jn : ℕ) {sigmaBarM : ℝ}
    (hsig : 0 < sigmaBarM) (s : FractionalOrder) :
    0 ≤ recutPinnedE1Flux M L omega m jn hsig s := ENNReal.toReal_nonneg

theorem recutPinnedE2Flux_nonneg [NeZero d] (M : ABKModel d) (L : ℤ)
    (omega : Cutoff.CutoffSample d) (m : ℤ) (jn : ℕ) {sigmaBarM : ℝ}
    (hsig : 0 < sigmaBarM) (s : FractionalOrder) :
    0 ≤ recutPinnedE2Flux M L omega m jn hsig s := ENNReal.toReal_nonneg

/-! ## 5. The one remaining input, in its honest shape -/

/-- **THE `ã` IDENTIFICATION** — the coefficient half of the seam, at the
print's own coefficient.

At a fixed sample and every admissible `L`, `CoarseGraining`'s literal `q = 2`
truncated parent error of the FLUX-CORRECTED field `ã_{L,m}` on `□_m` is below
the measurable two-argument flux-corrected observable at the same order.  Both
sides carry `ã_{L,m}`; the content is the a.e. identification of the literal
`Ch02` object with its measurable representative, at one sample.

This is the standing `bounds_mathcal_E_aL` provider obligation; nothing in this
file asserts it.

SIGMA PIN.  The
comparator is the printed `σ_m` itself, not a free scalar: the right-hand
observable is hard-pinned at `Annealed.sigmaBar M m` inside
`fluxCorrectedTwoScaleErrorFunctional`, so a freely quantified `σ` made the
statement unprovable off the pin.  The §4.5 spine instantiates the whole chain
only at `Annealed.sigmaBar M m` (`HomSpineInstallPins`),
so the pin costs nothing downstream.  The `𝓔₁`/`𝓔₂` slot definitions above stay
general, because `SpineDatumRecutCoreFlux` consumes them at a free `σ`. -/
def FluxCorrectedParentIdentification (M : ABKModel d) (m : ℤ) (jn : ℕ)
    (omega : Cutoff.CutoffSample d) : Prop :=
  ∀ L : ℤ, m ≤ L → ∀ t : FractionalOrder,
    Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar (originCube d m)
        ((originCube d m).scale - (jn : ℤ)) (recutParentScale m jn)
        (fluxCorrectedCoeffOn M L m (originCube d m) omega)
        ((Annealed.sigmaBar M m : ℝ)) (Annealed.sigmaBar M m).2 t ≤
      fluxCorrectedTwoScaleErrorObservableSup M m (homN M m) ⟨t.1, t.2.1⟩ omega

/-! ## 6. The two domination slots, at the re-pinned base and the print's field -/

/-- **THE FIRST DOMINATION SLOT, AT THE PRINT'S COEFFICIENT.**

The bundle's `𝓔₁` slot — the `q = 1` parent error at the display order `s/8`,
at the flux-corrected field — is below the FIRST `𝓔` factor of `EthmB(m)`
re-pinned at the base `s' = s/8`, i.e. the factor of order `s/16`.  Constant
one: the `q`-index step is Cauchy--Schwarz at a probability weight, and it is
coefficient-agnostic. -/
theorem seamDom1Flux_of_identification [NeZero d] (M : ABKModel d) (m : ℤ) (jn : ℕ)
    (omega : Cutoff.CutoffSample d)
    (hs : 0 < homS M) (hlog : 4 ≤ |Real.log M.gamma|)
    (hid : FluxCorrectedParentIdentification M m jn omega) (L : ℤ) (hL : m ≤ L) :
    ENNReal.ofReal (recutPinnedE1Flux M L omega m jn (Annealed.sigmaBar M m).2
        (recutOrderBase M hlog)) ≤
      fluxCorrectedTwoScaleErrorObservableSup M m (homN M m)
        (homHalf (homSeamBase M hs)) omega := by
  set u : FractionalOrder :=
    fractionalOrderHalf (recutOrderLow (recutOrderBase M hlog)) with hu
  have hcut :
      ENNReal.ofReal (recutPinnedE1Flux M L omega m jn (Annealed.sigmaBar M m).2
        (recutOrderBase M hlog)) ≤
      Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar (originCube d m)
        ((originCube d m).scale - (jn : ℤ)) (recutParentScale m jn)
        (fluxCorrectedCoeffOn M L m (originCube d m) omega)
        ((Annealed.sigmaBar M m : ℝ)) (Annealed.sigmaBar M m).2
        (recutOrderLow (recutOrderBase M hlog)) := ENNReal.ofReal_toReal_le
  have hq := parentTruncatedOne_le_parentTruncatedTwo_half (originCube d m)
    ((originCube d m).scale - (jn : ℤ)) (recutParentScale m jn)
    (fluxCorrectedCoeffOn M L m (originCube d m) omega)
    ((Annealed.sigmaBar M m : ℝ)) (Annealed.sigmaBar M m).2
    (recutOrderLow (recutOrderBase M hlog)) u rfl
  have hbr := hid L hL u
  have horder : ((⟨u.1, u.2.1⟩ : {s : ℝ // 0 < s}) : ℝ) =
      ((homHalf (homSeamBase M hs) : {s : ℝ // 0 < s}) : ℝ) := by
    simp only [hu, fractionalOrderHalf_value, recutOrderLow_val, recutOrderBase_val,
      homHalf_val, homSeamBase_val]
  rw [fluxCorrectedTwoScaleErrorObservableSup_congr_order M m (homN M m) horder] at hbr
  exact le_trans hcut (le_trans hq hbr)

/-- **THE SECOND DOMINATION SLOT, AT THE PRINT'S COEFFICIENT.**

The bundle's `𝓔₂` slot — the `q = 2` parent error at the half display order
`s/16`, at the flux-corrected field — is below the `γ⁵` factor of the re-pinned
`EthmB(m)`, of order `s/32`, times `√2`.  The constant is exactly the ratio of
the two geometric normalizations. -/
theorem seamDom2Flux_of_identification [NeZero d] (M : ABKModel d) (m : ℤ) (jn : ℕ)
    (omega : Cutoff.CutoffSample d)
    (hs : 0 < homS M) (hlog : 4 ≤ |Real.log M.gamma|)
    (hid : FluxCorrectedParentIdentification M m jn omega) (L : ℤ) (hL : m ≤ L) :
    ENNReal.ofReal (recutPinnedE2Flux M L omega m jn (Annealed.sigmaBar M m).2
        (recutOrderBase M hlog)) ≤
      ENNReal.ofReal (Real.sqrt 2) *
        fluxCorrectedTwoScaleErrorObservableSup M m (homN M m)
          (homQuarterOf (homSeamBase M hs)) omega := by
  set u : FractionalOrder :=
    fractionalOrderHalf (recutOrderLow (recutOrderBase M hlog)) with hu
  set v : FractionalOrder := fractionalOrderHalf u with hv
  have hcut :
      ENNReal.ofReal (recutPinnedE2Flux M L omega m jn (Annealed.sigmaBar M m).2
        (recutOrderBase M hlog)) ≤
      Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar (originCube d m)
        ((originCube d m).scale - (jn : ℤ)) (recutParentScale m jn)
        (fluxCorrectedCoeffOn M L m (originCube d m) omega)
        ((Annealed.sigmaBar M m : ℝ)) (Annealed.sigmaBar M m).2 u :=
    ENNReal.ofReal_toReal_le
  have hord := parentTruncatedTwo_le_sqrtTwo_half (originCube d m)
    ((originCube d m).scale - (jn : ℤ)) (recutParentScale m jn)
    (fluxCorrectedCoeffOn M L m (originCube d m) omega)
    ((Annealed.sigmaBar M m : ℝ)) (Annealed.sigmaBar M m).2 u v rfl
  have hbr := hid L hL v
  have horder : ((⟨v.1, v.2.1⟩ : {s : ℝ // 0 < s}) : ℝ) =
      ((homQuarterOf (homSeamBase M hs) : {s : ℝ // 0 < s}) : ℝ) := by
    simp only [hv, hu, fractionalOrderHalf_value, recutOrderLow_val, recutOrderBase_val,
      homQuarterOf_val, homSeamBase_val]
    ring
  rw [fluxCorrectedTwoScaleErrorObservableSup_congr_order M m (homN M m) horder] at hbr
  exact le_trans hcut (le_trans hord (mul_le_mul' le_rfl hbr))

end

end Algsuperdiff.Section4.Provider.Homogenization

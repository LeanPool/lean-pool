/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Annealed.RunningDiffusivity.Definition
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffHomogenizationErrorRaw

/-!
# ErrorAtoms

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Section 4 homogenization-error atoms

The Section 4 good events and the annular decomposition
(`d.good.event.for.lambda`; `p.mathcalE.annular.decomp`) read the
homogenization-error functional at two exponent pairs and at two coefficient
shapes that Section 3 does not already carry:

* the `(2,2)` atoms `𝓔_{s,2,2}(z+□_n; a_{n−2}, σ_{n−2} Id)` of `𝒢₂`, and
* the `(∞,2)` functionals of the flux-corrected coefficient
  `a_L − (k_L − k_m)_{□_m}` appearing on the left of
  `e.mathcalE.annular.decomp`.

Both are built from exactly the proved carriers: the frozen general-exponent
functional `Algsuperdiff.Frozen.Section24.unitCubeHomogenizationError` (which
is already quantified over `p q : MultiscaleExponent`), the triadic change of
variables `Algsuperdiff.Section3.Observable.unitRescaledCoeffOn`, the
coefficient cutoff `Cutoff.coefficientCutoff M.nu L`, and the running
diffusivity `Annealed.sigmaBar M k` (already a `PositiveScalar`).

## Translation convention

Every declaration here is stated at the **origin** cube `□_n`, matching the
Section 3 raw-observable discipline.  The manuscript's translated atom at `z +
□_n` is *rendered* by translating the sample, never the cube.  Consumers
therefore write

```
  annularErrorAtom M n s ∘ Cutoff.translateCutoffSample z
```

for the atom at `z + □_n`.  The same convention applies to
`fluxCorrectedError`.  No identity between the translated rendering and a
moved cube is asserted here; that is provider content.

## Main definitions

* `homogenizationErrorAtScale22` — the `(2,2)` sibling of
  `Observable.homogenizationErrorAtScale`.
* `cutoffHomogenizationErrorRaw22` — the `(2,2)` sibling of
  `Observable.cutoffHomogenizationErrorRaw`.
* `annularErrorAtom` — the `𝒢₂` atom `𝓔_{s,2,2}(□_n; a_{n−2}, σ_{n−2} Id)`.
* `fluxIncrementAverage` — the constant matrix `(k_L − k_m)_Q`.
* `fluxCorrectedCoeffOn` — the coefficient `a_L − (k_L − k_m)_Q` on `Q`.
* `fluxCorrectedError` — the `(∞,2)` functional of the flux-corrected
  coefficient, in `[0,∞]`.

## Measurability

The literal `𝓔` observables are deliberately *not* claimed measurable here, and
the omission mirrors the proved Section 3 layer exactly.  The `(∞,2)` literal
`Observable.cutoffHomogenizationErrorRaw` carries no genuine measurability
theorem: Section 3 obtains a measurable observable by *defining*
`Observable.cutoffHomogenizationError` to be the selected representative
`Observable.cutoffHomogenizationErrorRepresentative` and recording its a.e.
identity with the literal
(`Observable.cutoffHomogenizationErrorRaw_ae_eq_representative`). The
corresponding `(2,2)` representative — and the representative for the
flux-corrected coefficient, whose constant shift is itself sample-dependent —
are provider constructions and are not built in this support layer.

What *is* proved genuinely measurable here is `fluxIncrementAverage`: each of
its entries is a Carathéodory cube integral of the stream increment, jointly
measurable in `(ω, x)` by continuity in the point and measurability in the
sample.

## References

* ABK26, `d.mathcal.E`, (2.28); `d.good.event.for.lambda`;
  `p.mathcalE.annular.decomp`.
-/

namespace Algsuperdiff.Section4.Support

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The `(2,2)` homogenization error at one triadic scale -/

/-- The `p = q = 2` reading of `scaleResponseAtScale`, by definitional
unfolding of the `MultiscaleExponent` match. -/
private theorem scaleResponseAtScale_finite_eq
    (Q : TriadicCube d) (k : ℤ) (p : ℝ) (F : TriadicCoeffFamily d) (a0 : Mat d) :
    scaleResponseAtScale Q k (.finite p) F a0 =
      Real.rpow
        (finsetAverageReal (descendantsAtScale Q k)
          (fun R => Real.rpow (normalizedBlockResponseMax R F a0) (p / 2)))
        (1 / p) :=
  rfl

private theorem scaleResponseAtScale_finite_nonneg
    (Q : TriadicCube d) (k : ℤ) (p : ℝ)
    (F : TriadicCoeffFamily d) (a0 : Mat d) :
    0 ≤ scaleResponseAtScale Q k (.finite p) F a0 := by
  rw [scaleResponseAtScale_finite_eq]
  refine Real.rpow_nonneg ?_ _
  refine mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) ?_
  refine Finset.sum_nonneg fun R _ => ?_
  exact Real.rpow_nonneg (normalizedBlockResponseMax_nonneg R F a0) _

/-- The exact Section 4 error `𝓔_{s,2,2}(□_m; a, σ Id)`.

This is the `(p,q) = (2,2)` instance of exactly the same frozen unit-cube
functional and triadic change of variables that
`Observable.homogenizationErrorAtScale` uses at `(∞,2)`; no new error family
and no fallback branch is introduced. -/
noncomputable def homogenizationErrorAtScale22
    (m : ℤ) (s : ℝ) (a : CoeffOn (cubeDomain (originCube d m)))
    (sigma : PositiveScalar) : ℝ  :=
  Algsuperdiff.Frozen.Section24.unitCubeHomogenizationError
    s (.finite 2) (.finite 2) (unitRescaledCoeffOn m a)
    (isotropicComparatorMatrix sigma)

/-- Characterization by the manuscript's literal `𝓔_{s,2,2}` on `□_m`, with
the scalar gauge `σ Id` exhibited.  This mirrors
`Observable.homogenizationErrorAtScale_characterization` at the new
exponents. -/
theorem homogenizationErrorAtScale22_characterization
    (m : ℤ) (s : ℝ) (a : CoeffOn (cubeDomain (originCube d m)))
    (sigma : PositiveScalar) (F : TriadicCoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d m)) a) :
    homogenizationErrorAtScale22 m s a sigma =
      HomogenizationErrorOnCube (originCube d m) s (.finite 2) (.finite 2) F
        (isotropicComparatorMatrix sigma)  := by
  let B := TriadicCoeffFamily.dilate (-m) F
  calc
    homogenizationErrorAtScale22 m s a sigma =
        HomogenizationErrorOnCube (originCube d 0) s (.finite 2) (.finite 2) B
          (isotropicComparatorMatrix sigma) :=
      Algsuperdiff.Frozen.Section24.unitCubeHomogenizationError_characterization
        s (.finite 2) (.finite 2) (unitRescaledCoeffOn m a)
        (isotropicComparatorMatrix sigma) B
        (dilatedFamily_root_aeeq_unitRescaledCoeffOn m a F hF)
    _ = HomogenizationErrorOnCube (originCube d m) s (.finite 2) (.finite 2) F
          (isotropicComparatorMatrix sigma) := by
      simpa only [B, dilateOriginCube_neg_scale] using
        (HomogenizationErrorOnCube_dilate
          (TriadicCoeffFamily.isDilation_dilate (-m) F) (originCube d m)
          s (.finite 2) (.finite 2) (isotropicComparatorMatrix sigma))

theorem homogenizationErrorAtScale22_nonneg [NeZero d]
    (m : ℤ) {s : ℝ} (hs : 0 < s)
    (a : CoeffOn (cubeDomain (originCube d m)))
    (sigma : PositiveScalar) :
    0 ≤ homogenizationErrorAtScale22 m s a sigma := by
  let a0 := unitRescaledCoeffOn m a
  let F := Classical.choose
    (Algsuperdiff.Section24.UnitCubeMultiscale.exists_compatibleTriadicCoeffFamily a0)
  have hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a0 :=
    Classical.choose_spec
      (Algsuperdiff.Section24.UnitCubeMultiscale.exists_compatibleTriadicCoeffFamily a0)
  rw [homogenizationErrorAtScale22,
    Algsuperdiff.Frozen.Section24.unitCubeHomogenizationError_characterization
      s (.finite 2) (.finite 2) a0 (isotropicComparatorMatrix sigma) F hF]
  unfold Book.Ch02.HomogenizationErrorOnCube Book.Ch02.HomogenizationError
    Book.Ch02.HomogenizationErrorFinite
  refine Real.rpow_nonneg (tsum_nonneg fun l => mul_nonneg ?_ ?_) _
  · simpa only [geometricWeight_eq_old] using
      (HCPolySupport.geometricWeight_nonneg (s := s) (q := 2) l
        (by positivity : 0 ≤ s * (2 : ℝ)))
  · exact Real.rpow_nonneg
      (scaleResponseAtScale_finite_nonneg (originCube d 0) _ 2 F
        (isotropicComparatorMatrix sigma)) _

/-! ## The literal `(2,2)` cutoff observable -/

/-- The literal cutoff expression `𝓔_{s,2,2}(□_m; a_L, σ Id)`.

The `(2,2)` sibling of `Observable.cutoffHomogenizationErrorRaw`: the same
literal chain, with the spatial exponent moved from `∞` to `2`.  As there,
`coefficientScale` is the cutoff level `L` of `a_L` and `domainScale` is the
scale of the observed cube `□_m`; neither is silently substituted for the
other. -/
noncomputable def cutoffHomogenizationErrorRaw22
    (M : ABKModel d) (coefficientScale domainScale : ℤ) (s : ℝ)
    (sigma : PositiveScalar) (omega : Cutoff.CutoffSample d) : ℝ  :=
  homogenizationErrorAtScale22 domainScale s
    (Cutoff.coefficientCutoffCoeffOn M coefficientScale omega
      (originCube d domainScale))
    sigma

/-- The raw `(2,2)` cutoff expression is exactly the manuscript's
homogenization error on the genuine compatible cutoff family. -/
theorem cutoffHomogenizationErrorRaw22_characterization
    (M : ABKModel d) (coefficientScale domainScale : ℤ) (s : ℝ)
    (sigma : PositiveScalar) (omega : Cutoff.CutoffSample d) :
    cutoffHomogenizationErrorRaw22 M coefficientScale domainScale s sigma omega =
      HomogenizationErrorOnCube (originCube d domainScale) s (.finite 2) (.finite 2)
        (Cutoff.coefficientCutoffTriadicCoeffFamily M coefficientScale omega)
        (isotropicComparatorMatrix sigma)  :=
  homogenizationErrorAtScale22_characterization domainScale s
    (Cutoff.coefficientCutoffCoeffOn M coefficientScale omega
      (originCube d domainScale)) sigma
    (Cutoff.coefficientCutoffTriadicCoeffFamily M coefficientScale omega)
    (Cutoff.coefficientCutoffTriadicCoeffFamily_coeffOn_aeeq M coefficientScale omega
      (originCube d domainScale))

theorem cutoffHomogenizationErrorRaw22_nonneg [NeZero d]
    (M : ABKModel d) (coefficientScale domainScale : ℤ) {s : ℝ}
    (hs : 0 < s) (sigma : PositiveScalar) (omega : Cutoff.CutoffSample d) :
    0 ≤ cutoffHomogenizationErrorRaw22 M coefficientScale domainScale s sigma omega :=
  homogenizationErrorAtScale22_nonneg domainScale hs
    (Cutoff.coefficientCutoffCoeffOn M coefficientScale omega
      (originCube d domainScale)) sigma

/-! ## The `𝒢₂` annular atom -/

/-- The `𝒢₂` atom `𝓔_{s,2,2}(□_n; a_{n−2}, σ_{n−2} Id)` at the origin cube.

The manuscript's translated atom at `z + □_n` is `annularErrorAtom M n s
(Cutoff.translateCutoffSample z ω)` (resolution A4). -/
noncomputable def annularErrorAtom
    (M : ABKModel d) (n : ℤ) (s : ℝ) (omega : Cutoff.CutoffSample d) : ℝ  :=
  cutoffHomogenizationErrorRaw22 M (n - 2) n s (Annealed.sigmaBar M (n - 2)) omega

theorem annularErrorAtom_def (M : ABKModel d) (n : ℤ) (s : ℝ) (omega : Cutoff.CutoffSample d) :
    annularErrorAtom M n s omega =
      cutoffHomogenizationErrorRaw22 M (n - 2) n s (Annealed.sigmaBar M (n - 2)) omega  :=
  rfl

/-! ## The cube-averaged flux increment `(k_L − k_m)_Q` -/

/-- The entrywise cube average over `Q` of the coefficient increment `a_L − a_m`.
Since `a_L = ν Id + k_L`, the `ν Id` legs cancel and this is exactly the
manuscript's constant matrix `(k_L − k_m)_Q` (`p.mathcalE.annular.decomp`). -/
noncomputable def fluxIncrementAverage (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) : Mat d :=
  volumeAverageMat (openCubeSet Q)
    (fun x => Cutoff.coefficientCutoff M.nu L omega x -
      Cutoff.coefficientCutoff M.nu m omega x)

theorem fluxIncrementAverage_apply (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) (i j : Fin d) :
    fluxIncrementAverage M L m Q omega i j =
      volumeAverage (openCubeSet Q)
        (fun x => Cutoff.coefficientCutoff M.nu L omega x i j -
          Cutoff.coefficientCutoff M.nu m omega x i j) :=
  rfl

/-- The `ν Id` legs cancel: the averaged increment really is the increment of
the skew stream fields. -/
theorem coefficientCutoff_sub_coefficientCutoff (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) (x : Vec d) :
    Cutoff.coefficientCutoff M.nu L omega x -
        Cutoff.coefficientCutoff M.nu m omega x =
      Cutoff.cutoff L omega x - Cutoff.cutoff m omega x := by
  rw [Cutoff.coefficientCutoff_apply, Cutoff.coefficientCutoff_apply]
  abel

private theorem volumeAverage_neg (U : Set (Vec d)) (f : Vec d → ℝ) :
    volumeAverage U (fun x => -f x) = -volumeAverage U f := by
  unfold volumeAverage
  rw [MeasureTheory.integral_neg, mul_neg]

/-- The cube-averaged flux increment is skew-symmetric, because each `k_ℓ` is.
This is what keeps the corrected coefficient elliptic. -/
theorem fluxIncrementAverage_skew (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) (i j : Fin d) :
    fluxIncrementAverage M L m Q omega j i =
      -fluxIncrementAverage M L m Q omega i j := by
  have hpt : ∀ x : Vec d,
      Cutoff.coefficientCutoff M.nu L omega x j i -
          Cutoff.coefficientCutoff M.nu m omega x j i =
        -(Cutoff.coefficientCutoff M.nu L omega x i j -
          Cutoff.coefficientCutoff M.nu m omega x i j) := by
    intro x
    have hL := congrFun (congrFun (Cutoff.cutoff_skew L omega x) i) j
    have hm := congrFun (congrFun (Cutoff.cutoff_skew m omega x) i) j
    have hLji : Cutoff.cutoff L omega x j i = -Cutoff.cutoff L omega x i j := by
      simpa only [Matrix.transpose_apply, Matrix.neg_apply] using hL
    have hmji : Cutoff.cutoff m omega x j i = -Cutoff.cutoff m omega x i j := by
      simpa only [Matrix.transpose_apply, Matrix.neg_apply] using hm
    have hsubji := congrFun (congrFun
      (coefficientCutoff_sub_coefficientCutoff M L m omega x) j) i
    have hsubij := congrFun (congrFun
      (coefficientCutoff_sub_coefficientCutoff M L m omega x) i) j
    simp only [Matrix.sub_apply] at hsubji hsubij
    rw [hsubji, hsubij, hLji, hmji]
    ring
  rw [fluxIncrementAverage_apply, fluxIncrementAverage_apply]
  rw [show (fun x : Vec d => Cutoff.coefficientCutoff M.nu L omega x j i -
        Cutoff.coefficientCutoff M.nu m omega x j i) =
      fun x : Vec d => -(Cutoff.coefficientCutoff M.nu L omega x i j -
        Cutoff.coefficientCutoff M.nu m omega x i j) from funext hpt]
  exact volumeAverage_neg _ _

/-! ### Genuine measurability of the averaged flux increment -/

private theorem coefficientCutoff_sub_entry (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) (x : Vec d) (i j : Fin d) :
    Cutoff.coefficientCutoff M.nu L omega x i j -
        Cutoff.coefficientCutoff M.nu m omega x i j =
      Cutoff.cutoff L omega x i j - Cutoff.cutoff m omega x i j := by
  have h := congrFun (congrFun
    (coefficientCutoff_sub_coefficientCutoff M L m omega x) i) j
  simpa only [Matrix.sub_apply] using h

/-- The averaged increment read on the stream fields directly. -/
theorem fluxIncrementAverage_eq_cutoffAverage (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) (i j : Fin d) :
    fluxIncrementAverage M L m Q omega i j =
      volumeAverage (openCubeSet Q)
        (fun x => Cutoff.cutoff L omega x i j - Cutoff.cutoff m omega x i j) := by
  rw [fluxIncrementAverage_apply]
  exact congrArg _ (funext fun x => coefficientCutoff_sub_entry M L m omega x i j)

/-- Carathéodory joint `(ω, x)` measurability of the stream increment entries:
each entry is continuous in the point and measurable in the sample. -/
private theorem measurable_uncurry_cutoffIncrement_entry (L m : ℤ) (i j : Fin d) :
    Measurable (fun p : Cutoff.CutoffSample d × Vec d =>
      Cutoff.cutoff L p.1 p.2 i j - Cutoff.cutoff m p.1 p.2 i j) := by
  have hjoint : Measurable (Function.uncurry
      (fun (x : Vec d) (omega : Cutoff.CutoffSample d) =>
        Cutoff.cutoff L omega x i j - Cutoff.cutoff m omega x i j)) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun omega => (Cutoff.continuous_cutoff_entry L omega i j).sub
        (Cutoff.continuous_cutoff_entry m omega i j))
      (fun x => (Cutoff.measurable_cutoff_apply_entry L x i j).sub
        (Cutoff.measurable_cutoff_apply_entry m x i j))
  have hcomp : (fun p : Cutoff.CutoffSample d × Vec d =>
      Cutoff.cutoff L p.1 p.2 i j - Cutoff.cutoff m p.1 p.2 i j) =
      (Function.uncurry
        (fun (x : Vec d) (omega : Cutoff.CutoffSample d) =>
          Cutoff.cutoff L omega x i j - Cutoff.cutoff m omega x i j)) ∘ Prod.swap := by
    funext p
    rfl
  rw [hcomp]
  exact hjoint.comp measurable_swap

/-- Every entry of the averaged flux increment is genuinely measurable on the
cutoff-sample carrier. -/
theorem measurable_fluxIncrementAverage_entry (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (i j : Fin d) :
    Measurable (fun omega : Cutoff.CutoffSample d =>
      fluxIncrementAverage M L m Q omega i j) := by
  have hsm : StronglyMeasurable (fun omega : Cutoff.CutoffSample d =>
      ∫ x in openCubeSet Q,
        (Cutoff.cutoff L omega x i j - Cutoff.cutoff m omega x i j) ∂volume) :=
    (measurable_uncurry_cutoffIncrement_entry L m i j).stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (openCubeSet Q))
  have hfun : (fun omega : Cutoff.CutoffSample d =>
      fluxIncrementAverage M L m Q omega i j) =
      fun omega : Cutoff.CutoffSample d =>
        (volume (openCubeSet Q)).toReal⁻¹ *
          ∫ x in openCubeSet Q,
            (Cutoff.cutoff L omega x i j - Cutoff.cutoff m omega x i j) ∂volume := by
    funext omega
    rw [fluxIncrementAverage_eq_cutoffAverage]
    rfl
  rw [hfun]
  exact (hsm.const_mul _).measurable

/-! ## The flux-corrected coefficient `a_L − (k_L − k_m)_Q` -/

/-- The `ℓ¹` entry mass of the averaged flux increment.  It is a uniform
bound on every entry of that constant matrix, and is the only new ingredient
needed to carry the ellipticity of the corrected coefficient. -/
noncomputable def fluxIncrementAbsSum (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, |fluxIncrementAverage M L m Q omega i j|

theorem abs_fluxIncrementAverage_le_absSum (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) (i j : Fin d) :
    |fluxIncrementAverage M L m Q omega i j| ≤ fluxIncrementAbsSum M L m Q omega := by
  have hinner : |fluxIncrementAverage M L m Q omega i j| ≤
      ∑ j' : Fin d, |fluxIncrementAverage M L m Q omega i j'| :=
    Finset.single_le_sum
      (f := fun j' : Fin d => |fluxIncrementAverage M L m Q omega i j'|)
      (fun j' _ => abs_nonneg _) (Finset.mem_univ j)
  have houter : (∑ j' : Fin d, |fluxIncrementAverage M L m Q omega i j'|) ≤
      fluxIncrementAbsSum M L m Q omega :=
    Finset.single_le_sum
      (f := fun i' : Fin d => ∑ j' : Fin d, |fluxIncrementAverage M L m Q omega i' j'|)
      (fun i' _ => Finset.sum_nonneg fun j' _ => abs_nonneg _) (Finset.mem_univ i)
  exact hinner.trans houter

/-- The corrected coefficient field `a_L − (k_L − k_m)_Q` on the whole space.
Only its restriction to `Q` is used. -/
noncomputable def fluxCorrectedField (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) : CoeffField d :=
  fun x => Cutoff.coefficientCutoff M.nu L omega x - fluxIncrementAverage M L m Q omega

@[simp]
theorem fluxCorrectedField_apply (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) (x : Vec d) :
    fluxCorrectedField M L m Q omega x =
      Cutoff.coefficientCutoff M.nu L omega x - fluxIncrementAverage M L m Q omega :=
  rfl

/-- Subtracting the skew averaged increment does not move the symmetric part:
it is still exactly `ν Id`.  This is the whole content of the ellipticity of
the corrected coefficient. -/
private theorem symmPart_fluxCorrectedField (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) (x : Vec d) :
    symmPart (fluxCorrectedField M L m Q omega x) = M.nu • (1 : Mat d) := by
  ext i j
  have hA := congrFun (congrFun
    (Cutoff.symmPart_coefficientCutoff M.nu L omega x) i) j
  have hC := fluxIncrementAverage_skew M L m Q omega i j
  simp only [symmPart, fluxCorrectedField, Matrix.sub_apply] at hA ⊢
  linarith only [hA, hC]

/-- The uniform entry envelope of the corrected coefficient on `Q`. -/
noncomputable def fluxCorrectedEntryBound (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) : ℝ :=
  Cutoff.coefficientCutoffCubeEntryBound M L omega Q +
    fluxIncrementAbsSum M L m Q omega

/-- The upper ellipticity constant of the corrected coefficient on `Q`, produced by
the proved skew-plus-entry-bound certificate. -/
noncomputable def fluxCorrectedEllipticityUpper (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) : ℝ :=
  ((d : ℝ) * (d : ℝ) * (fluxCorrectedEntryBound M L m Q omega) ^ 2 + M.nu ^ 2) / M.nu

private theorem abs_fluxCorrectedField_entry_le (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) {x : Vec d}
    (hx : x ∈ openCubeSet Q) (i j : Fin d) :
    |fluxCorrectedField M L m Q omega x i j| ≤
      fluxCorrectedEntryBound M L m Q omega := by
  have h1 := Cutoff.abs_coefficientCutoff_entry_le_cubeEntryBound M L omega Q hx i j
  have h2 := abs_fluxIncrementAverage_le_absSum M L m Q omega i j
  calc
    |fluxCorrectedField M L m Q omega x i j| =
        |Cutoff.coefficientCutoff M.nu L omega x i j -
          fluxIncrementAverage M L m Q omega i j| := rfl
    _ ≤ |Cutoff.coefficientCutoff M.nu L omega x i j| +
          |fluxIncrementAverage M L m Q omega i j| := abs_sub _ _
    _ ≤ fluxCorrectedEntryBound M L m Q omega := add_le_add h1 h2

theorem isEllipticMatrix_fluxCorrectedField (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) {x : Vec d}
    (hx : x ∈ openCubeSet Q) :
    IsEllipticMatrix M.nu (fluxCorrectedEllipticityUpper M L m Q omega)
      (fluxCorrectedField M L m Q omega x) :=
  Cutoff.isEllipticMatrix_of_symmPart_and_entry_bound M.nu_pos
    (symmPart_fluxCorrectedField M L m Q omega x)
    (fun i j => abs_fluxCorrectedField_entry_le M L m Q omega hx i j)

theorem cubeCenter_mem_openCubeSet (Q : TriadicCube d) :
    cubeCenter Q ∈ openCubeSet Q := by
  rw [← ball_cubeCenter_eq_openCubeSet]
  exact Metric.mem_ball_self (cubeRadius_pos Q)

/-- The Chapter 2 coefficient object of the flux-corrected coefficient
`a_L − (k_L − k_m)_Q` on the cube `Q`.  The lower ellipticity constant is
still the molecular diffusivity `ν`, because the subtracted matrix is skew. -/
noncomputable def fluxCorrectedCoeffOn (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) : CoeffOn (cubeDomain Q) where
  toCoeffField := fluxCorrectedField M L m Q omega
  lam := M.nu
  Lam := fluxCorrectedEllipticityUpper M L m Q omega
  lam_pos := M.nu_pos
  lam_le_Lam :=
    (isEllipticMatrix_fluxCorrectedField M L m Q omega
      (cubeCenter_mem_openCubeSet Q)).2.1
  aeStronglyMeasurable := by
    classical
    intro i j
    have hmeas : Measurable (fun x : Vec d =>
        restrictCoeffField (openCubeSet Q) (fluxCorrectedField M L m Q omega) x i j) := by
      have hEq : (fun x : Vec d =>
          restrictCoeffField (openCubeSet Q) (fluxCorrectedField M L m Q omega) x i j) =
          fun x => if x ∈ openCubeSet Q then
            fluxCorrectedField M L m Q omega x i j else 0 := by
        funext x
        by_cases hx : x ∈ openCubeSet Q <;> simp [restrictCoeffField, hx]
      rw [hEq]
      exact (((Cutoff.coefficientCutoff M.nu L omega).entry_measurable i j).sub
        measurable_const).ite (measurableSet_openCubeSet Q) measurable_const
    exact hmeas.aestronglyMeasurable
  aeElliptic := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    exact isEllipticMatrix_fluxCorrectedField M L m Q omega hx

@[simp]
theorem fluxCorrectedCoeffOn_toCoeffField (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) :
    (fluxCorrectedCoeffOn M L m Q omega).toCoeffField =
      fluxCorrectedField M L m Q omega :=
  rfl

/-! ## The flux-corrected `(∞,2)` error and its `L ≥ m` supremum -/

/-- The manuscript's `𝓔_{s,∞,2}(□_k; a_L − (k_L − k_k)_{□_k}, σ_k Id)` at the
origin cube (`p.mathcalE.annular.decomp`).

The averaged increment is taken over the same cube `□_k` that carries the
functional, matching the printed `(k_L − k_m)_{□_m}`.  The translated version
at `z + □_k` is `fluxCorrectedError M L k s (Cutoff.translateCutoffSample z ω)`
(resolution A4). -/
noncomputable def fluxCorrectedError (M : ABKModel d) (L k : ℤ) (s : ℝ)
    (omega : Cutoff.CutoffSample d) : ℝ  :=
  homogenizationErrorAtScale k s
    (fluxCorrectedCoeffOn M L k (originCube d k) omega) (Annealed.sigmaBar M k)

theorem fluxCorrectedError_nonneg [NeZero d] (M : ABKModel d) (L k : ℤ) {s : ℝ}
    (hs : 0 < s) (omega : Cutoff.CutoffSample d) :
    0 ≤ fluxCorrectedError M L k s omega :=
  homogenizationErrorAtScale_nonneg k hs
    (fluxCorrectedCoeffOn M L k (originCube d k) omega) (Annealed.sigmaBar M k)

end

end Algsuperdiff.Section4.Support

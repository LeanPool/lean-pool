/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.ErrorAtoms
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffHomogenizationErrorRepresentative

/-!
# FluxCorrectedRepresentative

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The measurable flux-corrected `(∞,2)` representative

`Algsuperdiff.Section4.Support.ErrorAtoms` records the literal flux-corrected
observable `fluxCorrectedError` — the `(∞,2)` homogenization error of
`a_L − (k_L − k_m)_Q` on `□_k` — and its `L ≥ m` supremum in `[0,∞]`.  As at
`(∞,2)` in Section 3, the literal is not measurable by composition.

The proved Section 3 chain (`Observable/CutoffCoarseBlockRepresentative.lean`,
`Observable/CutoffHomogenizationErrorRepresentative.lean`) is built for
`Cutoff.coefficientCutoff` *specifically*: its a.e.-measurable coarse-block
input comes from `Cutoff.coefficientCutoffLaw_lawCarrier`, the Chapter 4
`RestrictionLawCarrier` of the pushforward of the cutoff sample law along
`coefficientCutoff`.  This module re-derives that input at the flux-corrected
field, and reuses everything downstream of it verbatim.

The re-derivation has exactly three ingredients.

1. The flux-corrected field is a genuine *carrier* element and the map into the
   carrier is genuinely measurable: `a_L − (k_L − k_m)_Q` is
   `Cutoff.coefficientCutoff M.nu L ω` plus the constant carrier field
   `constRegCoeffField (−(k_L − k_m)_Q(ω))`, whose sample dependence is
   measurable by `measurable_fluxIncrementAverage_entry`.  Both `RegCoeffField`
   lanes of the constant summand are handled directly: the pointwise lane is an
   entry evaluation, and the entry-test lane is `(k_L−k_m)_Q(ω)_{ij} ∫ φ`.
2. *Every* sample of the flux-corrected field is locally a.e.-uniformly
   elliptic, because the subtracted matrix is skew (so the symmetric part is
   still `ν Id`) and its entries are uniformly bounded on each cube.
3. Hence the pushforward law is a Chapter 4 `RestrictionLawCarrier`, which
   supplies CoarseGraining's a.e.-measurable coarse full-block observable.

Nothing else changes: `normalizedBlockResponseMaxRepresentativeFunctional`, the
compact-sphere identification
`normalizedBlockResponseMaxFromFullCoarseBlock_eq_representativeFunctional_of_nonneg`
and the geometric scale sum are exponent- and coefficient-agnostic and are used
exactly as proved.

## Main definitions

* `fluxCorrectedRegField`, `fluxCorrectedCoeffFamily` — the carrier field and
  its canonical Chapter 2 triadic family.
* `fluxCorrectedErrorRepresentative` — the genuine measurable representative.
* `fluxCorrectedErrorObservableSup`, `fluxCorrectedErrorObservableSqSup` — the
  `sup_{L ≥ m}` observables of `p.mathcalE.annular.decomp` (§B4).

## References

* ABK26, `p.mathcalE.annular.decomp`.
-/

namespace Algsuperdiff.Section4.Support

open Filter MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch04
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The flux-corrected coefficient as a carrier field -/

/-- The flux-corrected coefficient `a_L − (k_L − k_m)_Q` as an element of
CoarseGraining's regular-fields carrier: the cutoff coefficient plus a constant
carrier field. -/
noncomputable def fluxCorrectedRegField (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) : RegCoeffField d :=
  Cutoff.coefficientCutoff M.nu L omega +
    RegCoeffField.constRegCoeffField (-fluxIncrementAverage M L m Q omega)

@[simp]
theorem fluxCorrectedRegField_apply (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) (x : Vec d) :
    fluxCorrectedRegField M L m Q omega x = fluxCorrectedField M L m Q omega x := by
  simp only [fluxCorrectedRegField, RegCoeffField.add_apply,
    RegCoeffField.constRegCoeffField_apply, fluxCorrectedField_apply]
  exact (sub_eq_add_neg _ _).symm

theorem fluxCorrectedRegField_toFun (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) :
    (fluxCorrectedRegField M L m Q omega).toFun = fluxCorrectedField M L m Q omega :=
  funext (fluxCorrectedRegField_apply M L m Q omega)

/-- A constant carrier field with measurable matrix value is a measurable
carrier-valued map: the pointwise lane is an entry evaluation, and the
entry-test lane is the entry times the fixed probe integral. -/
private theorem measurable_constRegCoeffField_comp {alpha : Type*}
    [MeasurableSpace alpha] (C : alpha → Mat d)
    (hC : ∀ i j, Measurable fun a => C a i j) :
    Measurable fun a => RegCoeffField.constRegCoeffField (C a) := by
  refine HCPolySupport.measurable_into_regCoeffField' ?_ ?_
  · intro y i j
    simpa only [RegCoeffField.constRegCoeffField_apply] using hC i j
  · intro i j phi _hphi
    have hEq :
        (fun a => entryTestR i j phi (RegCoeffField.constRegCoeffField (C a))) =
          fun a => C a i j * ∫ x, phi x ∂volume := by
      funext a
      simp only [entryTestR, RegCoeffField.constRegCoeffField_apply]
      exact integral_const_mul (C a i j) phi
    rw [hEq]
    exact (hC i j).mul_const _

/-- The flux-corrected carrier field is a genuinely measurable function of the
cutoff sample. -/
theorem measurable_fluxCorrectedRegField (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) :
    Measurable (fluxCorrectedRegField M L m Q) :=
  (Cutoff.measurable_coefficientCutoff M.nu L).add
    (measurable_constRegCoeffField_comp _ fun i j => by
      simpa only [Matrix.neg_apply] using!
        (measurable_fluxIncrementAverage_entry M L m Q i j).neg)

/-! ## Local uniform ellipticity of every flux-corrected sample -/

private theorem symmPart_fluxCorrectedRegField (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) (x : Vec d) :
    symmPart (fluxCorrectedRegField M L m Q omega x) = M.nu • (1 : Mat d) := by
  ext i j
  have hA := congrFun (congrFun
    (Cutoff.symmPart_coefficientCutoff M.nu L omega x) i) j
  have hC := fluxIncrementAverage_skew M L m Q omega i j
  simp only [symmPart, fluxCorrectedRegField_apply, fluxCorrectedField_apply,
    Matrix.sub_apply] at hA ⊢
  linarith only [hA, hC]

/-- The uniform entry envelope of the flux-corrected field on a cube `R`: the
proved cutoff envelope on `R` plus the entry mass of the constant shift. -/
noncomputable def fluxCorrectedCubeEntryBound (M : ABKModel d) (L m : ℤ)
    (Q R : TriadicCube d) (omega : Cutoff.CutoffSample d) : ℝ :=
  Cutoff.coefficientCutoffCubeEntryBound M L omega R + fluxIncrementAbsSum M L m Q omega

/-- The upper ellipticity constant of the flux-corrected field on a cube `R`. -/
noncomputable def fluxCorrectedCubeEllipticityUpper (M : ABKModel d) (L m : ℤ)
    (Q R : TriadicCube d) (omega : Cutoff.CutoffSample d) : ℝ :=
  ((d : ℝ) * (d : ℝ) * (fluxCorrectedCubeEntryBound M L m Q R omega) ^ 2 + M.nu ^ 2) / M.nu

private theorem abs_fluxCorrectedRegField_entry_le (M : ABKModel d) (L m : ℤ)
    (Q R : TriadicCube d) (omega : Cutoff.CutoffSample d) {x : Vec d}
    (hx : x ∈ openCubeSet R) (i j : Fin d) :
    |fluxCorrectedRegField M L m Q omega x i j| ≤
      fluxCorrectedCubeEntryBound M L m Q R omega := by
  have h1 := Cutoff.abs_coefficientCutoff_entry_le_cubeEntryBound M L omega R hx i j
  have h2 := abs_fluxIncrementAverage_le_absSum M L m Q omega i j
  calc
    |fluxCorrectedRegField M L m Q omega x i j| =
        |Cutoff.coefficientCutoff M.nu L omega x i j -
          fluxIncrementAverage M L m Q omega i j| := by
      rw [fluxCorrectedRegField_apply, fluxCorrectedField_apply, Matrix.sub_apply]
    _ ≤ |Cutoff.coefficientCutoff M.nu L omega x i j| +
          |fluxIncrementAverage M L m Q omega i j| := abs_sub _ _
    _ ≤ fluxCorrectedCubeEntryBound M L m Q R omega := add_le_add h1 h2

private theorem isEllipticMatrix_fluxCorrectedRegField (M : ABKModel d) (L m : ℤ)
    (Q R : TriadicCube d) (omega : Cutoff.CutoffSample d) {x : Vec d}
    (hx : x ∈ openCubeSet R) :
    IsEllipticMatrix M.nu (fluxCorrectedCubeEllipticityUpper M L m Q R omega)
      (fluxCorrectedRegField M L m Q omega x) :=
  Cutoff.isEllipticMatrix_of_symmPart_and_entry_bound M.nu_pos
    (symmPart_fluxCorrectedRegField M L m Q omega x)
    (fun i j => abs_fluxCorrectedRegField_entry_le M L m Q R omega hx i j)

private theorem cubeCenter_mem_openCubeSet_fluxCorrected (R : TriadicCube d) :
    cubeCenter R ∈ openCubeSet R := by
  rw [← ball_cubeCenter_eq_openCubeSet]
  exact Metric.mem_ball_self (cubeRadius_pos R)

private theorem aeStronglyMeasurable_restrict_fluxCorrectedRegField
    (M : ABKModel d) (L m : ℤ) (Q R : TriadicCube d)
    (omega : Cutoff.CutoffSample d) (i j : Fin d) :
    AEStronglyMeasurable
      (fun x : Vec d =>
        restrictCoeffField (openCubeSet R)
          (fluxCorrectedRegField M L m Q omega).toFun x i j)
      (volumeMeasureOn (openCubeSet R)) := by
  classical
  have hmeas : Measurable fun x : Vec d =>
      restrictCoeffField (openCubeSet R)
        (fluxCorrectedRegField M L m Q omega).toFun x i j := by
    have hEq : (fun x : Vec d =>
        restrictCoeffField (openCubeSet R)
          (fluxCorrectedRegField M L m Q omega).toFun x i j) =
        fun x => if x ∈ openCubeSet R then
          fluxCorrectedRegField M L m Q omega x i j else 0 := by
      funext x
      by_cases hx : x ∈ openCubeSet R <;> simp [restrictCoeffField, hx]
    rw [hEq]
    exact ((fluxCorrectedRegField M L m Q omega).entry_measurable i j).ite
      (measurableSet_openCubeSet R) measurable_const
  exact hmeas.aestronglyMeasurable

/-- Every flux-corrected sample lies in CoarseGraining's Chapter 4 local
a.e.-uniform ellipticity carrier: the subtracted matrix is skew, so the
symmetric part is still `ν Id`, and on each cube the entries are uniformly
bounded. -/
theorem aeLocallyUniformlyEllipticField_fluxCorrectedRegField (M : ABKModel d)
    (L m : ℤ) (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) :
    AELocallyUniformlyEllipticField (fluxCorrectedRegField M L m Q omega) := by
  intro R
  refine ⟨M.nu, fluxCorrectedCubeEllipticityUpper M L m Q R omega, M.nu_pos,
    (isEllipticMatrix_fluxCorrectedRegField M L m Q R omega
      (cubeCenter_mem_openCubeSet_fluxCorrected R)).2.1, ?_⟩
  refine ⟨measurableSet_openCubeSet R,
    fun i j => aeStronglyMeasurable_restrict_fluxCorrectedRegField M L m Q R omega i j, ?_⟩
  filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
  exact isEllipticMatrix_fluxCorrectedRegField M L m Q R omega hx

/-- The canonical Chapter 2 triadic coefficient family of the flux-corrected field.
It is CoarseGraining's own dependent family construction at the witness above;
no new family is introduced. -/
noncomputable def fluxCorrectedCoeffFamily (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) : Ch02.TriadicCoeffFamily d :=
  triadicCoeffFamilyOfAELocallyUniformlyEllipticField
    (fluxCorrectedRegField M L m Q omega)
    (aeLocallyUniformlyEllipticField_fluxCorrectedRegField M L m Q omega)

/-- The literal flux-corrected error of `ErrorAtoms` is exactly CoarseGraining's
homogenization error on the canonical family of the flux-corrected field. -/
theorem fluxCorrectedError_characterization (M : ABKModel d) (L k : ℤ)
    (s : ℝ) (omega : Cutoff.CutoffSample d) :
    fluxCorrectedError M L k s omega =
      Ch02.HomogenizationErrorOnCube (originCube d k) s .infinity (.finite 2)
        (fluxCorrectedCoeffFamily M L k (originCube d k) omega)
        (isotropicComparatorMatrix (Annealed.sigmaBar M k))  :=
  homogenizationErrorAtScale_characterization k s
    (fluxCorrectedCoeffOn M L k (originCube d k) omega) (Annealed.sigmaBar M k)
    (fluxCorrectedCoeffFamily M L k (originCube d k) omega)
    (Filter.EventuallyEq.of_eq
      (fluxCorrectedRegField_toFun M L k (originCube d k) omega))

/-! ## The Chapter 4 law carrier of the flux-corrected law -/

/-- The set of locally a.e.-uniformly elliptic carrier fields is measurable: it is
the countable `⋂_Q ⋃_k` of the A quantitative-slice sets, each genuinely
`LocalSigmaR`-measurable.  This mirrors the same private lemma of
`Section3/Cutoff/LawCarrier.lean`, kept local for the same reason: so that the
flux-corrected construction does not depend on the unrelated high-contrast
development where the general lemma also occurs. -/
private theorem measurableSet_aeLocallyUniformlyEllipticField :
    MeasurableSet {a : RegCoeffField d | AELocallyUniformlyEllipticField a} := by
  classical
  have hEq : {a : RegCoeffField d | AELocallyUniformlyEllipticField a}
      = ⋂ Q : TriadicCube d, ⋃ k : ℕ,
          {a : RegCoeffField d |
            AEEQuantitativeEllipticSlice (cubeSet Q) k a.toFun} := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · intro ha Q
      exact ha.exists_aeeQuantitativeEllipticSlice_cubeSet Q
    · intro ha Q
      obtain ⟨k, hk⟩ := ha Q
      have hkpos : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
      have h1le : (1 : ℝ) ≤ (k : ℝ) + 1 := by
        have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by positivity
        linarith only [hk_nonneg]
      have hle : ((k : ℝ) + 1)⁻¹ ≤ (k : ℝ) + 1 :=
        le_trans ((inv_le_one₀ (by positivity)).2 h1le) h1le
      refine ⟨((k : ℝ) + 1)⁻¹, (k : ℝ) + 1, hkpos, hle, ?_⟩
      have hslice : IsAEEllipticFieldOn ((k : ℝ) + 1)⁻¹ ((k : ℝ) + 1)
          (cubeSet Q) a.toFun := hk
      exact hslice.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  rw [hEq]
  refine MeasurableSet.iInter fun Q => MeasurableSet.iUnion fun k => ?_
  exact LocalSigmaR_le (cubeSet Q) _
    (measurableSet_localSigmaR_aeeQuantitativeEllipticSlice Q k)

/-- The pushforward of the cutoff-sample law along the flux-corrected carrier
map is a Chapter 4 `RestrictionLawCarrier`. -/
theorem lawCarrier_map_fluxCorrectedRegField (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) :
    RestrictionLawCarrier
      (Measure.map (fluxCorrectedRegField M L m Q)
        (Cutoff.cutoffSampleLaw M).toMeasure) := by
  have hT : Measurable (fluxCorrectedRegField M L m Q) :=
    measurable_fluxCorrectedRegField M L m Q
  have : IsProbabilityMeasure
      (Measure.map (fluxCorrectedRegField M L m Q)
        (Cutoff.cutoffSampleLaw M).toMeasure) :=
    inferInstance
  refine lawCarrier_of_aeLocallyUniformlyElliptic ?_
  rw [AELocallyUniformlyEllipticLaw,
    ae_map_iff hT.aemeasurable measurableSet_aeLocallyUniformlyEllipticField]
  exact Filter.Eventually.of_forall fun omega =>
    aeLocallyUniformlyEllipticField_fluxCorrectedRegField M L m Q omega

/-! ## The flux-corrected coarse-block representative -/

/-- The literal full coarse block matrix of the flux-corrected coefficient. -/
noncomputable def fluxCorrectedCoarseFullBlockRaw (M : ABKModel d) (L m : ℤ)
    (Q R : TriadicCube d) : Cutoff.CutoffSample d → FullBlockMat d :=
  fun omega => toFullBlockMat
    (coarseBlockMatrix (cubeSet R) (fluxCorrectedRegField M L m Q omega).toFun)

theorem aemeasurable_fluxCorrectedCoarseFullBlockRaw (M : ABKModel d) (L m : ℤ)
    (Q R : TriadicCube d) :
    AEMeasurable (fluxCorrectedCoarseFullBlockRaw M L m Q R)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hcoarse :=
    (lawCarrier_map_fluxCorrectedRegField M L m Q).aemeasurable_coarseFullBlockMatrix_cubeSet R
  simpa only [fluxCorrectedCoarseFullBlockRaw, Function.comp_def] using!
    hcoarse.comp_measurable (measurable_fluxCorrectedRegField M L m Q)

/-- The common coarse-block representative of the flux-corrected coefficient. -/
noncomputable def fluxCorrectedCoarseFullBlockRepresentative (M : ABKModel d)
    (L m : ℤ) (Q R : TriadicCube d) : Cutoff.CutoffSample d → FullBlockMat d :=
  AEMeasurable.mk (fluxCorrectedCoarseFullBlockRaw M L m Q R)
    (aemeasurable_fluxCorrectedCoarseFullBlockRaw M L m Q R)

theorem measurable_fluxCorrectedCoarseFullBlockRepresentative (M : ABKModel d)
    (L m : ℤ) (Q R : TriadicCube d) :
    Measurable (fluxCorrectedCoarseFullBlockRepresentative M L m Q R) :=
  (aemeasurable_fluxCorrectedCoarseFullBlockRaw M L m Q R).measurable_mk

theorem fluxCorrectedCoarseFullBlock_ae_eq_representative (M : ABKModel d)
    (L m : ℤ) (Q R : TriadicCube d) :
    fluxCorrectedCoarseFullBlockRaw M L m Q R =ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure]
      fluxCorrectedCoarseFullBlockRepresentative M L m Q R :=
  (aemeasurable_fluxCorrectedCoarseFullBlockRaw M L m Q R).ae_eq_mk

/-- The everywhere-defined normalized response functional of the common
flux-corrected coarse-block representative. -/
noncomputable def fluxCorrectedNormalizedBlockResponseRepresentative
    (M : ABKModel d) (L m : ℤ) (Q R : TriadicCube d) (a0 : Mat d) :
    Cutoff.CutoffSample d → ℝ  :=
  fun omega => normalizedBlockResponseMaxRepresentativeFunctional a0
    (fluxCorrectedCoarseFullBlockRepresentative M L m Q R omega)

theorem measurable_fluxCorrectedNormalizedBlockResponseRepresentative
    (M : ABKModel d) (L m : ℤ) (Q R : TriadicCube d) (a0 : Mat d) :
    Measurable (fluxCorrectedNormalizedBlockResponseRepresentative M L m Q R a0)  :=
  (continuous_normalizedBlockResponseMaxRepresentativeFunctional a0).measurable.comp
    (measurable_fluxCorrectedCoarseFullBlockRepresentative M L m Q R)

theorem fluxCorrectedNormalizedBlockResponseRepresentative_nonneg
    (M : ABKModel d) (L m : ℤ) (Q R : TriadicCube d) (a0 : Mat d)
    (omega : Cutoff.CutoffSample d) :
    0 ≤ fluxCorrectedNormalizedBlockResponseRepresentative M L m Q R a0 omega  :=
  norm_nonneg _

private theorem fluxCorrected_rawCoarseBlock_normalizedQuadratic_nonneg [NeZero d]
    (M : ABKModel d) (L m : ℤ) (Q R : TriadicCube d) (a0 : Mat d)
    (omega : Cutoff.CutoffSample d) (e : FullBlockVec d) :
    0 ≤ blockJQuadraticFullBlockMat
      (fluxCorrectedCoarseFullBlockRaw M L m Q R omega)
      (ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixInvSqrt a0) e))
      (ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixSqrt a0) e)) := by
  have hlocal := aeLocallyUniformlyEllipticField_fluxCorrectedRegField M L m Q omega
  calc
    (0 : ℝ) ≤ Ch02.doubledResponseJ (Ch02.cubeDomain R)
        ((triadicCoeffFamilyOfAELocallyUniformlyEllipticField
          (fluxCorrectedRegField M L m Q omega) hlocal).coeffOn R)
        (ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixInvSqrt a0) e))
        (ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixSqrt a0) e)) :=
      Ch02.doubledResponseJ_nonneg _ _ _ _
    _ = blockJObservableCubeSetBlockVec R _ _ (fluxCorrectedRegField M L m Q omega) :=
      doubledResponseJ_eq_blockJObservableCubeSetBlockVec_of_aelocallyUniformlyEllipticField
        hlocal R _ _
    _ = blockJQuadraticFullBlockMat
        (fluxCorrectedCoarseFullBlockRaw M L m Q R omega) _ _ :=
      blockJObservable_eq_blockJQuadraticForm_of_uniformEllipticity
        hlocal R _ _

/-- The literal normalized block-response maximum of the flux-corrected family
is the finite-dimensional sphere maximum of its literal full coarse matrix. -/
theorem normalizedBlockResponseMax_fluxCorrected_eq_fromRawCoarseBlock [NeZero d]
    (M : ABKModel d) (L m : ℤ) (Q R : TriadicCube d) (a0 : Mat d)
    (omega : Cutoff.CutoffSample d) :
    Ch02.normalizedBlockResponseMax R (fluxCorrectedCoeffFamily M L m Q omega) a0 =
      normalizedBlockResponseMaxFromFullCoarseBlock a0
        (fluxCorrectedCoarseFullBlockRaw M L m Q R omega) := by
  have hlocal := aeLocallyUniformlyEllipticField_fluxCorrectedRegField M L m Q omega
  unfold Ch02.normalizedBlockResponseMax Ch02.normalizedBlockResponseValueSet
    normalizedBlockResponseMaxFromFullCoarseBlock
  congr 1
  ext value
  constructor
  · rintro ⟨e, he, rfl⟩
    refine ⟨e, he, ?_⟩
    calc
      Ch02.doubledResponseJ (Ch02.cubeDomain R)
          ((fluxCorrectedCoeffFamily M L m Q omega).coeffOn R)
          (ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixInvSqrt a0) e))
          (ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixSqrt a0) e)) =
          blockJObservableCubeSetBlockVec R _ _ (fluxCorrectedRegField M L m Q omega) :=
        doubledResponseJ_eq_blockJObservableCubeSetBlockVec_of_aelocallyUniformlyEllipticField
          hlocal R _ _
      _ = blockJQuadraticFullBlockMat
          (fluxCorrectedCoarseFullBlockRaw M L m Q R omega) _ _ :=
        blockJObservable_eq_blockJQuadraticForm_of_uniformEllipticity
          hlocal R _ _
  · rintro ⟨e, he, rfl⟩
    refine ⟨e, he, ?_⟩
    calc
      blockJQuadraticFullBlockMat (fluxCorrectedCoarseFullBlockRaw M L m Q R omega)
          (ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixInvSqrt a0) e))
          (ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixSqrt a0) e)) =
          blockJObservableCubeSetBlockVec R _ _ (fluxCorrectedRegField M L m Q omega) :=
        (blockJObservable_eq_blockJQuadraticForm_of_uniformEllipticity
          hlocal R _ _).symm
      _ = Ch02.doubledResponseJ (Ch02.cubeDomain R)
          ((fluxCorrectedCoeffFamily M L m Q omega).coeffOn R) _ _ :=
        (doubledResponseJ_eq_blockJObservableCubeSetBlockVec_of_aelocallyUniformlyEllipticField
          hlocal R _ _).symm

/-- At every fixed cube, the flux-corrected coarse-block representative realizes
CoarseGraining's literal normalized response maximum almost everywhere. -/
theorem ae_normalizedBlockResponseMax_fluxCorrected_eq_representative [NeZero d]
    (M : ABKModel d) (L m : ℤ) (Q R : TriadicCube d) (a0 : Mat d) :
    (fun omega => Ch02.normalizedBlockResponseMax R
      (fluxCorrectedCoeffFamily M L m Q omega) a0) =ᵐ[
        (Cutoff.cutoffSampleLaw M).toMeasure]
      fluxCorrectedNormalizedBlockResponseRepresentative M L m Q R a0 := by
  filter_upwards [fluxCorrectedCoarseFullBlock_ae_eq_representative M L m Q R]
    with omega hmatrix
  calc
    Ch02.normalizedBlockResponseMax R (fluxCorrectedCoeffFamily M L m Q omega) a0 =
        normalizedBlockResponseMaxFromFullCoarseBlock a0
          (fluxCorrectedCoarseFullBlockRaw M L m Q R omega) :=
      normalizedBlockResponseMax_fluxCorrected_eq_fromRawCoarseBlock M L m Q R a0 omega
    _ = normalizedBlockResponseMaxRepresentativeFunctional a0
          (fluxCorrectedCoarseFullBlockRaw M L m Q R omega) :=
      normalizedBlockResponseMaxFromFullCoarseBlock_eq_representativeFunctional_of_nonneg
        a0 _ (fun e _ =>
          fluxCorrected_rawCoarseBlock_normalizedQuadratic_nonneg M L m Q R a0 omega e)
    _ = fluxCorrectedNormalizedBlockResponseRepresentative M L m Q R a0 omega := by
      simpa [fluxCorrectedNormalizedBlockResponseRepresentative] using
        congrArg (normalizedBlockResponseMaxRepresentativeFunctional a0) hmatrix

/-- A single probability-one event identifies the literal normalized maximum
with its representative on *every* triadic cube. -/
theorem ae_forall_normalizedBlockResponseMax_fluxCorrected_eq_representative [NeZero d]
    (M : ABKModel d) (L m : ℤ) (Q : TriadicCube d) (a0 : Mat d) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ R : TriadicCube d,
        Ch02.normalizedBlockResponseMax R (fluxCorrectedCoeffFamily M L m Q omega) a0 =
          fluxCorrectedNormalizedBlockResponseRepresentative M L m Q R a0 omega :=
  MeasureTheory.ae_all_iff.2 fun R =>
    ae_normalizedBlockResponseMax_fluxCorrected_eq_representative M L m Q R a0

/-! ## The flux-corrected error representative -/

private theorem measurable_finset_sup' {Omega iota : Type*} [MeasurableSpace Omega]
    {S : Finset iota} (hS : S.Nonempty) {f : iota → Omega → ℝ}
    (hf : ∀ i ∈ S, Measurable (f i)) :
    Measurable (S.sup' hS f) :=
  Finset.sup'_induction (s := S) (H := hS) (f := f)
    (p := fun g => Measurable g)
    (fun _ hf' _ hg' => hf'.sup hg')
    (fun i hi => hf i hi)

/-- The finite descendant maximum of the flux-corrected coarse-block
representatives. -/
noncomputable def fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative
     (M : ABKModel d) (L m : ℤ) (Q : TriadicCube d) (k : ℤ)
    (a0 : Mat d) : Cutoff.CutoffSample d → ℝ  :=
  fun omega => Ch02.finsetSupReal (descendantsAtScale Q k)
    (fun R => fluxCorrectedNormalizedBlockResponseRepresentative M L m Q R a0 omega)

theorem measurable_fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative
     (M : ABKModel d) (L m : ℤ) (Q : TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) (a0 : Mat d) :
    Measurable
      (fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative M L m Q k a0)  := by
  classical
  have hS : (descendantsAtScale Q k).Nonempty := descendantsAtScale_nonempty Q hk
  have hsup : Measurable
      ((descendantsAtScale Q k).sup' hS
        (fun R => fluxCorrectedNormalizedBlockResponseRepresentative M L m Q R a0)) :=
    measurable_finset_sup' hS fun R _ =>
      measurable_fluxCorrectedNormalizedBlockResponseRepresentative M L m Q R a0
  have hfun : fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative M L m Q k a0 =
      (descendantsAtScale Q k).sup' hS
        (fun R => fluxCorrectedNormalizedBlockResponseRepresentative M L m Q R a0) := by
    funext omega
    rw [Finset.sup'_apply]
    exact RestrictionLawCarrier.finsetSupReal_eq_sup' (descendantsAtScale Q k) hS
      (fun R => fluxCorrectedNormalizedBlockResponseRepresentative M L m Q R a0 omega)
  rw [hfun]
  exact hsup

theorem fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative_nonneg
     (M : ABKModel d) (L m : ℤ) (Q : TriadicCube d) (k : ℤ) (a0 : Mat d)
    (omega : Cutoff.CutoffSample d) :
    0 ≤ fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative
      M L m Q k a0 omega  := by
  apply Ch02.finsetSupReal_nonneg
  intro R _
  exact fluxCorrectedNormalizedBlockResponseRepresentative_nonneg M L m Q R a0 omega

theorem measurable_tsum_of_nonneg
    {Omega : Type*} [MeasurableSpace Omega] (term : ℕ → Omega → ℝ)
    (hmeas : ∀ n, Measurable (term n)) (hnonneg : ∀ n omega, 0 ≤ term n omega) :
    Measurable (fun omega => ∑' n, term n omega) := by
  have hnn : Measurable (fun omega => ∑' n, (term n omega).toNNReal) :=
    Measurable.tsum (L := SummationFilter.unconditional ℕ) fun n =>
      (hmeas n).real_toNNReal
  have hnn := hnn.coe_nnreal_real
  convert hnn using 1
  funext omega
  rw [NNReal.coe_tsum]
  apply tsum_congr
  intro n
  rw [Real.toNNReal_of_nonneg (hnonneg n omega)]
  rfl

/-- The nonnegative everywhere-defined functional of the flux-corrected error.
Unlike the proved `(∞,2)` cutoff chain, no `A.mk` is needed at this layer:
every descendant maximum above is *genuinely* measurable, so the geometric
scale sum is too. -/
noncomputable def fluxCorrectedErrorFunctional (M : ABKModel d)
    (L k : ℤ) (s : ℝ) : Cutoff.CutoffSample d → ℝ  :=
  fun omega => Real.sqrt (∑' l : ℕ, Ch02.geometricWeight s 2 l *
    fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative M L k
      (originCube d k) ((originCube d k).scale - (l : ℤ))
      (isotropicComparatorMatrix (Annealed.sigmaBar M k)) omega)

private theorem fluxCorrectedErrorFunctional_term_nonneg (M : ABKModel d)
    (L k : ℤ) {s : ℝ} (hs : 0 < s) (l : ℕ) (omega : Cutoff.CutoffSample d) :
    0 ≤ Ch02.geometricWeight s 2 l *
      fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative M L k
        (originCube d k) ((originCube d k).scale - (l : ℤ))
        (isotropicComparatorMatrix (Annealed.sigmaBar M k)) omega  := by
  refine mul_nonneg ?_ ?_
  · simpa only [Ch02.geometricWeight_eq_old] using
      HCPolySupport.geometricWeight_nonneg l (by positivity : 0 ≤ s * (2 : ℝ))
  · exact fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative_nonneg
      M L k (originCube d k) ((originCube d k).scale - (l : ℤ))
      (isotropicComparatorMatrix (Annealed.sigmaBar M k)) omega

theorem fluxCorrectedErrorFunctional_nonneg (M : ABKModel d) (L k : ℤ)
    (s : ℝ) (omega : Cutoff.CutoffSample d) :
    0 ≤ fluxCorrectedErrorFunctional M L k s omega  :=
  Real.sqrt_nonneg _

theorem measurable_fluxCorrectedErrorFunctional (M : ABKModel d) (L k : ℤ) {s : ℝ} (hs : 0 < s) :
    Measurable (fluxCorrectedErrorFunctional M L k s)  := by
  have hterm : ∀ l : ℕ, Measurable
      (fun omega => Ch02.geometricWeight s 2 l *
        fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative M L k
          (originCube d k) ((originCube d k).scale - (l : ℤ))
          (isotropicComparatorMatrix (Annealed.sigmaBar M k)) omega) := fun l =>
    (measurable_fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative
      M L k (originCube d k)
      (sub_le_self _ (by exact_mod_cast Nat.zero_le l))
      (isotropicComparatorMatrix (Annealed.sigmaBar M k))).const_mul _
  exact Real.continuous_sqrt.measurable.comp
    (measurable_tsum_of_nonneg _ hterm
      (fluxCorrectedErrorFunctional_term_nonneg M L k hs))

/-- The paper-wide assumption `2 ≤ d`, stored in the model, supplies the
nonzero-dimension instance required by CoarseGraining's doubled-response A. -/
theorem neZero_of_model_FluxCorrectedRepresentative (M : ABKModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩

/-- The genuine measurable, nonnegative representative of the flux-corrected
`(∞,2)` error `𝓔_{s,∞,2}(□_k; a_L − (k_L − k_k)_{□_k}, σ_k Id)`. -/
noncomputable def fluxCorrectedErrorRepresentative (M : ABKModel d) (L k : ℤ)
    (s : {s : ℝ // 0 < s}) : Cutoff.CutoffSample d → ℝ := by
  letI : NeZero d := neZero_of_model_FluxCorrectedRepresentative M
  exact fluxCorrectedErrorFunctional M L k (s : ℝ)

theorem measurable_fluxCorrectedErrorRepresentative (M : ABKModel d) (L k : ℤ)
    (s : {s : ℝ // 0 < s}) :
    Measurable (fluxCorrectedErrorRepresentative M L k s) := by
  let : NeZero d := neZero_of_model_FluxCorrectedRepresentative M
  change Measurable (fluxCorrectedErrorFunctional M L k (s : ℝ))
  exact measurable_fluxCorrectedErrorFunctional M L k s.2

theorem fluxCorrectedErrorRepresentative_nonneg (M : ABKModel d) (L k : ℤ)
    (s : {s : ℝ // 0 < s}) (omega : Cutoff.CutoffSample d) :
    0 ≤ fluxCorrectedErrorRepresentative M L k s omega := by
  let : NeZero d := neZero_of_model_FluxCorrectedRepresentative M
  change 0 ≤ fluxCorrectedErrorFunctional M L k (s : ℝ) omega
  exact fluxCorrectedErrorFunctional_nonneg M L k (s : ℝ) omega

private theorem fluxCorrectedError_eq_functional_on_common_event [NeZero d]
    (M : ABKModel d) (L k : ℤ) {s : ℝ} (hs : 0 < s)
    (omega : Cutoff.CutoffSample d)
    (hall : ∀ R : TriadicCube d,
      Ch02.normalizedBlockResponseMax R
        (fluxCorrectedCoeffFamily M L k (originCube d k) omega)
        (isotropicComparatorMatrix (Annealed.sigmaBar M k)) =
      fluxCorrectedNormalizedBlockResponseRepresentative M L k (originCube d k) R
        (isotropicComparatorMatrix (Annealed.sigmaBar M k)) omega) :
    fluxCorrectedError M L k s omega = fluxCorrectedErrorFunctional M L k s omega := by
  have hsum_eq :
      (∑' l : ℕ, Ch02.geometricWeight s 2 l *
        Ch02.maxDescendantNormalizedBlockResponseAtScale (originCube d k)
          ((originCube d k).scale - (l : ℤ))
          (fluxCorrectedCoeffFamily M L k (originCube d k) omega)
          (isotropicComparatorMatrix (Annealed.sigmaBar M k))) =
      ∑' l : ℕ, Ch02.geometricWeight s 2 l *
        fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative M L k
          (originCube d k) ((originCube d k).scale - (l : ℤ))
          (isotropicComparatorMatrix (Annealed.sigmaBar M k)) omega :=
    tsum_congr fun l => congrArg (fun x => Ch02.geometricWeight s 2 l * x)
      (Ch02.finsetSupReal_congr _ fun R _ => hall R)
  have hsum_nonneg : 0 ≤ ∑' l : ℕ, Ch02.geometricWeight s 2 l *
      fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative M L k
        (originCube d k) ((originCube d k).scale - (l : ℤ))
        (isotropicComparatorMatrix (Annealed.sigmaBar M k)) omega :=
    tsum_nonneg fun l => fluxCorrectedErrorFunctional_term_nonneg M L k hs l omega
  have hrawsq : fluxCorrectedError M L k s omega ^ 2 =
      ∑' l : ℕ, Ch02.geometricWeight s 2 l *
        fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative M L k
          (originCube d k) ((originCube d k).scale - (l : ℤ))
          (isotropicComparatorMatrix (Annealed.sigmaBar M k)) omega := by
    rw [fluxCorrectedError_characterization,
      Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum (originCube d k) hs,
      hsum_eq]
  have hfuncsq : fluxCorrectedErrorFunctional M L k s omega ^ 2 =
      ∑' l : ℕ, Ch02.geometricWeight s 2 l *
        fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative M L k
          (originCube d k) ((originCube d k).scale - (l : ℤ))
          (isotropicComparatorMatrix (Annealed.sigmaBar M k)) omega :=
    Real.sq_sqrt hsum_nonneg
  calc
    fluxCorrectedError M L k s omega =
        Real.sqrt (fluxCorrectedError M L k s omega ^ 2) :=
      (Real.sqrt_sq (fluxCorrectedError_nonneg M L k hs omega)).symm
    _ = Real.sqrt (fluxCorrectedErrorFunctional M L k s omega ^ 2) := by
      rw [hrawsq, hfuncsq]
    _ = fluxCorrectedErrorFunctional M L k s omega :=
      Real.sqrt_sq (fluxCorrectedErrorFunctional_nonneg M L k s omega)

/-- The flux-corrected representative is almost everywhere exactly the literal
flux-corrected error of `ErrorAtoms`. -/
theorem fluxCorrectedError_ae_eq_representative (M : ABKModel d) (L k : ℤ)
    (s : {s : ℝ // 0 < s}) :
    @fluxCorrectedError d (neZero_of_model_FluxCorrectedRepresentative M) M L k (s : ℝ) =ᵐ[
        (Cutoff.cutoffSampleLaw M).toMeasure]
      fluxCorrectedErrorRepresentative M L k s := by
  let : NeZero d := neZero_of_model_FluxCorrectedRepresentative M
  change fluxCorrectedError M L k (s : ℝ) =ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure]
    fluxCorrectedErrorFunctional M L k (s : ℝ)
  filter_upwards [ae_forall_normalizedBlockResponseMax_fluxCorrected_eq_representative
    M L k (originCube d k) (isotropicComparatorMatrix (Annealed.sigmaBar M k))]
    with omega hall
  exact fluxCorrectedError_eq_functional_on_common_event M L k s.2 omega hall

/-! ## The public `sup_{L ≥ m}` observables -/

/-- The `sup_{L ≥ m} 𝓔_{s,∞,2}(□_m; a_L − (k_L − k_m)_{□_m}, σ_m Id)` of
`p.mathcalE.annular.decomp`, taken in `[0,∞]` so that no convergence side
condition enters the statement. -/
noncomputable def fluxCorrectedErrorObservableSup (M : ABKModel d) (m : ℤ)
    (s : {s : ℝ // 0 < s}) : Cutoff.CutoffSample d → ℝ≥0∞ :=
  fun omega => ⨆ L : {L : ℤ // m ≤ L},
    ENNReal.ofReal (fluxCorrectedErrorRepresentative M L.1 m s omega)

/-- The squared supremum `sup_{L ≥ m} 𝓔_{s,∞,2}(…)²`, the left-hand side of the
main display of `p.mathcalE.annular.decomp` read literally (the square is
inside the supremum, as printed). -/
noncomputable def fluxCorrectedErrorObservableSqSup (M : ABKModel d) (m : ℤ)
    (s : {s : ℝ // 0 < s}) : Cutoff.CutoffSample d → ℝ≥0∞ :=
  fun omega => ⨆ L : {L : ℤ // m ≤ L},
    ENNReal.ofReal (fluxCorrectedErrorRepresentative M L.1 m s omega ^ 2)

theorem measurable_fluxCorrectedErrorObservableSup (M : ABKModel d) (m : ℤ)
    (s : {s : ℝ // 0 < s}) :
    Measurable (fluxCorrectedErrorObservableSup M m s) :=
  Measurable.iSup fun L =>
    (measurable_fluxCorrectedErrorRepresentative M L.1 m s).ennreal_ofReal

theorem le_fluxCorrectedErrorObservableSup (M : ABKModel d) (m : ℤ)
    (s : {s : ℝ // 0 < s}) (omega : Cutoff.CutoffSample d) {L : ℤ} (hL : m ≤ L) :
    ENNReal.ofReal (fluxCorrectedErrorRepresentative M L m s omega) ≤
      fluxCorrectedErrorObservableSup M m s omega :=
  le_iSup
    (fun L : {L : ℤ // m ≤ L} =>
      ENNReal.ofReal (fluxCorrectedErrorRepresentative M L.1 m s omega)) ⟨L, hL⟩

theorem fluxCorrectedErrorObservableSup_le (M : ABKModel d) (m : ℤ)
    (s : {s : ℝ // 0 < s}) (omega : Cutoff.CutoffSample d) {t : ℝ≥0∞}
    (h : ∀ L : ℤ, m ≤ L →
      ENNReal.ofReal (fluxCorrectedErrorRepresentative M L m s omega) ≤ t) :
    fluxCorrectedErrorObservableSup M m s omega ≤ t :=
  iSup_le fun L => h L.1 L.2

/-- A single probability-one event carries the per-`L` identities
simultaneously, because the index set is countable. -/
theorem ae_forall_fluxCorrectedError_eq_representative (M : ABKModel d) (m : ℤ)
    (s : {s : ℝ // 0 < s}) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ L : {L : ℤ // m ≤ L},
        @fluxCorrectedError d (neZero_of_model_FluxCorrectedRepresentative M) M L.1 m (s : ℝ)
          omega =
          fluxCorrectedErrorRepresentative M L.1 m s omega :=
  MeasureTheory.ae_all_iff.2 fun L =>
    fluxCorrectedError_ae_eq_representative M L.1 m s

end

end Algsuperdiff.Section4.Support

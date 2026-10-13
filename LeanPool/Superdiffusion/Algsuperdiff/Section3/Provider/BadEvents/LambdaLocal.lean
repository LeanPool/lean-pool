/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.Definitions
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.CoefficientLocality
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Internal.AEESliceAssembly.CarrierMuFamily

/-!
# LambdaLocal

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Integral-local measurability of the multiscale ellipticity of the actual cutoff

CoarseGraining's ambient observables `Ch04.lambdaSqCoeffField` /
`Ch04.LambdaSqCoeffField` are defined by a *global* dichotomy: `if h: A a`, a
condition quantified over **every** triadic cube of `R^d`
(`Homogenization/Book/Ch04/Law.lean`).  Read on an arbitrary coefficient field
this destroys locality.  On the *actual cutoff samples* it does not: every
`omega : CutoffSample d` satisfies the dichotomy
(`Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField`), so the branch is
always the `Ch02` branch and the observable reads only the descendant tree of
its cube.

This module turns that observation into genuine measurability for the
integral-local information of the cutoff sample space.  Nothing is a.e.: the
whole chain

```
Mu  ->  coarseBlockMatrix entries  ->  operator norms  ->  descendant maxima
    ->  weighted series           ->  lambda_{s,q}^{-1}, Lambda_{s,q}
```

is proved `Cutoff.cutoffSampleLocalSigma M m U`-measurable for every `U`
containing the closed cube, by re-running CoarseGraining's own A `Mu` engine
(`measurable_Mu_comp_aeeSlice_of_measurable_entryTest`) on the
*everywhere*-valid slice cover of the cutoff samples.  No CoarseGraining file
is changed.

The only a.e. step is the very last one, and it is forced by the *definition*
of `badLoc`: `Provider/BadEvents/CubeEllipticity.lean` totalizes the multiscale
ellipticity observables through `A.mk` representatives, which are determined
only up to a null set.  `measurableSet_cutoffSampleLocalSigma_of_ae_eq` below
shows that the cutoff-sample local sigma-field — a `comap` of the *completed*
lower-shell local sigma-field — is closed under almost-everywhere modification,
which is exactly what absorbs that step.

## Main results

* `measurable_Mu_coefficientCutoff_cutoffSampleLocal`: genuine locality of the
  coarse-grained energy of the actual cutoff.
* `measurable_cubeLowerEllipticityInvLiteral_cutoffSampleLocal`,
  `measurable_cubeUpperEllipticityLiteral_cutoffSampleLocal`: genuine locality
  of the *literal* multiscale ellipticity observables of the actual cutoff.
* `measurableSet_cutoffSampleLocalSigma_of_ae_eq`: the cutoff-sample local
  sigma-field is closed under a.e. modification.
* `measurableSet_badLoc_cutoffSampleLocal`: `e.Bloc.def` at the cube `Q` is
  measurable for the integral-local information of any set containing the
  closed cube `Q`, at shell index `Q.scale`.

## Range constants (disclosed)

The whole chain is stated for an arbitrary observation set `U` with
`cubeSet Q ⊆ U`: the descendant tree of `Q` used by `lambda_{s,q}` and
`Lambda_{s,q}` consists of cubes `R ⊆ Q`, so nothing outside the closed cube
is ever read.

## References

* ABK26, `e.Bloc.def`.
* ABK26, (2.22)--(2.23).
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## Genuine locality of the coarse-grained energy of the actual cutoff -/

/-- **The coarse-grained energy of the actual cutoff is integral-local.**  The A
quantitative slices of `cubeSet R` cover *all* cutoff samples, because every
cutoff sample is a locally a.e.-uniformly elliptic field; each slice is
`LocalSigmaR (cubeSet R)`-measurable and CoarseGraining's carrier `Mu` engine
is measurable on it, so the genuine cover assembles with no null bookkeeping. -/
theorem measurable_Mu_coefficientCutoff_cutoffSampleLocal (M : ABKModel d) (m : ℤ)
    (R : TriadicCube d) {U : Set (Vec d)} (hRU : cubeSet R ⊆ U) (P0 : BlockVec d) :
    @Measurable (CutoffSample d) ℝ (cutoffSampleLocalSigma M m U) _
      (fun omega => Mu (cubeSet R) P0 (coefficientCutoff M.nu m omega).toFun) := by
  classical
  let : MeasurableSpace (CutoffSample d) := cutoffSampleLocalSigma M m U
  set cover : ℕ → Set (CutoffSample d) := fun k =>
    {omega : CutoffSample d |
      AEEQuantitativeEllipticSlice (cubeSet R) k
        (coefficientCutoff M.nu m omega).toFun} with hcoverdef
  have hcm : ∀ k : ℕ, MeasurableSet (cover k) := by
    intro k
    have hloc : @MeasurableSet (RegCoeffField d) (LocalSigmaR U)
        {a : RegCoeffField d | AEEQuantitativeEllipticSlice (cubeSet R) k a.toFun} :=
      HCPolySupport.localSigmaR_mono hRU _
        (Ch04.measurableSet_localSigmaR_aeeQuantitativeEllipticSlice R k)
    exact measurable_coefficientCutoff_local M m U hloc
  have hcover : (⋃ k : ℕ, cover k) = Set.univ := by
    ext omega
    refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
    obtain ⟨k, hk⟩ :=
      (coefficientCutoff_aeLocallyUniformlyEllipticField M m
        omega).exists_aeeQuantitativeEllipticSlice_cubeSet R
    exact Set.mem_iUnion.2 ⟨k, hk⟩
  set f : (k : ℕ) → cover k → ℝ := fun _k x =>
    Mu (cubeSet R) P0 (coefficientCutoff M.nu m (x : CutoffSample d)).toFun with hfdef
  have hagree : ∀ (i j : ℕ) (x : CutoffSample d) (hxi : x ∈ cover i) (hxj : x ∈ cover j),
      f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩ := fun _ _ _ _ _ => rfl
  have hfm : ∀ k : ℕ, Measurable (f k) := by
    intro k
    refine HCPolySupport.measurable_Mu_comp_aeeSlice_of_measurable_entryTest
      (k := k) R (A := fun x : cover k => coefficientCutoff M.nu m (x : CutoffSample d))
      (fun x => x.2) ?_ P0
    intro i j φ hφ_cont hφ_compact hsupp
    have hφ_probe : IsProbeR φ := IsProbeR.of_smooth hφ_cont hφ_compact
    have hφ_support : Function.support φ ⊆ U :=
      ((Function.support_subset_iff.2 fun x hx => subset_tsupport φ hx).trans hsupp).trans hRU
    exact ((HCPolySupport.measurable_entryTestR_localSigmaR i j hφ_probe
        hφ_support).comp (measurable_coefficientCutoff_local M m U)).comp
      measurable_subtype_coe
  have heq : (fun omega : CutoffSample d =>
      Mu (cubeSet R) P0 (coefficientCutoff M.nu m omega).toFun) =
      Set.liftCover cover f hagree hcover := by
    funext omega
    have hmem : omega ∈ ⋃ k : ℕ, cover k := by rw [hcover]; exact Set.mem_univ _
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hmem
    exact (Set.liftCover_of_mem (S := cover) (f := f) (hf := hagree) (hS := hcover)
      (i := k) hk).symm
  rw [heq]
  exact measurable_liftCover cover hcm f hfm hagree hcover

/-- Every entry of the lower-right coarse block `sigma_*^{-1}` of the actual cutoff
is integral-local.  This is CoarseGraining's finite polarization identity, run
at genuine measurability. -/
theorem measurable_coarseSigmaStarInv_apply_cutoffSampleLocal (M : ABKModel d) (m : ℤ)
    (R : TriadicCube d) {U : Set (Vec d)} (hRU : cubeSet R ⊆ U) (i j : Fin d) :
    @Measurable (CutoffSample d) ℝ (cutoffSampleLocalSigma M m U) _
      (fun omega =>
        (coarseBlockMatrix (cubeSet R)
          (coefficientCutoff M.nu m omega).toFun).lowerRight i j) := by
  let : MeasurableSpace (CutoffSample d) := cutoffSampleLocalSigma M m U
  by_cases hij : i = j
  · subst hij
    have hEq : (fun omega : CutoffSample d =>
        (coarseBlockMatrix (cubeSet R)
          (coefficientCutoff M.nu m omega).toFun).lowerRight i i) =
        fun omega : CutoffSample d => (2 : ℝ) *
          Mu (cubeSet R) (0, Pi.single i 1) (coefficientCutoff M.nu m omega).toFun := by
      funext omega
      simp [coarseBlockMatrix_lowerRight_apply]
    rw [hEq]
    exact (measurable_Mu_coefficientCutoff_cutoffSampleLocal M m R hRU
      (0, Pi.single i 1)).const_mul (2 : ℝ)
  · have hEq : (fun omega : CutoffSample d =>
        (coarseBlockMatrix (cubeSet R)
          (coefficientCutoff M.nu m omega).toFun).lowerRight i j) =
        fun omega : CutoffSample d =>
          Mu (cubeSet R) ((0, Pi.single i 1) + (0, Pi.single j 1))
              (coefficientCutoff M.nu m omega).toFun -
            Mu (cubeSet R) (0, Pi.single i 1) (coefficientCutoff M.nu m omega).toFun -
            Mu (cubeSet R) (0, Pi.single j 1) (coefficientCutoff M.nu m omega).toFun := by
      funext omega
      simp [coarseBlockMatrix_lowerRight_apply, hij]
    rw [hEq]
    exact ((measurable_Mu_coefficientCutoff_cutoffSampleLocal M m R hRU _).sub
      (measurable_Mu_coefficientCutoff_cutoffSampleLocal M m R hRU _)).sub
      (measurable_Mu_coefficientCutoff_cutoffSampleLocal M m R hRU _)

/-- Every entry of the upper-left coarse block `b` of the actual cutoff is
integral-local. -/
theorem measurable_coarseB_apply_cutoffSampleLocal (M : ABKModel d) (m : ℤ)
    (R : TriadicCube d) {U : Set (Vec d)} (hRU : cubeSet R ⊆ U) (i j : Fin d) :
    @Measurable (CutoffSample d) ℝ (cutoffSampleLocalSigma M m U) _
      (fun omega =>
        (coarseBlockMatrix (cubeSet R)
          (coefficientCutoff M.nu m omega).toFun).upperLeft i j) := by
  let : MeasurableSpace (CutoffSample d) := cutoffSampleLocalSigma M m U
  by_cases hij : i = j
  · subst hij
    have hEq : (fun omega : CutoffSample d =>
        (coarseBlockMatrix (cubeSet R)
          (coefficientCutoff M.nu m omega).toFun).upperLeft i i) =
        fun omega : CutoffSample d => (2 : ℝ) *
          Mu (cubeSet R) (Pi.single i 1, 0) (coefficientCutoff M.nu m omega).toFun := by
      funext omega
      simp [coarseBlockMatrix_upperLeft_apply]
    rw [hEq]
    exact (measurable_Mu_coefficientCutoff_cutoffSampleLocal M m R hRU
      (Pi.single i 1, 0)).const_mul (2 : ℝ)
  · have hEq : (fun omega : CutoffSample d =>
        (coarseBlockMatrix (cubeSet R)
          (coefficientCutoff M.nu m omega).toFun).upperLeft i j) =
        fun omega : CutoffSample d =>
          Mu (cubeSet R) ((Pi.single i 1, 0) + (Pi.single j 1, 0))
              (coefficientCutoff M.nu m omega).toFun -
            Mu (cubeSet R) (Pi.single i 1, 0) (coefficientCutoff M.nu m omega).toFun -
            Mu (cubeSet R) (Pi.single j 1, 0) (coefficientCutoff M.nu m omega).toFun := by
      funext omega
      simp [coarseBlockMatrix_upperLeft_apply, hij]
    rw [hEq]
    exact ((measurable_Mu_coefficientCutoff_cutoffSampleLocal M m R hRU _).sub
      (measurable_Mu_coefficientCutoff_cutoffSampleLocal M m R hRU _)).sub
      (measurable_Mu_coefficientCutoff_cutoffSampleLocal M m R hRU _)

/-- The `L^2` operator norm of the lower-right coarse block is integral-local. -/
theorem measurable_coarseSigmaStarInvNorm_cutoffSampleLocal (M : ABKModel d) (m : ℤ)
    (R : TriadicCube d) {U : Set (Vec d)} (hRU : cubeSet R ⊆ U) :
    @Measurable (CutoffSample d) ℝ (cutoffSampleLocalSigma M m U) _
      (fun omega => Ch02.matrixNorm
        (coarseBlockMatrix (cubeSet R)
          (coefficientCutoff M.nu m omega).toFun).lowerRight) := by
  let : MeasurableSpace (CutoffSample d) := cutoffSampleLocalSigma M m U
  have hmat : @Measurable (CutoffSample d) (Mat d) _ _
      (fun omega => (coarseBlockMatrix (cubeSet R)
        (coefficientCutoff M.nu m omega).toFun).lowerRight) := by
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    exact measurable_coarseSigmaStarInv_apply_cutoffSampleLocal M m R hRU i j
  simpa [Ch02.matrixNorm, Matrix.l2_opNorm_toEuclideanCLM] using hmat.norm

/-- The `L^2` operator norm of the upper-left coarse block is integral-local. -/
theorem measurable_coarseBNorm_cutoffSampleLocal (M : ABKModel d) (m : ℤ)
    (R : TriadicCube d) {U : Set (Vec d)} (hRU : cubeSet R ⊆ U) :
    @Measurable (CutoffSample d) ℝ (cutoffSampleLocalSigma M m U) _
      (fun omega => Ch02.matrixNorm
        (coarseBlockMatrix (cubeSet R)
          (coefficientCutoff M.nu m omega).toFun).upperLeft) := by
  let : MeasurableSpace (CutoffSample d) := cutoffSampleLocalSigma M m U
  have hmat : @Measurable (CutoffSample d) (Mat d) _ _
      (fun omega => (coarseBlockMatrix (cubeSet R)
        (coefficientCutoff M.nu m omega).toFun).upperLeft) := by
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    exact measurable_coarseB_apply_cutoffSampleLocal M m R hRU i j
  simpa [Ch02.matrixNorm, Matrix.l2_opNorm_toEuclideanCLM] using hmat.norm

/-! ## Descendant maxima and the weighted series -/

private theorem measurable_finset_sup' {Omega iota : Type*} [MeasurableSpace Omega]
    {S : Finset iota} (hS : S.Nonempty) {f : iota → Omega → ℝ}
    (hf : ∀ i ∈ S, Measurable (f i)) :
    Measurable (S.sup' hS f) :=
  Finset.sup'_induction (s := S) (H := hS) (f := f) (p := fun g => Measurable g)
    (fun _ hf' _ hg' => hf'.sup hg') (fun i hi => hf i hi)

section NeZeroSection

variable [NeZero d]

/-- The descendant maximum of `|sigma_*^{-1}|` of the actual cutoff is
integral-local: every descendant of `R` is a subcube of `R`. -/
theorem measurable_maxDescendantSigmaStarInv_cutoffSampleLocal (M : ABKModel d) (m : ℤ)
    (R : TriadicCube d) {U : Set (Vec d)} (hRU : cubeSet R ⊆ U) (n : ℕ) :
    @Measurable (CutoffSample d) ℝ (cutoffSampleLocalSigma M m U) _
      (fun omega => Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
        R (R.scale - (n : ℤ)) (coefficientCutoff M.nu m omega)) := by
  classical
  let : MeasurableSpace (CutoffSample d) := cutoffSampleLocalSigma M m U
  have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
  have hle : R.scale - (n : ℤ) ≤ R.scale := sub_le_self R.scale hn
  set S := descendantsAtScale R (R.scale - (n : ℤ)) with hSdef
  have hS : S.Nonempty := descendantsAtScale_nonempty R hle
  have hsup : Measurable (S.sup' hS (fun R' (omega : CutoffSample d) =>
      Ch02.matrixNorm (coarseBlockMatrix (cubeSet R')
        (coefficientCutoff M.nu m omega).toFun).lowerRight)) := by
    refine measurable_finset_sup' hS ?_
    intro R' hR'
    exact measurable_coarseSigmaStarInvNorm_cutoffSampleLocal M m R'
      ((cubeSet_subset_of_mem_descendantsAtScale hle hR').trans hRU)
  have hfin : Measurable (fun omega : CutoffSample d => Ch02.finsetSupReal S
      (fun R' => Ch02.matrixNorm (coarseBlockMatrix (cubeSet R')
        (coefficientCutoff M.nu m omega).toFun).lowerRight)) := by
    convert hsup using 1
    ext omega
    rw [Finset.sup'_apply]
    exact Ch04.RestrictionLawCarrier.finsetSupReal_eq_sup' S hS
      (fun R' => Ch02.matrixNorm (coarseBlockMatrix (cubeSet R')
        (coefficientCutoff M.nu m omega).toFun).lowerRight)
  have heq : (fun omega : CutoffSample d =>
      Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
        R (R.scale - (n : ℤ)) (coefficientCutoff M.nu m omega)) =
      fun omega : CutoffSample d => Ch02.finsetSupReal S
        (fun R' => Ch02.matrixNorm (coarseBlockMatrix (cubeSet R')
          (coefficientCutoff M.nu m omega).toFun).lowerRight) := by
    funext omega
    exact Ch04.RestrictionLawCarrier.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_eq_finsetSupReal_ae
      (coefficientCutoff_aeLocallyUniformlyEllipticField M m omega) R (R.scale - (n : ℤ))
  rw [heq]
  exact hfin

/-- The descendant maximum of `|b|` of the actual cutoff is integral-local. -/
theorem measurable_maxDescendantB_cutoffSampleLocal (M : ABKModel d) (m : ℤ)
    (R : TriadicCube d) {U : Set (Vec d)} (hRU : cubeSet R ⊆ U) (n : ℕ) :
    @Measurable (CutoffSample d) ℝ (cutoffSampleLocalSigma M m U) _
      (fun omega => Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
        R (R.scale - (n : ℤ)) (coefficientCutoff M.nu m omega)) := by
  classical
  let : MeasurableSpace (CutoffSample d) := cutoffSampleLocalSigma M m U
  have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
  have hle : R.scale - (n : ℤ) ≤ R.scale := sub_le_self R.scale hn
  set S := descendantsAtScale R (R.scale - (n : ℤ)) with hSdef
  have hS : S.Nonempty := descendantsAtScale_nonempty R hle
  have hsup : Measurable (S.sup' hS (fun R' (omega : CutoffSample d) =>
      Ch02.matrixNorm (coarseBlockMatrix (cubeSet R')
        (coefficientCutoff M.nu m omega).toFun).upperLeft)) := by
    refine measurable_finset_sup' hS ?_
    intro R' hR'
    exact measurable_coarseBNorm_cutoffSampleLocal M m R'
      ((cubeSet_subset_of_mem_descendantsAtScale hle hR').trans hRU)
  have hfin : Measurable (fun omega : CutoffSample d => Ch02.finsetSupReal S
      (fun R' => Ch02.matrixNorm (coarseBlockMatrix (cubeSet R')
        (coefficientCutoff M.nu m omega).toFun).upperLeft)) := by
    convert hsup using 1
    ext omega
    rw [Finset.sup'_apply]
    exact Ch04.RestrictionLawCarrier.finsetSupReal_eq_sup' S hS
      (fun R' => Ch02.matrixNorm (coarseBlockMatrix (cubeSet R')
        (coefficientCutoff M.nu m omega).toFun).upperLeft)
  have heq : (fun omega : CutoffSample d =>
      Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
        R (R.scale - (n : ℤ)) (coefficientCutoff M.nu m omega)) =
      fun omega : CutoffSample d => Ch02.finsetSupReal S
        (fun R' => Ch02.matrixNorm (coarseBlockMatrix (cubeSet R')
          (coefficientCutoff M.nu m omega).toFun).upperLeft) := by
    funext omega
    exact Ch04.RestrictionLawCarrier.maxDescendantBMatrixNormCoeffFieldAtScale_eq_finsetSupReal_ae
      (coefficientCutoff_aeLocallyUniformlyEllipticField M m omega) R (R.scale - (n : ℤ))
  rw [heq]
  exact hfin

/-! ### The weighted descendant series -/

theorem measurable_weightedSigmaSeries_cutoffSampleLocal (M : ABKModel d) (m : ℤ)
    (R : TriadicCube d) {U : Set (Vec d)} (hRU : cubeSet R ⊆ U) {s q : ℝ}
    (hs : 0 < s) (hq : 0 < q) :
    @Measurable (CutoffSample d) ℝ (cutoffSampleLocalSigma M m U) _
      (fun omega => ∑' n : ℕ, Ch02.geometricWeight s q n *
        Real.rpow (Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
          R (R.scale - (n : ℤ)) (coefficientCutoff M.nu m omega)) (q / 2)) := by
  let : MeasurableSpace (CutoffSample d) := cutoffSampleLocalSigma M m U
  refine measurable_of_tendsto_metrizable
    (f := fun N (omega : CutoffSample d) => ∑ n ∈ Finset.range N,
      Ch02.geometricWeight s q n *
        Real.rpow (Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
          R (R.scale - (n : ℤ)) (coefficientCutoff M.nu m omega)) (q / 2)) ?_ ?_
  · intro N
    refine Finset.measurable_sum _ fun n _ => ?_
    have hrpow : Measurable (fun x : ℝ => Real.rpow x (q / 2)) :=
      (Real.continuous_rpow_const (by positivity)).measurable
    exact (hrpow.comp
      (measurable_maxDescendantSigmaStarInv_cutoffSampleLocal M m R hRU n)).const_mul _
  · refine tendsto_pi_nhds.2 fun omega => ?_
    have ha := coefficientCutoff_aeLocallyUniformlyEllipticField M m omega
    simpa [Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale, ha] using
      HasSum.tendsto_sum_nat
        (Ch02.summable_sigmaStarInv_series_pointwiseCoeffField R
          (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
            (coefficientCutoff M.nu m omega) ha) hs hq).hasSum

theorem measurable_weightedBSeries_cutoffSampleLocal (M : ABKModel d) (m : ℤ)
    (R : TriadicCube d) {U : Set (Vec d)} (hRU : cubeSet R ⊆ U) {s q : ℝ}
    (hs : 0 < s) (hq : 0 < q) :
    @Measurable (CutoffSample d) ℝ (cutoffSampleLocalSigma M m U) _
      (fun omega => ∑' n : ℕ, Ch02.geometricWeight s q n *
        Real.rpow (Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
          R (R.scale - (n : ℤ)) (coefficientCutoff M.nu m omega)) (q / 2)) := by
  let : MeasurableSpace (CutoffSample d) := cutoffSampleLocalSigma M m U
  refine measurable_of_tendsto_metrizable
    (f := fun N (omega : CutoffSample d) => ∑ n ∈ Finset.range N,
      Ch02.geometricWeight s q n *
        Real.rpow (Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
          R (R.scale - (n : ℤ)) (coefficientCutoff M.nu m omega)) (q / 2)) ?_ ?_
  · intro N
    refine Finset.measurable_sum _ fun n _ => ?_
    have hrpow : Measurable (fun x : ℝ => Real.rpow x (q / 2)) :=
      (Real.continuous_rpow_const (by positivity)).measurable
    exact (hrpow.comp
      (measurable_maxDescendantB_cutoffSampleLocal M m R hRU n)).const_mul _
  · refine tendsto_pi_nhds.2 fun omega => ?_
    have ha := coefficientCutoff_aeLocallyUniformlyEllipticField M m omega
    simpa [Ch04.maxDescendantBMatrixNormCoeffFieldAtScale, ha] using
      HasSum.tendsto_sum_nat
        (Ch02.summable_B_series_pointwiseCoeffField R
          (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
            (coefficientCutoff M.nu m omega) ha) hs hq).hasSum

/-! ### The multiscale ellipticity observables of the actual cutoff -/

private theorem lambdaSqCoeffField_finite_inv_eq (R : TriadicCube d) {s q : ℝ}
    (hs : 0 ≤ s) (hq : 1 ≤ q) {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a) :
    (Ch04.lambdaSqCoeffField R s (.finite q) a)⁻¹ =
      Real.rpow (∑' n : ℕ, Ch02.geometricWeight s q n *
        Real.rpow (Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
          R (R.scale - (n : ℤ)) a) (q / 2)) (2 / q) := by
  simp only [Ch04.lambdaSqCoeffField, Ch02.lambdaSq_finite, Ch02.lambdaSqFinite,
    Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale, dite_eq_left ha]
  set F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha with hF
  set S : ℝ := ∑' n : ℕ, Ch02.geometricWeight s q n *
    Real.rpow (Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
      R (R.scale - (n : ℤ)) F) (q / 2) with hSdef
  have hS : 0 ≤ S := by
    rw [hSdef]
    exact Ch02.lambdaSqFinite_series_nonneg R s q F (le_trans zero_le_one hq)
      (mul_nonneg hs (le_trans zero_le_one hq))
  change (Real.rpow S (-(2 / q)))⁻¹ = Real.rpow S (2 / q)
  have hneg : Real.rpow S (-(2 / q)) = (Real.rpow S (2 / q))⁻¹ := Real.rpow_neg hS (2 / q)
  rw [hneg, inv_inv]

private theorem LambdaSqCoeffField_finite_eq (R : TriadicCube d) (s q : ℝ)
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a) :
    Ch04.LambdaSqCoeffField R s (.finite q) a =
      Real.rpow (∑' n : ℕ, Ch02.geometricWeight s q n *
        Real.rpow (Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
          R (R.scale - (n : ℤ)) a) (q / 2)) (2 / q) := by
  simp [Ch04.LambdaSqCoeffField, Ch02.LambdaSqFinite,
    Ch04.maxDescendantBMatrixNormCoeffFieldAtScale, ha]

private theorem lambdaSqCoeffField_infinity_inv_eq (R : TriadicCube d) (s : ℝ)
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a) :
    (Ch04.lambdaSqCoeffField R s .infinity a)⁻¹ =
      ⨆ n : ℕ, Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
        Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale R (R.scale - (n : ℤ)) a := by
  simp only [Ch04.lambdaSqCoeffField, Ch02.lambdaSq_infinity, Ch02.lambdaSqInfinity,
    Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale, dite_eq_left ha, iSup, inv_inv]
  congr 1
  ext x
  constructor <;> rintro ⟨n, hn⟩ <;> exact ⟨n, hn.symm⟩

private theorem LambdaSqCoeffField_infinity_eq (R : TriadicCube d) (s : ℝ)
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a) :
    Ch04.LambdaSqCoeffField R s .infinity a =
      ⨆ n : ℕ, Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
        Ch04.maxDescendantBMatrixNormCoeffFieldAtScale R (R.scale - (n : ℤ)) a := by
  simp only [Ch04.LambdaSqCoeffField, Ch02.LambdaSq_infinity, Ch02.LambdaSqInfinity,
    Ch04.maxDescendantBMatrixNormCoeffFieldAtScale, dite_eq_left ha, iSup]
  congr 1
  ext x
  constructor <;> rintro ⟨n, hn⟩ <;> exact ⟨n, hn.symm⟩

end NeZeroSection

/-- **The literal inverse lower multiscale ellipticity of the actual cutoff is
integral-local.**  Everything the observable reads lives in the descendant tree
of `R`, hence inside any `U` containing the closed cube. -/
theorem measurable_cubeLowerEllipticityInvLiteral_cutoffSampleLocal (M : ABKModel d)
    (m : ℤ) (R : TriadicCube d) {U : Set (Vec d)} (hRU : cubeSet R ⊆ U) {s : ℝ}
    (hs : 0 < s) (q : CoarseEllipticityExponent) :
    @Measurable (CutoffSample d) ℝ (cutoffSampleLocalSigma M m U) _
      (cubeLowerEllipticityInvLiteral M R m s q) := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega : 0 < 2) M.shellPrefix.dimension)⟩
  let : MeasurableSpace (CutoffSample d) := cutoffSampleLocalSigma M m U
  have hfun : cubeLowerEllipticityInvLiteral M R m s q =
      fun omega : CutoffSample d =>
        (Ch04.lambdaSqCoeffField R s q.1 (coefficientCutoff M.nu m omega))⁻¹ := rfl
  rw [hfun]
  obtain ⟨q1, hq1⟩ := q
  cases q1 with
  | finite qq =>
      have hqq : (1 : ℝ) ≤ qq := hq1
      have heq : (fun omega : CutoffSample d =>
          (Ch04.lambdaSqCoeffField R s (.finite qq)
            (coefficientCutoff M.nu m omega))⁻¹) =
          fun omega : CutoffSample d => Real.rpow (∑' n : ℕ,
            Ch02.geometricWeight s qq n *
              Real.rpow (Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
                R (R.scale - (n : ℤ)) (coefficientCutoff M.nu m omega)) (qq / 2))
            (2 / qq) := by
        funext omega
        exact lambdaSqCoeffField_finite_inv_eq R hs.le hqq
          (coefficientCutoff_aeLocallyUniformlyEllipticField M m omega)
      rw [heq]
      have hrpow : Measurable (fun x : ℝ => Real.rpow x (2 / qq)) :=
        (Real.continuous_rpow_const (by positivity)).measurable
      exact hrpow.comp (measurable_weightedSigmaSeries_cutoffSampleLocal M m R hRU hs
        (lt_of_lt_of_le zero_lt_one hqq))
  | infinity =>
      have heq : (fun omega : CutoffSample d =>
          (Ch04.lambdaSqCoeffField R s .infinity
            (coefficientCutoff M.nu m omega))⁻¹) =
          fun omega : CutoffSample d => ⨆ n : ℕ,
            Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
              Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
                R (R.scale - (n : ℤ)) (coefficientCutoff M.nu m omega) := by
        funext omega
        exact lambdaSqCoeffField_infinity_inv_eq R s
          (coefficientCutoff_aeLocallyUniformlyEllipticField M m omega)
      rw [heq]
      exact Measurable.iSup fun n =>
        (measurable_maxDescendantSigmaStarInv_cutoffSampleLocal M m R hRU n).const_mul _

/-- **The literal upper multiscale ellipticity of the actual cutoff is
integral-local.** -/
theorem measurable_cubeUpperEllipticityLiteral_cutoffSampleLocal (M : ABKModel d)
    (m : ℤ) (R : TriadicCube d) {U : Set (Vec d)} (hRU : cubeSet R ⊆ U) {s : ℝ}
    (hs : 0 < s) (q : CoarseEllipticityExponent) :
    @Measurable (CutoffSample d) ℝ (cutoffSampleLocalSigma M m U) _
      (cubeUpperEllipticityLiteral M R m s q) := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega : 0 < 2) M.shellPrefix.dimension)⟩
  let : MeasurableSpace (CutoffSample d) := cutoffSampleLocalSigma M m U
  have hfun : cubeUpperEllipticityLiteral M R m s q =
      fun omega : CutoffSample d =>
        Ch04.LambdaSqCoeffField R s q.1 (coefficientCutoff M.nu m omega) := rfl
  rw [hfun]
  obtain ⟨q1, hq1⟩ := q
  cases q1 with
  | finite qq =>
      have hqq : (1 : ℝ) ≤ qq := hq1
      have heq : (fun omega : CutoffSample d =>
          Ch04.LambdaSqCoeffField R s (.finite qq)
            (coefficientCutoff M.nu m omega)) =
          fun omega : CutoffSample d => Real.rpow (∑' n : ℕ,
            Ch02.geometricWeight s qq n *
              Real.rpow (Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
                R (R.scale - (n : ℤ)) (coefficientCutoff M.nu m omega)) (qq / 2))
            (2 / qq) := by
        funext omega
        exact LambdaSqCoeffField_finite_eq R s qq
          (coefficientCutoff_aeLocallyUniformlyEllipticField M m omega)
      rw [heq]
      have hrpow : Measurable (fun x : ℝ => Real.rpow x (2 / qq)) :=
        (Real.continuous_rpow_const (by positivity)).measurable
      exact hrpow.comp (measurable_weightedBSeries_cutoffSampleLocal M m R hRU hs
        (lt_of_lt_of_le zero_lt_one hqq))
  | infinity =>
      have heq : (fun omega : CutoffSample d =>
          Ch04.LambdaSqCoeffField R s .infinity
            (coefficientCutoff M.nu m omega)) =
          fun omega : CutoffSample d => ⨆ n : ℕ,
            Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
              Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
                R (R.scale - (n : ℤ)) (coefficientCutoff M.nu m omega) := by
        funext omega
        exact LambdaSqCoeffField_infinity_eq R s
          (coefficientCutoff_aeLocallyUniformlyEllipticField M m omega)
      rw [heq]
      exact Measurable.iSup fun n =>
        (measurable_maxDescendantB_cutoffSampleLocal M m R hRU n).const_mul _

/-! ## Monotonicity and a.e. stability of the cutoff-sample local sigma-fields -/

/-- The lower-shell local sigma-field is monotone in the shell index and in the
observation region. -/
theorem lowerShellLocalSigma_mono {m n : ℤ} (hmn : m ≤ n) {U V : Set (Vec d)}
    (hUV : U ⊆ V) : lowerShellLocalSigma (d := d) m U ≤ lowerShellLocalSigma n V := by
  refine iSup_le fun r => ?_
  have hindex : n - (((n - m).toNat + r : ℕ) : ℤ) = m - (r : ℤ) := by
    have : (((n - m).toNat : ℤ)) = n - m := Int.toNat_of_nonneg (by omega)
    push_cast
    omega
  have hcomp : (ShellField.lihLocalSigma U).comap
      (fun omega : ShellSeq d => omega (m - (r : ℤ))) ≤
      (ShellField.lihLocalSigma V).comap
        (fun omega : ShellSeq d => omega (n - (((n - m).toNat + r : ℕ) : ℤ))) := by
    rw [hindex]
    exact MeasurableSpace.comap_mono
      (MeasurableSpace.comap_mono (HCPolySupport.localSigmaR_mono hUV))
  exact hcomp.trans (le_iSup (fun t : ℕ => (ShellField.lihLocalSigma V).comap
    (fun omega : ShellSeq d => omega (n - (t : ℤ)))) ((n - m).toNat + r))

/-- The completed lower-shell local sigma-field is monotone in the shell index
and in the observation region. -/
theorem lowerShellLocalCompletion_mono (M : ABKModel d) {m n : ℤ} (hmn : m ≤ n)
    {U V : Set (Vec d)} (hUV : U ⊆ V) :
    lowerShellLocalCompletion M m U ≤ lowerShellLocalCompletion M n V := by
  rintro s ⟨t, ht, hst⟩
  exact ⟨t, lowerShellLocalSigma_mono hmn hUV t ht, hst⟩

/-- The cutoff-sample local sigma-field is monotone in the shell index and in
the observation region. -/
theorem cutoffSampleLocalSigma_mono (M : ABKModel d) {m n : ℤ} (hmn : m ≤ n)
    {U V : Set (Vec d)} (hUV : U ⊆ V) :
    cutoffSampleLocalSigma M m U ≤ cutoffSampleLocalSigma M n V :=
  MeasurableSpace.comap_mono (lowerShellLocalCompletion_mono M hmn hUV)

/-- **The cutoff-sample local sigma-field is closed under almost-everywhere
modification.**  It is the `Subtype.val`-comap of the *completed* lower-shell
local sigma-field, and `Subtype.val` is injective with full-measure range, so an
a.e. modification on the carrier is realized by an a.e. modification upstairs. -/
theorem measurableSet_cutoffSampleLocalSigma_of_ae_eq (M : ABKModel d) (m : ℤ)
    (U : Set (Vec d)) {s t : Set (CutoffSample d)}
    (ht : MeasurableSet[cutoffSampleLocalSigma M m U] t)
    (hst : s =ᵐ[(cutoffSampleLaw M).toMeasure] t) :
    MeasurableSet[cutoffSampleLocalSigma M m U] s := by
  classical
  obtain ⟨t0, ht0, hteq⟩ := MeasurableSpace.measurableSet_comap.1 ht
  subst hteq
  obtain ⟨t2, ht2, ht0t2⟩ := ht0
  set N : Set (CutoffSample d) :=
    (s \ (Subtype.val ⁻¹' t0)) ∪ ((Subtype.val ⁻¹' t0) \ s) with hNdef
  have hN0 : (cutoffSampleLaw M).toMeasure N = 0 := by
    obtain ⟨h1, h2⟩ := MeasureTheory.ae_eq_set.1 hst
    exact measure_union_null h1 h2
  obtain ⟨N1, hNN1, hN1meas, hN1zero⟩ := exists_measurable_superset_of_null hN0
  obtain ⟨B, hBmeas, hBpre⟩ := MeasurableSpace.measurableSet_comap.1 hN1meas
  have hB0 : M.P.toMeasure B = 0 := by
    rw [← map_cutoffSampleLaw_val M,
      Measure.map_apply measurable_subtype_coe hBmeas, hBpre]
    exact hN1zero
  set t1 : Set (ShellSeq d) :=
    (t0 \ B) ∪ Subtype.val '' (s ∩ (Subtype.val ⁻¹' B)) with ht1def
  have hagree : ∀ x : CutoffSample d, x ∉ Subtype.val ⁻¹' B →
      (x ∈ s ↔ x ∈ Subtype.val ⁻¹' t0) := by
    intro x hx
    rw [hBpre] at hx
    constructor
    · intro hxs
      by_contra hcon
      exact hx (hNN1 (Or.inl ⟨hxs, hcon⟩))
    · intro hxt
      by_contra hcon
      exact hx (hNN1 (Or.inr ⟨hxt, hcon⟩))
  have hpre : Subtype.val ⁻¹' t1 = s := by
    ext x
    constructor
    · rintro (⟨hxt0, hxB⟩ | hximg)
      · exact ((hagree x hxB).2 hxt0)
      · obtain ⟨y, hy, hyx⟩ := hximg
        have : y = x := Subtype.val_injective hyx
        exact this ▸ hy.1
    · intro hxs
      by_cases hxB : x ∈ Subtype.val ⁻¹' B
      · exact Or.inr ⟨x, ⟨hxs, hxB⟩, rfl⟩
      · exact Or.inl ⟨(hagree x hxB).1 hxs, hxB⟩
  have hsub1 : t1 \ t0 ⊆ B := by
    rintro y ⟨(⟨hy0, _⟩ | ⟨x, hx, hxy⟩), hyt0⟩
    · exact absurd hy0 hyt0
    · exact hxy ▸ hx.2
  have hsub2 : t0 \ t1 ⊆ B := by
    rintro y ⟨hy0, hy1⟩
    by_contra hyB
    exact hy1 (Or.inl ⟨hy0, hyB⟩)
  have ht1t0 : t1 =ᵐ[M.P.toMeasure] t0 :=
    MeasureTheory.ae_eq_set.2
      ⟨measure_mono_null hsub1 hB0, measure_mono_null hsub2 hB0⟩
  exact MeasurableSpace.measurableSet_comap.2
    ⟨t1, ⟨t2, ht2, ht1t0.trans ht0t2⟩, hpre⟩

/-! ## The local ellipticity bad event -/

/-- **`e.Bloc.def` is integral-local.**  The local coarse-grained ellipticity
failure of the cube `Q` is measurable for the integral-local information of any
region containing the closed cube `Q`, at the shell index `Q.scale`.  The only
a.e. step is the passage from the `A.mk` representatives used by the definition
of `badLoc` to the literal observables; the target sigma-field absorbs it. -/
theorem measurableSet_badLoc_cutoffSampleLocal (M : ABKModel d) (Q : TriadicCube d)
    {U : Set (Vec d)} (hQU : cubeSet Q ⊆ U) :
    MeasurableSet[cutoffSampleLocalSigma M Q.scale U] (badLoc M Q) := by
  have hs : (0 : ℝ) < 1 / 4 := by norm_num
  set A : Set (CutoffSample d) :=
    {omega | 10 * ((Algsuperdiff.Section3.Annealed.sigmaBar M Q.scale : ℝ))⁻¹ <
      cubeLowerEllipticityInvLiteral M Q Q.scale (1 / 4) exponentTwo omega}
  set B : Set (CutoffSample d) :=
    {omega | 10 * ((Algsuperdiff.Section3.Annealed.sigmaBar M Q.scale : ℝ)) <
      cubeUpperEllipticityLiteral M Q Q.scale (1 / 4) exponentTwo omega}
  have hA : MeasurableSet[cutoffSampleLocalSigma M Q.scale U] A := by
    let : MeasurableSpace (CutoffSample d) := cutoffSampleLocalSigma M Q.scale U
    exact measurableSet_lt measurable_const
      (measurable_cubeLowerEllipticityInvLiteral_cutoffSampleLocal M Q.scale Q hQU hs
        exponentTwo)
  have hB : MeasurableSet[cutoffSampleLocalSigma M Q.scale U] B := by
    let : MeasurableSpace (CutoffSample d) := cutoffSampleLocalSigma M Q.scale U
    exact measurableSet_lt measurable_const
      (measurable_cubeUpperEllipticityLiteral_cutoffSampleLocal M Q.scale Q hQU hs
        exponentTwo)
  have haeA : {omega : CutoffSample d |
      10 * ((Algsuperdiff.Section3.Annealed.sigmaBar M Q.scale : ℝ))⁻¹ <
        cubeLowerEllipticityInv M Q Q.scale (1 / 4) hs exponentTwo omega}
      =ᵐ[(cutoffSampleLaw M).toMeasure] A := by
    filter_upwards [cubeLowerEllipticityInv_ae_eq_literal M Q Q.scale (1 / 4) hs
      exponentTwo] with omega homega
    exact congrArg
      (fun x : ℝ => 10 * ((Algsuperdiff.Section3.Annealed.sigmaBar M Q.scale : ℝ))⁻¹ < x)
      homega
  have haeB : {omega : CutoffSample d |
      10 * ((Algsuperdiff.Section3.Annealed.sigmaBar M Q.scale : ℝ)) <
        cubeUpperEllipticity M Q Q.scale (1 / 4) hs exponentTwo omega}
      =ᵐ[(cutoffSampleLaw M).toMeasure] B := by
    filter_upwards [cubeUpperEllipticity_ae_eq_literal M Q Q.scale (1 / 4) hs
      exponentTwo] with omega homega
    exact congrArg
      (fun x : ℝ => 10 * ((Algsuperdiff.Section3.Annealed.sigmaBar M Q.scale : ℝ)) < x)
      homega
  exact measurableSet_cutoffSampleLocalSigma_of_ae_eq M Q.scale U (hA.union hB)
    (haeA.union haeB)

end

end Algsuperdiff.Section3.Provider.BadEvents

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.G2Score
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.TranslatedLocality
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.TranslationCovariance

/-!
# G2Locality

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `𝒢₂` representative-level locality, via a.e. stability

The `𝒢₂` leg of the frozen good event is
**representative-based and choice-dependent on a null set**: the public
observable `Support.annularErrorObservable` is an `A.mk` of the `(2,2)`
functional, so its values off one null set are an arbitrary measurable
modification.  Two consequences have to be discharged before the `𝒢₂` atoms can
be fed to the independence producer:

1. **Translation covariance must survive the choice.**  The manuscript's
   `𝓔_{s,2,2}(z+□_n; 𝐚_{n−2}, σ_{n−2})` is a *literal* object at a translated
   cube; the lane's atom is the *representative at the origin* read at the
   translated sample.  These agree only a.e., and the null set moves with `z`.
2. **Locality must survive the choice.**  `cutoffSampleLocalSigma` is the comap
   of a **completed** sigma-field, hence closed under a.e. modification; that is
   what makes the representative locally measurable at all, and it is the
   device this module exports at the function level.

Both are settled here, and the whole `𝒢₂` locality chain is then closed
unconditionally.

## The chain

```
Mu-locality (Section 3)
[measurable_Mu_coefficientCutoff_cutoffSampleLocal]
  → coarse full block matrix, literal                 [measurable_cutoffCoarseFullBlockRaw_local]
  → coarse full block matrix, representative          (a.e. stability)
  → normalized block response, representative         (continuous functional)
  → descendant average                                (finite average, subcubes stay inside)
  → the (2,2) functional at an ARBITRARY cube `Q`     [measurable_errorFunctionalAtCube_local]
  → the public 𝒢₂ observable read at the translated sample   (a.e. stability + covariance)
  → the annular maximum and the atom `X_j`
```

The coarse-block locality and a.e.-stability calculations use their common
Section 3 producers, while this module supplies the representative-level
and translated-observable applications.

## The centres are lattice points

§4.1 centres are triadic lattice points `z = 3^n v`, so `z + □_n` **is** the
triadic cube `Localize.latticeCube n v`.  No translated-region sigma-field and no
arbitrary-real-`z` locality is needed; the honest reading is the cube reading.

## Scope

Provider material: proved local helpers.

## References

* ABK26, `d.good.event.for.lambda`; `l.ratio.of.good.scales.for.mathcal.E`.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider
open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. a.e. stability of the cutoff-sample local sigma-field -/

/-- **The function-level a.e.-stability of `cutoffSampleLocalSigma`.**  The
sigma-field is the `Subtype.val`-comap of a *completed* lower-shell local
sigma-field, so a modification on a null set of a locally measurable map is
locally measurable, in every codomain.  This is the device that makes
representative-based observables — the whole `𝒢₂` leg — usable at all. -/
theorem measurable_cutoffSampleLocalSigma_of_ae_eq {alpha : Type*}
    [MeasurableSpace alpha] (M : ABKModel d) (m : ℤ) (U : Set (Vec d))
    {f g : Cutoff.CutoffSample d → alpha}
    (hf : Measurable[Cutoff.cutoffSampleLocalSigma M m U] f)
    (hfg : g =ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure] f) :
    Measurable[Cutoff.cutoffSampleLocalSigma M m U] g :=
  Homogenization.measurable_cutoffSampleLocalSigma_of_ae_eq
    M m U hf hfg

/-! ## 2. The coarse-block chain -/

/-- **Every entry of the coarse block matrix of the actual cutoff on a cube is
integral-local.**  CoarseGraining's four block-entry formulas express each
entry through the coarse energy `Mu`, whose locality on the closed cube is
proved. -/
theorem measurable_cutoffCoarseFullBlockRaw_local (M : ABKModel d) (L : ℤ)
    (Q : TriadicCube d) {U : Set (Vec d)} (hQU : cubeSet Q ⊆ U) :
    Measurable[Cutoff.cutoffSampleLocalSigma M L U]
      (Observable.cutoffCoarseFullBlockRaw M L Q) :=
  Homogenization.measurable_cutoffCoarseFullBlockRaw_cutoffSampleLocal M L Q hQU

/-- **The common coarse-block is local** — the first genuine use of a.e. stability:
the representative differs from the literal only on a null set. -/
theorem measurable_cutoffCoarseFullBlockRepresentative_local (M : ABKModel d)
    (L : ℤ) (Q : TriadicCube d) {U : Set (Vec d)} (hQU : cubeSet Q ⊆ U) :
    Measurable[Cutoff.cutoffSampleLocalSigma M L U]
      (Observable.cutoffCoarseFullBlockRepresentative M L Q) :=
  measurable_cutoffSampleLocalSigma_of_ae_eq M L U
    (measurable_cutoffCoarseFullBlockRaw_local M L Q hQU)
    (Observable.cutoffCoarseFullBlockMatrix_ae_eq_representative M L Q).symm

/-- The normalized block response of the common representative is local: it is a
continuous finite-dimensional functional of the block matrix. -/
theorem measurable_cutoffNormalizedBlockResponseRepresentative_local
    (M : ABKModel d) (L : ℤ) (Q : TriadicCube d) (a0 : Mat d) {U : Set (Vec d)}
    (hQU : cubeSet Q ⊆ U) :
    Measurable[Cutoff.cutoffSampleLocalSigma M L U]
      (Observable.cutoffNormalizedBlockResponseRepresentative M L Q a0) :=
  (Observable.continuous_normalizedBlockResponseMaxRepresentativeFunctional
    a0).measurable.comp (measurable_cutoffCoarseFullBlockRepresentative_local M L Q hQU)

/-- The descendant average is local: the subcubes of `Q` stay inside `Q`, hence
inside the observation region. -/
theorem measurable_cutoffAvgDescendantNormalizedBlockResponseRepresentative_local
     (M : ABKModel d) (L : ℤ) (Q : TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) (a0 : Mat d) {U : Set (Vec d)} (hQU : cubeSet Q ⊆ U) :
    Measurable[Cutoff.cutoffSampleLocalSigma M L U]
      (Support.cutoffAvgDescendantNormalizedBlockResponseRepresentative M L Q k a0) := by
  let : MeasurableSpace (Cutoff.CutoffSample d) := Cutoff.cutoffSampleLocalSigma M L U
  have hEq :
      Support.cutoffAvgDescendantNormalizedBlockResponseRepresentative M L Q k a0 =
        fun omega => ((descendantsAtScale Q k).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtScale Q k,
            Observable.cutoffNormalizedBlockResponseRepresentative M L R a0 omega :=
    rfl
  rw [hEq]
  refine measurable_const.mul (Finset.measurable_sum _ fun R hR => ?_)
  exact measurable_cutoffNormalizedBlockResponseRepresentative_local M L R a0
    (subset_trans (cubeSet_subset_of_mem_descendantsAtScale hk hR) hQU)

/-! ## 3. The `(2,2)` functional at an arbitrary cube -/

private theorem measurable_tsum_of_nonneg {Omega : Type*} [MeasurableSpace Omega]
    (T : ℕ → Omega → ℝ) (hmeas : ∀ n, Measurable (T n))
    (hnonneg : ∀ n omega, 0 ≤ T n omega) :
    Measurable fun omega => ∑' n, T n omega := by
  have hnn : Measurable (fun omega => ∑' n, (T n omega).toNNReal) :=
    Measurable.tsum (L := SummationFilter.unconditional ℕ) fun n =>
      (hmeas n).real_toNNReal
  have hnn := hnn.coe_nnreal_real
  convert hnn using 1
  funext omega
  rw [NNReal.coe_tsum]
  refine tsum_congr fun n => ?_
  rw [Real.toNNReal_of_nonneg (hnonneg n omega)]
  rfl

/-- **The `(2,2)` measurable functional at an A triadic cube.**  At `Q = □_n` this
is `Support.cutoffHomogenizationError22Functional` verbatim; the generality in
`Q` is what carries the translated cubes `z + □_n` of the `𝒢₂` lane. -/
def errorFunctionalAtCube (M : ABKModel d) (L : ℤ) (Q : TriadicCube d)
    (s : ℝ) (sigma : Observable.PositiveScalar) : Cutoff.CutoffSample d → ℝ :=
  fun omega => Real.sqrt (∑' l : ℕ, Ch02.geometricWeight s 2 l *
    Support.cutoffAvgDescendantNormalizedBlockResponseRepresentative M L Q
      (Q.scale - (l : ℤ)) (Observable.isotropicComparatorMatrix sigma) omega)

private theorem errorFunctional_term_nonneg (M : ABKModel d) (L : ℤ)
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) (sigma : Observable.PositiveScalar)
    (l : ℕ) (omega : Cutoff.CutoffSample d) :
    0 ≤ Ch02.geometricWeight s 2 l *
      Support.cutoffAvgDescendantNormalizedBlockResponseRepresentative M L Q
        (Q.scale - (l : ℤ)) (Observable.isotropicComparatorMatrix sigma) omega := by
  refine mul_nonneg ?_ ?_
  · simpa only [Ch02.geometricWeight_eq_old] using
      HCPolySupport.geometricWeight_nonneg l (by positivity : 0 ≤ s * (2 : ℝ))
  · exact Support.cutoffAvgDescendantNormalizedBlockResponseRepresentative_nonneg
      M L Q _ _ omega

/-- **The `(2,2)` functional is local.** -/
theorem measurable_errorFunctionalAtCube_local (M : ABKModel d) (L : ℤ)
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) (sigma : Observable.PositiveScalar)
    {U : Set (Vec d)} (hQU : cubeSet Q ⊆ U) :
    Measurable[Cutoff.cutoffSampleLocalSigma M L U]
      (errorFunctionalAtCube M L Q s sigma) := by
  let : MeasurableSpace (Cutoff.CutoffSample d) := Cutoff.cutoffSampleLocalSigma M L U
  refine Real.continuous_sqrt.measurable.comp ?_
  refine measurable_tsum_of_nonneg _ (fun l => ?_)
    (fun l omega => errorFunctional_term_nonneg M L Q hs sigma l omega)
  exact (measurable_cutoffAvgDescendantNormalizedBlockResponseRepresentative_local
    M L Q (by omega) _ hQU).const_mul _

/-! ### The functional IS the manuscript's literal, a.e. -/

private theorem scaleResponse_finite_nonneg (Q : TriadicCube d) (k : ℤ)
    (p : ℝ) (F : Ch02.TriadicCoeffFamily d) (a0 : Mat d) :
    0 ≤ Ch02.scaleResponseAtScale Q k (.finite p) F a0 := by
  change (0 : ℝ) ≤ Real.rpow (Ch02.finsetAverageReal (descendantsAtScale Q k)
    (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2))) (1 / p)
  refine Real.rpow_nonneg ?_ _
  exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun R _ =>
      Real.rpow_nonneg (Ch02.normalizedBlockResponseMax_nonneg R F a0) _)

/-- Nonnegativity of the literal `(2,2)` error at an arbitrary cube. -/
theorem homogenizationErrorOnCube_two_two_nonneg (Q : TriadicCube d)
    {s : ℝ} (hs : 0 < s) (F : Ch02.TriadicCoeffFamily d) (a0 : Mat d) :
    0 ≤ Ch02.HomogenizationErrorOnCube Q s (.finite 2) (.finite 2) F a0 := by
  unfold Ch02.HomogenizationErrorOnCube Ch02.HomogenizationError
    Ch02.HomogenizationErrorFinite
  refine Real.rpow_nonneg (tsum_nonneg fun l => mul_nonneg ?_ ?_) _
  · simpa only [Ch02.geometricWeight_eq_old] using
      (HCPolySupport.geometricWeight_nonneg (s := s) (q := 2) l
        (by positivity : 0 ≤ s * (2 : ℝ)))
  · exact Real.rpow_nonneg (scaleResponse_finite_nonneg Q _ 2 F a0) _

/-- On the probability-one event on which the literal block responses agree with
their representatives triadic cube, the literal `(2,2)` error at `Q` equals the
functional at `Q`. -/
theorem errorFunctionalAtCube_eq_of_common_event (M : ABKModel d)
    (L : ℤ) (Q : TriadicCube d) {s : ℝ} (hs : 0 < s)
    (sigma : Observable.PositiveScalar) (omega : Cutoff.CutoffSample d)
    (hall : ∀ R : TriadicCube d,
      Ch02.normalizedBlockResponseMax R
        (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega)
        (Observable.isotropicComparatorMatrix sigma) =
      Observable.cutoffNormalizedBlockResponseRepresentative M L R
        (Observable.isotropicComparatorMatrix sigma) omega) :
    Ch02.HomogenizationErrorOnCube Q s (.finite 2) (.finite 2)
        (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega)
        (Observable.isotropicComparatorMatrix sigma)
      = errorFunctionalAtCube M L Q s sigma omega := by
  have hsum : (∑' l : ℕ, Ch02.geometricWeight s 2 l *
      Ch02.finsetAverageReal (descendantsAtScale Q (Q.scale - (l : ℤ)))
        (fun R => Ch02.normalizedBlockResponseMax R
          (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega)
          (Observable.isotropicComparatorMatrix sigma)))
      = ∑' l : ℕ, Ch02.geometricWeight s 2 l *
        Support.cutoffAvgDescendantNormalizedBlockResponseRepresentative M L Q
          (Q.scale - (l : ℤ)) (Observable.isotropicComparatorMatrix sigma) omega := by
    refine tsum_congr fun l => congrArg (fun x => Ch02.geometricWeight s 2 l * x) ?_
    exact congrArg (fun f => ((descendantsAtScale Q (Q.scale - (l : ℤ))).card : ℝ)⁻¹ * f)
      (Finset.sum_congr rfl fun R _ => hall R)
  have hnn : 0 ≤ ∑' l : ℕ, Ch02.geometricWeight s 2 l *
      Support.cutoffAvgDescendantNormalizedBlockResponseRepresentative M L Q
        (Q.scale - (l : ℤ)) (Observable.isotropicComparatorMatrix sigma) omega :=
    tsum_nonneg fun l => errorFunctional_term_nonneg M L Q hs sigma l omega
  have hsq := Support.homogenizationErrorOnCube_two_two_sq_eq_tsum Q hs
    (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega)
    (Observable.isotropicComparatorMatrix sigma)
  rw [hsum] at hsq
  have h0 := homogenizationErrorOnCube_two_two_nonneg Q hs
    (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega)
    (Observable.isotropicComparatorMatrix sigma)
  calc Ch02.HomogenizationErrorOnCube Q s (.finite 2) (.finite 2)
        (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega)
        (Observable.isotropicComparatorMatrix sigma)
      = Real.sqrt (Ch02.HomogenizationErrorOnCube Q s (.finite 2) (.finite 2)
          (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega)
          (Observable.isotropicComparatorMatrix sigma) ^ 2) := (Real.sqrt_sq h0).symm
    _ = errorFunctionalAtCube M L Q s sigma omega := by rw [hsq]; rfl

/-- **The literal `(2,2)` error at an arbitrary cube is a.e. the local
functional.** -/
theorem homogenizationErrorOnCube_two_two_ae_eq_errorFunctionalAtCube [NeZero d]
    (M : ABKModel d) (L : ℤ) (Q : TriadicCube d) {s : ℝ} (hs : 0 < s)
    (sigma : Observable.PositiveScalar) :
    (fun omega => Ch02.HomogenizationErrorOnCube Q s (.finite 2) (.finite 2)
        (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega)
        (Observable.isotropicComparatorMatrix sigma))
      =ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure] errorFunctionalAtCube M L Q s sigma := by
  filter_upwards
    [Observable.ae_forall_normalizedBlockResponseMax_cutoff_eq_representative M L
      (Observable.isotropicComparatorMatrix sigma)] with omega hall
  exact errorFunctionalAtCube_eq_of_common_event M L Q hs sigma omega hall

/-! ## 4. The a.e. translation covariance of the public `𝒢₂` observable -/

/-- The paper-wide assumption `2 ≤ d` supplies the nonzero-dimension instance. -/
private theorem neZero_of_model (M : ABKModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩

/-- The manuscript's literal event is recovered a.e. through the
characterization lemmas, at the one place where that is load-bearing:
the null set depends on `v`, and the identity is *not* pointwise. -/
theorem annularErrorObservable_comp_translate_ae_eq_literal (M : ABKModel d)
    (n : ℤ) (s : {s : ℝ // 0 < s}) (v : Fin d → ℤ) :
    (fun omega => Support.annularErrorObservable M n s
        (Cutoff.translateCutoffSample (Support.triadicLatticePoint n v) omega))
      =ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure]
    fun omega => @Ch02.HomogenizationErrorOnCube d (Localize.latticeCube n v) (s : ℝ) (.finite 2)
      (.finite 2)
      (Cutoff.coefficientCutoffTriadicCoeffFamily M (n - 2) omega)
      (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M (n - 2))) := by
  let : NeZero d := neZero_of_model M
  have hshift := Localize.triadicCubeShift_latticeCube (d := d) n v
  have hae : (fun omega => Support.annularErrorAtom M n (s : ℝ)
        (Cutoff.translateCutoffSample (Support.triadicLatticePoint n v) omega))
      =ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure]
    fun omega => Support.annularErrorObservable M n s
      (Cutoff.translateCutoffSample (Support.triadicLatticePoint n v) omega) := by
    have hbase := Support.annularErrorAtom_ae_eq_annularErrorObservable M n s
    exact (GoodEvents.measurePreserving_translateCutoffSample M
      (Support.triadicLatticePoint n v)).quasiMeasurePreserving.ae hbase
  refine (Filter.EventuallyEq.symm hae).trans (Filter.Eventually.of_forall fun omega => ?_)
  have hchar := Support.cutoffHomogenizationErrorRaw22_characterization M (n - 2) n
    (s : ℝ) (Annealed.sigmaBar M (n - 2))
    (Cutoff.translateCutoffSample (Support.triadicLatticePoint n v) omega)
  have hcov := Provider.BadEvents.homogenizationErrorOnCube_translateCutoffSample
    M (n - 2) (Localize.latticeCube n v) (s : ℝ) (.finite 2) (.finite 2)
    (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M (n - 2))) omega
  rw [hshift] at hcov
  have hscale : (Localize.latticeCube n v).scale = n := rfl
  rw [hscale] at hcov
  change Support.annularErrorAtom M n (s : ℝ)
      (Cutoff.translateCutoffSample (Support.triadicLatticePoint n v) omega) = _
  rw [Support.annularErrorAtom, hchar]
  exact hcov.symm

/-- The public `𝒢₂` observable read at the translated sample is a.e. the local
functional at the translated cube.  Composing the atom bridge with the
functional's a.e. identity. -/
theorem annularErrorObservable_comp_translate_ae_eq_functional (M : ABKModel d)
    (n : ℤ) (s : {s : ℝ // 0 < s}) (v : Fin d → ℤ) :
    (fun omega => Support.annularErrorObservable M n s
        (Cutoff.translateCutoffSample (Support.triadicLatticePoint n v) omega))
      =ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure]
    @errorFunctionalAtCube d M (n - 2) (Localize.latticeCube n v)
      (s : ℝ) (Annealed.sigmaBar M (n - 2)) := by
  let : NeZero d := neZero_of_model M
  exact (annularErrorObservable_comp_translate_ae_eq_literal M n s v).trans
    (homogenizationErrorOnCube_two_two_ae_eq_errorFunctionalAtCube M (n - 2)
      (Localize.latticeCube n v) s.2 (Annealed.sigmaBar M (n - 2)))

/-! ## 5. Locality of the `𝒢₂` atom, the annular maximum, and `X_j` -/

/-- **The `𝒢₂` per-cube atom is local**, at the truncation level `n − 2` and every
region containing the closed cube `z + □_n = ⟨n, v⟩`.  This is the `𝒢₂` twin's
translate-locality export, and the a.e.-stability step is where the
representative choice is absorbed. -/
theorem measurable_errorAtomSq_local (M : ABKModel d) (n : ℤ)
    (s : {s : ℝ // 0 < s}) (v : Fin d → ℤ) {m : ℤ} (hm : n - 2 ≤ m)
    {U : Set (Vec d)} (hQU : cubeSet (Localize.latticeCube n v) ⊆ U) :
    Measurable[Cutoff.cutoffSampleLocalSigma M m U]
      (errorAtomSq M n s (Support.triadicLatticePoint n v)) := by
  let : NeZero d := neZero_of_model M
  have hloc : Measurable[Cutoff.cutoffSampleLocalSigma M (n - 2) U]
      (fun omega => Support.annularErrorObservable M n s
        (Cutoff.translateCutoffSample (Support.triadicLatticePoint n v) omega)) :=
    measurable_cutoffSampleLocalSigma_of_ae_eq M (n - 2) U
      (measurable_errorFunctionalAtCube_local M (n - 2) (Localize.latticeCube n v)
        s.2 (Annealed.sigmaBar M (n - 2)) hQU)
      (annularErrorObservable_comp_translate_ae_eq_functional M n s v)
  have hmono := Provider.BadEvents.cutoffSampleLocalSigma_mono M hm
    (Set.Subset.refl U)
  exact ((hloc.mono hmono le_rfl).pow_const 2)

/-- **The `𝒢₂` annular maximum is local** on the annulus region of its own index:
every read cube `⟨n, v⟩` with `v` in the annulus enumeration sits inside
`annulusRegion d j`, and every truncation level `n − 2` is at or below `j − 2`. -/
theorem measurable_errorAnnMax_annulusRegion_local (M : ABKModel d)
    (s : {s : ℝ // 0 < s}) {j n : ℤ} (hn : n ≤ j - 1) :
    Measurable[Cutoff.cutoffSampleLocalSigma M (j - 2) (annulusRegion d j)]
      (errorAnnMax M s j n) := by
  refine @measurable_fmax_of_mem (Cutoff.CutoffSample d) (Fin d → ℤ)
    (Cutoff.cutoffSampleLocalSigma M (j - 2) (annulusRegion d j)) _ _ ?_
  intro v hv
  have hvset : v ∈ Support.latticeAnnulusSet d n j (j - 1) :=
    (mem_latticeAnnulusFinset_iff (d := d) (by omega)).1 hv
  exact measurable_errorAtomSq_local M n s v (by omega)
    (cubeSet_latticeCube_subset_annulusRegion (d := d) hn hvset)

/-- **`X_j` is local** on `annulusRegion d j` at truncation level `j − 2` — the
`hloc` slot the independence producer consumes for the `𝒢₂` lane. -/
theorem measurable_Xcal_annulusRegion_local (M : ABKModel d)
    (s : {s : ℝ // 0 < s}) (j : ℤ) :
    Measurable[Cutoff.cutoffSampleLocalSigma M (j - 2) (annulusRegion d j)]
      (fun omega => (XcalE M s j omega).toReal) := by
  have heq : (fun omega : Cutoff.CutoffSample d => (XcalE M s j omega).toReal)
      = wsum (fun i => errorAnnMax M s j (j - 1 - (i : ℤ)))
        (fun i => weightThird ((s : ℝ) / 4) (i + 1)) := by
    funext omega
    rw [XcalE_eq_wsumE M s j omega]
    rfl
  rw [heq]
  refine @measurable_wsum (Cutoff.CutoffSample d)
    (Cutoff.cutoffSampleLocalSigma M (j - 2) (annulusRegion d j)) _ _ fun i => ?_
  exact measurable_errorAnnMax_annulusRegion_local M s (by omega)

end

end Algsuperdiff.Section4.Provider.Proportion

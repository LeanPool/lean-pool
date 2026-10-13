/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.Mu
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.WidetildeTheta
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Representatives

/-!
# LiteralMeasurabilityEngine

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The genuine measurability engine for multiscale ellipticity of a carrier source

This module is the CoarseGraining-only half of
`Provider/BadEvents/LiteralMeasurability.lean`, split off as an importable leaf
so that the files owning the Section 3 ellipticity observables
(`Observable/CutoffMultiscaleEllipticity.lean`,
`Provider/BadEvents/CubeEllipticity.lean`) can prove genuine measurability of
their own definitions without importing anything above them.  The split point
is the `section Literals` header of the original module; **no statement and no
proof below is changed by the split**, and every public name is preserved
(namespace `Algsuperdiff.Section3.Provider.BadEvents`, as before).  Nothing
here mentions a Section 3 object.

Given a measurable carrier source `X : Omega -> RegCoeffField d` that is locally
a.e.-uniformly elliptic at **every** sample, the two multiscale endpoints
`Lambda_{s,q}(Q; X omega)` and `lambda_{s,q}(Q; X omega)^{-1}` are genuinely
measurable, not merely a.e.-measurable.

## Why the CoarseGraining a.e. interface does not already give this

CoarseGraining's public multiscale-ellipticity measurability
(`aemeasurable_lambdaSqCoeffField_inv`, `aemeasurable_LambdaSqCoeffField`, and
their Section 3 mirrors in `Observable/Ch04MultiscaleMeasurability.lean`) is
law-relative for a reason recorded in
`Homogenization/Book/Ch04/Theorems/Mu.lean`: `Mu ∘ toFun` is *not*
`LocalSigmaR`-measurable on all of the honest carrier, because off the
a.e.-elliptic locus the carrier contains fields on which `Mu` is uninformative.
Every step above `Mu` — the coarse blocks, the descendant maxima, the weighted
series, the two endpoints — is then reduced modulo a null set by
`filter_upwards [hP.ae_locallyUniformlyEllipticField]`.

The genuine statement is available all the same, because a composite that never
visits the bad locus never needs the null set.  So the route taken here is:

1. `exists_localSigmaR_measurable_eq_Mu_cubeSet` rebuilds CoarseGraining's
   `liftCover` assembly and keeps the *everywhere-on-the-covered-locus*
   equality that `exists_isLocalRandomVariable_ae_eq_Mu_cubeSet` discards,
   giving a genuinely `LocalSigmaR (cubeSet Q)`-measurable `Y` with `Mu
   (cubeSet Q) a.toFun = Y a` at every field lying in some countable
   a.e.-elliptic quantitative slice;
2. `measurable_comp_Mu_cubeSet` composes that with any measurable, everywhere
   locally a.e.-uniformly elliptic carrier source `X : Omega -> RegCoeffField d`;
3. the `measurable_comp_*` chain then re-runs the Section 3 a.e. proof with
   `filter_upwards` replaced by `funext omega`, since each pointwise identity
   holds at every `omega`.

The Section 3 instantiation `X := Cutoff.coefficientCutoff M.nu cutoffScale`,
which discharges the two generic hypotheses unconditionally, is made in the
files that own the observables.

## Main results

* `measurable_comp_coarseB_cubeSet`, `measurable_comp_coarseSigmaStarInv_cubeSet`,
  `measurable_comp_coarseBMatrixNorm`,
  `measurable_comp_coarseSigmaStarInvMatrixNorm`: the coarse blocks and their
  operator norms.
* `measurable_comp_maxDescendantB`, `measurable_comp_maxDescendantSigmaStarInv`,
  `measurable_comp_weightedBSeries`, `measurable_comp_weightedSigmaSeries`: the
  finite descendant maxima and the two weighted series.
* `measurable_comp_LambdaSqCoeffField`, `measurable_comp_lambdaSqCoeffField_inv`
  (with their finite/infinity halves): the two multiscale endpoints for an
  arbitrary carrier source.

## Related statements elsewhere

`Provider/BadEvents/LambdaLocal.lean` already states the pivotal
everywhere-ellipticity dichotomy in its own docstring and carries the analogous
liftCover assembly (a plain ℕ-indexed cover on `CutoffSample d`; the `Option ℕ`
cover with its `none` branch is this file's, on `RegCoeffField d`) and genuine
measurability of the two general-cube literals at the local σ-algebra
`cutoffSampleLocalSigma` --- a completion-comap that is incomparable with the
ambient carrier σ-algebra, so nothing here is redundant.

## References

* ABK26, (2.22)--(2.23) (the coarse-grained ellipticity constants).
* `Homogenization/Book/Ch04/Theorems/Mu.lean` (the a.e. endpoint and the
  statement-check note explaining why it is a.e.).
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open Filter MeasureTheory Set
open HCPolySupport HCPolySupport.Book
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- A genuinely `LocalSigmaR (cubeSet Q)`-measurable function on the honest carrier
agreeing with the coarse-grained energy `Mu` at every field lying in some
countable a.e.-elliptic quantitative slice of the cube.  This is CoarseGraining's
`exists_isLocalRandomVariable_ae_eq_Mu_cubeSet` assembly with the
everywhere-on-the-covered-locus equality retained instead of discarded. -/
theorem exists_localSigmaR_measurable_eq_Mu_cubeSet (Q : TriadicCube d)
    (P0 : BlockVec d) :
    ∃ Y : RegCoeffField d → ℝ,
      @Measurable (RegCoeffField d) ℝ (LocalSigmaR (cubeSet Q)) _ Y ∧
      ∀ a : RegCoeffField d,
        (∃ k : ℕ, AEEQuantitativeEllipticSlice (cubeSet Q) k a.toFun) →
          Mu (cubeSet Q) P0 a.toFun = Y a := by
  classical
  let slice : ℕ → Set (RegCoeffField d) :=
    fun k => {a : RegCoeffField d | AEEQuantitativeEllipticSlice (cubeSet Q) k a.toFun}
  let covered : Set (RegCoeffField d) := ⋃ k : ℕ, slice k
  let cover : Option ℕ → Set (RegCoeffField d)
    | none => coveredᶜ
    | some k => slice k
  let f : (i : Option ℕ) → cover i → ℝ
    | none, _ => 0
    | some _k, a => Mu (cubeSet Q) P0 a.1.toFun
  have hagree :
      ∀ (i j : Option ℕ) (a : RegCoeffField d)
        (hai : a ∈ cover i) (haj : a ∈ cover j),
          f i ⟨a, hai⟩ = f j ⟨a, haj⟩ := by
    intro i j a hai haj
    cases i with
    | none =>
        cases j with
        | none => rfl
        | some k => exact absurd (Set.mem_iUnion.mpr ⟨k, haj⟩) hai
    | some k =>
        cases j with
        | none => exact absurd (Set.mem_iUnion.mpr ⟨k, hai⟩) haj
        | some _ => rfl
  have hcover : ⋃ i : Option ℕ, cover i = Set.univ := by
    ext a
    refine ⟨fun _ => Set.mem_univ a, fun _ => ?_⟩
    by_cases ha : a ∈ covered
    · rcases Set.mem_iUnion.mp ha with ⟨k, hk⟩
      exact Set.mem_iUnion.mpr ⟨some k, by simpa [cover] using hk⟩
    · exact Set.mem_iUnion.mpr ⟨none, by simpa [cover] using ha⟩
  refine ⟨Set.liftCover cover f hagree hcover, ?_, ?_⟩
  · let : MeasurableSpace (RegCoeffField d) := LocalSigmaR (cubeSet Q)
    have hcover_meas : ∀ i : Option ℕ, MeasurableSet (cover i) := by
      intro i
      cases i with
      | none =>
          exact (MeasurableSet.iUnion fun k =>
            Ch04.measurableSet_localSigmaR_aeeQuantitativeEllipticSlice Q k).compl
      | some k => exact Ch04.measurableSet_localSigmaR_aeeQuantitativeEllipticSlice Q k
    have hfm : ∀ i : Option ℕ, Measurable (f i) := by
      intro i
      cases i with
      | none => exact measurable_const
      | some k =>
          have hEntry :
              ∀ (i' j' : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
                  HasCompactSupport φ → tsupport φ ⊆ cubeSet Q →
                @Measurable (cover (some k)) ℝ _ _
                  (fun x => entryTestR i' j' φ (x : RegCoeffField d)) := by
            intro i' j' φ hφ_cont hφ_compact hφ_support
            have hφ_probe : IsProbeR φ := IsProbeR.of_smooth hφ_cont hφ_compact
            have hφ_support' : Function.support φ ⊆ cubeSet Q :=
              (Function.support_subset_iff.2 fun x hx => subset_tsupport φ hx).trans hφ_support
            exact (measurable_entryTestR_localSigmaR i' j' hφ_probe hφ_support').comp
              measurable_subtype_coe
          simpa [f] using
            measurable_Mu_comp_aeeSlice_of_measurable_entryTest Q
              (A := fun x : cover (some k) => (x : RegCoeffField d))
              (fun x => x.2) hEntry P0
    exact measurable_liftCover cover hcover_meas f hfm hagree hcover
  · rintro a ⟨k, hk⟩
    have ha_cover : a ∈ cover (some k) := hk
    exact (Set.liftCover_of_mem (S := cover) (f := f) (hf := hagree) (hS := hcover)
      (i := some k) ha_cover).symm

/-- The coarse-grained energy of a measurable, everywhere locally
a.e.-uniformly elliptic carrier source is genuinely measurable. -/
theorem measurable_comp_Mu_cubeSet {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → RegCoeffField d} (hX : Measurable X)
    (hell : ∀ omega, Ch04.AELocallyUniformlyEllipticField (X omega))
    (Q : TriadicCube d) (P0 : BlockVec d) :
    Measurable fun omega => Mu (cubeSet Q) P0 (X omega).toFun := by
  obtain ⟨Y, hY, hYeq⟩ := exists_localSigmaR_measurable_eq_Mu_cubeSet Q P0
  have hrw : (fun omega => Mu (cubeSet Q) P0 (X omega).toFun) = Y ∘ X := by
    funext omega
    exact hYeq (X omega) ((hell omega).exists_aeeQuantitativeEllipticSlice_cubeSet Q)
  rw [hrw]
  exact (hY.mono (LocalSigmaR_le (cubeSet Q)) le_rfl).comp hX

section Composition

variable {Ω : Type*} [MeasurableSpace Ω] {X : Ω → RegCoeffField d}

/-- The upper-left coarse block `b(Q; a)` of a measurable, everywhere locally
a.e.-uniformly elliptic carrier source is genuinely measurable. -/
theorem measurable_comp_coarseB_cubeSet (hX : Measurable X)
    (hell : ∀ omega, Ch04.AELocallyUniformlyEllipticField (X omega))
    (Q : TriadicCube d) :
    Measurable fun omega => (coarseBlockMatrix (cubeSet Q) (X omega).toFun).upperLeft := by
  refine measurable_pi_iff.2 fun i => ?_
  refine measurable_pi_iff.2 fun j => ?_
  by_cases hij : i = j
  · subst hij
    have hrw :
        (fun omega => (coarseBlockMatrix (cubeSet Q) (X omega).toFun).upperLeft i i) =
          fun omega => (2 : ℝ) * Mu (cubeSet Q) (Pi.single i 1, 0) (X omega).toFun := by
      funext omega
      simp [coarseBlockMatrix_upperLeft_apply]
    rw [hrw]
    exact (measurable_comp_Mu_cubeSet hX hell Q (Pi.single i 1, 0)).const_mul _
  · have hrw :
        (fun omega => (coarseBlockMatrix (cubeSet Q) (X omega).toFun).upperLeft i j) =
          fun omega =>
            Mu (cubeSet Q) ((Pi.single i 1, 0) + (Pi.single j 1, 0)) (X omega).toFun -
              Mu (cubeSet Q) (Pi.single i 1, 0) (X omega).toFun -
              Mu (cubeSet Q) (Pi.single j 1, 0) (X omega).toFun := by
      funext omega
      simp [coarseBlockMatrix_upperLeft_apply, hij]
    rw [hrw]
    exact ((measurable_comp_Mu_cubeSet hX hell Q ((Pi.single i 1, 0) + (Pi.single j 1, 0))).sub
      (measurable_comp_Mu_cubeSet hX hell Q (Pi.single i 1, 0))).sub
      (measurable_comp_Mu_cubeSet hX hell Q (Pi.single j 1, 0))

/-- The lower-right coarse block `σ_*⁻¹(Q; a)` of a measurable, everywhere
locally a.e.-uniformly elliptic carrier source is genuinely measurable. -/
theorem measurable_comp_coarseSigmaStarInv_cubeSet (hX : Measurable X)
    (hell : ∀ omega, Ch04.AELocallyUniformlyEllipticField (X omega))
    (Q : TriadicCube d) :
    Measurable fun omega => (coarseBlockMatrix (cubeSet Q) (X omega).toFun).lowerRight := by
  refine measurable_pi_iff.2 fun i => ?_
  refine measurable_pi_iff.2 fun j => ?_
  by_cases hij : i = j
  · subst hij
    have hrw :
        (fun omega => (coarseBlockMatrix (cubeSet Q) (X omega).toFun).lowerRight i i) =
          fun omega => (2 : ℝ) * Mu (cubeSet Q) (0, Pi.single i 1) (X omega).toFun := by
      funext omega
      simp [coarseBlockMatrix_lowerRight_apply]
    rw [hrw]
    exact (measurable_comp_Mu_cubeSet hX hell Q (0, Pi.single i 1)).const_mul _
  · have hrw :
        (fun omega => (coarseBlockMatrix (cubeSet Q) (X omega).toFun).lowerRight i j) =
          fun omega =>
            Mu (cubeSet Q) ((0, Pi.single i 1) + (0, Pi.single j 1)) (X omega).toFun -
              Mu (cubeSet Q) (0, Pi.single i 1) (X omega).toFun -
              Mu (cubeSet Q) (0, Pi.single j 1) (X omega).toFun := by
      funext omega
      simp [coarseBlockMatrix_lowerRight_apply, hij]
    rw [hrw]
    exact ((measurable_comp_Mu_cubeSet hX hell Q ((0, Pi.single i 1) + (0, Pi.single j 1))).sub
      (measurable_comp_Mu_cubeSet hX hell Q (0, Pi.single i 1))).sub
      (measurable_comp_Mu_cubeSet hX hell Q (0, Pi.single j 1))

/-- The operator norm of the upper-left coarse block is measurable. -/
theorem measurable_comp_coarseBMatrixNorm (hX : Measurable X)
    (hell : ∀ omega, Ch04.AELocallyUniformlyEllipticField (X omega))
    (Q : TriadicCube d) :
    Measurable fun omega =>
      Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) (X omega).toFun).upperLeft := by
  simpa [Ch02.matrixNorm, Matrix.l2_opNorm_toEuclideanCLM] using
    (measurable_comp_coarseB_cubeSet hX hell Q).norm

/-- The operator norm of the lower-right coarse block is measurable. -/
theorem measurable_comp_coarseSigmaStarInvMatrixNorm (hX : Measurable X)
    (hell : ∀ omega, Ch04.AELocallyUniformlyEllipticField (X omega))
    (Q : TriadicCube d) :
    Measurable fun omega =>
      Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) (X omega).toFun).lowerRight := by
  simpa [Ch02.matrixNorm, Matrix.l2_opNorm_toEuclideanCLM] using
    (measurable_comp_coarseSigmaStarInv_cubeSet hX hell Q).norm

end Composition

/-- Finite nonempty suprema of measurable real observables are measurable. -/
private theorem measurable_finset_sup' {Ω ι : Type*} [MeasurableSpace Ω]
    {S : Finset ι} (hS : S.Nonempty) {f : ι → Ω → ℝ}
    (hf : ∀ i ∈ S, Measurable (f i)) :
    Measurable (S.sup' hS f) :=
  Finset.sup'_induction (s := S) (H := hS) (f := f)
    (p := fun g => Measurable g)
    (fun _ hf' _ hg' => hf'.sup hg')
    (fun i hi => hf i hi)

section Multiscale

variable [NeZero d] {Ω : Type*} [MeasurableSpace Ω] {X : Ω → RegCoeffField d}

/-- The descendant maximum of upper-left coarse block norms is measurable. -/
theorem measurable_comp_maxDescendantB (hX : Measurable X)
    (hell : ∀ omega, Ch04.AELocallyUniformlyEllipticField (X omega))
    (Q : TriadicCube d) (n : ℕ) :
    Measurable fun omega =>
      Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) (X omega) := by
  classical
  have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
  have hS : (descendantsAtScale Q (Q.scale - (n : ℤ))).Nonempty :=
    descendantsAtScale_nonempty Q (sub_le_self Q.scale hn)
  have hsup : Measurable
      ((descendantsAtScale Q (Q.scale - (n : ℤ))).sup' hS (fun R (omega : Ω) =>
        Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) (X omega).toFun).upperLeft)) := by
    refine measurable_finset_sup' hS ?_
    intro R _
    exact measurable_comp_coarseBMatrixNorm hX hell R
  have hfin : Measurable (fun omega =>
      Ch02.finsetSupReal (descendantsAtScale Q (Q.scale - (n : ℤ)))
        (fun R => Ch02.matrixNorm
          (coarseBlockMatrix (cubeSet R) (X omega).toFun).upperLeft)) := by
    convert hsup using 1
    ext omega
    rw [Finset.sup'_apply]
    exact Ch04.RestrictionLawCarrier.finsetSupReal_eq_sup' _ hS
      (fun R => Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) (X omega).toFun).upperLeft)
  have hrw : (fun omega =>
      Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) (X omega)) =
      fun omega => Ch02.finsetSupReal (descendantsAtScale Q (Q.scale - (n : ℤ)))
        (fun R => Ch02.matrixNorm
          (coarseBlockMatrix (cubeSet R) (X omega).toFun).upperLeft) := by
    funext omega
    exact Ch04.RestrictionLawCarrier.maxDescendantBMatrixNormCoeffFieldAtScale_eq_finsetSupReal_ae
      (hell omega) Q (Q.scale - (n : ℤ))
  rw [hrw]
  exact hfin

/-- The descendant maximum of lower-right coarse block norms is measurable. -/
theorem measurable_comp_maxDescendantSigmaStarInv (hX : Measurable X)
    (hell : ∀ omega, Ch04.AELocallyUniformlyEllipticField (X omega))
    (Q : TriadicCube d) (n : ℕ) :
    Measurable fun omega =>
      Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
        Q (Q.scale - (n : ℤ)) (X omega) := by
  classical
  have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
  have hS : (descendantsAtScale Q (Q.scale - (n : ℤ))).Nonempty :=
    descendantsAtScale_nonempty Q (sub_le_self Q.scale hn)
  have hsup : Measurable
      ((descendantsAtScale Q (Q.scale - (n : ℤ))).sup' hS (fun R (omega : Ω) =>
        Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) (X omega).toFun).lowerRight)) := by
    refine measurable_finset_sup' hS ?_
    intro R _
    exact measurable_comp_coarseSigmaStarInvMatrixNorm hX hell R
  have hfin : Measurable (fun omega =>
      Ch02.finsetSupReal (descendantsAtScale Q (Q.scale - (n : ℤ)))
        (fun R => Ch02.matrixNorm
          (coarseBlockMatrix (cubeSet R) (X omega).toFun).lowerRight)) := by
    convert hsup using 1
    ext omega
    rw [Finset.sup'_apply]
    exact Ch04.RestrictionLawCarrier.finsetSupReal_eq_sup' _ hS
      (fun R => Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) (X omega).toFun).lowerRight)
  have hrw : (fun omega =>
      Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
        Q (Q.scale - (n : ℤ)) (X omega)) =
      fun omega => Ch02.finsetSupReal (descendantsAtScale Q (Q.scale - (n : ℤ)))
        (fun R => Ch02.matrixNorm
          (coarseBlockMatrix (cubeSet R) (X omega).toFun).lowerRight) := by
    funext omega
    exact Ch04.RestrictionLawCarrier.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_eq_finsetSupReal_ae
      (hell omega) Q (Q.scale - (n : ℤ))
  rw [hrw]
  exact hfin

/-- The weighted upper-block series is measurable. -/
theorem measurable_comp_weightedBSeries (hX : Measurable X)
    (hell : ∀ omega, Ch04.AELocallyUniformlyEllipticField (X omega))
    (Q : TriadicCube d) {s q : ℝ} (hs : 0 < s) (hq : 0 < q) :
    Measurable fun omega => ∑' n : ℕ,
      Ch02.geometricWeight s q n *
        Real.rpow
          (Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) (X omega))
          (q / 2) := by
  have hrpow : Measurable (fun x : ℝ => Real.rpow x (q / 2)) :=
    (Real.continuous_rpow_const (by positivity)).measurable
  refine measurable_of_tendsto_metrizable
    (f := fun N omega => ∑ n ∈ Finset.range N,
      Ch02.geometricWeight s q n *
        Real.rpow
          (Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) (X omega))
          (q / 2))
    (fun N => Finset.measurable_fun_sum (Finset.range N) fun n _ =>
      (hrpow.comp (measurable_comp_maxDescendantB hX hell Q n)).const_mul
        (Ch02.geometricWeight s q n)) ?_
  rw [tendsto_pi_nhds]
  intro omega
  simpa [Ch04.maxDescendantBMatrixNormCoeffFieldAtScale, hell omega] using
    HasSum.tendsto_sum_nat
      (Ch02.summable_B_series_pointwiseCoeffField Q
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField (X omega) (hell omega))
        hs hq).hasSum

/-- The weighted lower-block series is measurable. -/
theorem measurable_comp_weightedSigmaSeries (hX : Measurable X)
    (hell : ∀ omega, Ch04.AELocallyUniformlyEllipticField (X omega))
    (Q : TriadicCube d) {s q : ℝ} (hs : 0 < s) (hq : 0 < q) :
    Measurable fun omega => ∑' n : ℕ,
      Ch02.geometricWeight s q n *
        Real.rpow
          (Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
            Q (Q.scale - (n : ℤ)) (X omega))
          (q / 2) := by
  have hrpow : Measurable (fun x : ℝ => Real.rpow x (q / 2)) :=
    (Real.continuous_rpow_const (by positivity)).measurable
  refine measurable_of_tendsto_metrizable
    (f := fun N omega => ∑ n ∈ Finset.range N,
      Ch02.geometricWeight s q n *
        Real.rpow
          (Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
            Q (Q.scale - (n : ℤ)) (X omega))
          (q / 2))
    (fun N => Finset.measurable_fun_sum (Finset.range N) fun n _ =>
      (hrpow.comp (measurable_comp_maxDescendantSigmaStarInv hX hell Q n)).const_mul
        (Ch02.geometricWeight s q n)) ?_
  rw [tendsto_pi_nhds]
  intro omega
  simpa [Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale, hell omega] using
    HasSum.tendsto_sum_nat
      (Ch02.summable_sigmaStarInv_series_pointwiseCoeffField Q
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField (X omega) (hell omega))
        hs hq).hasSum

/-- Finite-exponent upper multiscale ellipticity of a measurable, everywhere
locally a.e.-uniformly elliptic carrier source is measurable. -/
theorem measurable_comp_LambdaSqCoeffField_finite (hX : Measurable X)
    (hell : ∀ omega, Ch04.AELocallyUniformlyEllipticField (X omega))
    (Q : TriadicCube d) {s q : ℝ} (hs : 0 < s) (hq : 1 ≤ q) :
    Measurable fun omega => Ch04.LambdaSqCoeffField Q s (.finite q) (X omega) := by
  have hseries := measurable_comp_weightedBSeries hX hell Q hs (lt_of_lt_of_le zero_lt_one hq)
  have hrpow : Measurable (fun x : ℝ => Real.rpow x (2 / q)) :=
    (Real.continuous_rpow_const (by positivity)).measurable
  have hrw : (fun omega => Real.rpow (∑' n : ℕ,
      Ch02.geometricWeight s q n *
        Real.rpow
          (Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) (X omega))
          (q / 2)) (2 / q)) =
      fun omega => Ch04.LambdaSqCoeffField Q s (.finite q) (X omega) := by
    funext omega
    simp [Ch04.LambdaSqCoeffField, Ch02.LambdaSqFinite,
      Ch04.maxDescendantBMatrixNormCoeffFieldAtScale, hell omega]
  rw [← hrw]
  exact hrpow.comp hseries

/-- Infinity-exponent upper multiscale ellipticity of a measurable, everywhere
locally a.e.-uniformly elliptic carrier source is measurable. -/
theorem measurable_comp_LambdaSqCoeffField_infinity (hX : Measurable X)
    (hell : ∀ omega, Ch04.AELocallyUniformlyEllipticField (X omega))
    (Q : TriadicCube d) (s : ℝ) :
    Measurable fun omega => Ch04.LambdaSqCoeffField Q s .infinity (X omega) := by
  have hsup : Measurable fun omega => ⨆ n : ℕ,
      Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
        Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) (X omega) :=
    Measurable.iSup fun n =>
      (measurable_comp_maxDescendantB hX hell Q n).const_mul
        (Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)))
  have hrw : (fun omega => ⨆ n : ℕ,
      Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
        Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) (X omega)) =
      fun omega => Ch04.LambdaSqCoeffField Q s .infinity (X omega) := by
    funext omega
    simp only [Ch04.LambdaSqCoeffField, Ch02.LambdaSq_infinity,
      Ch02.LambdaSqInfinity, Ch04.maxDescendantBMatrixNormCoeffFieldAtScale,
      dite_eq_left (hell omega), iSup]
    congr 1
    ext x
    constructor <;> rintro ⟨n, hn⟩ <;> exact ⟨n, hn.symm⟩
  rw [← hrw]
  exact hsup

/-- Finite-exponent inverse lower multiscale ellipticity of a measurable,
everywhere locally a.e.-uniformly elliptic carrier source is measurable. -/
theorem measurable_comp_lambdaSqCoeffField_finite_inv (hX : Measurable X)
    (hell : ∀ omega, Ch04.AELocallyUniformlyEllipticField (X omega))
    (Q : TriadicCube d) {s q : ℝ} (hs : 0 < s) (hq : 1 ≤ q) :
    Measurable fun omega => (Ch04.lambdaSqCoeffField Q s (.finite q) (X omega))⁻¹ := by
  have hseries := measurable_comp_weightedSigmaSeries hX hell Q hs
    (lt_of_lt_of_le zero_lt_one hq)
  have hrpow : Measurable (fun x : ℝ => Real.rpow x (2 / q)) :=
    (Real.continuous_rpow_const (by positivity)).measurable
  have hrw : (fun omega => Real.rpow (∑' n : ℕ,
      Ch02.geometricWeight s q n *
        Real.rpow
          (Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
            Q (Q.scale - (n : ℤ)) (X omega))
          (q / 2)) (2 / q)) =
      fun omega => (Ch04.lambdaSqCoeffField Q s (.finite q) (X omega))⁻¹ := by
    funext omega
    simp only [Ch04.lambdaSqCoeffField, Ch02.lambdaSq_finite,
      Ch02.lambdaSqFinite, Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale,
      dite_eq_left (hell omega)]
    let F : Ch02.TriadicCoeffFamily d :=
      Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField (X omega) (hell omega)
    let S : ℝ := ∑' n : ℕ, Ch02.geometricWeight s q n *
      Real.rpow (Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        Q (Q.scale - (n : ℤ)) F) (q / 2)
    have hS : 0 ≤ S := by
      dsimp [S]
      exact Ch02.lambdaSqFinite_series_nonneg Q s q F (le_trans zero_le_one hq)
        (mul_nonneg hs.le (le_trans zero_le_one hq))
    change Real.rpow S (2 / q) = (Real.rpow S (-(2 / q)))⁻¹
    have hneg : Real.rpow S (-(2 / q)) = (Real.rpow S (2 / q))⁻¹ :=
      Real.rpow_neg hS (2 / q)
    calc
      Real.rpow S (2 / q) = ((Real.rpow S (2 / q))⁻¹)⁻¹ := (inv_inv _).symm
      _ = (Real.rpow S (-(2 / q)))⁻¹ := by rw [hneg]
  rw [← hrw]
  exact hrpow.comp hseries

/-- Infinity-exponent inverse lower multiscale ellipticity of a measurable,
everywhere locally a.e.-uniformly elliptic carrier source is measurable. -/
theorem measurable_comp_lambdaSqCoeffField_infinity_inv (hX : Measurable X)
    (hell : ∀ omega, Ch04.AELocallyUniformlyEllipticField (X omega))
    (Q : TriadicCube d) (s : ℝ) :
    Measurable fun omega => (Ch04.lambdaSqCoeffField Q s .infinity (X omega))⁻¹ := by
  have hsup : Measurable fun omega => ⨆ n : ℕ,
      Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
        Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
          Q (Q.scale - (n : ℤ)) (X omega) :=
    Measurable.iSup fun n =>
      (measurable_comp_maxDescendantSigmaStarInv hX hell Q n).const_mul
        (Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)))
  have hrw : (fun omega => ⨆ n : ℕ,
      Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
        Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
          Q (Q.scale - (n : ℤ)) (X omega)) =
      fun omega => (Ch04.lambdaSqCoeffField Q s .infinity (X omega))⁻¹ := by
    funext omega
    simp only [Ch04.lambdaSqCoeffField, Ch02.lambdaSq_infinity,
      Ch02.lambdaSqInfinity, Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale,
      dite_eq_left (hell omega), iSup, inv_inv]
    congr 1
    ext x
    constructor <;> rintro ⟨n, hn⟩ <;> exact ⟨n, hn.symm⟩
  rw [← hrw]
  exact hsup

/-- Full finite-or-infinite upper multiscale ellipticity measurability. -/
theorem measurable_comp_LambdaSqCoeffField (hX : Measurable X)
    (hell : ∀ omega, Ch04.AELocallyUniformlyEllipticField (X omega))
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s)
    (q : Ch02.MultiscaleExponent) (hq : q.IsAdmissible) :
    Measurable fun omega => Ch04.LambdaSqCoeffField Q s q (X omega) := by
  cases q with
  | finite q => exact measurable_comp_LambdaSqCoeffField_finite hX hell Q hs hq
  | infinity => exact measurable_comp_LambdaSqCoeffField_infinity hX hell Q s

/-- Full finite-or-infinite inverse lower multiscale ellipticity
measurability. -/
theorem measurable_comp_lambdaSqCoeffField_inv (hX : Measurable X)
    (hell : ∀ omega, Ch04.AELocallyUniformlyEllipticField (X omega))
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s)
    (q : Ch02.MultiscaleExponent) (hq : q.IsAdmissible) :
    Measurable fun omega => (Ch04.lambdaSqCoeffField Q s q (X omega))⁻¹ := by
  cases q with
  | finite q => exact measurable_comp_lambdaSqCoeffField_finite_inv hX hell Q hs hq
  | infinity => exact measurable_comp_lambdaSqCoeffField_infinity_inv hX hell Q s

end Multiscale

end

end Algsuperdiff.Section3.Provider.BadEvents

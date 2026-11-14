/-
Copyright (c) 2026 Lukas Liehr, Mitchell A. Taylor, Peiyang Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Liehr, Mitchell A. Taylor, Peiyang Yu
-/
module

public import LeanPool.GrothendieckBessel.FiniteRealization
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
public import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Countable moment measures
Adapted for Lean Pool from the Apache-2.0 upstream formalization, with module-system,
Mathlib API, and compilation changes.
-/

@[expose] public section


noncomputable section

open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate ENNReal BoundedContinuousFunction

namespace GrothendieckBessel

/-- The closed unit disk in `ℂ`, as a compact measurable subtype. -/
abbrev ClosedComplexUnitDisk : Type :=
  Metric.closedBall (0 : ℂ) 1

/-- Countable products of the closed complex unit disk. -/
abbrev ClosedComplexUnitDiskProduct (J : Type*) : Type _ :=
  J → ClosedComplexUnitDisk

instance closedComplexUnitDisk_compactSpace : CompactSpace ClosedComplexUnitDisk :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) 1)

instance closedComplexUnitDisk_standardBorelSpace :
    StandardBorelSpace ClosedComplexUnitDisk :=
  MeasurableSet.standardBorel Metric.isClosed_closedBall.measurableSet

instance closedComplexUnitDisk_nonempty : Nonempty ClosedComplexUnitDisk :=
  ⟨⟨0, by simp⟩⟩

/-- Coercions from the closed unit disk have norm at most one. -/
theorem ClosedComplexUnitDisk.norm_coe_le_one (z : ClosedComplexUnitDisk) :
    ‖(z : ℂ)‖ ≤ 1 := by
  simpa using (mem_closedBall_zero_iff.mp z.2)

/-- Package a complex number whose norm is at most one as a point of the closed unit disk. -/
def Complex.toClosedUnitDisk (z : ℂ) (hz : ‖z‖ ≤ 1) : ClosedComplexUnitDisk :=
  ⟨z, by simpa [ClosedComplexUnitDisk] using (mem_closedBall_zero_iff.mpr hz)⟩

/-- The zero point of the closed complex unit disk. -/
def zeroClosedComplexUnitDisk : ClosedComplexUnitDisk :=
  Complex.toClosedUnitDisk 0 (by simp)

/-- Compact standard Borel structure for the product `closedDisk^J`. -/
theorem compact_standard_borel_product
    (J : Type*) [Countable J] :
    CompactSpace (ClosedComplexUnitDiskProduct J) ∧
      StandardBorelSpace (ClosedComplexUnitDiskProduct J) := by
  constructor <;> infer_instance

/-- Compactness of probability measures on a
compact metrizable space. -/
theorem probability_measures_compact
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [T2Space X] [BorelSpace X] :
    CompactSpace (ProbabilityMeasure X) := by
  infer_instance

/-- The bounded continuous test function for the `(j,k)` moment. -/
def diskMomentBCF {J : Type*} (j k : J) :
    ClosedComplexUnitDiskProduct J →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact
    { toFun := fun x : ClosedComplexUnitDiskProduct J =>
        ((x j : ClosedComplexUnitDisk) : ℂ) *
          star (((x k : ClosedComplexUnitDisk) : ℂ))
      continuous_toFun := by
        exact ((continuous_subtype_val.comp (continuous_apply j)).mul
          (continuous_star.comp
            (continuous_subtype_val.comp (continuous_apply k)))) }

/-- Complex-valued weak-continuity of integration of a bounded continuous test function. -/
theorem continuous_probability_integral_complex
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (f : X →ᵇ ℂ) :
    Continuous fun μ : ProbabilityMeasure X => ∫ x, f x ∂(μ : Measure X) := by
  rw [continuous_iff_continuousAt]
  intro μ
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1
    tendsto_id f

/-- The map sending a probability measure to its `(j,k)` moment is continuous. -/
theorem momentIntegral_continuous
    {J : Type*} [Countable J] (j k : J) :
    Continuous fun μ : ProbabilityMeasure (ClosedComplexUnitDiskProduct J) =>
      ∫ x, diskMomentBCF j k x ∂(μ : Measure (ClosedComplexUnitDiskProduct J)) := by
  exact continuous_probability_integral_complex (diskMomentBCF j k)

/-- The closed set of probability measures satisfying one prescribed moment. -/
def momentConstraint
    {J : Type*} (h : J → J → ℂ) (j k : J) :
    Set (ProbabilityMeasure (ClosedComplexUnitDiskProduct J)) :=
  {μ | ∫ x, diskMomentBCF j k x ∂(μ : Measure (ClosedComplexUnitDiskProduct J)) =
    h j k}

/-- Closedness of one moment constraint. -/
theorem closed_moment_constraints
    {J : Type*} [Countable J]
    (h : J → J → ℂ) (j k : J) :
    IsClosed (momentConstraint h j k) := by
  exact isClosed_eq (momentIntegral_continuous j k) continuous_const

/--
Restriction of a positive-contraction kernel to a finite subtype. This is the
adapter needed before applying the finite Olevskii realization to finitely many
coordinates of a countable kernel.
-/
theorem FiniteHermitianPositiveContraction.restrictSubtype
    {J : Type*} {h : J → J → ℂ}
    (hh : FiniteHermitianPositiveContraction h) (S : Finset J) :
    FiniteHermitianPositiveContraction
      (fun a b : {j // j ∈ S} => h a b) := by
  classical
  constructor
  · intro j k
    exact hh.1 j k
  · intro F c
    let emb : {j // j ∈ S} ↪ J := ⟨Subtype.val, Subtype.val_injective⟩
    let cJ : J → ℂ := fun j => if hj : j ∈ S then c ⟨j, hj⟩ else 0
    have hquad := hh.2 (F.map emb) cJ
    have hsum_eq :
        (F.map emb).sum
            (fun j => (F.map emb).sum
              (fun k => cJ j * star (cJ k) * h j k)) =
          F.sum (fun j => F.sum
            (fun k => c j * star (c k) * h j k)) := by
      simp [Finset.sum_map, emb, cJ]
    have hnorm_eq :
        (F.map emb).sum (fun j => ‖cJ j‖ ^ 2) =
          F.sum (fun j => ‖c j‖ ^ 2) := by
      simp [Finset.sum_map, emb, cJ]
    constructor
    · change 0 ≤
        (F.sum (fun j => F.sum
          (fun k => c j * star (c k) * h j k))).re
      rw [← congrArg Complex.re hsum_eq]
      exact hquad.1
    · change
        (F.sum (fun j => F.sum
          (fun k => c j * star (c k) * h j k))).re ≤
        F.sum (fun j => ‖c j‖ ^ 2)
      rw [← congrArg Complex.re hsum_eq, ← hnorm_eq]
      exact hquad.2

/-- Coordinates appearing in a finite set of requested moment pairs. -/
def pairCoordinateFinset {J : Type*} [DecidableEq J]
    (S : Finset (J × J)) : Finset J :=
  S.image Prod.fst ∪ S.image Prod.snd

theorem pairCoordinateFinset_fst_mem
    {J : Type*} [DecidableEq J] {S : Finset (J × J)} {p : J × J}
    (hp : p ∈ S) :
    p.1 ∈ pairCoordinateFinset S := by
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)

theorem pairCoordinateFinset_snd_mem
    {J : Type*} [DecidableEq J] {S : Finset (J × J)} {p : J × J}
    (hp : p ∈ S) :
    p.2 ∈ pairCoordinateFinset S := by
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)

theorem pairCoordinateFinset_nonempty_of_nonempty
    {J : Type*} [DecidableEq J] {S : Finset (J × J)}
    (hS : S.Nonempty) :
    (pairCoordinateFinset S).Nonempty := by
  rcases hS with ⟨p, hp⟩
  exact ⟨p.1, pairCoordinateFinset_fst_mem hp⟩

/-- The restricted Lebesgue measure on the ambient `[0,1]` is a probability measure. -/
theorem μOn_unitInterval_isProbabilityMeasure :
    IsProbabilityMeasure (μOn unitInterval) := by
  constructor
  rw [μOn, Measure.restrict_apply_univ]
  simp [unitInterval, Real.volume_Icc]

/-- Build a disk-product sample from finitely many bounded coordinate functions. -/
def diskProductSample
    {J : Type*} [DecidableEq J]
    (T : Finset J)
    (a : {j // j ∈ T} → ℝ → ℂ)
    (ha_bound : ∀ j t, t ∈ unitInterval → ‖a j t‖ ≤ 1) :
    ℝ → ClosedComplexUnitDiskProduct J := by
  classical
  exact fun t j =>
    if hj : j ∈ T then
      if ht : t ∈ unitInterval then
        Complex.toClosedUnitDisk (a ⟨j, hj⟩ t) (ha_bound ⟨j, hj⟩ t ht)
      else
        zeroClosedComplexUnitDisk
    else
      zeroClosedComplexUnitDisk

theorem diskProductSample_of_mem
    {J : Type*} [DecidableEq J]
    {T : Finset J}
    {a : {j // j ∈ T} → ℝ → ℂ}
    {ha_bound : ∀ j t, t ∈ unitInterval → ‖a j t‖ ≤ 1}
    {j : J} (hj : j ∈ T) {t : ℝ} (ht : t ∈ unitInterval) :
    ((diskProductSample T a ha_bound t j : ClosedComplexUnitDisk) : ℂ) =
      a ⟨j, hj⟩ t := by
  classical
  simp [diskProductSample, hj, ht, Complex.toClosedUnitDisk]

/-- The finite disk-product sample map is measurable for the restricted unit-interval measure. -/
theorem diskProductSample_aemeasurable
    {J : Type*} [Countable J] [DecidableEq J]
    {T : Finset J}
    {a : {j // j ∈ T} → ℝ → ℂ}
    {ha_bound : ∀ j t, t ∈ unitInterval → ‖a j t‖ ≤ 1}
    (ha_meas : ∀ j, AEStronglyMeasurable (a j) (μOn unitInterval)) :
    AEMeasurable (diskProductSample T a ha_bound) (μOn unitInterval) := by
  classical
  refine AEMeasurable.of_eval ?_
  intro j
  by_cases hj : j ∈ T
  · have hraw :
        AEMeasurable
          (fun t => if ht : t ∈ unitInterval then a ⟨j, hj⟩ t else 0)
          (μOn unitInterval) := by
      refine (ha_meas ⟨j, hj⟩).aemeasurable.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      simp [ht]
    have hsub :
        AEMeasurable
          (fun t =>
            Complex.toClosedUnitDisk
              (if ht : t ∈ unitInterval then a ⟨j, hj⟩ t else 0)
              (by
                by_cases ht : t ∈ unitInterval
                · simpa [ht] using ha_bound ⟨j, hj⟩ t ht
                · simp [ht]))
          (μOn unitInterval) :=
      AEMeasurable.subtype_mk hraw
    refine hsub.congr ?_
    filter_upwards with t
    by_cases ht : t ∈ unitInterval
    · simp [diskProductSample, hj, ht, Complex.toClosedUnitDisk]
    · simp [diskProductSample, hj, ht, zeroClosedComplexUnitDisk,
        Complex.toClosedUnitDisk]
  · have hconst :
        AEMeasurable (fun _ : ℝ => zeroClosedComplexUnitDisk)
          (μOn unitInterval) :=
      measurable_const.aemeasurable
    refine hconst.congr ?_
    filter_upwards with t
    simp [diskProductSample, hj]

/-- Push the restricted unit-interval measure forward through a finite disk-product sample. -/
def diskProductSampleMeasure
    {J : Type*} [Countable J] [DecidableEq J]
    (T : Finset J)
    (a : {j // j ∈ T} → ℝ → ℂ)
    (ha_bound : ∀ j t, t ∈ unitInterval → ‖a j t‖ ≤ 1)
    (ha_meas : ∀ j, AEStronglyMeasurable (a j) (μOn unitInterval)) :
    ProbabilityMeasure (ClosedComplexUnitDiskProduct J) := by
  letI : IsProbabilityMeasure (μOn unitInterval) :=
    μOn_unitInterval_isProbabilityMeasure
  exact
    ⟨Measure.map (diskProductSample T a ha_bound) (μOn unitInterval),
      (Measure.isProbabilityMeasure_map_iff
        (diskProductSample_aemeasurable (T := T) (a := a)
          (ha_bound := ha_bound) ha_meas)).mpr inferInstance⟩

/--
Moments of the finite disk-product sample agree with the original finite
coordinate functions for coordinates in the finite coordinate set.
-/
theorem diskProductSampleMeasure_moment_of_mem
    {J : Type*} [Countable J] [DecidableEq J]
    {T : Finset J}
    {a : {j // j ∈ T} → ℝ → ℂ}
    {ha_bound : ∀ j t, t ∈ unitInterval → ‖a j t‖ ≤ 1}
    {ha_meas : ∀ j, AEStronglyMeasurable (a j) (μOn unitInterval)}
    {j k : J} (hj : j ∈ T) (hk : k ∈ T) :
    ∫ x, diskMomentBCF j k x
        ∂((diskProductSampleMeasure T a ha_bound ha_meas :
          ProbabilityMeasure (ClosedComplexUnitDiskProduct J)) :
          Measure (ClosedComplexUnitDiskProduct J)) =
      l2InnerOn unitInterval (a ⟨j, hj⟩) (a ⟨k, hk⟩) := by
  change
    ∫ x, diskMomentBCF j k x
        ∂Measure.map (diskProductSample T a ha_bound) (μOn unitInterval) =
      ∫ x, a ⟨j, hj⟩ x * star (a ⟨k, hk⟩ x) ∂μOn unitInterval
  rw [MeasureTheory.integral_map
    (diskProductSample_aemeasurable (T := T) (a := a)
      (ha_bound := ha_bound) ha_meas)
    (by
      exact (diskMomentBCF j k).continuous.measurable.aestronglyMeasurable)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  simp [diskMomentBCF, diskProductSample_of_mem (T := T) (a := a)
    (ha_bound := ha_bound) hj ht,
    diskProductSample_of_mem (T := T) (a := a) (ha_bound := ha_bound) hk ht]

/--
Finite satisfiability of moment constraints, obtained by applying the finite
Olevskii realization theorem to the coordinates appearing in the finite set of pairs and
pushing the restricted unit-interval measure forward to the full disk product.
-/
theorem finite_moment_constraints_nonempty
    {J : Type*} [Countable J]
    (h : J → J → ℂ)
    (hh : FiniteHermitianPositiveContraction h)
    (S : Finset (J × J)) :
    (⋂ p ∈ S, momentConstraint h p.1 p.2).Nonempty := by
  classical
  by_cases hS_empty : S = ∅
  · subst S
    let ν : ProbabilityMeasure (ClosedComplexUnitDiskProduct J) :=
      ⟨Measure.dirac (fun _ => zeroClosedComplexUnitDisk),
        Measure.dirac.isProbabilityMeasure⟩
    exact ⟨ν, by simp⟩
  · let T : Finset J := pairCoordinateFinset S
    have hhT :
        FiniteHermitianPositiveContraction
          (fun a b : {j // j ∈ T} => h a b) :=
      hh.restrictSubtype T
    rcases finite_complex_olevskii_gram_realization
        (fun a b : {j // j ∈ T} => h a b) hhT with
      ⟨a, ha_meas, ha_bound, ha_inner⟩
    let μ : ProbabilityMeasure (ClosedComplexUnitDiskProduct J) :=
      diskProductSampleMeasure T a ha_bound ha_meas
    refine ⟨μ, ?_⟩
    refine mem_iInter.2 ?_
    intro p
    refine mem_iInter.2 ?_
    intro hp
    have hp_fst : p.1 ∈ T := by
      exact pairCoordinateFinset_fst_mem (S := S) hp
    have hp_snd : p.2 ∈ T := by
      exact pairCoordinateFinset_snd_mem (S := S) hp
    change
      ∫ x, diskMomentBCF p.1 p.2 x
          ∂(μ : Measure (ClosedComplexUnitDiskProduct J)) =
        h p.1 p.2
    rw [diskProductSampleMeasure_moment_of_mem
      (T := T) (a := a) (ha_bound := ha_bound) (ha_meas := ha_meas)
      hp_fst hp_snd]
    exact ha_inner ⟨p.1, hp_fst⟩ ⟨p.2, hp_snd⟩

/-- Finite intersection property in the compact space of disk-product probability measures. -/
theorem moment_constraints_all_nonempty_of_finite
    {J : Type*} [Countable J]
    (h : J → J → ℂ)
    (hfinite : ∀ S : Finset (J × J),
      (⋂ p ∈ S, momentConstraint h p.1 p.2).Nonempty) :
    (⋂ p : J × J, momentConstraint h p.1 p.2).Nonempty := by
  exact CompactSpace.iInter_nonempty
    (fun p => closed_moment_constraints h p.1 p.2)
    (by
      intro S
      simpa using hfinite S)

/--
If every finite family of moment constraints is satisfiable, then there is one
probability measure satisfying all countably many constraints.
-/
theorem countable_moment_measure_of_finite_satisfiable
    {J : Type*} [Countable J]
    (h : J → J → ℂ)
    (hfinite : ∀ S : Finset (J × J),
      (⋂ p ∈ S, momentConstraint h p.1 p.2).Nonempty) :
    ∃ μ : ProbabilityMeasure (ClosedComplexUnitDiskProduct J),
      ∀ j k,
        ∫ x, diskMomentBCF j k x ∂(μ : Measure (ClosedComplexUnitDiskProduct J)) =
          h j k := by
  rcases moment_constraints_all_nonempty_of_finite h hfinite with ⟨μ, hμ⟩
  refine ⟨μ, ?_⟩
  intro j k
  exact show μ ∈ momentConstraint h j k from (mem_iInter.mp hμ (j, k))

/-- Finite-intersection step for finitely many moment constraints. -/
theorem finite_intersection_step
    {J : Type*} [Countable J]
    (h : J → J → ℂ)
    (hh : FiniteHermitianPositiveContraction h)
    (S : Finset (J × J)) :
    (⋂ p ∈ S, momentConstraint h p.1 p.2).Nonempty := by
  classical
  exact finite_moment_constraints_nonempty h hh S

/-- Countable moment measure obtained from finite satisfiability and compactness. -/
theorem countable_moment_measure
    {J : Type*} [Countable J]
    (h : J → J → ℂ)
    (hh : FiniteHermitianPositiveContraction h) :
    ∃ μ : ProbabilityMeasure (ClosedComplexUnitDiskProduct J),
      ∀ j k,
        ∫ x, diskMomentBCF j k x ∂(μ : Measure (ClosedComplexUnitDiskProduct J)) =
          h j k := by
  classical
  exact countable_moment_measure_of_finite_satisfiable h
    (fun S => finite_moment_constraints_nonempty h hh S)

end GrothendieckBessel

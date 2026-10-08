/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Statements.TheoremC
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolutionIntegrable
public import LeanPool.CaffarelliKohnNirenberg.Statements.RegularPoint
public import LeanPool.CaffarelliKohnNirenberg.Statements.SingularSet
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Topology.MetricSpace.Holder

/-!
# Time projections of the singular set

This file proves the projection and regular-neighborhood conclusions of
`lem:time-projection`.
-/

public section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal NNReal Topology
open CKN CKN.Foundation.Parabolic


namespace ESS

/-- The time-coordinate projection of a parabolic set. -/
@[expose] def parabolicTimeProjection (S : Set ParabolicPoint) : Set ℝ := Prod.snd '' S

/-- A zero one-dimensional parabolic Hausdorff measure has a Lebesgue-null
time projection. -/
theorem parabolicTimeProjection_null_of_hausdorffMeasure_zero
    (S : Set ParabolicPoint)
    (hS : parabolicHausdorffMeasure 1 S = 0) :
    volume (parabolicTimeProjection S) = 0 := by
  let f : ParabolicPoint → SnowTime :=
    fun z => Metric.Snowflaking.toSnowflaking z.2
  have hf : LipschitzWith 1 f := by
    apply LipschitzWith.of_dist_le_mul
    intro z z'
    change dist (Metric.Snowflaking.toSnowflaking z.2)
        (Metric.Snowflaking.toSnowflaking z'.2) ≤
      (1 : ℝ≥0) * dist z z'
    rw [Metric.Snowflaking.dist_toSnowflaking_toSnowflaking, Real.dist_eq,
      dist_eq_parabolicDist]
    simp only [parabolicDist, NNReal.coe_one, one_mul, Real.sqrt_eq_rpow]
    exact le_max_right _ _
  have hf_image :
      Measure.hausdorffMeasure 1 (f '' S) = 0 := by
    have himage := hf.hausdorffMeasure_image_le (by norm_num : 0 ≤ (1 : ℝ)) S
    have hS' : Measure.hausdorffMeasure 1 S = 0 := by
      simpa [parabolicHausdorffMeasure] using hS
    exact le_antisymm (by simpa [hS'] using himage) bot_le
  have hof : HolderOnWith 1 2
      (Metric.Snowflaking.ofSnowflaking : SnowTime → ℝ) Set.univ := by
    intro y hy z hz
    simp
  have hofS := hof.mono (Set.subset_univ (f '' S))
  have hof_image :
      Measure.hausdorffMeasure (1 / 2 : ℝ)
        (Metric.Snowflaking.ofSnowflaking '' (f '' S)) = 0 := by
    have hbound := hofS.hausdorffMeasure_image_le
      (by norm_num : 0 < (2 : ℝ)) (by norm_num : 0 ≤ (1 / 2 : ℝ))
    norm_num at hbound
    rw [hf_image] at hbound
    exact le_antisymm (by simpa using hbound) bot_le
  have himage :
      Metric.Snowflaking.ofSnowflaking '' (f '' S) = parabolicTimeProjection S := by
    rw [Set.image_image]
    rfl
  have hhalf : MeasureTheory.Measure.hausdorffMeasure (1 / 2 : ℝ)
      (parabolicTimeProjection S) = 0 := by
    rw [← himage]
    exact hof_image
  have hdim := MeasureTheory.Measure.hausdorffMeasure_mono
    (by norm_num : (1 / 2 : ℝ) ≤ 1) (parabolicTimeProjection S)
  rw [hhalf] at hdim
  have htime : MeasureTheory.Measure.hausdorffMeasure 1
      (parabolicTimeProjection S) = 0 := le_antisymm hdim bot_le
  simpa [MeasureTheory.hausdorffMeasure_real] using htime

/-- The set of CKN regular points in a full spatial domain. -/
@[expose] def regularPointLocus (I : Set ℝ) (u : ParabolicPoint → Vec3) :
    Set ParabolicPoint := {z | IsRegularPoint Set.univ I u z}

/-- The regular-point locus is open because a Hölder representative on a
neighborhood remains a witness at each point of that neighborhood. -/
theorem isOpen_regularPointLocus (I : Set ℝ) (u : ParabolicPoint → Vec3) :
    IsOpen (regularPointLocus I u) := by
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  change IsRegularPoint Set.univ I u z at hz
  rcases hz with ⟨hzDom, N, hNopen, hzN, hNdom, γ, hγ, hγle,
    w, hAE, hHolder⟩
  refine ⟨N, ?_, hNopen, hzN⟩
  · intro z' hz'N
    change IsRegularPoint Set.univ I u z'
    exact ⟨hNdom hz'N, N, hNopen, hz'N, hNdom, γ, hγ, hγle,
      w, hAE, hHolder⟩

/-- A compact spatial slice disjoint from the singular set has a time collar
contained in the regular-point locus. -/
theorem exists_regularTimeNeighborhood_of_time_not_singular
    (I : Set ℝ) (u : ParabolicPoint → Vec3) (t ρ : ℝ)
    (hρ : 0 < ρ) (ht : t ∈ I)
    (htSing : t ∉ parabolicTimeProjection (SingularSet Set.univ I u)) :
    ∃ δ > 0,
      closure (vec3Ball (0 : Vec3) ρ) ×ˢ Ioo (t - δ) (t + δ) ⊆
        regularPointLocus I u := by
  let K : Set ParabolicPoint := parabolicHomeomorph ⁻¹'
    (closure (vec3Ball (0 : Vec3) ρ) ×ˢ ({t} : Set ℝ))
  have hKcompact : IsCompact K := by
    have hprod : IsCompact
        (closure (vec3Ball (0 : Vec3) ρ) ×ˢ ({t} : Set ℝ) : Set (Vec3 × ℝ)) :=
      (isCompact_closure_vec3Ball hρ).prod isCompact_singleton
    exact parabolicHomeomorph.isCompact_preimage.mpr (by simpa [K] using hprod)
  have hKsubset : K ⊆ regularPointLocus I u := by
    intro z hz
    have hzprod : (z.1, z.2) ∈
        closure (vec3Ball (0 : Vec3) ρ) ×ˢ ({t} : Set ℝ) := by
      change parabolicHomeomorph z ∈
        closure (vec3Ball (0 : Vec3) ρ) ×ˢ ({t} : Set ℝ) at hz
      simpa [parabolicHomeomorph_apply] using hz
    rcases hzprod with ⟨hzBall, hzt⟩
    have hzDom : z ∈ spaceTimeSet Set.univ I := by
      change z.1 ∈ Set.univ ∧ z.2 ∈ I
      exact ⟨Set.mem_univ _, hzt ▸ ht⟩
    have hzReg : IsRegularPoint Set.univ I u z := by
      by_contra hzNotReg
      apply htSing
      rw [← hzt]
      change z.2 ∈ parabolicTimeProjection (SingularSet Set.univ I u)
      refine ⟨z, ?_, rfl⟩
      change z ∈ spaceTimeSet Set.univ I ∧ ¬ IsRegularPoint Set.univ I u z
      exact ⟨hzDom, hzNotReg⟩
    change IsRegularPoint Set.univ I u z
    exact hzReg
  obtain ⟨δ, hδ, hthick⟩ := hKcompact.exists_thickening_subset_open
    (isOpen_regularPointLocus I u) hKsubset
  refine ⟨δ ^ 2, sq_pos_of_pos hδ, ?_⟩
  intro z hz
  rcases hz with ⟨hzBall, hztime⟩
  have hzlo : t - δ ^ 2 < z.2 := hztime.1
  have hzhi : z.2 < t + δ ^ 2 := hztime.2
  have habs : |z.2 - t| < δ ^ 2 := by
    rw [abs_lt]
    constructor <;> linarith only [hzlo, hzhi]
  have hsqrt : Real.sqrt |z.2 - t| < δ :=
    (Real.sqrt_lt' hδ).2 habs
  let zP : ParabolicPoint := parabolicHomeomorph.symm z
  let zCenter : ParabolicPoint := parabolicHomeomorph.symm (z.1, t)
  have hcenterP : zCenter ∈ K := by
    change parabolicHomeomorph zCenter ∈
      closure (vec3Ball (0 : Vec3) ρ) ×ˢ ({t} : Set ℝ)
    change parabolicHomeomorph (parabolicHomeomorph.symm (z.1, t)) ∈ _
    rw [parabolicHomeomorph.apply_symm_apply]
    exact ⟨hzBall, rfl⟩
  have hdist : dist zP zCenter < δ := by
    rw [dist_eq_parabolicDist]
    simpa [zP, zCenter, parabolicHomeomorph_symm_apply, parabolicDist,
      vec3EuclideanNorm_zero, max_eq_right (Real.sqrt_nonneg _)] using hsqrt
  have hthickZ : zP ∈ Metric.thickening δ K :=
    Metric.mem_thickening_iff.mpr ⟨zCenter, hcenterP, hdist⟩
  exact hthick hthickZ

/-- For an exponent-three suitable solution with zero force on all of space,
almost every time has a regular neighborhood around every fixed compact ball.
-/
theorem timeProjection_regularNeighborhoods_of_suitable
    (I : Set ℝ) (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ)
    (hSuitable : IsSuitableWeakSolution Set.univ I 3 u Du p 0) :
    ∀ᵐ t ∂volume, t ∈ I → ∀ ρ : ℝ, 0 < ρ →
      ∃ δ > 0,
        closure (vec3Ball (0 : Vec3) ρ) ×ˢ Ioo (t - δ) (t + δ) ⊆
          regularPointLocus I u := by
  have hHaus : parabolicHausdorffMeasure 1 (SingularSet Set.univ I u) = 0 :=
    CKN.caffarelliKohnNirenberg 3 (by norm_num) Set.univ I u Du p 0 hSuitable
  have hproj := parabolicTimeProjection_null_of_hausdorffMeasure_zero
    (SingularSet Set.univ I u) hHaus
  have htgood : ∀ᵐ t ∂volume,
      t ∉ parabolicTimeProjection (SingularSet Set.univ I u) := by
    rw [ae_iff]
    simpa [parabolicTimeProjection] using hproj
  filter_upwards [htgood] with t htgood htI
  intro ρ hρ
  exact exists_regularTimeNeighborhood_of_time_not_singular I u t ρ hρ htI htgood

end ESS

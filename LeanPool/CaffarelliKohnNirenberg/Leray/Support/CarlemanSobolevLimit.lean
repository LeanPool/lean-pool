/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanSobolevApprox
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialGradient
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Weighted limits for the Carleman density argument

Finite sums of weak derivative components retain `L²` convergence, so the weighted quadratic
terms in `lem:carleman-sobolev` of the Escauriaza–Seregin–Šverák manuscript converge on a fixed
compact support neighborhood.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Pointwise
open CKN CKN.Foundation.Parabolic

noncomputable section

local instance carlemanLimitVolumeIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure (Vec3 × ℝ)) := by
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddHaarMeasure (volume : Measure Vec3) (volume : Measure ℝ)

local instance carlemanLimitVolumeIsAddLeftInvariant :
    Measure.IsAddLeftInvariant (volume : Measure (Vec3 × ℝ)) :=
  carlemanLimitVolumeIsAddHaar.toIsAddLeftInvariant

namespace CKN

private theorem tendsto_finset_sum_real
    {ι : Type*} {s : Finset ι} {f : ι → ℕ → ℝ} {g : ι → ℝ}
    (h : ∀ i ∈ s, Tendsto (f i) atTop (nhds (g i))) :
    Tendsto (fun n => ∑ i ∈ s, f i n) atTop (nhds (∑ i ∈ s, g i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      have hs : ∀ j ∈ s, Tendsto (f j) atTop (nhds (g j)) := by
        intro j hj
        exact h j (Finset.mem_insert_of_mem hj)
      simpa [Finset.sum_insert hi] using
        (h i (Finset.mem_insert_self i s)).add (ih hs)

/-- Finite sums of `Lᵖ` scalar fields remain in `Lᵖ` (`lem:carleman-sobolev`, ESS). -/
theorem memLp_finset_sum
    {X ι : Type*} [MeasurableSpace X]
    {μ : Measure X} {p : ℝ≥0∞} {f : ι → X → ℝ}
    (s : Finset ι) (h : ∀ i ∈ s, MemLp (f i) p μ) :
    MemLp (fun x => ∑ i ∈ s, f i x) p μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hs : ∀ j ∈ s, MemLp (f j) p μ := by
        intro j hj
        exact h j (Finset.mem_insert_of_mem hj)
      have hsum : (fun x => ∑ j ∈ insert i s, f j x) =
          (fun x => f i x + ∑ j ∈ s, f j x) := by
        funext x
        simp [Finset.sum_insert, hi]
      rw [hsum]
      exact (h i (Finset.mem_insert_self i s)).add (ih hs)

/-- Space-time mollification is additive for globally `L²` fields (`lem:carleman-sobolev`, ESS). -/
theorem spaceTimeMollify_add_of_memLp
    {f g : Vec3 × ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hf : MemLp f (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)))
    (hg : MemLp g (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ))) :
    spaceTimeMollify (f + g) δ hδ =
      spaceTimeMollify f δ hδ + spaceTimeMollify g δ hδ := by
  have hfc : ConvolutionExists (spaceTimeMollifier δ hδ) f
      (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure (Vec3 × ℝ)) :=
    (spaceTimeMollifier_hasCompactSupport hδ).convolutionExists_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      ((spaceTimeMollifier_contDiff hδ (n := 0)).continuous)
      (hf.locallyIntegrable (by norm_num : 1 ≤ (2 : ℝ≥0∞)))
  have hgc : ConvolutionExists (spaceTimeMollifier δ hδ) g
      (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure (Vec3 × ℝ)) :=
    (spaceTimeMollifier_hasCompactSupport hδ).convolutionExists_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      ((spaceTimeMollifier_contDiff hδ (n := 0)).continuous)
      (hg.locallyIntegrable (by norm_num : 1 ≤ (2 : ℝ≥0∞)))
  have h := hfc.distrib_add hgc
  exact h

/-- Space-time mollification commutes with finite sums of globally `L²` fields
(`lem:carleman-sobolev`, ESS). -/
theorem spaceTimeMollify_finset_sum
    {ι : Type*} {s : Finset ι} {f : ι → Vec3 × ℝ → ℝ} {δ : ℝ}
    (hδ : 0 < δ)
    (hf : ∀ i ∈ s, MemLp (f i) (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ))) :
    spaceTimeMollify (fun x => ∑ i ∈ s, f i x) δ hδ =
      fun x => ∑ i ∈ s, spaceTimeMollify (f i) δ hδ x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      funext x
      change spaceTimeMollify (0 : Vec3 × ℝ → ℝ) δ hδ x = 0
      simp [spaceTimeMollify]
  | @insert i s hi ih =>
      have hs : ∀ j ∈ s, MemLp (f j) (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)) := by
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)
      have hsum : (fun x => ∑ j ∈ insert i s, f j x) =
          (fun x => f i x + ∑ j ∈ s, f j x) := by
        funext x
        simp [Finset.sum_insert, hi]
      have hrest := memLp_finset_sum s hs
      have hlin := spaceTimeMollify_add_of_memLp hδ
        (hf i (Finset.mem_insert_self i s)) hrest
      have hrestM := ih hs
      funext x
      change spaceTimeMollify (fun y => ∑ j ∈ insert i s, f j y) δ hδ x =
        ∑ j ∈ insert i s, spaceTimeMollify (f j) δ hδ x
      rw [hsum]
      have haddfun : f i + (fun y => ∑ j ∈ s, f j y) =
          (fun y => f i y + ∑ j ∈ s, f j y) := rfl
      rw [← haddfun, hlin, hrestM]
      simp [Finset.sum_insert, hi]

private theorem weightedSq_integrable
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {ρ : X → ℝ} {C : ℝ}
    (hρ : AEStronglyMeasurable ρ μ)
    (hρbound : ∀ᵐ x ∂μ, ‖ρ x‖ ≤ C)
    {f : X → ℝ} (hf : MemLp f (2 : ℝ≥0∞) μ) :
    Integrable (fun x => ρ x * f x ^ 2) μ := by
  have hsq : Integrable (fun x => f x * f x) μ := hf.integrable_mul hf
  have hmul := hsq.mul_bdd hρ hρbound
  convert hmul using 1
  ext x
  ring

/-- A bounded measurable coefficient makes a finite weighted sum of `L²` squares integrable
(`lem:carleman-sobolev`, ESS). -/
theorem weightedPiSq_integrable
    {X ι : Type*} [MeasurableSpace X] {μ : Measure X} [Fintype ι]
    {ρ : X → ℝ} {C : ℝ} (hρ : AEStronglyMeasurable ρ μ)
    (hρbound : ∀ᵐ x ∂μ, ‖ρ x‖ ≤ C)
    {f : X → ι → ℝ} (hf : ∀ i, MemLp (fun x => f x i) (2 : ℝ≥0∞) μ) :
    Integrable (fun x => ρ x * ∑ i, (f x i) ^ 2) μ := by
  classical
  let s : Finset ι := Finset.univ
  have hterm (i : ι) : Integrable (fun x => ρ x * (f x i) ^ 2) μ :=
    weightedSq_integrable hρ hρbound (hf i)
  have hsum : Integrable (fun x => ∑ i ∈ s, ρ x * (f x i) ^ 2) μ :=
    MeasureTheory.integrable_finsetSum s (by
      intro i hi
      exact hterm i)
  have hEq : (fun x => ρ x * ∑ i, (f x i) ^ 2) =
      fun x => ∑ i ∈ s, ρ x * (f x i) ^ 2 := by
    funext x
    change ρ x * ∑ i ∈ s, (f x i) ^ 2 =
      ∑ i ∈ s, ρ x * (f x i) ^ 2
    exact Finset.mul_sum s (fun i => (f x i) ^ 2) (ρ x)
  rw [hEq]
  exact hsum

/-- If an integrand vanishes almost everywhere off a compact subset, its integral reduces to
that subset (`lem:carleman-sobolev`, ESS). -/
theorem setIntegral_eq_of_zero_off
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hBA : B ⊆ A)
    {f : X → ℝ}
    (hzero : ∀ᵐ x ∂μ, x ∈ A → x ∉ B → f x = 0) :
    (∫ x in A, f x ∂μ) = ∫ x in B, f x ∂μ := by
  have hindicator : A.indicator f =ᵐ[μ] B.indicator f := by
    filter_upwards [hzero] with x hx
    by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B
    · simp [hxA, hxB]
    · have hf0 := hx hxA hxB
      simp [hxA, hxB, hf0]
    · exact (False.elim (hxA (hBA hxB)))
    · simp [hxA, hxB]
  rw [← integral_indicator hA, ← integral_indicator hB]
  exact integral_congr_ae hindicator

/-- Space-time mollification preserves global `L²` membership (`lem:carleman-sobolev`, ESS). -/
theorem spaceTimeMollify_memLp_of_memLp
    {f : Vec3 × ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hf : MemLp f (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ))) :
    MemLp (spaceTimeMollify f δ hδ) (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)) := by
  change eLpNorm (spaceTimeMollify f δ hδ) 2 (volume : Measure (Vec3 × ℝ)) < ⊤
  exact (spaceTimeMollify_eLpNorm_le hδ hf).trans_lt hf.eLpNorm_lt_top

/-- Global `L²` convergence of mollifications restricts to every measurable subset
(`lem:carleman-sobolev`, ESS). -/
theorem tendsto_mollify_l2_restrict
    {f : Vec3 × ℝ → ℝ} (hf : MemLp f (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)))
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (nhds 0)) (hεpos : ∀ n, 0 < ε n)
    (S : Set (Vec3 × ℝ)) :
    Tendsto
      (fun n => eLpNorm
        (fun x => spaceTimeMollify f (ε n) (hεpos n) x - f x)
        2 ((volume : Measure (Vec3 × ℝ)).restrict S)) atTop (nhds 0) := by
  have hglobal := tendsto_eLpNorm_sub_zero_spaceTimeMollify hf hε hεpos
  apply ENNReal.tendsto_nhds_zero.2
  intro η hη
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hglobal η hη] with n hn
  exact (eLpNorm_restrict_le
    (fun x => spaceTimeMollify f (ε n) (hεpos n) x - f x) 2
    (volume : Measure (Vec3 × ℝ)) S).trans hn

/-- The squared Euclidean norm on Vec3 is the sum of coordinate squares
(`lem:carleman-sobolev`, ESS). -/
theorem vec3EuclideanNorm_sq (v : Vec3) :
    vec3EuclideanNorm v ^ 2 = ∑ i, (v i) ^ 2 := by
  rw [vec3EuclideanNorm, Real.sq_sqrt]
  exact Finset.sum_nonneg fun i hi => sq_nonneg (v i)

/-- A scalar field vanishes off any set containing its topological support
(`lem:carleman-sobolev`, ESS). -/
theorem value_eq_zero_of_tsupport_subset
    {f : Vec3 × ℝ → ℝ} {S : Set (Vec3 × ℝ)}
    (hfsupport : tsupport f ⊆ S) {z : Vec3 × ℝ} (hz : z ∉ S) : f z = 0 := by
  have hnot : z ∉ Function.support f := by
    intro hs
    exact hz (hfsupport (subset_tsupport f hs))
  simpa [Function.mem_support] using hnot

/-- Two coordinate sums identify with a sum over ordered coordinate pairs
(`lem:carleman-sobolev`, ESS). -/
theorem fin3_double_sum_eq_product (f : Fin 3 → Fin 3 → ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3, f i j) =
      ∑ ij : Fin 3 × Fin 3, f ij.1 ij.2 := by
  classical
  rw [← Finset.sum_product' (Finset.univ : Finset (Fin 3))
    (Finset.univ : Finset (Fin 3)) f]
  simp

/-- Bounded weights preserve convergence of finite sums of componentwise quadratic integrals.
This is the mass, gradient, and parabolic residual limit used by `lem:carleman-sobolev` (ESS). -/
theorem weightedPiSq_tendsto
    {X ι : Type*} [MeasurableSpace X] {μ : Measure X} [Fintype ι]
    {ρ : X → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hρ : AEStronglyMeasurable ρ μ)
    (hρbound : ∀ᵐ x ∂μ, ‖ρ x‖ ≤ C)
    {f : X → ι → ℝ} {fseq : ℕ → X → ι → ℝ}
    (hf : ∀ i, MemLp (fun x => f x i) (2 : ℝ≥0∞) μ)
    (hfseq : ∀ n i, MemLp (fun x => fseq n x i) (2 : ℝ≥0∞) μ)
    (hconv : ∀ i, Tendsto
      (fun n => eLpNorm (fun x => fseq n x i - f x i) (2 : ℝ≥0∞) μ)
      atTop (nhds 0)) :
    Tendsto
      (fun n => ∫ x, ρ x * ∑ i, (fseq n x i) ^ 2 ∂μ)
      atTop
      (nhds (∫ x, ρ x * ∑ i, (f x i) ^ 2 ∂μ)) := by
  classical
  let s : Finset ι := Finset.univ
  have hweight (g : X → ℝ) (hg : MemLp g (2 : ℝ≥0∞) μ) :=
    weightedSq_integrable hρ hρbound hg
  have hcomponent (i : ι) : Tendsto
      (fun n => ∫ x, ρ x * (fseq n x i) ^ 2 ∂μ)
      atTop (nhds (∫ x, ρ x * (f x i) ^ 2 ∂μ)) :=
    weightedSq_tendsto hC hρ hρbound (hf i) (fun n => hfseq n i) (hconv i)
  have hsum : Tendsto
      (fun n => ∑ i ∈ s, ∫ x, ρ x * (fseq n x i) ^ 2 ∂μ)
      atTop (nhds (∑ i ∈ s, ∫ x, ρ x * (f x i) ^ 2 ∂μ)) := by
    apply tendsto_finset_sum_real
    intro i hi
    exact hcomponent i
  have hseqint (n : ℕ) :
      (∫ x, ρ x * ∑ i, (fseq n x i) ^ 2 ∂μ) =
        ∑ i ∈ s, ∫ x, ρ x * (fseq n x i) ^ 2 ∂μ := by
    have hfun : (fun x => ρ x * ∑ i, (fseq n x i) ^ 2) =
        fun x => ∑ i ∈ s, ρ x * (fseq n x i) ^ 2 := by
      funext x
      change ρ x * ∑ i ∈ s, (fseq n x i) ^ 2 =
        ∑ i ∈ s, ρ x * (fseq n x i) ^ 2
      exact Finset.mul_sum s (fun i => (fseq n x i) ^ 2) (ρ x)
    rw [hfun]
    exact MeasureTheory.integral_finsetSum s (by
      intro i hi
      exact hweight _ (hfseq n i))
  have hlimint :
      (∫ x, ρ x * ∑ i, (f x i) ^ 2 ∂μ) =
        ∑ i ∈ s, ∫ x, ρ x * (f x i) ^ 2 ∂μ := by
    have hfun : (fun x => ρ x * ∑ i, (f x i) ^ 2) =
        fun x => ∑ i ∈ s, ρ x * (f x i) ^ 2 := by
      funext x
      change ρ x * ∑ i ∈ s, (f x i) ^ 2 =
        ∑ i ∈ s, ρ x * (f x i) ^ 2
      exact Finset.mul_sum s (fun i => (f x i) ^ 2) (ρ x)
    rw [hfun]
    exact MeasureTheory.integral_finsetSum s (by
      intro i hi
      exact hweight _ (hf i))
  simpa only [hseqint, hlimint] using hsum


end CKN

/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.RellichBallsCore

/-!
# Rellich Balls

Supporting estimates for the Navier–Stokes development.
-/

public section
open MeasureTheory
open Set Metric
open CKN.Foundation.Parabolic
open scoped ENNReal

namespace CKN.Foundation

/-- A finite cover of a compact set by equal-radius Euclidean balls admits
measurable nonnegative weights summing to one, with each weight supported in
its ball. These weights are used with the bounded-overlap ball cover in the
spatial compactness argument for lem:compactness. -/
theorem exists_measurable_weights_for_finite_vec3_ball_cover
    {K : Set Vec3} (hK : IsCompact K) {ι : Type*} [Fintype ι]
    (c : ι → Vec3) {r : ℝ} (hr : 0 < r)
    (hcover : K ⊆ ⋃ i, vec3Ball (c i) r) :
    ∃ φ : ι → Vec3 → ℝ,
      (∀ i, Measurable (φ i)) ∧
      (∀ i x, 0 ≤ φ i x ∧ φ i x ≤ 1) ∧
      (∀ x ∈ K, ∑ i, φ i x = 1) ∧
      (∀ i x, x ∉ K → φ i x = 0) ∧
      (∀ i x, x ∈ K → φ i x ≠ 0 → x ∈ vec3Ball (c i) r) := by
  classical
  let β : ContDiffBump (0 : ℝ) :=
    ⟨r ^ 2 / 2, r ^ 2, by positivity, by nlinarith only [hr]⟩
  let χ : ι → Vec3 → ℝ := fun i x => β (CKN.euclideanSqDist x (c i))
  have hχcont (i : ι) : Continuous (χ i) := by
    exact (β.contDiff.comp (CKN.contDiff_euclideanSqDist_left (c i))).continuous
  have hχmeas (i : ι) : Measurable (χ i) := (hχcont i).measurable
  have hχnonneg (i : ι) (x : Vec3) : 0 ≤ χ i x := β.nonneg
  have hχpos (i : ι) {x : Vec3} (hx : x ∈ vec3Ball (c i) r) : 0 < χ i x := by
    have hx' : x ∈ CKN.euclideanBall (c i) r := by
      rw [CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball hr]
      exact hx
    have hd : CKN.euclideanSqDist x (c i) < r ^ 2 := hx'
    have hdnonneg : 0 ≤ CKN.euclideanSqDist x (c i) := by
      exact CKN.vecNormSq_nonneg _
    have hmem : CKN.euclideanSqDist x (c i) ∈ Metric.ball (0 : ℝ) β.rOut := by
      simpa [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hdnonneg, β] using hd
    exact β.pos_of_mem_ball hmem
  have hχzero (i : ι) {x : Vec3} (hx : χ i x ≠ 0) :
      x ∈ vec3Ball (c i) r := by
    by_contra hnot
    have hd : r ^ 2 ≤ CKN.euclideanSqDist x (c i) := by
      have hnot' : x ∉ CKN.euclideanBall (c i) r := by
        rw [CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball hr]
        exact hnot
      change ¬ CKN.euclideanSqDist x (c i) < r ^ 2 at hnot'
      exact le_of_not_gt hnot'
    have hdnonneg : 0 ≤ CKN.euclideanSqDist x (c i) := by
      exact CKN.vecNormSq_nonneg _
    have hzero : χ i x = 0 := by
      apply β.zero_of_le_dist
      simpa [Real.dist_eq, sub_zero, abs_of_nonneg hdnonneg, β] using hd
    exact hx hzero
  let S : Vec3 → ℝ := fun x => ∑ i, χ i x
  have hSmeas : Measurable S := by
    exact Finset.measurable_sum _ (fun i hi => hχmeas i)
  have hSpos {x : Vec3} (hx : x ∈ K) : 0 < S x := by
    rcases Set.mem_iUnion.mp (hcover hx) with ⟨i, hi⟩
    exact (hχpos i hi).trans_le (Finset.single_le_sum
      (fun j hj => hχnonneg j x) (Finset.mem_univ i))
  let φ : ι → Vec3 → ℝ := fun i x =>
    if hx : x ∈ K then χ i x / S x else 0
  have hφmeas (i : ι) : Measurable (φ i) := by
    exact Measurable.piecewise hK.measurableSet
      ((hχmeas i).div hSmeas) measurable_const
  have hpartition (x : Vec3) (hx : x ∈ K) : ∑ i, φ i x = 1 := by
    calc
      ∑ i, φ i x = (∑ i, χ i x) / S x := by
        simp only [φ, dite_eq_left hx]
        rw [← Finset.sum_div]
      _ = 1 := by
        change (∑ i, χ i x) / (∑ i, χ i x) = 1
        exact div_self (ne_of_gt (hSpos hx))
  have hnonneg (i : ι) (x : Vec3) : 0 ≤ φ i x := by
    by_cases hx : x ∈ K
    · simp only [φ, dite_eq_left hx]
      exact div_nonneg (hχnonneg i x) (le_of_lt (hSpos hx))
    · simp [φ, hx]
  have hleone (i : ι) (x : Vec3) : φ i x ≤ 1 := by
    by_cases hx : x ∈ K
    · have hsingle : φ i x ≤ ∑ j, φ j x :=
        Finset.single_le_sum (fun j hj => hnonneg j x) (Finset.mem_univ i)
      simpa [hpartition x hx] using hsingle
    · simp [φ, hx]
  refine ⟨φ, hφmeas, ?_, hpartition, ?_, ?_⟩
  · exact fun i x => ⟨hnonneg i x, hleone i x⟩
  · intro i x hx
    simp [φ, hx]
  · intro i x hxK hφ
    have hχ : χ i x ≠ 0 := by
      intro hχzero
      simp [φ, hxK, hχzero] at hφ
    exact hχzero i hχ

/-- Squared Euclidean norm is convex under a finite partition of unity. This
is the pointwise estimate used to combine the ball-average approximations in
the local compactness argument. -/
theorem vec3EuclideanNorm_sq_weighted_sum_le
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (v : ι → Vec3)
    (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) :
    vec3EuclideanNorm (∑ i, w i • v i) ^ 2 ≤
      ∑ i, w i * vec3EuclideanNorm (v i) ^ 2 := by
  have hnormsq (x : Vec3) : vec3EuclideanNorm x ^ 2 = ∑ j, x j ^ 2 := by
    rw [vec3EuclideanNorm]
    exact Real.sq_sqrt (Finset.sum_nonneg fun j hj => sq_nonneg (x j))
  have hcoordinate (j : Fin 3) :
      (∑ i, w i * v i j) ^ 2 ≤ ∑ i, w i * (v i j) ^ 2 := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      (s := Finset.univ) (f := w) (g := fun i => w i * (v i j) ^ 2)
      (r := fun i => w i * v i j)
      (fun i hi => hw i) (fun i hi => mul_nonneg (hw i) (sq_nonneg _))
      (fun i hi => by
        calc
          (w i * v i j) ^ 2 = w i * (w i * (v i j) ^ 2) := by ring
          _ ≤ _ := le_rfl)
    have hsum' : ∑ i ∈ Finset.univ, w i = 1 := by simpa using hsum
    simpa [hsum'] using hcs
  calc
    vec3EuclideanNorm (∑ i, w i • v i) ^ 2 =
        ∑ j, (∑ i, w i * v i j) ^ 2 := by
      rw [hnormsq]
      congr 1
      ext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    _ ≤ ∑ j, ∑ i, w i * (v i j) ^ 2 :=
      Finset.sum_le_sum fun j hj => hcoordinate j
    _ = ∑ i, w i * ∑ j, (v i j) ^ 2 := by
      rw [Finset.sum_comm]
      congr 1
      ext i
      rw [Finset.mul_sum]
    _ = ∑ i, w i * vec3EuclideanNorm (v i) ^ 2 := by
      congr 1
      ext i
      rw [← hnormsq]

/-- The integral of a nonnegative density over finitely many pairwise
disjoint sets is bounded by its integral over any common containing set. -/
theorem sum_lintegral_le_of_finite_disjoint
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (t : Finset ι) (s : ι → Set α) (V : Set α) (f : α → ℝ≥0∞)
    (hdisj : Set.PairwiseDisjoint (↑t) s)
    (hmeas : ∀ i ∈ t, MeasurableSet (s i))
    (hsubset : ⋃ i ∈ t, s i ⊆ V) :
    (∑ i ∈ t, ∫⁻ x in s i, f x ∂μ) ≤ ∫⁻ x in V, f x ∂μ := by
  calc
    (∑ i ∈ t, ∫⁻ x in s i, f x ∂μ) =
        ∫⁻ x in ⋃ i ∈ t, s i, f x ∂μ := by
          symm
          exact lintegral_biUnion_finset hdisj hmeas f
    _ ≤ ∫⁻ x in V, f x ∂μ := lintegral_mono_set hsubset

end CKN.Foundation

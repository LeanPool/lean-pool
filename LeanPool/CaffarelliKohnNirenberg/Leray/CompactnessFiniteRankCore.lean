/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.RellichBalls
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessCover
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessApprox
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessStrong
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanSobolevLimit
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareConstantFinite

/-!
# Compactness Finite Rank Core

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory
open Filter
open CKN.Foundation.Parabolic
open scoped ENNReal

namespace CKN.Leray

/-- A uniform finite spatial integral on each time slice gives a finite
space-time integral on a finite time window. -/
theorem finite_lintegral_prod_of_uniform_slice_bound
    {K : Set Vec3} {J : Set ℝ} (f : ParabolicPoint → ℝ≥0∞)
    (hf : Measurable f) (hJ : MeasurableSet J)
    [IsFiniteMeasure (volume.restrict J)]
    (B : ℝ≥0∞) (hB : B < ⊤)
    (hslice : ∀ t ∈ J, ∫⁻ x in K, f (x, t) ∂volume ≤ B) :
    (∫⁻ t in J, ∫⁻ x in K, f (x, t) ∂volume) < ⊤ := by
  let A : ℝ → ℝ≥0∞ := fun t => ∫⁻ x in K, f (x, t) ∂volume
  have hA : Measurable A := by
    dsimp [A]
    exact hf.lintegral_prod_left'
  have hbound : ∫⁻ t in J, A t ∂volume ≤ B * volume J := by
    calc
      ∫⁻ t in J, A t ∂volume ≤ ∫⁻ t in J, B ∂volume := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hJ] with t ht
        exact hslice t ht
      _ = B * volume J := by
        rw [lintegral_const, Measure.restrict_apply_univ]
  have hvol : volume J < ⊤ := by
    have := measure_ne_top (volume.restrict J) Set.univ
    apply lt_top_iff_ne_top.mpr
    simpa only [Measure.restrict_apply_univ, Set.univ_inter] using this
  have hprod : B * volume J < ⊤ := ENNReal.mul_lt_top hB hvol
  exact lt_of_le_of_lt (by simpa [A] using hbound) hprod

/-- Integrating on a spatial-time rectangle agrees with the iterated
Lebesgue integral in time and then space. -/
theorem lintegral_parabolic_rectangle_eq_iterated
    {K : Set Vec3} {J : Set ℝ} (f : ParabolicPoint → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ z in K ×ˢ J, f z ∂(volume : Measure ParabolicPoint)) =
      ∫⁻ t in J, ∫⁻ x in K, f (x, t) ∂volume ∂volume := by
  change (∫⁻ z in K ×ˢ J, f z ∂((volume : Measure Vec3).prod (volume : Measure ℝ))) = _
  rw [← Measure.prod_restrict K J]
  have hfae : AEMeasurable f ((volume.restrict K).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict]
    exact hf.aemeasurable.restrict
  rw [MeasureTheory.lintegral_prod_symm f hfae]

/-- Pointwise error for a finite-rank spatial approximation assembled from
local averages with a measurable partition of unity. -/
theorem vec3_norm_sq_sub_finite_rank_average_le
    {ι : Type*} [Fintype ι] (K : Set Vec3)
    (φ : ι → Vec3 → ℝ) (a : ι → ℝ → Vec3)
    (u : Vec3) (x : Vec3) (t : ℝ)
    (hweight : ∀ i y, 0 ≤ φ i y ∧ φ i y ≤ 1)
    (hsum : x ∈ K → ∑ i, φ i x = 1)
    (hx : x ∈ K) :
    vec3EuclideanNorm
        (u - ∑ i, φ i x • a i t) ^ 2 ≤
      ∑ i, φ i x * vec3EuclideanNorm (u - a i t) ^ 2 := by
  have hsumx : ∑ i, φ i x = 1 := hsum hx
  have hidentity : u - ∑ i, φ i x • a i t =
      ∑ i, φ i x • (u - a i t) := by
    calc
      u - ∑ i, φ i x • a i t = (∑ i, φ i x) • u -
          ∑ i, φ i x • a i t := by rw [hsumx, one_smul]
      _ = ∑ i, (φ i x • u - φ i x • a i t) := by
        rw [Finset.sum_smul]
        rw [← Finset.sum_sub_distrib]
      _ = ∑ i, φ i x • (u - a i t) := by
        congr 1
        ext i
        rw [smul_sub]
  rw [hidentity]
  exact CKN.Foundation.vec3EuclideanNorm_sq_weighted_sum_le
    (fun i => φ i x) (fun i => u - a i t)
    (fun i => (hweight i x).1) hsumx

/-- A pointwise finite-rank error bound integrates to the sum of the local
errors when each summand vanishes outside its assigned spatial set. -/
theorem lintegral_error_le_sum_of_supported_terms
    {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype ι] {μ : Measure (α × β)}
    (K : Set α) (J : Set β) (B : ι → Set α)
    (e : α × β → ℝ≥0∞) (q : ι → α × β → ℝ≥0∞)
    (hK : MeasurableSet K) (hJ : MeasurableSet J)
    (hB : ∀ i, MeasurableSet (B i))
    (hpoint : ∀ z, z ∈ K ×ˢ J → e z ≤ ∑ i, q i z)
    (hsupport : ∀ i z, z ∉ B i ×ˢ (Set.univ : Set β) → q i z = 0)
    (hq : ∀ i, Measurable (q i)) :
    (∫⁻ z in K ×ˢ J, e z ∂μ) ≤
      ∑ i, ∫⁻ z in B i ×ˢ J, q i z ∂μ := by
  have hpoint' : ∀ᵐ z ∂(μ.restrict (K ×ˢ J)), e z ≤ ∑ i, q i z := by
    filter_upwards [ae_restrict_mem (hK.prod hJ)] with z hz
    exact hpoint z hz
  calc
    (∫⁻ z in K ×ˢ J, e z ∂μ) ≤
        ∫⁻ z in K ×ˢ J, ∑ i, q i z ∂μ := lintegral_mono_ae hpoint'
    _ = ∑ i, ∫⁻ z in K ×ˢ J, q i z ∂μ := by
      simpa using (lintegral_finsetSum' (μ := μ.restrict (K ×ˢ J))
        Finset.univ (f := fun i z => q i z)
        (fun i hi => (hq i).aemeasurable.restrict))
    _ ≤ ∑ i, ∫⁻ z in B i ×ˢ J, q i z ∂μ := by
      apply Finset.sum_le_sum
      intro i hi
      have hEq : (∫⁻ z in K ×ˢ J, q i z ∂μ) =
          ∫⁻ z in K ×ˢ J, (B i ×ˢ J).indicator (q i) z ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem (hK.prod hJ)] with z hz
        by_cases hzi : z ∈ B i ×ˢ J
        · simp [hzi]
        · have hzi' : z ∉ B i ×ˢ (Set.univ : Set β) := by
            intro h
            exact hzi ⟨h.1, hz.2⟩
          simp [hzi, hsupport i z hzi']
      rw [hEq]
      rw [setLIntegral_indicator (μ := μ) (s := B i ×ˢ J)
        (t := K ×ˢ J) ((hB i).prod hJ)]
      apply lintegral_mono_set
      intro z hz
      exact hz.1

/-- The measurable finite-rank average error is bounded by the sum of its
local ball errors. The weights form a partition on the compact region and
each weight is supported in its assigned ball. -/
theorem lintegral_vec3_finite_rank_average_error_le
    {ι : Type*} [Fintype ι] {μ : Measure ParabolicPoint}
    (J : Set ℝ) (K : Set Vec3) (B : ι → Set Vec3)
    (φ : ι → Vec3 → ℝ) (u : ParabolicPoint → Vec3)
    (a : ι → ℝ → Vec3)
    (hJ : MeasurableSet J) (hK : MeasurableSet K)
    (hB : ∀ i, MeasurableSet (B i))
    (hφ : ∀ i, Measurable (φ i)) (hu : Measurable u)
    (ha : ∀ i, Measurable (a i))
    (hweight : ∀ i x, 0 ≤ φ i x ∧ φ i x ≤ 1)
    (hsum : ∀ x ∈ K, ∑ i, φ i x = 1)
    (hsupport : ∀ i x, φ i x ≠ 0 → x ∈ B i) :
    (∫⁻ z in K ×ˢ J,
      ENNReal.ofReal (vec3EuclideanNorm
        (u z - ∑ i, φ i z.1 • a i z.2) ^ 2) ∂μ) ≤
      ∑ i, ∫⁻ z in B i ×ˢ J,
        ENNReal.ofReal (φ i z.1 *
          vec3EuclideanNorm (u z - a i z.2) ^ 2) ∂μ := by
  let e : ParabolicPoint → ℝ≥0∞ := fun z => ENNReal.ofReal
    (vec3EuclideanNorm (u z - ∑ i, φ i z.1 • a i z.2) ^ 2)
  let q : ι → ParabolicPoint → ℝ≥0∞ := fun i z => ENNReal.ofReal
    (φ i z.1 * vec3EuclideanNorm (u z - a i z.2) ^ 2)
  have hq (i : ι) : Measurable (q i) := by
    dsimp [q]
    have hdiff : Measurable (fun z : ParabolicPoint => u z - a i z.2) :=
      hu.sub ((ha i).comp measurable_snd)
    have hnorm : Measurable
        (fun z : ParabolicPoint => vec3EuclideanNorm (u z - a i z.2)) :=
      (continuous_vec3EuclideanNorm).measurable.comp hdiff
    have hphi : Measurable (fun z : ParabolicPoint => φ i z.1) :=
      (hφ i).comp measurable_fst
    exact ENNReal.measurable_ofReal.comp (hphi.mul (hnorm.pow_const 2))
  have he : ∀ z, z ∈ K ×ˢ J → e z ≤ ∑ i, q i z := by
    intro z hz
    have hjensen := vec3_norm_sq_sub_finite_rank_average_le K φ a
      (u z) z.1 z.2 (fun i x => hweight i x)
      (fun hx => hsum z.1 hx) hz.1
    have hsum_nonneg : ∀ i, i ∈ Finset.univ →
        0 ≤ φ i z.1 * vec3EuclideanNorm (u z - a i z.2) ^ 2 := by
      intro i hi
      exact mul_nonneg (hweight i z.1).1 (sq_nonneg _)
    have hreal : ENNReal.ofReal
        (∑ i, φ i z.1 * vec3EuclideanNorm (u z - a i z.2) ^ 2) =
        ∑ i, ENNReal.ofReal
          (φ i z.1 * vec3EuclideanNorm (u z - a i z.2) ^ 2) := by
      simpa using ENNReal.ofReal_sum_of_nonneg hsum_nonneg
    calc
      e z ≤ ENNReal.ofReal
          (∑ i, φ i z.1 * vec3EuclideanNorm (u z - a i z.2) ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        exact hjensen
      _ = ∑ i, q i z := by
        rw [hreal]
  have hsupport' : ∀ i z,
      z ∉ B i ×ˢ (Set.univ : Set ℝ) → q i z = 0 := by
    intro i z hz
    have hx : z.1 ∉ B i := by
      intro hx
      exact hz ⟨hx, Set.mem_univ z.2⟩
    have hφzero : φ i z.1 = 0 := by
      by_contra hne
      exact hx (hsupport i z.1 hne)
    simp [q, hφzero]
  have hq' : ∀ i, Measurable (q i) := hq
  have hbound := lintegral_error_le_sum_of_supported_terms (μ := μ) K J B e q
    hK hJ hB he hsupport' hq'
  change (∫⁻ z in K ×ˢ J, e z ∂μ) ≤
    ∑ i, ∫⁻ z in B i ×ˢ J, q i z ∂μ
  exact hbound

/-- Replacing each weighted local error by its full ball error preserves the
finite-rank space-time estimate. -/
theorem lintegral_vec3_finite_rank_average_error_le_unweighted
    {ι : Type*} [Fintype ι] {μ : Measure ParabolicPoint}
    (J : Set ℝ) (K : Set Vec3) (B : ι → Set Vec3)
    (φ : ι → Vec3 → ℝ) (u : ParabolicPoint → Vec3)
    (a : ι → ℝ → Vec3)
    (hJ : MeasurableSet J) (hK : MeasurableSet K)
    (hB : ∀ i, MeasurableSet (B i))
    (hφ : ∀ i, Measurable (φ i)) (hu : Measurable u)
    (ha : ∀ i, Measurable (a i))
    (hweight : ∀ i x, 0 ≤ φ i x ∧ φ i x ≤ 1)
    (hsum : ∀ x ∈ K, ∑ i, φ i x = 1)
    (hsupport : ∀ i x, φ i x ≠ 0 → x ∈ B i) :
    (∫⁻ z in K ×ˢ J,
      ENNReal.ofReal (vec3EuclideanNorm
        (u z - ∑ i, φ i z.1 • a i z.2) ^ 2) ∂μ) ≤
      ∑ i, ∫⁻ z in B i ×ˢ J,
        ENNReal.ofReal (vec3EuclideanNorm (u z - a i z.2) ^ 2) ∂μ := by
  have hweighted := lintegral_vec3_finite_rank_average_error_le (μ := μ)
    J K B φ u a hJ hK hB hφ hu ha hweight hsum hsupport
  calc
    (∫⁻ z in K ×ˢ J,
        ENNReal.ofReal (vec3EuclideanNorm
          (u z - ∑ i, φ i z.1 • a i z.2) ^ 2) ∂μ) ≤
        ∑ i, ∫⁻ z in B i ×ˢ J,
          ENNReal.ofReal (φ i z.1 *
            vec3EuclideanNorm (u z - a i z.2) ^ 2) ∂μ := hweighted
    _ ≤ ∑ i, ∫⁻ z in B i ×ˢ J,
          ENNReal.ofReal (vec3EuclideanNorm (u z - a i z.2) ^ 2) ∂μ := by
      apply Finset.sum_le_sum
      intro i hi
      apply lintegral_mono
      intro z
      apply ENNReal.ofReal_le_ofReal
      calc
        φ i z.1 * vec3EuclideanNorm (u z - a i z.2) ^ 2 ≤
            1 * vec3EuclideanNorm (u z - a i z.2) ^ 2 :=
          mul_le_mul_of_nonneg_right (hweight i z.1).2 (sq_nonneg _)
        _ = vec3EuclideanNorm (u z - a i z.2) ^ 2 := one_mul _

/-- The squared Poincare factor for equal-radius spatial balls vanishes with
the radius. -/
theorem tendsto_vec3_ball_poincare_factor_zero :
    Tendsto
      (fun n : ℕ => (CKN.sobolevPoincareL6Constant *
        (volume (CKN.euclideanBall (0 : Vec3) (1 / (n + 1)))) ^ (1 / 3 : ℝ)) ^
          (2 : ℕ)) atTop (nhds 0) := by
  let r : ℕ → ℝ := fun n => 1 / (n + 1)
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.pi * 4 / 3) ^ (1 / 3 : ℝ)
  have hr : Tendsto (fun n => ENNReal.ofReal (r n)) atTop (nhds 0) := by
    have hreal : Tendsto r atTop (nhds 0) := by
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have hcont := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using hcont
  have hvolume (n : ℕ) :
      (volume (CKN.euclideanBall (0 : Vec3) (r n))) ^ (1 / 3 : ℝ) =
        ENNReal.ofReal (r n) * c := by
    have hrpos : 0 < r n := by dsimp [r]; positivity
    rw [CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball hrpos,
      CKN.Foundation.Parabolic.volume_vec3Ball_eq]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 3)]
    rw [← ENNReal.rpow_natCast]
    rw [← ENNReal.rpow_mul]
    simp [r, c]
  have hc : c < ⊤ := by
    dsimp [c]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (by finiteness)
  have hsc : CKN.sobolevPoincareL6Constant < ⊤ :=
    CKN.sobolevPoincareL6Constant_lt_top
  let C : ℝ≥0∞ := CKN.sobolevPoincareL6Constant * c
  have hC : C < ⊤ := by
    dsimp [C]
    exact ENNReal.mul_lt_top hsc hc
  have hlin : Tendsto (fun n => C * ENNReal.ofReal (r n)) atTop (nhds 0) := by
    have hmul : Continuous (fun x : ℝ≥0∞ => C * x) := by
      exact ENNReal.continuous_const_mul hC.ne
    simpa only [Function.comp_def, mul_zero] using
      hmul.continuousAt.tendsto.comp hr
  have hfactor : Tendsto
      (fun n => CKN.sobolevPoincareL6Constant *
        (volume (CKN.euclideanBall (0 : Vec3) (r n))) ^ (1 / 3 : ℝ))
      atTop (nhds 0) := by
    have heq :
        (fun n => CKN.sobolevPoincareL6Constant *
          (volume (CKN.euclideanBall (0 : Vec3) (r n))) ^ (1 / 3 : ℝ)) =
        (fun n => C * ENNReal.ofReal (r n)) := by
      funext n
      rw [hvolume n]
      simp [C, mul_left_comm, mul_comm]
    rw [heq]
    exact hlin
  have hsq :=
    (ENNReal.continuous_rpow_const (y := (2 : ℝ))).continuousAt.tendsto.comp hfactor
  have hrw : (fun n : ℕ => (CKN.sobolevPoincareL6Constant *
        (volume (CKN.euclideanBall (0 : Vec3) (1 / (n + 1)))) ^
          (1 / 3 : ℝ)) ^ (2 : ℕ)) =
      (fun n => (CKN.sobolevPoincareL6Constant *
        (volume (CKN.euclideanBall (0 : Vec3) (r n))) ^ (1 / 3 : ℝ)) ^ 2) := by
    funext n
    simp [r]
  rw [hrw]
  let F : ℕ → ℝ≥0∞ := fun n =>
    CKN.sobolevPoincareL6Constant *
      (volume (CKN.euclideanBall (0 : Vec3) (r n))) ^ (1 / 3 : ℝ)
  have hpow : (fun n => F n ^ (2 : ℕ)) = (fun n => F n ^ (2 : ℝ)) := by
    funext n
    exact (ENNReal.rpow_natCast (F n) 2).symm
  rw [hpow]
  have hsq' := hsq
  rw [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] at hsq'
  simpa only [F, Function.comp_def] using hsq'

/-- The integrated finite-rank error coefficient is eventually smaller than
any prescribed tolerance when the local gradient energy is uniformly bounded. -/
theorem eventually_small_colored_ball_energy_factor
    {N : ℕ} (G : ℝ≥0∞) (hG : G < ⊤) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ n : ℕ in atTop,
      3 * (CKN.sobolevPoincareL6Constant *
        (volume (CKN.euclideanBall (0 : Vec3) (1 / (n + 1)))) ^
          (1 / 3 : ℝ)) ^ (2 : ℕ) *
      (∑ _j : Fin N, G) ≤ ε := by
  intro ε hε
  let A : ℕ → ℝ≥0∞ := fun n =>
    (CKN.sobolevPoincareL6Constant *
      (volume (CKN.euclideanBall (0 : Vec3) (1 / (n + 1)))) ^
        (1 / 3 : ℝ)) ^ (2 : ℕ)
  let D : ℝ≥0∞ := 3 * ∑ _j : Fin N, G
  have hD : D < ⊤ := by
    dsimp [D]
    exact ENNReal.mul_lt_top (by norm_num)
      (ENNReal.sum_lt_top.mpr fun _ _ => hG)
  have hA : Tendsto A atTop (nhds 0) := by
    simpa only [A] using tendsto_vec3_ball_poincare_factor_zero
  have hmul : Tendsto (fun n => D * A n) atTop (nhds 0) := by
    have hcont : Continuous (fun x : ℝ≥0∞ => D * x) :=
      ENNReal.continuous_const_mul hD.ne
    simpa only [Function.comp_def, mul_zero] using
      hcont.continuousAt.tendsto.comp hA
  have hsmall : ∀ᶠ n in atTop, D * A n ≤ ε :=
    (ENNReal.tendsto_nhds_zero.mp hmul) ε hε
  filter_upwards [hsmall] with n hn
  have heq : D * A n = 3 * A n * (∑ _j : Fin N, G) := by
    dsimp [D]
    ac_rfl
  rw [← heq]
  exact hn

/-- A finite family of spatial balls split into finitely many disjoint colors
has total local gradient energy bounded by the number of colors times the
energy on its containing set. -/
theorem sum_lintegral_ball_gradient_energy_le_of_coloring
    {ι : Type*} [Fintype ι] {N : ℕ} {U : Set Vec3} {J : Set ℝ}
    (B : ι → Set Vec3) (color : ι → Fin N)
    (f : ParabolicPoint → ℝ≥0∞)
    (hB : ∀ i, MeasurableSet (B i))
    (hsubset : ∀ i, B i ⊆ U)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j → Disjoint (B i) (B j))
    (hf : Measurable f) :
    (∑ i, ∫⁻ t in J, ∫⁻ x in B i, f (x,t) ∂volume ∂volume) ≤
      ∑ _j : Fin N, ∫⁻ t in J, ∫⁻ x in U, f (x,t) ∂volume ∂volume := by
  classical
  let G : ℝ → ℝ≥0∞ := fun t => ∫⁻ x in U, f (x,t) ∂volume
  have hG : Measurable G := hf.lintegral_prod_left'
  let E : ι → ℝ≥0∞ := fun i => ∫⁻ t in J, ∫⁻ x in B i, f (x,t) ∂volume
  have hpartition :
      (∑ i, E i) = ∑ j : Fin N, ∑ i : {i : ι // color i = j}, E i.1 := by
    let e : ι ≃ Σ j : Fin N, {i : ι // color i = j} := {
      toFun := fun i => ⟨color i, ⟨i, rfl⟩⟩
      invFun := fun p => p.2.1
      left_inv := by intro i; rfl
      right_inv := by
        rintro ⟨j, ⟨i, hij⟩⟩
        cases hij
        rfl }
    calc
      (∑ i, E i) = ∑ p : Σ j : Fin N, {i : ι // color i = j}, E p.2.1 :=
        Fintype.sum_equiv e E (fun p => E p.2.1) (by intro i; rfl)
      _ = ∑ j : Fin N, ∑ i : {i : ι // color i = j}, E i.1 := by
        simpa using Fintype.sum_sigma'
          (fun j (i : {i : ι // color i = j}) => E i.1)
  have hcolor (j : Fin N) :
      (∑ i : {i : ι // color i = j}, E i.1) ≤
        ∫⁻ t in J, G t ∂volume := by
    let D : Finset {i : ι // color i = j} := Finset.univ
    have hdisj : Set.PairwiseDisjoint
        (↑D : Set {i : ι // color i = j}) (fun i => B i.1) := by
      intro i hi k hk hne
      apply Set.disjoint_left.mpr
      intro y hyi hyk
      have hik : i.1 ≠ k.1 := by
        intro heq
        apply hne
        exact Subtype.ext heq
      have hsame : color i.1 = color k.1 := i.2.trans k.2.symm
      exact (hdisjoint i.1 k.1 hik hsame).le_bot ⟨hyi, hyk⟩
    have hmeas : ∀ i ∈ D, MeasurableSet (B i.1) := by
      intro i hi
      exact hB i.1
    have hcover' : Set.iUnion (fun i : {i : ι // color i = j} => B i.1) ⊆ U := by
      intro y hy
      rcases Set.mem_iUnion.mp hy with ⟨i, hi⟩
      exact hsubset i.1 hi
    have hcover : ⋃ i ∈ D, B i.1 ⊆ U := by
      simpa [D] using hcover'
    have hspace (t : ℝ) :
        (∑ i : {i : ι // color i = j}, ∫⁻ x in B i.1, f (x,t) ∂volume) ≤
          G t := by
      change (∑ i ∈ D, ∫⁻ x in B i.1, f (x,t) ∂volume) ≤ G t
      exact CKN.Foundation.sum_lintegral_le_of_finite_disjoint D
        (fun i => B i.1) U (fun x => f (x,t)) hdisj hmeas hcover
    have hq (i : {i : ι // color i = j}) : Measurable (fun t : ℝ =>
        ∫⁻ x in B i.1, f (x,t) ∂volume) := by
      exact (hf).lintegral_prod_left'
    calc
      (∑ i : {i : ι // color i = j}, E i.1) =
          ∫⁻ t in J, ∑ i : {i : ι // color i = j},
            ∫⁻ x in B i.1, f (x,t) ∂volume ∂volume := by
        symm
        simpa [E] using (lintegral_finsetSum' (μ := volume.restrict J)
          Finset.univ (f := fun i t => ∫⁻ x in B i.1, f (x,t) ∂volume)
          (fun i hi => (hq i).aemeasurable.restrict))
      _ ≤ ∫⁻ t in J, G t ∂volume := by
        apply lintegral_mono
        exact hspace
  calc
    (∑ i, E i) = ∑ j : Fin N, ∑ i : {i : ι // color i = j}, E i.1 := hpartition
    _ ≤ ∑ _j : Fin N, ∫⁻ t in J, G t ∂volume :=
      Finset.sum_le_sum fun j hj => hcolor j
    _ = ∑ _j : Fin N, ∫⁻ t in J, ∫⁻ x in U, f (x,t) ∂volume ∂volume := rfl


end CKN.Leray

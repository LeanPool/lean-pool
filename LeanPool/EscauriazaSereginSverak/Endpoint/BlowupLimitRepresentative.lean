/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.WeakContL3Result
public import Mathlib.MeasureTheory.Covering.Differentiation
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Group.Measure

/-!
# Jointly measurable representatives of weakly continuous slices

Ball averages turn a weakly continuous family of spatial `L³` classes into a
jointly measurable pointwise field without changing any time slice almost
everywhere.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal Topology Pointwise symmDiff
open CKN CKN.Foundation.Parabolic

local instance : Fact (1 ≤ ENNReal.ofReal (3 / 2 : ℝ)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
noncomputable section

namespace ESS

/-- The spatial ball on which the blow-up representative is defined. -/
@[expose] def blowupRepresentativeDomain : Set Vec3 :=
  vec3Ball (0 : Vec3) (3 / 4 : ℝ)

/-- The positive radii tending to zero used to form local averages. -/
@[expose] def blowupRepresentativeRadius (n : ℕ) : ℝ :=
  ((n : ℝ) + 1)⁻¹

/-- The closed ball centered at `x` with the `n`th averaging radius. -/
@[expose] def blowupRepresentativeBall (x : Vec3) (n : ℕ) : Set Vec3 :=
  Metric.closedBall x (blowupRepresentativeRadius n)

/-- The part of the averaging ball contained in the representative domain. -/
@[expose] def blowupRepresentativeTestSet (x : Vec3) (n : ℕ) : Set Vec3 :=
  blowupRepresentativeDomain ∩ blowupRepresentativeBall x n

/-- Volume restricted to the spatial domain of the representative. -/
abbrev blowupRepresentativeMeasure : Measure Vec3 :=
  volume.restrict blowupRepresentativeDomain

private instance blowupRepresentativeMeasureFinite :
    IsFiniteMeasure blowupRepresentativeMeasure := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top

theorem blowupRepresentative_testSet_finite (x : Vec3) (n : ℕ) :
    blowupRepresentativeMeasure (blowupRepresentativeTestSet x n) ≠ ⊤ :=
  (measure_lt_top blowupRepresentativeMeasure _).ne

/-- The constant coordinate test on the local test set in the dual `L^{3/2}` space. -/
@[expose] noncomputable def blowupRepresentativeIndicator
    (n : ℕ) (x : Vec3) (i : Fin 3) :
  Lp L2Vec3 (ENNReal.ofReal (3 / 2 : ℝ))
      blowupRepresentativeMeasure :=
  indicatorConstLp (ENNReal.ofReal (3 / 2 : ℝ))
    (show MeasurableSet (blowupRepresentativeTestSet x n) from
      (isOpen_vec3Ball (0 : Vec3) (3 / 4 : ℝ)).measurableSet.inter
        (show MeasurableSet (blowupRepresentativeBall x n) from
          Metric.isClosed_closedBall.measurableSet))
    (blowupRepresentative_testSet_finite x n)
    (weakContL3VecToLp (Pi.single i (1 : ℝ)))

/-- The normalized integral of one velocity coordinate over the local test set. -/
@[expose] noncomputable def blowupRepresentativeCoordinateAverage
    (v : Icc (-(3 / 4 : ℝ) ^ 2) 0 →
      Lp L2Vec3 3 blowupRepresentativeMeasure)
    (n : ℕ) (x : Vec3) (t : Icc (-(3 / 4 : ℝ) ^ 2) 0) (i : Fin 3) : ℝ :=
  (volume.real (Metric.closedBall (0 : Vec3)
    (blowupRepresentativeRadius n)))⁻¹ *
      ∫ y, inner ℝ (v t y)
        (blowupRepresentativeIndicator n x i y) ∂blowupRepresentativeMeasure

/-- The vector of coordinate averages at radius indexed by `n`. -/
@[expose] noncomputable def blowupRepresentativeApprox
    (v : Icc (-(3 / 4 : ℝ) ^ 2) 0 →
      Lp L2Vec3 3 blowupRepresentativeMeasure)
    (n : ℕ) (x : Vec3) (t : Icc (-(3 / 4 : ℝ) ^ 2) 0) : Vec3 :=
  fun i => blowupRepresentativeCoordinateAverage v n x t i

/-- The weakly continuous slice, set to zero outside its domain. -/
@[expose] def blowupRepresentativeRaw
    (v : Icc (-(3 / 4 : ℝ) ^ 2) 0 →
      Lp L2Vec3 3 blowupRepresentativeMeasure)
    (t : Icc (-(3 / 4 : ℝ) ^ 2) 0) (x : Vec3) : Vec3 :=
  blowupRepresentativeDomain.indicator
    (fun y => weakContL3OfLp (v t y)) x

private theorem blowupRepresentative_inner_coordinate
    (z : L2Vec3) (i : Fin 3) :
    inner ℝ z (weakContL3VecToLp (Pi.single i (1 : ℝ))) =
      weakContL3OfLp z i := by
  simp [weakContL3VecToLp, weakContL3OfLp, PiLp.inner_apply]

private theorem blowupRepresentative_raw_memLp
    (v : Icc (-(3 / 4 : ℝ) ^ 2) 0 →
      Lp L2Vec3 3 blowupRepresentativeMeasure)
    (t : Icc (-(3 / 4 : ℝ) ^ 2) 0) :
    MemLp (blowupRepresentativeRaw v t) 3 volume := by
  change MemLp (blowupRepresentativeDomain.indicator
    (fun x => weakContL3OfLp (v t x))) 3 volume
  unfold blowupRepresentativeDomain
  rw [memLp_indicator_iff_restrict
    ((isOpen_vec3Ball (0 : Vec3) (3 / 4 : ℝ)).measurableSet)]
  exact (Lp.memLp (v t)).continuousLinearMap_comp weakContL3OfLp

private theorem blowupRepresentative_raw_coordinate_memLp
    (v : Icc (-(3 / 4 : ℝ) ^ 2) 0 →
      Lp L2Vec3 3 blowupRepresentativeMeasure)
    (t : Icc (-(3 / 4 : ℝ) ^ 2) 0) (i : Fin 3) :
    MemLp (fun x => blowupRepresentativeRaw v t x i) 3 volume := by
  exact (blowupRepresentative_raw_memLp v t).continuousLinearMap_comp
    (ContinuousLinearMap.proj (R := ℝ) i)

/-- The integral pairing of an `L³` field with an `L^{3/2}` test on the restricted domain. -/
@[expose] noncomputable def blowupRepresentativePairing
    (f : Lp L2Vec3 3 blowupRepresentativeMeasure) :
    Lp L2Vec3 (ENNReal.ofReal (3 / 2 : ℝ))
      blowupRepresentativeMeasure → ℝ :=
  fun g => ∫ y, inner ℝ (f y) (g y) ∂blowupRepresentativeMeasure

private theorem blowupRepresentative_testSet_measurable (x : Vec3) (n : ℕ) :
    MeasurableSet (blowupRepresentativeTestSet x n) := by
  exact (isOpen_vec3Ball (0 : Vec3) (3 / 4 : ℝ)).measurableSet.inter
    Metric.isClosed_closedBall.measurableSet

private theorem blowupRepresentative_integral_indicator
    {v : Icc (-(3 / 4 : ℝ) ^ 2) 0 →
      Lp L2Vec3 3 blowupRepresentativeMeasure}
    (n : ℕ) (x : Vec3) (t : Icc (-(3 / 4 : ℝ) ^ 2) 0) (i : Fin 3) :
    (∫ y, inner ℝ (v t y)
      (blowupRepresentativeIndicator n x i y) ∂blowupRepresentativeMeasure) =
      ∫ y in blowupRepresentativeTestSet x n,
        inner ℝ (v t y) (weakContL3VecToLp (Pi.single i (1 : ℝ)))
          ∂blowupRepresentativeMeasure := by
  calc
    _ = ∫ y, inner ℝ (v t y)
        ((blowupRepresentativeTestSet x n).indicator
          (fun _ => weakContL3VecToLp (Pi.single i (1 : ℝ))) y)
        ∂blowupRepresentativeMeasure := by
          apply integral_congr_ae
          filter_upwards [indicatorConstLp_coeFn
            (p := ENNReal.ofReal (3 / 2 : ℝ))
            (hs := blowupRepresentative_testSet_measurable x n)
            (hμs := blowupRepresentative_testSet_finite x n)
            (c := weakContL3VecToLp (Pi.single i (1 : ℝ)))] with y hy
          change blowupRepresentativeIndicator n x i y = _ at hy
          rw [hy]
    _ = ∫ y, (blowupRepresentativeTestSet x n).indicator
        (fun y => inner ℝ (v t y)
          (weakContL3VecToLp (Pi.single i (1 : ℝ)))) y
        ∂blowupRepresentativeMeasure := by
          apply integral_congr_ae
          filter_upwards [] with y
          by_cases hy : y ∈ blowupRepresentativeTestSet x n <;>
            simp [hy]
    _ = ∫ y in blowupRepresentativeTestSet x n,
        inner ℝ (v t y) (weakContL3VecToLp (Pi.single i (1 : ℝ)))
          ∂blowupRepresentativeMeasure :=
            integral_indicator (blowupRepresentative_testSet_measurable x n)

private theorem blowupRepresentative_average_eq_setAverage
    (v : Icc (-(3 / 4 : ℝ) ^ 2) 0 →
      Lp L2Vec3 3 blowupRepresentativeMeasure)
    (n : ℕ) (x : Vec3) (t : Icc (-(3 / 4 : ℝ) ^ 2) 0) (i : Fin 3)
    (hball : blowupRepresentativeBall x n ⊆ blowupRepresentativeDomain) :
    blowupRepresentativeCoordinateAverage v n x t i =
      ⨍ y in blowupRepresentativeBall x n,
        blowupRepresentativeRaw v t y i ∂volume := by
  have htest : blowupRepresentativeTestSet x n =
      blowupRepresentativeBall x n :=
    inter_eq_right.mpr hball
  have hrestrict :
      blowupRepresentativeMeasure.restrict (blowupRepresentativeBall x n) =
        volume.restrict (blowupRepresentativeBall x n) := by
    change (volume.restrict blowupRepresentativeDomain).restrict
      (blowupRepresentativeBall x n) = _
    exact Measure.restrict_restrict_of_subset hball
  have hnum :
      (∫ y, inner ℝ (v t y)
        (blowupRepresentativeIndicator n x i y) ∂blowupRepresentativeMeasure) =
        ∫ y in blowupRepresentativeBall x n,
          blowupRepresentativeRaw v t y i ∂volume := by
    rw [blowupRepresentative_integral_indicator, htest, hrestrict]
    apply setIntegral_congr_fun Metric.isClosed_closedBall.measurableSet
    intro y hy
    change inner ℝ (v t y) (weakContL3VecToLp (Pi.single i (1 : ℝ))) =
      blowupRepresentativeRaw v t y i
    rw [blowupRepresentative_inner_coordinate]
    simp [blowupRepresentativeRaw, hball hy]
  have hvol : volume.real (Metric.closedBall (0 : Vec3)
      (blowupRepresentativeRadius n)) =
      volume.real (blowupRepresentativeBall x n) := by
    have hmeasure : volume (Metric.closedBall (0 : Vec3)
        (blowupRepresentativeRadius n)) =
        volume (Metric.closedBall x (blowupRepresentativeRadius n)) := by
      have hpre : (fun y : Vec3 => x +ᵥ y) ⁻¹'
          Metric.closedBall x (blowupRepresentativeRadius n) =
          Metric.closedBall (0 : Vec3) (blowupRepresentativeRadius n) := by
        ext y
        change dist (x + y) x ≤ blowupRepresentativeRadius n ↔
          dist y 0 ≤ blowupRepresentativeRadius n
        have hdist : dist (x + y) x = dist y 0 := by
          rw [dist_eq_norm, dist_eq_norm]
          congr 1
          abel
        rw [hdist]
      calc
        volume (Metric.closedBall (0 : Vec3)
            (blowupRepresentativeRadius n)) =
            volume ((fun y : Vec3 => x +ᵥ y) ⁻¹'
              Metric.closedBall x (blowupRepresentativeRadius n)) := by
                rw [hpre]
        _ = volume (Metric.closedBall x (blowupRepresentativeRadius n)) :=
          (measurePreserving_vadd x volume).measure_preimage
            Metric.isClosed_closedBall.nullMeasurableSet
    change (volume (Metric.closedBall (0 : Vec3)
      (blowupRepresentativeRadius n))).toReal =
        (volume (Metric.closedBall x (blowupRepresentativeRadius n))).toReal
    exact congrArg ENNReal.toReal hmeasure
  unfold blowupRepresentativeCoordinateAverage
  rw [hnum, setAverage_eq, smul_eq_mul, hvol]

private theorem blowupRepresentative_pairing_lipschitz
    (f : Lp L2Vec3 3 blowupRepresentativeMeasure) :
    LipschitzWith
      ⟨(eLpNorm f 3 blowupRepresentativeMeasure).toReal,
        ENNReal.toReal_nonneg⟩
      (blowupRepresentativePairing f) := by
  apply LipschitzWith.of_dist_le_mul
  intro g h
  have hf : MemLp (fun y : Vec3 => f y) 3 blowupRepresentativeMeasure :=
    Lp.memLp f
  have hg : MemLp (fun y : Vec3 => g y)
      (ENNReal.ofReal (3 / 2 : ℝ)) blowupRepresentativeMeasure :=
    Lp.memLp g
  have hh : MemLp (fun y : Vec3 => h y)
      (ENNReal.ofReal (3 / 2 : ℝ)) blowupRepresentativeMeasure :=
    Lp.memLp h
  have hdiff : MemLp (fun y : Vec3 => (g - h) y)
      (ENNReal.ofReal (3 / 2 : ℝ)) blowupRepresentativeMeasure := by
    exact (Lp.memLp (g - h))
  have hgInt := weakContL3_integral_holder hf hg
  have hhInt := weakContL3_integral_holder hf hh
  have hdiffInt := weakContL3_integral_holder hf hdiff
  have hsub : blowupRepresentativePairing f g -
      blowupRepresentativePairing f h =
      ∫ y, inner ℝ (f y) ((g - h) y) ∂blowupRepresentativeMeasure := by
    unfold blowupRepresentativePairing
    rw [← integral_sub hgInt.1 hhInt.1]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub g h] with y hy
    rw [hy]
    simp [inner_sub_right]
  have hnorm :
      (eLpNorm (fun y : Vec3 => (g - h) y)
        (ENNReal.ofReal (3 / 2 : ℝ)) blowupRepresentativeMeasure).toReal =
        dist g h := by
    rw [Lp.dist_def]
    congr 1
    exact eLpNorm_congr_ae (Lp.coeFn_sub g h)
  rw [Real.dist_eq, hsub]
  calc
    ‖∫ y, inner ℝ (f y) ((g - h) y) ∂blowupRepresentativeMeasure‖ ≤
        (eLpNorm f 3 blowupRepresentativeMeasure).toReal *
          (eLpNorm (fun y : Vec3 => (g - h) y)
            (ENNReal.ofReal (3 / 2 : ℝ)) blowupRepresentativeMeasure).toReal :=
              hdiffInt.2
    _ = (eLpNorm f 3 blowupRepresentativeMeasure).toReal * dist g h := by
      rw [hnorm]

private theorem blowupRepresentative_radius_pos (n : ℕ) :
    0 < blowupRepresentativeRadius n := by
  dsimp [blowupRepresentativeRadius]
  positivity

private theorem blowupRepresentative_ball_translate (x y : Vec3) (r : ℝ) :
    Metric.closedBall y r = (y - x) +ᵥ Metric.closedBall x r := by
  ext z
  change dist z y ≤ r ↔ ∃ w ∈ Metric.closedBall x r, (y - x) + w = z
  constructor
  · intro hz
    refine ⟨z - (y - x), ?_, ?_⟩
    · change dist (z - (y - x)) x ≤ r
      have hdist : dist (z - (y - x)) x = dist z y := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        abel
      rw [hdist]
      exact hz
    · simp [sub_eq_add_neg, add_left_comm, add_assoc]
  · rintro ⟨w, hw, rfl⟩
    change dist w x ≤ r at hw
    have hdist : dist ((y - x) + w) y = dist w x := by
      rw [dist_eq_norm, dist_eq_norm]
      congr 1
      abel
    rw [hdist]
    exact hw

private theorem blowupRepresentative_ball_symmDiff_tendsto
    (x : Vec3) (r : ℝ) :
    Tendsto (fun y : Vec3 => volume
      (Metric.closedBall y r ∆ Metric.closedBall x r)) (𝓝 x) (𝓝 0) := by
  let K : Set Vec3 := Metric.closedBall x r
  have hKcompact : IsCompact K := isCompact_closedBall x r
  have hKclosed : IsClosed K := Metric.isClosed_closedBall
  have hplus : Tendsto (fun δ : Vec3 => volume ((δ +ᵥ K) \ K))
      (𝓝 0) (𝓝 0) :=
    tendsto_measure_vadd_sdiff_isCompact_isClosed hKcompact hKclosed
  have hminus : Tendsto (fun δ : Vec3 => volume ((-δ +ᵥ K) \ K))
      (𝓝 0) (𝓝 0) := by
    have hneg : Tendsto (fun δ : Vec3 => -δ) (𝓝 0) (𝓝 0) := by
      convert continuous_neg.tendsto (0 : Vec3) using 1
      simp
    exact hplus.comp hneg
  have hsecond (δ : Vec3) :
      volume (K \ (δ +ᵥ K)) = volume ((-δ +ᵥ K) \ K) := by
    have hpre : (fun z : Vec3 => δ +ᵥ z) ⁻¹' (K \ (δ +ᵥ K)) =
        (-δ +ᵥ K) \ K := by
      rw [preimage_sdiff, preimage_vadd, preimage_vadd]
      simp
    have hmeas : NullMeasurableSet (K \ (δ +ᵥ K)) volume := by
      have htrans : δ +ᵥ K = Metric.closedBall (δ + x) r := by
        change δ +ᵥ Metric.closedBall x r = Metric.closedBall (δ + x) r
        rw [blowupRepresentative_ball_translate x (δ + x) r]
        congr 1
        abel
      rw [htrans]
      exact (hKclosed.measurableSet.diff
        Metric.isClosed_closedBall.measurableSet).nullMeasurableSet
    rw [← hpre]
    exact ((measurePreserving_vadd δ volume).measure_preimage hmeas).symm
  have hsum : Tendsto (fun δ : Vec3 =>
      volume ((δ +ᵥ K) \ K) + volume ((-δ +ᵥ K) \ K)) (𝓝 0) (𝓝 0) :=
    by simpa using hplus.add hminus
  have htranslated (δ : Vec3) :
      volume ((δ +ᵥ K) ∆ K) =
        volume ((δ +ᵥ K) \ K) + volume ((-δ +ᵥ K) \ K) := by
    have htrans : δ +ᵥ K = Metric.closedBall (δ + x) r := by
      change δ +ᵥ Metric.closedBall x r = Metric.closedBall (δ + x) r
      rw [blowupRepresentative_ball_translate x (δ + x) r]
      congr 1
      abel
    rw [measure_symmDiff_eq]
    · rw [hsecond]
    · rw [htrans]
      exact Metric.isClosed_closedBall.measurableSet.nullMeasurableSet
    · exact hKclosed.measurableSet.nullMeasurableSet
  have hdelta : Tendsto (fun y : Vec3 => y - x) (𝓝 x) (𝓝 0) := by
    have hdelta' : Tendsto (fun y : Vec3 => y - x) (𝓝 x) (𝓝 (x - x)) := by
      have hcont : Continuous (fun y : Vec3 => y - x) := by fun_prop
      exact hcont.tendsto x
    simpa using hdelta'
  have hEq : (fun y : Vec3 => volume
      (Metric.closedBall y r ∆ Metric.closedBall x r)) =
      (fun y => volume (((y - x) +ᵥ K) ∆ K)) := by
    funext y
    rw [blowupRepresentative_ball_translate x y r]
  rw [hEq]
  exact (hsum.comp hdelta).congr' (Eventually.of_forall fun y =>
    (htranslated (y - x)).symm)

private theorem blowupRepresentative_testSet_symmDiff_tendsto
    (n : ℕ) (x : Vec3) :
    Tendsto (fun y : Vec3 => (volume.restrict blowupRepresentativeDomain)
      (blowupRepresentativeTestSet y n ∆ blowupRepresentativeTestSet x n))
      (𝓝 x) (𝓝 0) := by
  let A (y : Vec3) := blowupRepresentativeBall y n
  let D := blowupRepresentativeDomain
  let μ := volume.restrict D
  have hball := blowupRepresentative_ball_symmDiff_tendsto x
    (blowupRepresentativeRadius n)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hev := (ENNReal.tendsto_nhds_zero.mp hball) ε hε
  have hle (y : Vec3) : μ (blowupRepresentativeTestSet y n ∆
      blowupRepresentativeTestSet x n) ≤ volume (A y ∆ A x) := by
    have hsubset : blowupRepresentativeTestSet y n ∆
        blowupRepresentativeTestSet x n ⊆ A y ∆ A x := by
      intro z hz
      simp only [blowupRepresentativeTestSet, A, mem_symmDiff,
        mem_inter_iff] at hz ⊢
      tauto
    have hEmeas : MeasurableSet (A y ∆ A x) := by
      exact (Metric.isClosed_closedBall.measurableSet.symmDiff
        Metric.isClosed_closedBall.measurableSet)
    calc
      μ (blowupRepresentativeTestSet y n ∆ blowupRepresentativeTestSet x n) ≤
          μ (A y ∆ A x) := measure_mono hsubset
      _ = volume (D ∩ (A y ∆ A x)) := by
        rw [Measure.restrict_apply hEmeas]
        rw [inter_comm]
      _ ≤ volume (A y ∆ A x) := measure_mono inter_subset_right
  filter_upwards [hev] with y hy
  calc
    μ (blowupRepresentativeTestSet y n ∆ blowupRepresentativeTestSet x n) ≤
        volume (A y ∆ A x) := hle y
    _ ≤ ε := hy

private theorem blowupRepresentative_indicator_continuous
    (n : ℕ) (i : Fin 3) :
    Continuous (fun x : Vec3 => blowupRepresentativeIndicator n x i) := by
  change Continuous (fun x : Vec3 => indicatorConstLp
    (ENNReal.ofReal (3 / 2 : ℝ))
    (blowupRepresentative_testSet_measurable x n)
    (blowupRepresentative_testSet_finite x n)
    (weakContL3VecToLp (Pi.single i (1 : ℝ))) )
  apply continuous_indicatorConstLp_set
    (p := ENNReal.ofReal (3 / 2 : ℝ))
    (μ := blowupRepresentativeMeasure)
    (s := fun x => blowupRepresentativeTestSet x n)
    (hs := fun x => blowupRepresentative_testSet_measurable x n)
    (hμs := fun x => blowupRepresentative_testSet_finite x n)
    (c := weakContL3VecToLp (Pi.single i (1 : ℝ)))
  · norm_num
  · intro x
    exact blowupRepresentative_testSet_symmDiff_tendsto n x

private theorem blowupRepresentative_approx_continuous_space
    (v : Icc (-(3 / 4 : ℝ) ^ 2) 0 →
      Lp L2Vec3 3 blowupRepresentativeMeasure)
    (n : ℕ) (t : Icc (-(3 / 4 : ℝ) ^ 2) 0) :
    Continuous (fun x => blowupRepresentativeApprox v n x t) := by
  apply continuous_pi
  intro i
  have hpair := (blowupRepresentative_pairing_lipschitz (v t)).continuous
  have hcomp := hpair.comp (blowupRepresentative_indicator_continuous n i)
  change Continuous (fun x =>
    (volume.real (Metric.closedBall (0 : Vec3)
      (blowupRepresentativeRadius n)))⁻¹ *
        blowupRepresentativePairing (v t)
          (blowupRepresentativeIndicator n x i))
  exact continuous_const.mul hcomp

private theorem blowupRepresentative_approx_continuous_time
    (v : Icc (-(3 / 4 : ℝ) ^ 2) 0 →
      Lp L2Vec3 3 blowupRepresentativeMeasure)
    (hweak : ∀ w : Lp L2Vec3 (ENNReal.ofReal (3 / 2 : ℝ))
        blowupRepresentativeMeasure,
      Continuous (fun t => ∫ x, inner ℝ (v t x) (w x)
        ∂blowupRepresentativeMeasure))
    (n : ℕ) (x : Vec3) :
    Continuous (fun t => blowupRepresentativeApprox v n x t) := by
  apply continuous_pi
  intro i
  have h := hweak (blowupRepresentativeIndicator n x i)
  change Continuous (fun t =>
    (volume.real (Metric.closedBall (0 : Vec3)
      (blowupRepresentativeRadius n)))⁻¹ *
      ∫ y, inner ℝ (v t y) (blowupRepresentativeIndicator n x i y)
        ∂blowupRepresentativeMeasure)
  exact continuous_const.mul h

private theorem blowupRepresentative_approx_jointly_measurable
    (v : Icc (-(3 / 4 : ℝ) ^ 2) 0 →
      Lp L2Vec3 3 blowupRepresentativeMeasure)
    (hweak : ∀ w : Lp L2Vec3 (ENNReal.ofReal (3 / 2 : ℝ))
        blowupRepresentativeMeasure,
      Continuous (fun t => ∫ x, inner ℝ (v t x) (w x)
        ∂blowupRepresentativeMeasure))
    (n : ℕ) :
    Measurable (Function.uncurry (fun x t =>
      blowupRepresentativeApprox v n x t)) := by
  apply measurable_uncurry_of_continuous_of_measurable
  · intro t
    exact blowupRepresentative_approx_continuous_space v n t
  · intro x
    exact (blowupRepresentative_approx_continuous_time v hweak n x).measurable

private theorem blowupRepresentative_radius_tendsto :
    Tendsto blowupRepresentativeRadius atTop (𝓝[>] (0 : ℝ)) := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hzero : Tendsto blowupRepresentativeRadius atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0)
    exact tendsto_inv_atTop_zero.comp hden
  rw [tendsto_nhdsWithin_iff]
  refine ⟨hzero, Filter.Eventually.of_forall ?_⟩
  intro n
  exact blowupRepresentative_radius_pos n

private theorem blowupRepresentative_eventually_ball_subset
    (x : Vec3) (hx : x ∈ blowupRepresentativeDomain) :
    ∀ᶠ n in atTop,
      blowupRepresentativeBall x n ⊆ blowupRepresentativeDomain := by
  have hnhds : blowupRepresentativeDomain ∈ 𝓝 x :=
    (isOpen_vec3Ball (0 : Vec3) (3 / 4 : ℝ)).mem_nhds hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  have hr0 : Tendsto blowupRepresentativeRadius atTop (𝓝 0) :=
    (tendsto_nhdsWithin_iff.mp blowupRepresentative_radius_tendsto).1
  have hsmall : ∀ᶠ n in atTop, blowupRepresentativeRadius n < ε :=
    hr0.eventually (eventually_lt_nhds hε)
  filter_upwards [hsmall] with n hn y hy
  apply hball
  apply Metric.mem_ball.mpr
  have hy' : dist y x ≤ blowupRepresentativeRadius n := by
    simpa [blowupRepresentativeBall] using hy
  exact hy'.trans_lt hn

private theorem blowupRepresentative_coordinate_tendsto_ae
    (v : Icc (-(3 / 4 : ℝ) ^ 2) 0 →
      Lp L2Vec3 3 blowupRepresentativeMeasure)
    (t : Icc (-(3 / 4 : ℝ) ^ 2) 0) (i : Fin 3) :
    ∀ᵐ x ∂blowupRepresentativeMeasure,
      Tendsto (fun n => blowupRepresentativeApprox v n x t i)
        atTop (𝓝 (blowupRepresentativeRaw v t x i)) := by
  let f : Vec3 → ℝ := fun x => blowupRepresentativeRaw v t x i
  have hloc : LocallyIntegrable f volume := by
    exact (blowupRepresentative_raw_coordinate_memLp v t i).locallyIntegrable
      (by norm_num)
  have hldt := (Besicovitch.vitaliFamily volume).ae_tendsto_average hloc
  filter_upwards [ae_restrict_of_ae hldt,
    ae_restrict_mem ((isOpen_vec3Ball (0 : Vec3) (3 / 4 : ℝ)).measurableSet)]
    with x hldt hx
  have hr := (Besicovitch.tendsto_filterAt volume x).comp
    blowupRepresentative_radius_tendsto
  have havg : Tendsto
      (fun n => ⨍ y in blowupRepresentativeBall x n, f y ∂volume)
      atTop (𝓝 (f x)) := hldt.comp hr
  have hball := blowupRepresentative_eventually_ball_subset x hx
  have hseq : (fun n => blowupRepresentativeApprox v n x t i) =ᶠ[atTop]
      (fun n => ⨍ y in blowupRepresentativeBall x n, f y ∂volume) := by
    filter_upwards [hball] with n hn
    exact blowupRepresentative_average_eq_setAverage v n x t i hn
  exact Tendsto.congr' hseq.symm havg

/-- Weakly continuous local `L³` slices have a jointly measurable pointwise
representative whose every time slice agrees almost everywhere with the
given class. The representative is obtained from spatial ball averages and
Lebesgue differentiation. -/
theorem weakContL3_jointlyMeasurableRepresentative
    (v : Icc (-(3 / 4 : ℝ) ^ 2) 0 →
      Lp L2Vec3 3
        (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))))
    (hweak : ∀ (w : Lp L2Vec3 (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ)))),
      Continuous (fun t => ∫ x, inner ℝ (v t x) (w x)
        ∂(volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))))) :
    ∃ W : Vec3 × Icc (-(3 / 4 : ℝ) ^ 2) 0 → Vec3,
      Measurable W ∧ ∀ t,
        (fun x => W (x, t)) =ᵐ[volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))]
          (fun x => weakContL3OfLp (v t x)) := by
  let W : Vec3 × Icc (-(3 / 4 : ℝ) ^ 2) 0 → Vec3 := fun z i =>
    limsup (fun n => blowupRepresentativeApprox v n z.1 z.2 i) atTop
  have hW : Measurable W := by
    apply measurable_pi_iff.mpr
    intro i
    apply Measurable.limsup
    intro n
    have hn := blowupRepresentative_approx_jointly_measurable v hweak n
    have hn' : Measurable (fun z : Vec3 × Icc (-(3 / 4 : ℝ) ^ 2) 0 =>
        blowupRepresentativeApprox v n z.1 z.2) := by
      change Measurable (Function.uncurry (fun x t =>
        blowupRepresentativeApprox v n x t))
      exact hn
    exact (measurable_pi_apply i).comp hn'
  refine ⟨W, hW, ?_⟩
  intro t
  have hcoord (i : Fin 3) :
      (fun x => W (x, t) i) =ᵐ[blowupRepresentativeMeasure]
        (fun x => weakContL3OfLp (v t x) i) := by
    have hlim := blowupRepresentative_coordinate_tendsto_ae v t i
    filter_upwards [hlim,
      ae_restrict_mem ((isOpen_vec3Ball (0 : Vec3) (3 / 4 : ℝ)).measurableSet)]
      with x hlim hx
    have hpoint := hlim.limsup_eq
    have hraw : blowupRepresentativeRaw v t x i =
        weakContL3OfLp (v t x) i := by
      unfold blowupRepresentativeRaw
      rw [Set.indicator_of_mem hx]
      rfl
    exact hpoint.trans hraw
  have hall : ∀ᵐ x ∂blowupRepresentativeMeasure,
      ∀ i : Fin 3, W (x,t) i = weakContL3OfLp (v t x) i :=
    ae_all_iff.mpr hcoord
  filter_upwards [hall] with x hx
  ext i
  exact hx i

end ESS
